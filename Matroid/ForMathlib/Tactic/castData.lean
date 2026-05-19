/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Init
public import Lean.Meta.Tactic.Simp
public import Batteries.Logic

/-!
# Simproc for pulling `Eq.rec` / `▸` through function application spines

This module registers a simproc `castData` that finds an index transport in any argument
position of a constant-headed application. It first pulls that transport out of the prefix
application with `congr_eqRec_out`, then pushes the resulting outer transport through the
remaining tail arguments with `castData_eqRec_app`.

The implementation uses a single loop over argument positions and a single loop over tail
arguments; failures return `.continue`, and all produced proofs are kernel checked.
-/

theorem congr_eqRec_out {α : Sort*} {β : α → Sort*} {γ : α → Sort*} {x x' : α}
    (f : (i : α) → β i → γ i) (h : x = x') (y : β x) : f x' (h ▸ y) = h ▸ (f x y) := by
  cases h
  rfl

theorem castData_eqRec_app {α : Sort*} {x x' : α} {A : α → Sort*}
    {B : (i : α) → A i → Sort*}
    (h : x = x') (f : (a : A x) → B x a) (y : A x') :
    (h ▸ f) y = h ▸ f (h.symm ▸ y) := by
  cases h
  rfl

public meta section

open Lean Meta Simp

private structure EqRecArgData where
  ι : Expr
  a : Expr
  b : Expr
  h : Expr
  x : Expr
  β : Expr

private def parseEqRecArg? (arg : Expr) : MetaM (Option EqRecArgData) := do
  let castArg ← withTransparency .all <| whnf arg
  unless castArg.isAppOfArity ``Eq.rec 6 do return none
  let #[ι, a, motive, x, b, h] := castArg.getAppArgs | return none
  -- Recover `β : ι → Sort _` from `motive : (i : ι) → a = i → Sort _`,
  -- assuming `motive`'s body does not depend on the equality binder. This is the standard form
  -- elaborated by `▸` for index transport.
  let .lam _ _ (.lam _ _ body _) _ := motive | return none
  if body.hasLooseBVar 0 then return none
  let β := Expr.lam `i ι (body.lowerLooseBVars 1 1) .default
  return some ⟨ι, a, b, h, x, β⟩

private def mkTypeFamily (ι b ty : Expr) : MetaM (Option Expr) := do
  try
    let tyAbs ← kabstract ty b
    withLocalDeclD `i ι fun iVar => do
      some <$> mkLambdaFVars #[iVar] (tyAbs.instantiate1 iVar)
  catch e =>
    throw e

private def castArgAlongEq (A h t : Expr) : MetaM (Option Expr) := do
  try
    some <$> mkAppOptM ``Eq.ndrec #[none, none, some A, some t, none, ← mkEqSymm h]
  catch e =>
    throw e

private def mkCodomainFamily (ι b A lhsAcc : Expr) : MetaM (Option Expr) := do
  try
    let lhsAccTy ← whnf (← inferType lhsAcc)
    let lhsAccTyAbs ← kabstract lhsAccTy b
    withLocalDeclD `i ι fun iVar => do
      let lhsAccTy_i := lhsAccTyAbs.instantiate1 iVar
      let .forallE name _ body_i _ := lhsAccTy_i | return none
      let A_i ← whnf (mkApp A iVar)
      withLocalDeclD name A_i fun yVar => do
        some <$> mkLambdaFVars #[iVar, yVar] (body_i.instantiate1 yVar)
  catch _ =>
    return none

private def ensureEqProofFor (e proof : Expr) : MetaM (Option Expr) := do
  unless ← isTypeCorrect proof do return none
  let some (_, lhs, rhs) := (← inferType proof).eq? | return none
  let lhs ← instantiateMVars lhs
  let rhs ← instantiateMVars rhs
  unless ← withTransparency .all <| isDefEq lhs e do return none
  return some rhs

private def rhsOfEqProof? (proof : Expr) : MetaM (Option Expr) := do
  let some (_, _, rhs) := (← inferType proof).eq? | return none
  return some (← instantiateMVars rhs)

private def mkPrefixFamily (head : Expr) (args : Array Expr) (k : Nat) (ι β b : Expr) :
    MetaM (Option Expr) := do
  try
    withTransparency .all <| withLocalDeclD `i ι fun iVar => do
      withLocalDeclD `z (β.beta #[iVar]) fun zVar => do
        let mut parts : Array Expr := #[]
        for j in List.range k do
          parts := parts.push ((← kabstract args[j]! b).instantiate1 iVar)
        parts := parts.push zVar
        some <$> mkLambdaFVars #[iVar, zVar] (mkAppN head parts)
  catch _ =>
    return none

private def tryAt (e head : Expr) (args : Array Expr) (k : Nat) : MetaM (Option Simp.Result) := do
  let some d ← parseEqRecArg? args[k]! | return none
  let prefixB := args.extract 0 k
  let tail := args.extract (k + 1) args.size
  let mut lhsAcc := mkAppN head (prefixB.push args[k]!)
  let prefixAKab ← prefixB.mapM (kabstract · d.b)
  let mut inner := mkAppN head (prefixAKab.map (·.instantiate1 d.a) |>.push d.x)
  let some f ← mkPrefixFamily head args k d.ι d.β d.b | return none
  unless ← isTypeCorrect f do
    return none
  try
    let mut proof ← withTransparency .all <| mkAppM ``congr_eqRec_out #[f, d.h, d.x]
    proof ← instantiateMVars proof
    let some _ ← ensureEqProofFor lhsAcc proof | throwError "castData: prefix proof check failed"
    for t in tail do
      let proofApp ← mkCongrFun proof t
      let some A ← mkTypeFamily d.ι d.b (← inferType t) |
        throwError "castData: tail domain family failed"
      let some B ← mkCodomainFamily d.ι d.b A lhsAcc |
        throwError "castData: tail codomain family failed"
      let some tCast ← castArgAlongEq A d.h t | throwError "castData: tail cast failed"
      let step ← withTransparency .all <|
        mkAppOptM ``castData_eqRec_app
          #[none, none, none, some A, some B, some d.h, some inner, some t]
      unless ← isTypeCorrect step do throwError "castData: tail step ill-typed"
      proof ← mkEqTrans proofApp step
      proof ← instantiateMVars proof
      lhsAcc := mkApp lhsAcc t
      inner := mkApp inner tCast
      let _ := lhsAcc
    let some rhs ← rhsOfEqProof? proof | throwError "castData: final proof check failed"
    return some { expr := rhs, proof? := some proof }
  catch e =>
    throw e

/-- Simproc: pull index transports through constant-headed application spines. -/
simproc castData (_) := fun e => do
  let head := e.getAppFn
  let .const _ _ := head | return .continue
  if head.isConstOf ``Eq.rec then return .continue
  let args := e.getAppArgs
  if args.isEmpty then return .continue
  for k in List.range args.size do
    let idx := args.size - 1 - k
    if let some r ← tryAt e head args idx then
      return .visit r
  return .continue

end
