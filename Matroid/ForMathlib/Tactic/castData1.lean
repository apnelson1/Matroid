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
# Simproc for pulling `Eq.rec` / `▸` through the final argument of a function application

This module registers a simproc `castData` that rewrites `f ... (h ▸ x)` to `h ▸ f ... x`
when the final argument reduces to `Eq.rec` in the shape produced by index transport (the
motive's body does not depend on the equality proof binder).

`simp` may try this simproc on many applications; if the head is not amenable to the lemma,
`mkAppM` fails and the simproc returns `.continue`. Soundness is enforced by the kernel.

Only the **final** argument is inspected; nested transports are handled by repeated `simp`
passes.
-/

theorem congr_eqRec_out {α : Sort*} {β : α → Sort*} {γ : α → Sort*} {x x' : α}
    (f : (i : α) → β i → γ i) (h : x = x') (y : β x) : f x' (h ▸ y) = h ▸ (f x y) := by
  cases h
  rfl

public meta section

open Lean Meta Simp

/-- Simproc that rewrites `f ... (h ▸ x) ↦ h ▸ f ... x` when the final argument is `Eq.rec`
in the standard index-transport form. Uses `congr_eqRec_out`. -/
simproc castData (_) := fun e => do
  let head := e.getAppFn
  let .const _ _ := head | return .continue
  let args := e.getAppArgs
  if args.isEmpty then return .continue
  let castArg ← withTransparency .all <| whnf args[args.size - 1]!
  unless castArg.isAppOfArity ``Eq.rec 6 do return .continue
  let #[ι, _a, motive, x, b, h] := castArg.getAppArgs | return .continue
  -- Recover `β : ι → Sort _` from `motive : (i : ι) → a = i → Sort _`,
  -- assuming `motive`'s body does not depend on the equality binder. This is the standard form
  -- elaborated by `▸` for index transport.
  let .lam _ _ (.lam _ _ body _) _ := motive | return .continue
  if body.hasLooseBVar 0 then return .continue
  let β := Expr.lam `i ι (body.lowerLooseBVars 1 1) .default
  let earlyArgs := args.pop
  try
    let earlyArgsKab ← earlyArgs.mapM (kabstract · b)
    let f ← withTransparency .all <| withLocalDeclD `i ι fun iVar => do
      let earlyArgsAtI := earlyArgsKab.map (·.instantiate1 iVar)
      withLocalDeclD `z (β.beta #[iVar]) fun zVar => do
        mkLambdaFVars #[iVar, zVar] <| mkAppN head (earlyArgsAtI.push zVar)
    let proof ← withTransparency .all <| mkAppM ``congr_eqRec_out #[f, h, x]
    let some (_, _lhs, rhs) := (← inferType proof).eq? | return .continue
    return .visit { expr := rhs, proof? := some proof }
  catch _ =>
    return .continue

end
