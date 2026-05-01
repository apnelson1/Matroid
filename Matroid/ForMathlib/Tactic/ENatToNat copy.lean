import Mathlib.Data.Ineq
import Mathlib.Tactic.ENatToNat

open Lean Meta Mathlib.Tactic Qq

/-! ### Rule-based expression decomposition

A uniform walker `decomposeWith` traverses an expression and, at each node, consults a
`RuleSet` to decide whether to recurse (and into which argument positions), to stop
silently, or (on fall-through) to register the node as an atom via `AtomM.addAtom`.
Rule sets are just functions `Name → Option DecompRule`, so they compose with `|||`.
-/

/-- What to do with an expression whose head constant matches a rule. -/
inductive DecompRule
  /-- Recurse into the listed argument positions (0-based into the full app args array). -/
  | recurse (argIdxs : Array Nat)
  /-- Stop here; do not atomize this subexpression. -/
  | skip
  deriving Inhabited

/-- A rule set maps a head constant name to a decomposition rule. -/
abbrev RuleSet := Name → Option DecompRule

/-- Rules for propositional connectives and (in)equality heads. -/
def logicBundle : RuleSet
  | ``And | ``Or | ``Iff                  => some (.recurse #[0, 1])
  | ``Not                                 => some (.recurse #[0])
  | ``LE.le | ``LT.lt | ``GE.ge | ``GT.gt => some (.recurse #[2, 3])
  | ``Eq  | ``Ne                          => some (.recurse #[1, 2])
  | _                                     => none

/-- Rules for algebraic operations. -/
def algBundle : RuleSet
  | ``HAdd.hAdd | ``HSub.hSub | ``HMul.hMul | ``HDiv.hDiv | ``HPow.hPow => some (.recurse #[4, 5])
  | ``Min.min | ``Max.max => some (.recurse #[2, 3])
  | ``Neg.neg | ``Inv.inv => some (.recurse #[2])
  | ``OfNat.ofNat | ``Nat.cast | ``NatCast.natCast | ``Int.cast | ``IntCast.intCast | ``Top.top
  | ``Bot.bot | ``Zero.zero | ``One.one => some .skip
  | _ => none

def allRules : RuleSet := fun n => logicBundle n <|> algBundle n

/-- Walk `e` using `rs`. If a rule fires, follow it; otherwise, register `e` as an
atom (via `AtomM.addAtom`) iff `shouldAtomize e` is `true`. Non-dependent arrows
`a → b` are always recursed through like a binary logical connective. -/
partial def decomposeWith (rs : RuleSet) (shouldAtomize : Expr → MetaM Bool)
    (e : Expr) : AtomM Unit := do
  let e ← whnfR e
  if let some (a, b) := e.arrow? then
    decomposeWith rs shouldAtomize a; decomposeWith rs shouldAtomize b; return
  let (fn, args) := e.getAppFnArgs
  match rs fn with
  | some (.recurse idxs) => for i in idxs do decomposeWith rs shouldAtomize args[i]!
  | some .skip => return
  | none => if ← shouldAtomize e then let _ ← AtomM.addAtom e

def shouldAtomizeOfType (ty : Expr) (e : Expr) : MetaM Bool := do
  isDefEq (← inferType e) ty

/-- Collect the atoms of `g`'s hypotheses and target, using the supplied rule set
and atomization predicate. -/
def atoms (rs : RuleSet) (shouldAtomize : Expr → MetaM Bool) (g : MVarId) :
    AtomM (Array Expr) := g.withContext do
  for hyp in (← getLCtx) do
    decomposeWith rs shouldAtomize (← inferType hyp.toExpr)
  decomposeWith rs shouldAtomize (← g.getType)
  return (← get).atoms

-- this should exist in the library
def Array.zipLeft {α : Type} (l : Array α) (ns : Array Name) : Array (α × Option Name) :=
  let out := l.toList.zipLeft ns.toList
  out.toArray

/-- Generalize atoms collected via `atomsWith rs shouldAtomize g` in the local
hypotheses and goal of `g`, using `ns` as suggested variable names. -/
def generalizeAtomsWith (rs : RuleSet) (shouldAtomize : Expr → MetaM Bool) (ns : Array Name)
    (g : MVarId) : MetaM MVarId := do
  let atomsWithNames :=
    ((← (atoms rs shouldAtomize g).run .reducible).filter fun e ↦ !e.isFVar).zipLeft ns
  let args : Array GeneralizeArg := atomsWithNames.map fun (e, n) ↦ { expr := e, xName? := n }
  let (_, _, g') ← g.generalizeHyp args ((← getLocalHyps).map (·.fvarId!))
  return g'

/-- Generalize every maximal subexpression of type `ty` (under `enatRules`-style
logical/algebraic structure) in the goal and hypotheses, using `ns` as suggested
variable names. -/
def generalizeAtomsOfType (ty : Expr) (ns : Array Name) (g : MVarId) : MetaM MVarId :=
  generalizeAtomsWith allRules (shouldAtomizeOfType ty) ns g

/-- `generalize_all t` generalizes every maximal subexpression of type `t` in the
goal and all hypotheses to fresh variables. Use `generalize_all t with x y z` to
supply custom names. -/
elab "generalize_all" t:term " with" e:(ppSpace colGt ident)* : tactic => do
  let ty ← Elab.Tactic.elabTerm t none
  let names := e.map TSyntax.getId
  Elab.Tactic.liftMetaTactic' (generalizeAtomsOfType ty names)

elab "generalize_all" t:term : tactic => do
  let ty ← Elab.Tactic.elabTerm t none
  Elab.Tactic.liftMetaTactic' (generalizeAtomsOfType ty #[])

/-! ### Shadowing `enat_to_nat` with an `optConfig`

The version imported from `Mathlib.Tactic.ENatToNat` takes no arguments. We shadow it here
with a variant that accepts a boolean configuration flag. Writing `enat_to_nat +generalize`
first runs `generalize_all ENat` on the goal, matching the behaviour of `enat_to_nat!`.
-/

namespace Mathlib.Tactic.ENatToNat

/-- Configuration for the `enat_to_nat` tactic. -/
structure Config where
  /-- If `true`, first generalize every `ENat`-valued subterm in the goal and
  hypotheses to a fresh variable before running `enat_to_nat`. -/
  generalize : Bool := false
  deriving Inhabited

/-- Elaborates a `Config` from an `optConfig` syntax. -/
declare_config_elab elabConfig Config

end Mathlib.Tactic.ENatToNat

open Lean Elab Tactic Parser.Tactic Mathlib.Tactic.ENatToNat in
/-- `enat_to_nat` shifts all `ENat`s in the context to `Nat`, rewriting propositions about them.
A typical use case is `enat_to_nat; omega`.

The flag `+generalize` first generalizes every maximal `ENat`-valued subterm in the goal
and hypotheses to a fresh variable, so that e.g. `f x + f y` becomes a pair of variables
that `enat_to_nat` (and then `omega`) can reason about. -/
elab (name := enatToNatCfg) "enat_to_nat" cfg:optConfig : tactic => do
  let config ← elabConfig cfg
  if config.generalize then
    evalTactic (← `(tactic| generalize_all ENat))
  evalTactic (← `(tactic| focus (
      (repeat' cases_first_enat) <;>
      (try simp only [enat_to_nat_top, enat_to_nat_coe] at *)
    )))

/-- `enat_to_nat!` is shorthand for `enat_to_nat +generalize`. -/
macro "enat_to_nat!" : tactic => `(tactic| enat_to_nat +generalize)

/-- `enat_to_nat! with x y z` generalizes `ENat`-valued atoms to the named variables
before running `enat_to_nat`. -/
macro "enat_to_nat!" " with" e:(ppSpace colGt ident)* : tactic =>
  `(tactic| (generalize_all ENat with $e*; enat_to_nat))

/-- `eomega` is `enat_to_nat +generalize <;> omega`. -/
macro "eomega" : tactic => `(tactic| (enat_to_nat +generalize <;> omega))

-- Missing lemmas from the `enat_to_nat` simpset.
attribute [enat_to_nat_top] not_true add_top and_true true_and or_false false_or imp_false
  false_iff true_iff iff_true iff_false true_or or_true Nat.cast_le Nat.cast_lt false_imp_iff
  true_imp_iff false_and and_false

-- /-! ### Tests -/
variable {f : ℤ → ℕ∞}

example {a : ℤ} (h : 3 ≤ f a) : f a ≠ 0 := by
  eomega
  -- generalize_enats; omega

example {a b c : ℕ∞} {x : ℤ} (h : (f x + b) < f x) : a ≠ ⊤ := by
  eomega
  -- generalize_enats <;> omega

example {f : ℤ → ℕ∞} {a b e : ℤ} (h : 2 * f e + f a + f b ≤ f a) : 2 * f a ≤ 3 * f a + f b := by
  eomega
  -- generalize_enats; omega

example {P : ℕ∞ → Prop} {a b c : ℕ∞} (ha : ¬ P a) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  eomega
  -- generalize_enats; omega

example (a b c d : ℕ∞) (x : ℤ) (hab : a ≤ b) (hbc : 2 * f x + d < c) : f x ≠ ⊤ := by
  eomega

example {a : ℤ} : 0 ≤ f a := by
  eomega
  -- generalize_enats; omega

example {a b : ℤ} (h1 : ¬ (f a ≠ 0 ∧ 1 ≤ f a)): 0 ≤ f b := by
  eomega
  -- generalize_enats; omega

/-! ### Replacing `enat_to_nat`. -/


-- open Qq Lean Elab Tactic Term Meta in
-- elab "foo" : tactic => do
--   let g ← getMainGoal
--   g.withContext do
--     _

-- open Qq Lean Elab Tactic Term Meta in
-- /-- Finds the first `ENat` in the context and applies the `cases` tactic to it.
-- Then simplifies expressions involving `⊤` using the `enat_to_nat_top` simp set. -/
-- elab "cases_first_enat" : tactic => focus do
--   let g ← getMainGoal
--   g.withContext do
--     let ctx ← getLCtx
--     let decl? ← ctx.findDeclM? fun decl => do
--       if ← (isExprDefEq (← inferType decl.toExpr) q(ENat)) then
--         return Option.some decl
--       else
--         return Option.none
--     let some decl := decl? | throwError "No ENats"
--     let isInaccessible := ctx.inaccessibleFVars.find? (·.fvarId == decl.fvarId) |>.isSome
--     if isInaccessible then
--       let name : Name := `enat_to_nat_aux
--       setGoals [← g.rename decl.fvarId name]
--       let x := mkIdent name
--       evalTactic (← `(tactic| cases $x:ident using ENat.recTopCoe))
--     else
--       let x := mkIdent decl.userName
--       evalTactic
--         (← `(tactic| cases $x:ident using ENat.recTopCoe with | top => _ | coe $x:ident => _))
--     evalTactic (← `(tactic| all_goals try simp only [enat_to_nat_top] at *))
-- /-
-- `enat_to_nat` shifts all `ENat`s in the context to `Nat`, rewriting propositions about them.
-- A typical use case is `enat_to_nat; omega`. -/
-- macro "enat_to_nat" : tactic => `(tactic| focus (
--     (repeat' cases_first_enat) <;>
--     (try simp only [enat_to_nat_top, enat_to_nat_coe] at *)
--   )
-- )
--

/-! ### Tinkering -/


-- open Qq Lean Elab Tactic Term Meta in
-- def foo (toRecurse : List Expr) (g : MVarId) : TacticM MVarId := g.withContext do
--   Lean.logInfo m!"input : {toRecurse}"
--   match toRecurse with
--   | [] => return g
--   | a :: vars =>
--     Lean.logInfo m!"now : {a}, {vars}"
--     let some n := a.name? | return g
--     let x := mkIdent n
--     evalTactic
--       (← `(tactic | have h : 0 = 0 := rfl))
--     evalTactic
--       (← `(tactic| cases $x:ident using ENat.recTopCoe with | top => _ | coe $x:ident => _))
--     foo vars g

-- open Qq Lean Elab Tactic Term Meta in
-- def bar (g : MVarId) : TacticM MVarId := g.withContext do
--   let atoms ← AtomM.run .reducible (atoms g)
--   -- Lean.logInfo m!"{atoms}"
--   let atoms₁ := atoms.filter Expr.isFVar
--   let g' ← foo atoms₁.toList g
--   return g'

-- open Qq Lean Elab Tactic Term Meta in
-- elab "test'" : tactic => do
--   let g ← getMainGoal
--   g.withContext do
--     let g' ← bar g


--   evalTactic (← `(tactic| have h : 0 = 0 := rfl))



-- example {a b : ℕ∞} (hab : a ≤ b)  : 0 ≤ a := by
--   test'


/-! ### Oddities -/

-- WTF : from `Matroid.Connectivity.Higher`. Look into this.

-- lemma TutteConnected.contract {C : Set α} (h : M.TutteConnected (k + M.eRk C + 1))
--     (hnt : 2 * (k + M.eRk C) < M.E.encard + 1) (e : α) : (M ／ C).TutteConnected (k + 1) := by
--   obtain rfl | hne := eq_or_ne k 0
--   · simp
--   wlog hCE : C ⊆ M.E generalizing C with aux
--   · specialize aux (C := C ∩ M.E)
--     grw [M.eRk_mono inter_subset_left, imp_iff_right inter_subset_right,
--       contract_inter_ground_eq] at aux
--     exact aux h hnt
--   have hnt' := Order.le_of_lt_add_one hnt
--   have hgirth := h.le_girth hnt'
--   have hC : M.Indep C := by
--     apply indep_of_eRk_add_one_lt_girth _ hCE
--     enat_to_nat! <;> omega
--   rw [tutteConnected_iff_verticallyConnected_girth]
--   refine ⟨(h.verticallyConnected.mono ?_).contract, ?_⟩
--   · grw [add_right_comm]
--   · have hle := hgirth.trans (M.girth_le_girth_contract_add C)
--     · rwa [add_right_comm, WithTop.add_le_add_iff_right] at hle
--       generalize M.eRk C = x at *
--       clear h hle hC hgirth hnt' hCE hne e C
--       generalize M.E.encard = y at *
--       enat_to_nat
--       -- enat_to_nat is behaving absurdly here : `extract_goal` makes it work fine.
--       Something fishy.
--       sorry
--       sorry
--   sorry
