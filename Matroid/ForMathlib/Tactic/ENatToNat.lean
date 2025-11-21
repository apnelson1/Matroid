import Mathlib.Data.Ineq
import Mathlib.Tactic.ENatToNat

open Lean Meta Mathlib.Tactic Qq

partial def findENatAtoms (e : Q(ENat)) : AtomM Unit := do
  match e with
  | ~q($a + $b) => findENatAtoms a; findENatAtoms b
  | ~q($a - $b) => findENatAtoms a; findENatAtoms b
  | ~q($a * $b) => findENatAtoms a; findENatAtoms b
  | ~q(@OfNat.ofNat _ $n $_i) => return ()
  | ~q(Nat.cast $n) => return ()
  | ~q(⊤) => return ()
  | _ => let _ ← AtomM.addAtom e

def parseIneq (e : Expr) : AtomM Unit := do
  try
    let (_, α, a, b) ← e.ineq?
    if (← isDefEq α q(ENat)) then
      findENatAtoms a
      findENatAtoms b
  catch _ =>
    let some e := (← whnfR e).not? | return ()
    try
      let (_, α, a, b) ← e.ineq?
      if (← isDefEq α q(ENat)) then
        findENatAtoms a
        findENatAtoms b
    catch _ => return
  return

def atoms (g : MVarId) : AtomM (Array Expr) := g.withContext do
  for hyp in (← getLCtx) do
    parseIneq (← inferType hyp.toExpr)
  parseIneq (← g.getType')
  let r ← get
  return r.atoms

-- this should exist in the library
def Array.zipLeft {α : Type} (l : Array α) (ns : Array Name) : Array (α × Option Name) :=
  let out := l.toList.zipLeft ns.toList
  out.toArray

def generalizeAtoms (ns : Array Name) (g : MVarId) : MetaM MVarId := do
  let atoms ← AtomM.run .reducible (atoms g)
  let atoms₀ := atoms.filter fun e ↦ !e.isFVar
  let atomsWithNames := atoms₀.zipLeft ns
  let args : Array GeneralizeArg := atomsWithNames.map fun (e, n) ↦ { expr := e, xName? := n }
  let (_, _, g') ← g.generalizeHyp args ((← getLocalHyps).map (·.fvarId!))
  return g'

elab "generalize_enats" " with" e:(ppSpace colGt ident)* : tactic => do
  let names := e.map TSyntax.getId
  Elab.Tactic.liftMetaTactic' (generalizeAtoms names)

elab "generalize_enats" : tactic => do
  Elab.Tactic.liftMetaTactic' (generalizeAtoms #[])

-- this might give weird errors if the `generalize_enats` fails
macro "enat_to_nat!": tactic =>
  `(tactic | (generalize_enats; enat_to_nat))

-- this might give weird errors if the `generalize_enats` fails
macro "enat_to_nat!" " with" e:(ppSpace colGt ident)* : tactic =>
  `(tactic | (generalize_enats with $e*; enat_to_nat))

-- Missing lemmas from the `enat_to_nat` simpset.
attribute [enat_to_nat_top] not_true add_top

-- /-! ### Tests -/
variable {f : ℤ → ℕ∞}

example {a : ℤ} (h : 3 ≤ f a) : f a ≠ 0 := by
  enat_to_nat!; omega


  -- omega

-- example {a b c : ℕ∞} {x y : ℤ} (h : 2 * (f x + b) < f x) : a ≠ ⊤ := by


  -- enat_to_nat

-- example {f : ℤ → ℕ∞} {a b c d e : ℤ} (h : 2 * f e = f a + f b) : 2 * f a = f a + f b  := by
--   generalize_enats

--   omega



-- example {P : ℕ∞ → Prop} {a b c : ℕ∞} (ha : ¬ P a) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
--   enat_to_nat!
--   omega

-- example (a b c d : ℕ∞) (hab : a ≤ b) (hbc : 2 * b + d < c) : a ≠ ⊤ := by
--   enat_to_nat

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
