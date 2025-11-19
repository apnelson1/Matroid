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
    let some r := e.not? | return ()
    try
      let (_, α, a, b) ← r.ineq?
      if (← isDefEq α q(ENat)) then
        findENatAtoms a
        findENatAtoms b
    catch _ => return

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

example {f : ℤ → ℕ∞} {a b c : ℤ} (h1 : f a + 1 ≤ f b) (h2 : f b ≤ f c) (h3 : f a < ⊤) :
    f a < f c := by
  enat_to_nat!
  omega

example {P : ℕ∞ → Prop} {a b c : ℕ∞} (ha : ¬ P a) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  enat_to_nat!
  omega

example (a b c d : ℕ∞) (hab : a ≤ b) (hbc : 2 * b + d < c) : a ≠ ⊤ := by
  enat_to_nat
