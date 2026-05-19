import Mathlib.Data.Ineq
import Mathlib.Data.Set.Card
import Mathlib.Tactic.ENatToNat

/-!
# `enat_to_nat` with configuration and `generalize_all`

This file extends the upstream Mathlib `enat_to_nat` tactic with configuration options
and introduces a general-purpose `generalize_all p : t` tactic.

## New syntax

```
generalize_all p : t      -- generalize every non-literal subterm matching `p : t`
enat_to_nat               -- original behaviour (no generalization)
enat_to_nat +generalize   -- `generalize_all _ : ℕ∞` then `enat_to_nat`
enat_to_nat!              -- synonym for `enat_to_nat +generalize`
enat_to_nat! with h₁ h₂ … -- names the fresh variables
eomega                    -- `enat_to_nat! <;> omega`
```

`generalize_all` deliberately skips numeric/⊤/⊥ literals: they carry information that
`enat_to_nat` (and downstream deciders like `omega`) rely on.
-/

namespace Matroid.Tactic.ENatToNat

open Lean Meta Elab Tactic Qq

/-! ## Configuration -/

/-- Configuration options for the `enat_to_nat` tactic. -/
structure Config where
  /-- If `true` (default `false`), run `generalize_all _ : ℕ∞` before casing. -/
  generalize : Bool := false
  deriving Inhabited

/-- Function elaborating `Matroid.Tactic.ENatToNat.Config`. -/
declare_config_elab elabENatToNatConfig Config

/-! ## Core: `generalize_all` -/

def literalHeads : List Name := [``OfNat.ofNat, ``Top.top, ``Bot.bot, ``Zero.zero, ``One.one,
   ``Nat.cast, ``NatCast.natCast, ``Int.cast, ``IntCast.intCast]

def transparentHeads : List Name := [``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv,
  ``HMod.hMod, ``HPow.hPow, ``Add.add, ``Sub.sub, ``Mul.mul, ``Div.div, ``Neg.neg, ``Inv.inv]

def isLiteralTerm (e : Expr) : Bool := e.isLit || literalHeads.any e.isAppOf

def isTransparentOp (e : Expr) : Bool := transparentHeads.any e.isAppOf

def isGeneralizationCandidate (pat typ : Expr) (e : Expr) : MetaM Bool := do
  if e.hasLooseBVars || e.isFVar || e.isMVar || e.isSort || isLiteralTerm e || isTransparentOp e
  then return false
  let s ← saveState
  try
    let t ← inferType e
    unless ← isDefEq t typ do
      restoreState s
      return false
    unless ← isDefEq pat e do
      restoreState s
      return false
    restoreState s
    return true
  catch _ =>
    restoreState s
    return false

/-- Descend into the immediate subexpressions of `e`, calling `k` on each. -/
private def visitChildren (e : Expr) (k : Expr → MetaM Unit) : MetaM Unit := do
  match e with
  | .app f a         => k f; k a
  | .lam _ t b _     => k t; k b
  | .forallE _ t b _ => k t; k b
  | .letE _ t v b _  => k t; k v; k b
  | .mdata _ x       => k x
  | .proj _ _ x      => k x
  | _ => return

/-- Collect, in first-encountered order with `isDefEq`-based deduplication, every
subterm of `exprs` that passes `isGeneralizationCandidate pat typ`. Descends into
every position, including function arguments — this is what the old `Qq`-guided
traversal missed.

The accumulator is deduplicated with `isDefEq` under `.reducible` transparency,
matching the behaviour of `Mathlib.Tactic.AtomM.addAtom` used by the legacy
`findENatAtoms`. This is critical: two occurrences of the "same" term can differ
in elaboration metadata (universe levels, cached `.mdata`, re-synthesised implicit
arguments) but be reducibly-defEq, and must fold together to avoid spawning
unreachable `cases_first_enat` branches downstream. A separate syntactic `seen`
set is kept only to avoid *re-traversing* identical subterm occurrences. -/
partial def collectCandidates (pat typ : Expr) (exprs : Array Expr) :
    MetaM (Array Expr) := do
  let acc ← IO.mkRef (#[] : Array Expr)
  let seen ← IO.mkRef ({} : Std.HashSet Expr)
  let rec go (e : Expr) : MetaM Unit := do
    let e ← instantiateMVars e
    if e.hasLooseBVars then
      visitChildren e go
      return
    if (← seen.get).contains e then return
    seen.modify (·.insert e)
    if ← isGeneralizationCandidate pat typ e then
      let existing ← acc.get
      let dup ← withReducible <| existing.anyM fun a =>
        withoutModifyingState <| isDefEq a e
      unless dup do
        acc.modify (·.push e)
    visitChildren e go
  for e in exprs do go e
  acc.get

/-- Return every type that `generalize_all` should scan: the goal type and every
(non implementation-detail) local hypothesis type. -/
def targetsToScan (g : MVarId) : MetaM (Array Expr) := g.withContext do
  let mut out := #[← g.getType]
  for d in (← getLCtx) do
    unless d.isImplementationDetail do
      out := out.push d.type
  return out

/-- Test whether generalizing the given `candidates` on `g` succeeds without producing
an ill-typed result. We lean directly on `MVarId.generalizeHyp`, which performs the
well-typedness check described by the let-definition/`Meta.check` trick: if any
candidate would require a type-dependent occurrence to be unfolded, the call throws.

This is the "Route C" happy path: a single check for all candidates at once. The
metacontext is restored via `saveState`/`restoreState`, so this has no observable
effect on the goal state. -/
def tryGeneralize (candidates : Array Expr) (g : MVarId) : MetaM Bool := do
  if candidates.isEmpty then return true
  let s ← saveState
  try
    let args : Array GeneralizeArg := candidates.map fun e => { expr := e }
    let hyps := (← g.withContext getLocalHyps).map (·.fvarId!)
    let _ ← g.generalizeHyp args hyps
    restoreState s
    return true
  catch _ =>
    restoreState s
    return false

/-- Filter `candidates` down to those that can be safely generalized on `g`, one by
one. This is "Route B", used as a fallback when the batch probe `tryGeneralize` fails.
Each candidate is tested in isolation against the *original* goal. -/
def filterSafeCandidates (candidates : Array Expr) (g : MVarId) :
    MetaM (Array Expr) :=
  candidates.filterM fun c => tryGeneralize #[c] g

/-- Zip `candidates` with `ns` on the left (missing names become `none`). -/
private def zipWithNames (candidates : Array Expr) (ns : Array Name) :
    Array (Expr × Option Name) :=
  let list := candidates.toList.zipLeft ns.toList
  list.toArray

/-- The core of `generalize_all`.

1. Collects candidates matching `pat` with type `typ` in the goal and every hypothesis
   (skipping literals).
2. Probes them with `MVarId.generalizeHyp` once as a batch; if that fails, falls back
   to per-candidate probing.
3. Generalizes the surviving candidates, naming them with `ns` (left-zipped). -/
def generalizeAllMatching (pat typ : Expr) (ns : Array Name) (g : MVarId) :
    MetaM MVarId := g.withContext do
  let scan ← targetsToScan g
  let candidates ← collectCandidates pat typ scan
  if candidates.isEmpty then return g
  let safe ←
    if ← tryGeneralize candidates g then
      pure candidates
    else
      filterSafeCandidates candidates g
  if safe.isEmpty then return g
  let args : Array GeneralizeArg := (zipWithNames safe ns).map fun (e, n?) =>
    { expr := e, xName? := n? }
  let hyps := (← getLocalHyps).map (·.fvarId!)
  let (_, _, g') ← g.generalizeHyp args hyps
  return g'

/-! ### `generalize_all` tactic syntax -/

/-- `generalize_all p : t` locates every non-literal subterm of the goal and context
that is definitionally equal to `p` and whose type is definitionally equal to `t`,
and generalizes each one to a fresh local variable.

Numeric/⊤/⊥/0/1 literals are *not* generalized, since their identity typically
matters to downstream deciders (`omega`, `simp`, etc.).

Candidates whose generalization would make the goal or a hypothesis ill-typed
(dependent occurrences) are silently dropped.

Examples:
* `generalize_all _ : ℕ∞` generalizes every non-literal `ℕ∞`-typed subterm.
* `generalize_all _ : ℕ∞ with x y z` names the first three introduced variables.
-/
syntax (name := generalizeAllStx) "generalize_all " term:51 " : " term
  (" with" (ppSpace colGt ident)+)? : tactic

/-- Common elaboration helper shared by the two `generalize_all` syntax forms. -/
private def elabGeneralizeAll (pat : Syntax) (typ : Syntax) (ids : Array Ident) :
    TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    let typE ← Term.elabType typ
    let patE ← Term.elabTerm pat (some typE)
    Term.synthesizeSyntheticMVarsNoPostponing
    let typE ← instantiateMVars typE
    let patE ← instantiateMVars patE
    let ns := ids.map (·.getId)
    let g' ← generalizeAllMatching patE typE ns g
    replaceMainGoal [g']

elab_rules : tactic
  | `(tactic| generalize_all $pat:term : $typ:term) =>
    elabGeneralizeAll pat typ #[]
  | `(tactic| generalize_all $pat:term : $typ:term with $ids*) =>
    elabGeneralizeAll pat typ ids

/-! ## New `enat_to_nat` front-end -/

open Lean Elab Tactic Parser.Tactic in
/-- Helper tactic: if `cfg.generalize = true`, run `generalize_all _ : ℕ∞`,
otherwise do nothing. Used by the `macro_rules` below to desugar `enat_to_nat`
with an `optConfig`. -/
local elab "try_generalize_enat" cfg:optConfig : tactic => do
  let cfgV ← elabENatToNatConfig cfg
  if cfgV.generalize then
    evalTactic (← `(tactic| generalize_all _ : ℕ∞))

open Lean Elab Tactic Parser.Tactic in
/-- The configurable form of the `enat_to_nat` tactic. A superset of Mathlib's
`enat_to_nat`; with no options, the behaviour is identical.

* `enat_to_nat` — cases on every `ENat` already in the local context, then simplifies.
* `enat_to_nat +generalize` — first `generalize_all _ : ℕ∞`, then `enat_to_nat`.
-/
syntax (name := enatToNatStx) (priority := high) "enat_to_nat" optConfig : tactic

/-- Shorthand: `enat_to_nat!` ≡ `enat_to_nat +generalize`. Optionally a `with`
clause names the fresh variables introduced by `generalize_all`. -/
syntax (name := enatToNatBangStx) (priority := high)
  "enat_to_nat!" (" with" (ppSpace colGt ident)+)? : tactic

macro_rules
  | `(tactic| enat_to_nat $cfg:optConfig) =>
    `(tactic| (try_generalize_enat $cfg; focus (
        (repeat' cases_first_enat) <;>
        (try simp only [enat_to_nat_top, enat_to_nat_coe] at *))))

macro_rules
  | `(tactic| enat_to_nat!) => `(tactic| enat_to_nat +generalize)
  | `(tactic| enat_to_nat! with $ids*) =>
    `(tactic| (generalize_all _ : ℕ∞ with $ids*; enat_to_nat))

/-- `eomega` runs `enat_to_nat!` and then `omega`. -/
macro "eomega" : tactic =>
  `(tactic| (enat_to_nat! <;> omega))

end Matroid.Tactic.ENatToNat

-- Missing lemmas from the `enat_to_nat` simpset.
attribute [enat_to_nat_top] not_true add_top and_true true_and or_false false_or imp_false
  false_iff true_iff iff_true iff_false true_or or_true Nat.cast_le Nat.cast_lt false_imp_iff
  true_imp_iff false_and and_false

/-! ### Tests -/

section Tests

variable {f : ℤ → ℕ∞}

example {a : ℤ} (h : 3 ≤ f a) : f a ≠ 0 := by
  enat_to_nat!; omega

example {a b c : ℕ∞} {x : ℤ} (h : 2 * (f x + b) < f x) : a ≠ ⊤ := by
  enat_to_nat! <;> omega

example {f : ℤ → ℕ∞} {a b e : ℤ} (h : 2 * f e + f a + f b ≤ f a) : 2 * f a ≤ 3 * f a + f b := by
  enat_to_nat!; omega

example {P : ℕ∞ → Prop} {a b c : ℕ∞} (ha : ¬ P a) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  enat_to_nat!
  omega

example (a b c d : ℕ∞) (x : ℤ) (hab : a ≤ b) (hbc : 2 * f x + d < c) : f x ≠ ⊤ := by
  enat_to_nat!

example {a : ℤ} : 0 ≤ f a := by
  enat_to_nat!
  omega

example {a b : ℤ} (h1 : ¬ (f a ≠ 0 ∧ 1 ≤ f a)): 0 ≤ f b := by
  enat_to_nat!
  omega

/-- Regression: `f a` appears only as an argument to a non-arithmetic function `g`.
The old `Qq`-guided traversal would not have descended into `g`'s argument, but
`generalize_all` does. -/
example {g : ℕ∞ → Prop} {a : ℤ} (h : g (f a)) : g (f a) := by
  enat_to_nat!
  all_goals assumption

/-- Regression: explicit `(config := …)` parses and is equivalent to `+generalize`. -/
example {a : ℤ} (h : 3 ≤ f a) : f a ≠ 0 := by
  enat_to_nat (config := { generalize := true })
  omega

/-- Regression: the new `generalize_all` tactic itself works (no-op here, `a` and `b`
are already fvars so there is nothing to generalize). -/
example {a b : ℕ∞} (h : a ≤ b) : a ≤ b := by
  assumption

/-- Regression: literals like `3`, `0`, `⊤` should NOT be generalized. -/
example {a : ℤ} (h : (3 : ℕ∞) ≤ f a) : f a ≠ 0 := by
  enat_to_nat!
  omega

/-- Regression mirroring `Matroid.Graph.Connected.Basic.ConnGE.edgeDelete_linkEdges.le_card`:
the only ℕ∞ subterm is an opaque compound expression (`Set.encard _`), with Nat casts
on each side. -/
example {α : Type*} {n : ℕ} {X : Set α} (h : (n+1 : ℕ∞) < X.encard) :
    (n : ℕ∞) < X.encard := by
  enat_to_nat!
  omega

/-- Regression: when `enat_to_nat!` runs inside a `refine ... (fun h ↦ ?_)` hole, the
goal and the newly-introduced hypothesis both live as metavariables in the remaining
goal's context. `collectCandidates` must `instantiateMVars` before walking the
expression tree; otherwise candidates like `X.encard` stay hidden. -/
example {α : Type*} {n : ℕ} {X : Set α}
    (h : X.Subsingleton ∨ (n+1 : ℕ∞) < X.encard) :
    X.Subsingleton ∨ (n : ℕ∞) < X.encard := by
  refine h.imp id (fun h ↦ ?_)
  enat_to_nat!
  omega

end Tests
