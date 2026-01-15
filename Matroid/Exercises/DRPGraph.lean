import Matroid.Graph.Connected.Basic

/-!
This file is intended as a **student exercise sheet** for the `Graph` theory library used in this
project.

Each lemma is stated in the vocabulary of this repository (not Mathlib's `SimpleGraph`). The goal is
to replace each `sorry` with a proof.

Suggestions:

**Good tactics:**
- `simp` is your friend. Use `simp?` or `simp_all?` to see what it's doing.
- `simp_rw` is better than `rw` as it can rewrite expressions inside quantifiers.
- `obtain` combines `have` and `rcases` into one tactic.
- `ext` + `simp` solves many goals about sets, functions, or equality of structures.
- `constructor` breaks down `And`/`Iff` goals. Use `use` for `Exists` goals.

**Question mark tactics (auto-search):**
- `exact?` - finds exact matches for the goal.
- `apply?` - finds lemmas that can be applied.
- `rw?` - suggests rewrite lemmas.
- `rw??` - interactive rewrite search.

**Searching for lemmas:**
- `#loogle` - semantic search for lemmas (e.g., `#loogle Graph.Adj → Graph.Adj`).
- `#check` - check the type of an expression.
- `#find` - search for lemmas by pattern.
- `#print` - see the definition of a term.
- Browse imported files: put cursor on import and press `F12`.

**Logic and proof structure:**
- `by_contra!` - proof by contradiction.
- `contrapose!` - contrapositive.
- `grind` - useful if the goal is propositional logic away from your assumptions.
- `left`/`right` - for `Or` goals.
- `exfalso` - when you have `False` in the goal.

**Arithmetic:**
- `omega` - for linear arithmetic on `ℕ`/`ℤ`.
- `enat_to_nat!; omega` - for arithmetic on `ℕ∞` (extended naturals).
- `norm_num` - numeric computations.

**Working with definitions:**
- `unfold` - unfold a definition.
- `change` - change the goal to a definitionally equal one.
- `suffices` - forward reasoning: "it suffices to show X".
- `obtain` - add intermediate steps.

**Pattern matching and induction:**
- `induction` - proof by induction.
- `rcases` - recursive case analysis (e.g., `rcases h with ⟨x, y, hxy⟩`).
- `match` - pattern matching (more control than `cases`).

**Equality and congruence:**
- `congr` - congruence for equality of functions/structures.
- `ext` - function extensionality.
- `decide` - for decidable propositions.

**Miscellaneous:**
- `refine` - more control than `exact` (can leave holes with `_` or `?_`).
- `convert` - when you're close but not quite (leaves a difference to prove).
- `classical` - enable classical reasoning (choice/decidable equality).

**Troubleshooting:**
- If you see an error containing `Decidable`, try adding `classical` at the beginning.
- If `simp` is too aggressive, use `simp only [...]` to specify what to use.
- Use `set_option trace.simplify.rewrite true` to see what `simp` is doing.
-/

open Set WList

namespace Graph

variable {α β : Type*} {G H K : Graph α β} {x y z u v : α} {e f : β} {S T X Y : Set α}
  {F F' : Set β} {w P Q : WList α β}

/-! ### Section 1: From the definition of `Graph` -/
/-
Here, Graph is defined using `IsLink` as the main predicate.
`G.IsLink e x y` means that `e` is a linking edge between `x` and `y`.

Lemmas in this section already exist in the library and using them would trivialize the proofs.
Instead, I encourage you to prove the lemmas from scratch using the first principles.
Please have a look at the definition of `Graph` what are the first principles you can use to prove
the lemmas. Also, no `simp` is allowed.
Put your cursor on the lemma/definition you want know the definition of and press `F12` key.
-/
lemma exercise_isLink_comm : G.IsLink e x y ↔ G.IsLink e y x := by
  sorry

lemma exercise_inc_left_of_isLink : G.IsLink e x y → G.Inc e x := by
  sorry

lemma exercise_not_isLink_of_notMem_edgeSet : e ∉ E(G) → ¬ G.IsLink e x y := by
  -- try `apply mt`
  sorry

lemma exercise_incEdges_subset : E(G, x) ⊆ E(G) := by
  sorry

/-! ### Section 2: Walks and paths -/
/-
There is a type `WList α β` used to represent walks/paths/trails.
`G.IsWalk w` means that `w : WList α β` is a walk of `G : Graph α β` and
similar for `IsPath` and `IsTrail`.

`WList` is an inductive type so you can use pattern matching (`match` or `rcases`) to decompose it,
similar to `ℕ` or `List`.
-/

lemma exercise_nil_isWalk_iff : G.IsWalk (.nil x) ↔ x ∈ V(G) := by
  sorry

lemma exercise_cons_isWalk_iff : G.IsWalk (.cons x e w) ↔ G.IsLink e x w.first ∧ G.IsWalk w := by
  sorry

lemma exercise_get_zero_eq_first : w.get 0 = w.first := by
  -- try `match w with` and press `ctrl+.` to autofill the cases.
  sorry

lemma exercise_get_one_eq_second : w.get 1 = w.second := by
  sorry

/-! ### Section 3: Harder problems -/
/-
Here are some harder problems. You are allowed and encouraged to use every lemma/tactic you have
available to you.
These lemmas does not exist yet and proving even one of them would be a valuable contribution to
the library.
-/

-- Look at `vertexDelete` definition in `Graph/Subgraph/Defs.lean` and
-- `ConnBetween` definition in `Graph/Connected/Defs.lean`.
lemma exercise1 (hw : G.IsWalk w) (h : ¬ (G - ({x} : Set α)).ConnBetween w.first w.last) :
    x ∈ V(w) := by
  sorry

lemma exercise2 (h : ∀ v ∈ V(G), G.degree v = 1) (hH : H.IsCompOf G) : V(H).encard = 2 := by
  sorry

lemma exercise3 (h : G.ConnGE 2) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    ∃ H : Graph α β, H.IsCycleGraph ∧ x ∈ V(H) ∧ y ∈ V(H) := by
  sorry

end Graph
