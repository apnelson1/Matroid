module

public import Matroid.ForMathlib.Topology.Path
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# The Jordan curve theorem

A **Jordan curve** is the image of an embedded circle. `IsJordanCurve J` expresses this as the range
of a loop that is injective on `[0, 1)`. The Jordan curve theorem states that its complement in the
plane has two connected sides, each with the curve as frontier.

## The sphere form

On `OnePoint E`, the two sides are interchangeable. `IsJordanCurve.exists_sides_onePoint` derives
this sphere form from the plane form by adjoining `∞` to the unbounded side.

## The plane

`IsJordanCurve` is defined in any topological space. The plane form is stated for a real normed
space of finrank two; boundedness distinguishes its bounded and unbounded sides.

## Main definitions

* `IsJordanCurve`

## Main statements

* `IsJordanCurve.exists_sides` : the Jordan curve theorem.
* `IsJordanCurve.exists_sides_onePoint` : its sphere form, derived from the plane form.
* `eq_connectedComponentIn_of_frontier_subset` : an open connected set missing `K` and with frontier
  inside `K` is a connected component of `Kᶜ`.
-/

@[expose] public section

open Set Function Topology Bornology

variable {X : Type*} [TopologicalSpace X] {J K W : Set X} {a : X}

/-- `J` is a Jordan curve: the image of a loop traversing it exactly once. Equivalently, for
compact `J` in a Hausdorff space, `J` is homeomorphic to a circle. -/
def IsJordanCurve (J : Set X) : Prop :=
  ∃ (x : X) (P : Path x x), P.IsSimpleLoop ∧ range P = J

namespace IsJordanCurve

lemma isCompact (hJ : IsJordanCurve J) : IsCompact J := by
  obtain ⟨x, P, -, rfl⟩ := hJ
  exact isCompact_range P.continuous

lemma isClosed [T2Space X] (hJ : IsJordanCurve J) : IsClosed J :=
  hJ.isCompact.isClosed

lemma nonempty (hJ : IsJordanCurve J) : J.Nonempty := by
  obtain ⟨x, P, -, rfl⟩ := hJ
  exact range_nonempty P

end IsJordanCurve

/-- An open connected set disjoint from `K` whose frontier lies in `K` is a connected component of
the complement of `K`. -/
theorem eq_connectedComponentIn_of_frontier_subset (hW : IsOpen W) (hWc : IsPreconnected W)
    (hWK : Disjoint W K) (hfr : frontier W ⊆ K) (ha : a ∈ W) :
    W = connectedComponentIn Kᶜ a := by
  have hWKc : W ⊆ Kᶜ := hWK.subset_compl_right
  refine subset_antisymm (hWc.subset_connectedComponentIn ha hWKc) ?_
  refine IsPreconnected.subset_left_of_subset_union hW isClosed_closure.isOpen_compl
    (disjoint_compl_right_iff_subset.mpr subset_closure) (fun z hz ↦ ?_)
    ⟨a, mem_connectedComponentIn (hWKc ha), ha⟩ isPreconnected_connectedComponentIn
  by_cases hzc : z ∈ closure W
  · have hzf : z ∉ frontier W := fun h ↦ connectedComponentIn_subset _ _ hz (hfr h)
    rw [hW.frontier_eq] at hzf
    simp only [mem_sdiff, hzc, true_and, not_not] at hzf
    exact Or.inl hzf
  · exact Or.inr hzc

/-! ### The theorem -/

section Plane

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fact (Module.finrank ℝ E = 2)]
  {J : Set E}

/-- **The Jordan curve theorem.** The complement of a Jordan curve in the plane has exactly two
connected components — a bounded one and an unbounded one — and each has the curve as its frontier.
-/
theorem IsJordanCurve.exists_sides (hJ : IsJordanCurve J) :
    ∃ U V : Set E,
      IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ Disjoint U V ∧ U ∪ V = Jᶜ ∧
      IsBounded U ∧ ¬ IsBounded V ∧ frontier U = J ∧ frontier V = J := by
  sorry

/-- The two sides of a Jordan curve are its complement's only connected components. -/
theorem IsJordanCurve.eq_or_eq_connectedComponentIn
    (hJ : IsJordanCurve J) {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    (hUc : IsConnected U) (hVc : IsConnected V) (hUV : Disjoint U V) (hcover : U ∪ V = Jᶜ)
    {a : E} (ha : a ∉ J) :
    connectedComponentIn Jᶜ a = U ∨ connectedComponentIn Jᶜ a = V := by
  sorry

/-- On the one-point compactification, the complement of a Jordan curve has two components with the
curve as frontier, and neither component is distinguished. -/
theorem IsJordanCurve.exists_sides_onePoint (hJ : IsJordanCurve J) :
    ∃ U V : Set (OnePoint E),
      IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ Disjoint U V ∧
      U ∪ V = ((↑) '' J)ᶜ ∧ OnePoint.infty ∈ V ∧
      frontier U = (↑) '' J ∧ frontier V = (↑) '' J := by
  sorry

/-- The complement of a Jordan curve has two connected components. -/
theorem IsJordanCurve.card_connectedComponents_compl (hJ : IsJordanCurve J) :
    Nat.card (ConnectedComponents ↥Jᶜ) = 2 := by
  sorry

/-- The component count on the sphere. -/
theorem IsJordanCurve.card_connectedComponents_compl_onePoint (hJ : IsJordanCurve J) :
    Nat.card (ConnectedComponents ↥(((↑) '' J : Set (OnePoint E)))ᶜ) = 2 := by
  sorry

end Plane
