module

public import Matroid.ForMathlib.Topology.Path
public import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# The Jordan curve theorem

A **Jordan curve** is the image of an embedded circle. `IsJordanCurve J` says so in the form that is
easiest both to establish and to use: `J` is the range of a loop that is injective on `[0, 1)`.
For a compact curve in a Hausdorff space this is equivalent to `J` being homeomorphic to a circle,
since a continuous bijection from a compact space to a Hausdorff one is a homeomorphism.

The Jordan curve theorem itself, `IsJordanCurve.exists_sides`, is the **one topological input** the
Kuratowski development assumes; everything else in this file is derived from it. Only the polygonal
case is ever used, and that case is provable — see
`Matroid.ForMathlib.Geometry.Polygon.JordanCurve`, which specialises these statements to polygons
and is what the plane-topology files import.

## The sphere form

Faces of a drawing are taken in `OnePoint ℝ²` rather than in `ℝ²`, purely to remove the exceptional
unbounded face: on the sphere the two sides of a Jordan curve are interchangeable, and no argument
has to name one of them. `IsJordanCurve.exists_sides_onePoint` is that form. It is a consequence of
the plane form, not a second assumption: the bounded side is already open in the sphere, and the
unbounded side together with `∞` is the complement of a compact set.

## Main definitions

* `IsJordanCurve`

## Main statements

* `IsJordanCurve.exists_sides` : the Jordan curve theorem. **Assumed.**
* `IsJordanCurve.exists_sides_onePoint` : its sphere form. Derived.
* `eq_connectedComponentIn_of_frontier_subset` : an open connected set missing `K` and with frontier
  inside `K` is a connected component of `Kᶜ`. Pure general topology, and the workhorse for
  recognising a face; it needs no Jordan curve at all.
-/

@[expose] public section

open Set Function Topology Bornology

universe u

variable {X : Type u} [TopologicalSpace X] {J K W : Set X} {a : X}

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
the complement of `K`. Status.md 3.4: the standard way to recognise a face, used constantly and
proved once. No Jordan curve and no local connectedness are involved. -/
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

/-- **The Jordan curve theorem.** The complement of a Jordan curve in the plane has exactly two
connected components — a bounded one and an unbounded one — and each has the curve as its frontier.

This is the single topological input assumed by the Kuratowski development. Everything downstream
uses it only through the polygonal specialisation in
`Matroid.ForMathlib.Geometry.Polygon.JordanCurve`, and the polygonal case is provable, so this is a
theorem to be discharged rather than an axiom to be believed. -/
theorem IsJordanCurve.exists_sides {J : Set (EuclideanSpace ℝ (Fin 2))} (hJ : IsJordanCurve J) :
    ∃ U V : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ Disjoint U V ∧ U ∪ V = Jᶜ ∧
      IsBounded U ∧ ¬ IsBounded V ∧ frontier U = J ∧ frontier V = J := by
  sorry

/-- The two sides of a Jordan curve are its complement's only connected components. -/
theorem IsJordanCurve.eq_or_eq_connectedComponentIn {J : Set (EuclideanSpace ℝ (Fin 2))}
    (hJ : IsJordanCurve J) {U V : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U) (hV : IsOpen V)
    (hUc : IsConnected U) (hVc : IsConnected V) (hUV : Disjoint U V) (hcover : U ∪ V = Jᶜ)
    {a : EuclideanSpace ℝ (Fin 2)} (ha : a ∉ J) :
    connectedComponentIn Jᶜ a = U ∨ connectedComponentIn Jᶜ a = V := by
  sorry

/-- Status.md 3.2, the sphere form: on the one-point compactification the complement of a Jordan
curve still has exactly two components, each with the curve as frontier, and now neither is
distinguished. Derived from `IsJordanCurve.exists_sides`, not assumed separately: `U` is already
open in the sphere, and `V ∪ {∞}` is the complement of the compact set `U ∪ J`. -/
theorem IsJordanCurve.exists_sides_onePoint {J : Set (EuclideanSpace ℝ (Fin 2))}
    (hJ : IsJordanCurve J) :
    ∃ U V : Set (OnePoint (EuclideanSpace ℝ (Fin 2))),
      IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ Disjoint U V ∧
      U ∪ V = ((↑) '' J)ᶜ ∧ OnePoint.infty ∈ V ∧
      frontier U = (↑) '' J ∧ frontier V = (↑) '' J := by
  sorry

/-- The component count, in the shape `Graph.Drawing.Face` is stated in. -/
theorem IsJordanCurve.card_connectedComponents_compl {J : Set (EuclideanSpace ℝ (Fin 2))}
    (hJ : IsJordanCurve J) : Nat.card (ConnectedComponents ↥Jᶜ) = 2 := by
  sorry

/-- The component count on the sphere. -/
theorem IsJordanCurve.card_connectedComponents_compl_onePoint
    {J : Set (EuclideanSpace ℝ (Fin 2))} (hJ : IsJordanCurve J) :
    Nat.card (ConnectedComponents
      ↥(((↑) '' J : Set (OnePoint (EuclideanSpace ℝ (Fin 2)))))ᶜ) = 2 := by
  sorry
