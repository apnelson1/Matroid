module

public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Keeping a point away from a closed set

## Main statements

* `exists_pos_le_dist_of_notMem` : a point off a closed set stays a fixed positive distance from
  all of it.
* `exists_pos_le_dist_of_disjoint` : the same for a compact set and a disjoint closed set.

The bounds are pointwise inequalities, so empty sets are handled vacuously. The proofs use
`infDist` for a point off a closed set and attain a positive minimum on a compact set.
-/

@[expose] public section

open Metric

/-- A point off a closed set stays a fixed positive distance from all of it. -/
@[grind →]
lemma exists_pos_le_dist_of_notMem {X : Type*} [PseudoMetricSpace X] {K : Set X} (hK : IsClosed K)
    {p : X} (hp : p ∉ K) : ∃ δ > 0, ∀ x ∈ K, δ ≤ dist p x := by
  obtain rfl | hne := K.eq_empty_or_nonempty
  · exact ⟨1, one_pos, by simp⟩
  exact ⟨infDist p K, (hK.notMem_iff_infDist_pos hne).mp hp, fun _ hx ↦ infDist_le_dist_of_mem hx⟩

/-- A compact set stays a fixed positive distance from a disjoint closed set.

Compactness is needed on one side only, and only to attain the minimum of `infDist · t`; the other
side may be any closed set. As above, both degenerate cases are absorbed by the pointwise form. -/
@[grind →]
lemma exists_pos_le_dist_of_disjoint {X : Type*} [PseudoMetricSpace X] {s t : Set X}
    (hs : IsCompact s) (ht : IsClosed t) (hst : Disjoint s t) :
    ∃ δ > 0, ∀ x ∈ s, ∀ y ∈ t, δ ≤ dist x y := by
  obtain rfl | hsne := s.eq_empty_or_nonempty
  · exact ⟨1, one_pos, by simp⟩
  obtain rfl | htne := t.eq_empty_or_nonempty
  · exact ⟨1, one_pos, by simp⟩
  obtain ⟨x, hx, hmin⟩ := hs.exists_isMinOn hsne (continuous_infDist_pt (s := t)).continuousOn
  exact ⟨infDist x t, (ht.notMem_iff_infDist_pos htne).mp (hst.notMem_of_mem_left hx),
    fun _ hy _ hz ↦ (hmin hy).trans (infDist_le_dist_of_mem hz)⟩

end
