module

public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Keeping a point away from a closed set

## Main statements

* `exists_pos_le_dist_of_notMem` : a point off a closed set stays a fixed positive distance from
  all of it.
* `exists_pos_le_dist_of_disjoint` : the same for a compact set and a disjoint closed set.

## Implementation notes

The bound is stated pointwise, as `∀ x ∈ K, δ ≤ dist p x`, rather than as `0 < infDist p K`, and
that choice is the whole content of the lemma. `infDist p ∅ = 0`, so the `infDist` form is simply
false for `K = ∅`; every caller of it therefore has to open a case split on `K.Nonempty`, or carry
a nonemptiness hypothesis it does not otherwise need. Under the pointwise form the empty case is
vacuous, so the split is made once, here.

`PseudoMetricSpace` is the right generality: `IsClosed.notMem_iff_infDist_pos` and
`infDist_le_dist_of_mem` both hold there, and nothing in the statement needs separation or a norm.

Mathlib's `exists_pos_forall_lt_edist` (`Topology/MetricSpace/HausdorffDistance.lean`, the same
module imported here) is the set-to-set statement in `ℝ≥0∞`, and `Disjoint.exists_thickenings` is
its packaged consequence. `exists_pos_le_dist_of_disjoint` is the `ℝ`-valued form: a near-miss
rather than a duplicate, kept because every caller here works with `dist` and would otherwise pay
the `edist` conversion at each use.
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

/-! ### Regression tests for the tags

Both lemmas are `@[grind →]`: the conclusions are existentials with no head to key on, so the
pattern has to come from the antecedents, and here it does — `p ∉ K` and `Disjoint s t` mention
every variable of their lemma. Contrast `Path.exists_lastExit_firstEntry`, whose principal argument
appears only under the existential and which therefore admits no tag at all. -/

/-! The regression tests for the tags above live in `tests/MatroidTests/GrindTags.lean`;
see `tests/README.md`. -/

end
