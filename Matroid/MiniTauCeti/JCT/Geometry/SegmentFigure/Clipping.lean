module

public import Matroid.MiniTauCeti.JCT.Analysis.Convex.Segment
public import Matroid.MiniTauCeti.JCT.Geometry.SegmentFigure.Topology
public import Matroid.GraphTheory.GraphTopology.Subset

/-!
# Convex clipping of segment figures

Intersecting a figure with a closed convex set preserves segment figures. For an arbitrary
convex set the same statement holds after taking closure; the clipped intervals can have
missing endpoints before closure.
-/

@[expose] public section

open Set
open scoped GraphLike

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V] {S C : Set V} {a b : V}

namespace IsSegmentFigure

theorem closure_inter_convex (hS : IsSegmentFigure S) (hC : Convex ℝ C) :
    IsSegmentFigure (closure (S ∩ C)) := by
  refine hS.induction_on (by simp) ?_
  intro a b S _ ih
  rw [union_inter_distrib_right, closure_union]
  refine union ?_ ih
  have hsub : closure (segment ℝ a b ∩ C) ⊆ segment ℝ a b :=
    closure_minimal inter_subset_left (isCompact_segment a b).isClosed
  obtain h | h := (closure (segment ℝ a b ∩ C)).eq_empty_or_nonempty
  · simp [h]
  obtain ⟨p, q, hpq⟩ := IsCompact.exists_eq_segment_of_isConnected_of_subset_segment
    ((isCompact_segment a b).of_isClosed_subset isClosed_closure hsub)
    (((convex_segment a b).inter hC).closure.isConnected h) hsub
  rw [hpq]
  exact isSegmentFigure_segment p q

theorem inter_convex (hS : IsSegmentFigure S) (hC : Convex ℝ C) (hc : IsClosed C) :
    IsSegmentFigure (S ∩ C) := by
  simpa only [(hS.isClosed.inter hc).closure_eq] using hS.closure_inter_convex hC

end IsSegmentFigure

omit [T2Space V] in
/-- Relative closure of a difference is a figure when the left figure is Hausdorff.
Only the intersection with the right figure enters the common presentation. -/
theorem IsSegmentFigure.relativeClosure_sdiff [T2Space S] {T : Set V}
    (hS : IsSegmentFigure S) (hT : IsSegmentFigure T) :
    IsSegmentFigure (S ∩ closure (S \ T)) := by
  let U : Bool → Set V := fun i ↦ if i then S else S ∩ T
  have hU (i) : IsSegmentFigure (U i) := by grind
  have hUnion : (⋃ i, U i) = S := by
    ext x
    simp only [mem_iUnion, Bool.exists_bool, U, Bool.false_eq_true, ↓reduceIte, mem_inter_iff]
    tauto
  let : T2Space ↥(⋃ i, U i) := hUnion.symm ▸ inferInstance
  obtain ⟨G, hfin, hstraight, hcarrier, _, hcover⟩ :=
    exists_common_straightLineGraphLike_restrictions hU finite_empty (empty_subset _)
  have h := GraphLike.isSegmentFigure_relativeClosure_sdiff hstraight
    (U true) (U false)
    (GraphLike.Finite.vertexSet_finite.subset inter_subset_right)
    (GraphLike.Finite.edgeSet_finite.subset (sep_subset _ _))
  rw [hcover, hcover, hcarrier, hUnion] at h
  have hdiff : S \ (S ∩ T) = S \ T := by
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  simpa only [U, Bool.false_eq_true, ↓reduceIte, hdiff] using h

/-- Deleting a figure may remove endpoints, but closing the result restores a segment figure. -/
theorem IsSegmentFigure.closure_sdiff {T : Set V} (hS : IsSegmentFigure S)
    (hT : IsSegmentFigure T) : IsSegmentFigure (closure (S \ T)) := by
  have hsub : closure (S \ T) ⊆ S := closure_minimal sdiff_subset hS.isClosed
  simpa only [inter_eq_right.mpr hsub] using hS.relativeClosure_sdiff hT

end
