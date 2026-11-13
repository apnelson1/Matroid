module

public import Matroid.MiniTauCeti.JCT.Analysis.Convex.Segment
public import Matroid.MiniTauCeti.JCT.Topology.Path

@[expose] public section

open Set AffineMap

/-- A segment joining two closed sets contains a subsegment meeting each set only at its
corresponding endpoint. The subsegment may be a singleton when the sets overlap. -/
theorem IsClosed.exists_segment_inter_eq_singleton {E : Type*} [TopologicalSpace E]
    [AddCommGroup E] [Module ℝ E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    {A B : Set E} (hA : IsClosed A) (hB : IsClosed B) {a b : E} (ha : a ∈ A) (hb : b ∈ B) :
    ∃ u ∈ A, ∃ v ∈ B, segment ℝ u v ⊆ segment ℝ a b ∧
      segment ℝ u v ∩ A = {u} ∧ segment ℝ u v ∩ B = {v} := by
  let P := Path.segment a b
  let t := P.lastVisit A
  let s := P.firstVisitAfter B t
  have ht : P t ∈ A := P.lastVisit_mem (hA.preimage P.continuous) ⟨0, by simpa using ha⟩
  have hs : P s ∈ B := P.firstVisitAfter_mem
    (isClosed_Ici.inter (hB.preimage P.continuous)) ⟨1, unitInterval.le_one', by simpa using hb⟩
  have hts := P.le_firstVisitAfter B t
  have himage : P '' Icc t s = segment ℝ (P t) (P s) := by
    change (fun u : unitInterval ↦ lineMap a b (u : ℝ)) '' Icc t s = _
    rw [← image_image, image_subtype_val_Icc,
      ← segment_eq_Icc (show (t : ℝ) ≤ s from hts), image_segment]
    simp [P, Path.segment_apply]
  refine ⟨P t, ht, P s, hs, ?_, ?_, ?_⟩
  · rw [← himage, ← Path.range_segment a b]
    exact image_subset_range ..
  · rw [← himage, ← image_inter_preimage, P.Icc_lastVisit_inter_preimage ht hts, image_singleton]
  rw [← himage, ← image_inter_preimage, P.Icc_firstVisitAfter_inter_preimage hs, image_singleton]
