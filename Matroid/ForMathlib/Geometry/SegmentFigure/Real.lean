module

public import Matroid.ForMathlib.Geometry.SegmentFigure.Topology

/-!
# Segment figures on the real line

Real segment figures are finite unions of bounded closed intervals. Their nonempty
connected components are single intervals, so a connected real figure is a segment.
-/

@[expose] public section

open Set

theorem isSegmentFigure_Icc (a b : ℝ) : IsSegmentFigure (Icc a b) := by
  obtain h | h := le_total a b
  · exact segment_eq_Icc h ▸ isSegmentFigure_segment a b
  obtain rfl | h := h.eq_or_lt
  · exact IsSegmentFigure.of_finite (by simp)
  simp [Icc_eq_empty_of_lt h]

theorem isSegmentFigure_iff_finite_iUnion_Icc {S : Set ℝ} :
    IsSegmentFigure S ↔ ∃ E : Set (ℝ × ℝ), E.Finite ∧ S = ⋃ e ∈ E, Icc e.1 e.2 := by
  refine ⟨fun hS ↦ hS.induction_on ⟨∅, finite_empty, by simp⟩ ?_, ?_⟩
  · rintro ⟨E, hE, rfl⟩
    exact IsSegmentFigure.biUnion hE (fun e _ ↦ isSegmentFigure_Icc e.1 e.2)
  rintro a b S _ ⟨E, hE, rfl⟩
  refine ⟨insert (min a b, max a b) E, hE.insert _, ?_⟩
  simp [segment_eq_uIcc, uIcc]

theorem IsSegmentFigure.eq_Icc_of_isConnected {S : Set ℝ} (hS : IsSegmentFigure S)
    (hconn : IsConnected S) : S = Icc (sInf S) (sSup S) :=
  eq_Icc_of_connected_compact hconn hS.isCompact

end
