module

public import Matroid.ForMathlib.Geometry.SegmentFigure.Basic
public import Mathlib.Analysis.Real.Cardinality

/-!
# Finite and countable segment figures

A segment figure is either finite or contains a nondegenerate segment. Consequently a
countable segment figure is finite. These statements do not require an ambient topology.
-/

@[expose] public section

open Set

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {S : Set V} {a b : V}

@[simp]
theorem countable_segment_iff : (segment ℝ a b).Countable ↔ a = b := by
  refine ⟨fun h ↦ by_contra fun hab ↦ ?_, ?_⟩
  · rw [segment_eq_image_lineMap] at h
    have hi := h.preimage <| AffineMap.lineMap_injective ℝ hab
    rw [(AffineMap.lineMap_injective ℝ hab).preimage_image, Cardinal.Real.Icc_countable_iff] at hi
    exact zero_lt_one.not_ge hi
  rintro rfl
  simp

namespace IsSegmentFigure

theorem countable_iff_finite (hS : IsSegmentFigure S) : S.Countable ↔ S.Finite :=
  ⟨fun h ↦ hS.finite_iff.mpr fun _ _ hsub ↦ countable_segment_iff.mp (h.mono hsub),
    Finite.countable⟩

end IsSegmentFigure

end
