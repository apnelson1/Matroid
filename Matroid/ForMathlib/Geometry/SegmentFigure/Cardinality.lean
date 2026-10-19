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

@[simp]
theorem finite_segment_iff : (segment ℝ a b).Finite ↔ a = b :=
  ⟨fun h ↦ countable_segment_iff.mp h.countable, by rintro rfl; simp⟩

namespace IsSegmentFigure

theorem finite_iff (hS : IsSegmentFigure S) : S.Finite ↔ ∀ a b, segment ℝ a b ⊆ S → a = b := by
  refine ⟨fun h a b hab ↦ finite_segment_iff.mp (h.subset hab), fun h ↦ ?_⟩
  obtain ⟨E, hE, rfl⟩ := hS
  exact hE.biUnion fun e he ↦ finite_segment_iff.mpr <| h e.1 e.2 (fun x hx ↦ mem_biUnion he hx)

theorem countable_iff_finite (hS : IsSegmentFigure S) : S.Countable ↔ S.Finite :=
  ⟨fun h ↦ hS.finite_iff.mpr fun _ _ hsub ↦ countable_segment_iff.mp (h.mono hsub),
    Finite.countable⟩

theorem infinite_iff (hS : IsSegmentFigure S) : S.Infinite ↔ ∃ a b, a ≠ b ∧ segment ℝ a b ⊆ S := by
  rw [Set.Infinite, hS.finite_iff]
  push Not
  aesop

end IsSegmentFigure

end
