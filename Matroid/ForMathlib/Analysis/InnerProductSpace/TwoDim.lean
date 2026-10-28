module

public import Mathlib.Analysis.InnerProductSpace.TwoDim

/-! # Lines as fibres of the planar area form -/

@[expose] public section

open Set Module

namespace Orientation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (finrank ℝ E = 2)] (o : Orientation ℝ E (Fin 2))

open scoped RealInnerProductSpace in
/-- The vectors with zero area against a nonzero vector are its scalar multiples. -/
theorem areaForm_eq_zero_iff {v p : E} (hv : v ≠ 0) :
    o.areaForm v p = 0 ↔ ∃ t : ℝ, p = t • v := by
  constructor
  · intro h
    by_cases hn : 0 ≤ inner ℝ v p
    · obtain ⟨t, -, ht⟩ := ((o.nonneg_inner_and_areaForm_eq_zero_iff_sameRay v p).mp
        ⟨hn, h⟩).exists_nonneg_left hv
      exact ⟨t, ht.symm⟩
    have hr : SameRay ℝ v (-p) :=
      (o.nonneg_inner_and_areaForm_eq_zero_iff_sameRay v (-p)).mp
        ⟨by simpa only [inner_neg_right, neg_nonneg] using (le_of_not_ge hn), by simp [h]⟩
    obtain ⟨t, -, ht⟩ := hr.exists_nonneg_left hv
    exact ⟨-t, by simpa using congrArg Neg.neg ht.symm⟩
  · rintro ⟨t, rfl⟩
    simp

/-- The kernel of area against a nonzero vector is the line it spans. -/
theorem areaForm_ker {v : E} (hv : v ≠ 0) :
    LinearMap.ker (o.areaForm v) = Submodule.span ℝ {v} := by
  ext p
  simp only [LinearMap.mem_ker, o.areaForm_eq_zero_iff hv, Submodule.mem_span_singleton]
  exact exists_congr fun t ↦ eq_comm

/-- Each fibre of area against a nonzero vector is an affine line in that direction. -/
theorem areaForm_eq_iff {v p q : E} (hv : v ≠ 0) :
    o.areaForm v p = o.areaForm v q ↔ ∃ t : ℝ, p = q + t • v := by
  rw [← sub_eq_zero, ← map_sub, o.areaForm_eq_zero_iff hv]
  exact exists_congr fun t ↦ by rw [sub_eq_iff_eq_add]; exact add_comm (t • v) q ▸ Iff.rfl

theorem areaForm_ne_zero_iff_linearIndependent {u v : E} :
    o.areaForm u v ≠ 0 ↔ LinearIndependent ℝ ![u, v] := by
  rw [linearIndependent_fin2]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  constructor
  · intro h
    refine ⟨fun hv ↦ h (by simp [hv]), ?_⟩
    intro t ht
    apply h
    rw [← ht]
    simp
  · rintro ⟨hv, hlin⟩ h
    have h' : o.areaForm v u = 0 := by rw [o.areaForm_swap, h, neg_zero]
    obtain ⟨t, ht⟩ := (o.areaForm_eq_zero_iff hv).mp h'
    exact hlin t ht.symm

end Orientation
