module

public import Mathlib.Analysis.Normed.Module.Basic

/-!
# The normed space `Fin 1 → ℝ`

With the sup norm, `Fin 1 → ℝ` is the real line: its norm is the absolute value of the single
coordinate, so its closed unit ball is `[-1, 1]` and its unit sphere is the two-point set
`{-1, 1}`. Mathlib has the general `Pi.norm_def` but none of these specialisations, and the
one-dimensional cell of a CW structure needs all of them.
-/

@[expose] public section

open Set Metric

@[simp] lemma norm_le_one_iff_fin_one (x : Fin 1 → ℝ) : ‖x‖ ≤ 1 ↔ ‖x 0‖ ≤ 1 := by
  simp [Pi.norm_def]

@[simp] lemma norm_lt_one_iff_fin_one (x : Fin 1 → ℝ) : ‖x‖ < 1 ↔ ‖x 0‖ < 1 := by
  simp [Pi.norm_def]

@[simp] lemma norm_eq_one_iff_fin_one (x : Fin 1 → ℝ) : ‖x‖ = 1 ↔ ‖x 0‖ = 1 := by
  simp [Pi.norm_def]

/-- The unit sphere of `Fin 1 → ℝ` is its two-point boundary. -/
lemma sphere_fin_one : sphere (0 : Fin 1 → ℝ) 1 = {-1, 1} := by
  ext f
  simp only [mem_sphere_iff_norm, sub_zero, mem_insert_iff, mem_singleton_iff,
    norm_eq_one_iff_fin_one, Real.norm_eq_abs]
  refine ⟨fun hf ↦ ((abs_eq (zero_le_one' ℝ)).1 hf).symm.imp ?_ ?_, by rintro (rfl | rfl) <;> simp⟩
  <;>
  · intro h0
    ext i
    fin_cases i
    simp [h0]
