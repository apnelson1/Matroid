import Mathlib.Data.ENat.Basic


open WithTop
-- variable {α : Type*} {a x y : WithTop α} [DecidableEq α]

variable {a x y : ℕ∞}

theorem ENat.mul_left_strictMono (ha : a ≠ 0) (h_top : a ≠ ⊤) : StrictMono (a * ·) := by
  lift a to ℕ using h_top
  intro x y hxy
  induction' x with x
  · simp at hxy
  induction' y with y
  · simp only [mul_top ha, ← ENat.coe_mul]
    exact coe_lt_top (a * x)
  simp only
  rw [← ENat.coe_mul, ← ENat.coe_mul, ENat.coe_lt_coe]
  rw [ENat.coe_lt_coe] at hxy
  exact Nat.mul_lt_mul_of_pos_left hxy (Nat.pos_of_ne_zero (by simpa using ha))

theorem ENat.mul_right_strictMono (ha : a ≠ 0) (h_top : a ≠ ⊤) : StrictMono (· * a) := by
  intro x y hxy
  simp only [mul_comm _ a]
  exact ENat.mul_left_strictMono ha h_top hxy

theorem ENat.mul_le_mul_left_iff (ha : a ≠ 0) (h_top : a ≠ ⊤) : a * x ≤ a * y ↔ x ≤ y :=
  (ENat.mul_left_strictMono ha h_top).le_iff_le

theorem ENat.mul_le_mul_right_iff (ha : a ≠ 0) (h_top : a ≠ ⊤) : x * a ≤ y * a ↔ x ≤ y :=
  (ENat.mul_right_strictMono ha h_top).le_iff_le


  -- rintro (rfl | x : ℕ∞) (rfl | y : ℕ∞) h
  -- · simp at h
  -- · simp [none_eq_top] at h
  -- · simp only [some_eq_coe, ENat.some_eq_coe, none_eq_top, mul_top ha, lt_top_iff_ne_top]
  --   norm_cast
  --   exact ENat.coe_ne_top (a * x)
  -- simp only [WithTop.some_eq_coe] at h ⊢
  -- replace ha := Nat.pos_of_ne_zero (by simpa using ha)
  -- rw [← ENat.coe_mul]
  -- have := mul_left_strictMono
  -- have := ENat.coe_mul a x
  -- rw [← ENat.coe_mul a x]
