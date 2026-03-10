import Mathlib.Data.ENat.Basic

example : (2 : ℕ∞) < (5 : ℕ∞) := by
  norm_num -- fails
  sorry

example {a b : ℕ∞} (hab : a ≤ b) : min a b = a := by
  rw [min_eq_left] -- fails
  -- exact? gives
  -- exact Std.LawfulOrderLeftLeaningMin.min_eq_left a b hab
  -- exact min_eq_left hab -- succeeds
