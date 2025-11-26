import Mathlib.Data.ENat.Lattice

variable {a b c : ℕ∞}

namespace ENat

protected theorem top_mul_eq_ite (a : ℕ∞) : ⊤ * a = if a = 0 then 0 else ⊤ := by
  split_ifs with h
  · simp [h]
  simp [top_mul h]

protected theorem mul_top_eq_ite (a : ℕ∞) : a * ⊤ = if a = 0 then 0 else ⊤ := by
  rw [mul_comm, ENat.top_mul_eq_ite]

protected theorem mul_eq_top_iff : a * b = ⊤ ↔ (a = ⊤ ∧ b ≠ 0) ∨ (a ≠ 0 ∧ b = ⊤) := by
  cases a with
  | top => simp +contextual [ENat.top_mul_eq_ite]
  | coe a =>
  cases b with
  | top => simp +contextual [ENat.mul_top_eq_ite]
  | coe b => simp only [coe_ne_top, ne_eq, Nat.cast_eq_zero, false_and, and_false, or_self,
    ← coe_mul]

protected theorem add_eq_top_iff : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ := by
  rw [WithTop.add_eq_top]

-- protected theorem add_eq_top_iff : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ := by
--   rw [WithTop.add_eq_top]
