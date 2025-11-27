import Mathlib.Tactic.Attr.Register
import Mathlib.Data.ENat.Basic

namespace ENat

section ENat

variable {a b c : ℕ∞}

-- Some `ENat` lemmas that should exist anyway.

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

-- `WithTop.add_eq_top` doesn't work with simp.
protected theorem add_eq_top : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ := WithTop.add_eq_top

@[simp]
protected theorem add_one_eq_top : a + 1 = ⊤ ↔ a = ⊤ := by
  simp [ENat.add_eq_top]

-- The lemmas below can be used in a first pass to rephrase some
-- low-hanging fruit in terms of zero/top equalities.

protected theorem add_le_left_iff : a + b ≤ a ↔ a = ⊤ ∨ b = 0 := by
  cases a with
  | top => simp
  | coe a => cases b with
    | top => simp
    | coe b => norm_cast; simp

protected theorem add_le_right_iff : a + b ≤ b ↔ a = 0 ∨ b = ⊤ := by
  rw [add_comm, ENat.add_le_left_iff, or_comm]

protected theorem add_eq_left_iff : a + b = a ↔ a = ⊤ ∨ b = 0 := by
  rw [← ENat.add_le_left_iff, le_antisymm_iff, and_iff_left (self_le_add_right ..)]

protected theorem add_eq_right_iff : a + b = b ↔ a = 0 ∨ b = ⊤ := by
  rw [← add_comm, ENat.add_eq_left_iff, or_comm]

protected theorem eq_left_add_iff : a = a + b ↔ a = ⊤ ∨ b = 0 := by
  rw [eq_comm, ENat.add_eq_left_iff]

protected theorem eq_right_add_iff : b = a + b ↔ b = ⊤ ∨ a = 0 := by
  rw [eq_comm, ENat.add_eq_right_iff, or_comm]

protected theorem lt_add_left_iff : a < a + b ↔ a ≠ ⊤ ∧ b ≠ 0 := by
  simp [lt_iff_le_and_ne, ENat.eq_left_add_iff]

protected theorem lt_add_right_iff : a < b + a ↔ a ≠ ⊤ ∧ b ≠ 0 := by
  rw [add_comm, ENat.lt_add_left_iff, and_comm]

protected lemma add_eq_add_left_iff : a + b = a + c ↔ b = c ∨ a = ⊤ := by
  cases a with simp [WithTop.add_left_inj (ENat.coe_ne_top _)]

protected lemma add_eq_add_right_iff : a + c = b + c ↔ a = b ∨ c = ⊤ := by
  simp [add_comm _ c, ENat.add_eq_add_left_iff]

protected lemma add_le_add_left_iff : a + b ≤ a + c ↔ b ≤ c ∨ a = ⊤ := by
  cases a with simp [WithTop.add_le_add_iff_left (ENat.coe_ne_top _)]

protected lemma add_le_add_right_iff : a + c ≤ b + c ↔ a ≤ b ∨ c = ⊤ := by
  simp [add_comm _ c, ENat.add_le_add_left_iff]

protected lemma add_lt_add_left_iff : a + b < a + c ↔ b < c ∧ a ≠ ⊤ := by
  cases a with simp [WithTop.add_lt_add_iff_left (ENat.coe_ne_top _)]

protected lemma add_lt_add_right_iff : a + c < b + c ↔ a < b ∧ c ≠ ⊤ := by
  simp [add_comm _ c, ENat.add_lt_add_left_iff]

end ENat

register_simp_attr enat_grind_presimp
register_simp_attr enat_grind_canonize
