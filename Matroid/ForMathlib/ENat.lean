import Mathlib.Data.ENat.Lattice
import Mathlib.Order.SuccPred.CompleteLinearOrder


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

lemma ENat.exists_eq_iInf {α : Type*} [Nonempty α] (f : α → ℕ∞) : ∃ a, f a = ⨅ x, f x := by
  obtain htop | hlt := eq_top_or_lt_top (⨅ x, f x)
  · rw [htop]
    simp only [iInf_eq_top] at htop
    exact ⟨Classical.arbitrary α, htop _⟩
  apply exists_eq_iInf_of_not_isPredPrelimit
  simp only [Order.IsPredPrelimit, not_forall, not_not]
  refine ⟨Order.succ (⨅ x, f x), Order.covBy_succ_of_not_isMax fun hmax ↦ ?_⟩
  simp only [isMax_iff_eq_top, iInf_eq_top] at hmax
  simp [hmax] at hlt
