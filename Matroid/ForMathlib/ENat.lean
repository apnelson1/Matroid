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

@[simp]
lemma ENat.even_top : Even (⊤ : ℕ∞) := ⟨⊤, by simp⟩

@[simp]
lemma ENat.odd_top : Odd (⊤ : ℕ∞) := ⟨⊤, by simp⟩

@[simp]
lemma ENat.even_natCast {n : ℕ} : Even (n : ℕ∞) ↔ Even n := by
  refine ⟨fun ⟨r, hr⟩ ↦ ?_, fun ⟨r, hr⟩ ↦ ⟨r, by norm_cast⟩⟩
  lift r to ℕ using (by rintro rfl; simp at hr)
  obtain rfl : n = r + r := by norm_cast at hr
  exact Even.add_self r

@[simp]
lemma ENat.odd_natCast {n : ℕ} : Odd (n : ℕ∞) ↔ Odd n := by
  refine ⟨fun ⟨r, hr⟩ ↦ ?_, fun ⟨r, hr⟩ ↦ ⟨r, by norm_cast⟩⟩
  lift r to ℕ using (by rintro rfl; simp at hr)
  norm_cast at hr
  obtain rfl : n = 2 * r + 1 := by norm_cast at hr
  exact odd_two_mul_add_one r

lemma ENat.not_odd_iff_even {n : ℕ∞} (hn : n ≠ ⊤) : ¬ Odd n ↔ Even n := by
  lift n to ℕ using hn
  simp

lemma ENat.not_even_iff_odd {n : ℕ∞} (hn : n ≠ ⊤) : ¬ Even n ↔ Odd n := by
  rw [← not_odd_iff_even hn, not_not]

lemma ENat.even_or_odd (ha : a ≠ ⊤) : Even a ∨ Odd a := by
  lift a to ℕ using ha
  simp only [ENat.even_natCast, ENat.odd_natCast]
  exact Nat.even_or_odd a

lemma ENat.even_add {m n : ℕ∞} (hm : m ≠ ⊤) (hn : n ≠ ⊤) : Even (m + n) ↔ (Even m ↔ Even n) := by
  lift m to ℕ using hm
  lift n to ℕ using hn
  norm_cast
  simp only [even_natCast]
  rw [Nat.even_add]
