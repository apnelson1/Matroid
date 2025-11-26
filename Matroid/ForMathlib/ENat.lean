import Mathlib.Data.ENat.Lattice
import Mathlib.Order.SuccPred.CompleteLinearOrder


open WithTop

namespace ENat

variable {a b c x y m n : ℕ∞}

def recTopZeroCoe {C : ℕ∞ → Sort*} (top : C ⊤) (zero : C 0) (coe : (a : ℕ) → C ↑(a + 1)) (n : ℕ∞) :
    C n := by
  cases n with
  | top => assumption
  | coe n =>
  · cases n with
  | zero => assumption
  | succ n => exact coe n

-- this won't fire as `simp` without an explicit `ENat` version.
@[simp]
protected theorem add_eq_top : x + y = ⊤ ↔ x = ⊤ ∨ y = ⊤ :=
  WithTop.add_eq_top

protected theorem add_ne_top : x + y ≠ ⊤ ↔ x ≠ ⊤ ∧ y ≠ ⊤ :=
  by simp

protected theorem top_mul_eq_ite (a : ℕ∞) : ⊤ * a = if a = 0 then 0 else ⊤ := by
  split_ifs with h
  · simp [h]
  simp [top_mul h]

protected theorem mul_top_eq_ite (a : ℕ∞) : a * ⊤ = if a = 0 then 0 else ⊤ := by
  rw [mul_comm, ENat.top_mul_eq_ite]

theorem mul_eq_top_iff : a * b = ⊤ ↔ (a = ⊤ ∧ b ≠ 0) ∨ (a ≠ 0 ∧ b = ⊤) := by
  cases a with
  | top => simp +contextual [ENat.top_mul_eq_ite]
  | coe a =>
  cases b with
  | top => simp +contextual [ENat.mul_top_eq_ite]
  | coe b => simp only [coe_ne_top, ne_eq, Nat.cast_eq_zero, false_and, and_false, or_self,
    ← coe_mul]

@[simp]
theorem add_eq_left_iff {a b : ℕ∞} : a + b = a ↔ a = ⊤ ∨ b = 0 := by
  cases a with
  | top => simp
  | coe a => cases b with | top => simp | coe b => norm_cast; simp

@[simp]
theorem add_eq_right_iff {a b : ℕ∞} : a + b = b ↔ a = 0 ∨ b = ⊤ := by
  rw [add_comm, add_eq_left_iff, or_comm]

@[simp]
theorem eq_add_right_iff {a b : ℕ∞} : b = a + b ↔ a = 0 ∨ b = ⊤ := by
  rw [eq_comm, add_eq_right_iff]

@[simp]
theorem eq_add_left_iff {a b : ℕ∞} : a = a + b ↔ b = 0 ∨ a = ⊤ := by
  rw [eq_comm, add_eq_left_iff, or_comm]

@[simp]
theorem add_le_left_iff {a b : ℕ∞} : a + b ≤ a ↔ a = ⊤ ∨ b = 0 := by
  rw [← add_eq_left_iff, le_antisymm_iff, and_iff_left (by simp)]

@[simp]
theorem add_le_right_iff {a b : ℕ∞} : a + b ≤ b ↔ a = 0 ∨ b = ⊤ := by
  rw [add_comm, add_le_left_iff, or_comm]

@[simp]
lemma add_one_le_add_one_iff {a b : ℕ∞} : a + 1 ≤ b + 1 ↔ a ≤ b :=
  WithTop.add_le_add_iff_right (by simp)

@[simp]
lemma one_add_le_one_add_iff {a b : ℕ∞} : 1 + a ≤ 1 + b ↔ a ≤ b :=
  WithTop.add_le_add_iff_left (by simp)

@[simp]
lemma add_one_lt_add_one_iff {a b : ℕ∞} : a + 1 < b + 1 ↔ a < b :=
  WithTop.add_lt_add_iff_right (by simp)

@[simp]
lemma one_add_lt_one_add_iff {a b : ℕ∞} : 1 + a < 1 + b ↔ a < b :=
  WithTop.add_lt_add_iff_left (by simp)

@[simp]
lemma add_one_inj {a b : ℕ∞} : a + 1 = b + 1 ↔ a = b :=
  WithTop.add_right_inj (by simp)

@[simp]
lemma one_add_inj {a b : ℕ∞} : 1 + a = 1 + b ↔ a = b :=
  WithTop.add_left_inj (by simp)

lemma lt_add_right_iff {a b : ℕ∞} : a < a + b ↔ a ≠ ⊤ ∧ b ≠ 0 := by
  obtain rfl | hne := eq_zero_or_pos b
  · simp
  cases a with
  | top => simp
  | coe a =>
  · cases b with
    | top => simp
    | coe b =>
    · norm_cast at *
      simp [hne, hne.ne.symm]

lemma lt_add_left_iff {a b : ℕ∞} : b < a + b ↔ b ≠ ⊤ ∧ a ≠ 0 := by
  rw [add_comm, lt_add_right_iff]

@[simp]
lemma lt_add_one_self_iff {a : ℕ∞} : a < a + 1 ↔ a ≠ ⊤ := by
  simp [lt_add_right_iff]

@[simp]
lemma lt_one_add_self_iff {a : ℕ∞} : a < 1 + a ↔ a ≠ ⊤ := by
  simp [lt_add_left_iff]

lemma add_sub_cancel_right (a : ℕ∞) (hb : b ≠ ⊤) : a + b - b = a := by
  lift b to ℕ using hb
  cases a with
  | top => simp
  | coe a =>
    norm_cast
    exact Nat.add_sub_cancel_right ..

lemma add_sub_cancel_left (b : ℕ∞) (ha : a ≠ ⊤) : a + b - a = b := by
  rw [add_comm, add_sub_cancel_right _ ha]

lemma sub_eq_iff_eq_add {a k : ℕ∞} (hka : k ≤ a) (hne : k ≠ ⊤) : a - k = b ↔ a = b + k := by
  obtain ⟨c, rfl⟩ := exists_add_of_le hka
  rw [add_sub_cancel_left _ hne, add_comm, WithTop.add_right_inj hne]

protected lemma mul_lt_mul_right_iff (hc0 : c ≠ 0) (hc : c ≠ ⊤) : a * c < b * c ↔ a < b := by
  rw [lt_iff_le_and_ne, ENat.mul_le_mul_right_iff hc0 hc, Ne,
    (ENat.mul_left_strictMono hc0 hc).injective.eq_iff, lt_iff_le_and_ne]

protected lemma mul_lt_mul_left_iff (hc0 : c ≠ 0) (hc : c ≠ ⊤) : c * a < c * b ↔ a < b := by
  simp_rw [mul_comm c, ENat.mul_lt_mul_right_iff hc0 hc]

section Parity

@[simp]
protected lemma even_top : Even (⊤ : ℕ∞) :=
  ⟨⊤, by simp⟩

@[simp]
protected lemma odd_top : Odd (⊤ : ℕ∞) :=
  ⟨⊤, by simp⟩

@[simp]
protected lemma even_natCast {n : ℕ} : Even (n : ℕ∞) ↔ Even n := by
  refine ⟨fun ⟨r, hr⟩ ↦ ?_, fun ⟨r, hr⟩ ↦ ⟨r, by norm_cast⟩⟩
  lift r to ℕ using (by rintro rfl; simp at hr)
  obtain rfl : n = r + r := by norm_cast at hr
  exact Even.add_self r

@[simp]
protected lemma odd_natCast {n : ℕ} : Odd (n : ℕ∞) ↔ Odd n := by
  refine ⟨fun ⟨r, hr⟩ ↦ ?_, fun ⟨r, hr⟩ ↦ ⟨r, by norm_cast⟩⟩
  lift r to ℕ using (by rintro rfl; simp at hr)
  norm_cast at hr
  obtain rfl : n = 2 * r + 1 := by norm_cast at hr
  exact odd_two_mul_add_one r

protected lemma not_odd_iff_even {n : ℕ∞} (hn : n ≠ ⊤) : ¬ Odd n ↔ Even n := by
  lift n to ℕ using hn
  simp

protected lemma not_even_iff_odd {n : ℕ∞} (hn : n ≠ ⊤) : ¬ Even n ↔ Odd n := by
  rw [← ENat.not_odd_iff_even hn, not_not]

protected lemma even_or_odd (ha : a ≠ ⊤) : Even a ∨ Odd a := by
  lift a to ℕ using ha
  simp only [ENat.even_natCast, ENat.odd_natCast]
  exact Nat.even_or_odd a

protected lemma even_add {m n : ℕ∞} (hm : m ≠ ⊤) (hn : n ≠ ⊤) :
    Even (m + n) ↔ (Even m ↔ Even n) := by
  lift m to ℕ using hm
  lift n to ℕ using hn
  norm_cast
  simp only [ENat.even_natCast]
  rw [Nat.even_add]

end Parity
