import Mathlib.Data.ENat.Lattice
import Mathlib.Order.SuccPred.CompleteLinearOrder


open WithTop

namespace ENat

variable {a b c x y m n : ℕ∞}

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
    iff_false, ← coe_mul]


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
