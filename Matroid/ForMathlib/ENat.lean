import Mathlib.Data.ENat.Lattice
import Mathlib.Order.SuccPred.CompleteLinearOrder


open WithTop

namespace ENat

variable {a b c x y m n : ℕ∞}

-- this won't fire as `simp` without an explicit `ENat` version.
@[simp]
protected theorem add_eq_top : x + y = ⊤ ↔ x = ⊤ ∨ y = ⊤ :=
  WithTop.add_eq_top

protected theorem top_mul_eq_ite (a : ℕ∞) : ⊤ * a = if a = 0 then 0 else ⊤ := by
  split_ifs with h
  · simp [h]
  simp [top_mul h]

protected theorem mul_top_eq_ite (a : ℕ∞) : a * ⊤ = if a = 0 then 0 else ⊤ := by
  rw [mul_comm, ENat.top_mul_eq_ite]

theorem mul_left_strictMono (ha : a ≠ 0) (h_top : a ≠ ⊤) : StrictMono (a * ·) := by
  lift a to ℕ using h_top
  intro x y hxy
  induction x with
  | top => simp at hxy
  | coe x =>
  induction y with
  | top =>
    simp only [mul_top ha, ← ENat.coe_mul]
    exact coe_lt_top (a * x)
  | coe y =>
  simp only
  rw [← ENat.coe_mul, ← ENat.coe_mul, ENat.coe_lt_coe]
  rw [ENat.coe_lt_coe] at hxy
  exact Nat.mul_lt_mul_of_pos_left hxy (Nat.pos_of_ne_zero (by simpa using ha))

protected theorem mul_right_strictMono (ha : a ≠ 0) (h_top : a ≠ ⊤) : StrictMono (· * a) := by
  intro x y hxy
  simp only [mul_comm _ a]
  exact ENat.mul_left_strictMono ha h_top hxy

protected theorem mul_le_mul_left_iff (ha : a ≠ 0) (h_top : a ≠ ⊤) : a * x ≤ a * y ↔ x ≤ y :=
  (ENat.mul_left_strictMono ha h_top).le_iff_le

protected theorem mul_le_mul_right_iff (ha : a ≠ 0) (h_top : a ≠ ⊤) : x * a ≤ y * a ↔ x ≤ y :=
  (ENat.mul_right_strictMono ha h_top).le_iff_le

protected theorem self_le_mul_right (a : ℕ∞) (hc : c ≠ 0) : a ≤ a * c := by
  obtain rfl | hne := eq_or_ne a ⊤
  · simp [top_mul hc]
  obtain rfl | h0 := eq_or_ne a 0
  · simp
  nth_rewrite 1 [← mul_one a, ENat.mul_le_mul_left_iff h0 hne, ENat.one_le_iff_ne_zero]
  assumption

protected theorem self_le_mul_left (a : ℕ∞) (hc : c ≠ 0) : a ≤ c * a := by
  rw [mul_comm]
  exact ENat.self_le_mul_right a hc

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

section Lattice

variable {ι : Sort*}

@[simp] protected theorem iSup_zero_eq_zero : ⨆ _ : ι, (0 : ℕ∞) = 0 := by
  simp

protected lemma exists_eq_iInf {α : Type*} [Nonempty α] (f : α → ℕ∞) : ∃ a, f a = ⨅ x, f x := by
  obtain htop | hlt := eq_top_or_lt_top (⨅ x, f x)
  · rw [htop]
    simp only [iInf_eq_top] at htop
    exact ⟨Classical.arbitrary α, htop _⟩
  apply exists_eq_iInf_of_not_isPredPrelimit
  simp only [Order.IsPredPrelimit, not_forall, not_not]
  refine ⟨Order.succ (⨅ x, f x), Order.covBy_succ_of_not_isMax fun hmax ↦ ?_⟩
  simp only [isMax_iff_eq_top, iInf_eq_top] at hmax
  simp [hmax] at hlt

protected theorem mul_iSup (c : ℕ∞) (f : ι → ℕ∞) : c * (⨆ i, f i) = ⨆ i, (c * f i) := by
  refine (iSup_le fun i ↦ mul_le_mul' rfl.le <| le_iSup_iff.2 fun _ a ↦ a i).antisymm' <|
    le_iSup_iff.2 fun d h ↦ ?_
  obtain rfl | hne := eq_or_ne c 0
  · simp
  obtain hι | hι := isEmpty_or_nonempty ι
  · simp
  induction d using ENat.recTopCoe with
  | top => simp
  | coe d =>
  obtain htop | hlt := (le_top (a := ⨆ i, f i)).eq_or_lt
  · obtain ⟨i, hi : d < f i⟩ := (iSup_eq_top ..).1 htop d (by simp)
    exact False.elim <| (((h i).trans_lt hi).trans_le (ENat.self_le_mul_left _ hne)).ne rfl
  obtain ⟨j, hj⟩ := exists_eq_iSup_of_lt_top hlt
  rw [← hj]
  apply h

protected theorem iSup_mul (c : ℕ∞) (f : ι → ℕ∞) : (⨆ i, f i) * c = ⨆ i, (f i * c) := by
  simp_rw [mul_comm, ENat.mul_iSup]

end Lattice
