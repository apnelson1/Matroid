module

public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Data.Set.Function
public import Mathlib.Order.Nat
public import Init.Data.Nat.Div.Basic
-- public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

open Nat

namespace Set

lemma Icc_zero {α : Type*} [Zero α] [Preorder α] [IsBotZeroClass α] (x : α) : Icc 0 x = Iic x := by
  simp [Icc, Iic]

lemma Ico_zero {α : Type*} [Zero α] [Preorder α] [IsBotZeroClass α] (x : α) : Ico 0 x = Iio x := by
  simp [Ico, Iio]

lemma mod_injOn_Iio (n : ℕ) : InjOn (fun x ↦ x % n) (Iio n) :=
  fun x hx y hy hxy ↦ by simpa [mod_eq_of_lt hx, mod_eq_of_lt hy] using hxy

lemma add_mod_bijOn_Iio (n k : ℕ) : BijOn (fun i ↦ (i + k) % n) (Iio n) (Iio n) := by
  obtain rfl | n := n
  · simp
  refine ⟨fun i hi ↦ mod_lt _ (by simp), fun i hi j hj hij ↦ mod_injOn_Iio _ hi hj ?_, ?_⟩
  · obtain ⟨i', j', hij⟩ := mod_eq_mod_iff.1 hij
    rw [Nat.add_right_comm, j.add_right_comm, Nat.add_left_inj] at hij
    simpa using congr_arg (fun x ↦ x % (n + 1)) hij
  refine fun x hx ↦ ⟨(x + (n + 1) - (k % (n + 1))) % (n + 1), mod_lt _ (by simp), ?_⟩
  simp only [mod_add_mod]
  rw [Nat.add_comm, ← mod_add_mod, Nat.add_comm,
    Nat.sub_add_cancel (by grind [Nat.mod_lt k (show 0 < n + 1 by simp)])]
  simpa
