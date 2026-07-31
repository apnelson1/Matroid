module

public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Algebra.Order.IsBotOne

@[expose] public section

namespace Set

lemma Icc_zero {α : Type*} [Zero α] [Preorder α] [IsBotZeroClass α] (x : α) : Icc 0 x = Iic x := by
  simp [Icc, Iic]

lemma Ico_zero {α : Type*} [Zero α] [Preorder α] [IsBotZeroClass α] (x : α) : Ico 0 x = Iio x := by
  simp [Ico, Iio]
