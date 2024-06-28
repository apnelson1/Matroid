import Matroid.Minor.Basic

namespace Matroid

variable {α : Type*}

def Quotient (M N : Matroid α) : Prop :=
  M.E = N.E ∧ ∀ F, M.Flat F → N.Flat F

def WeakLE (M N : Matroid α) : Prop :=
  M.E = N.E ∧ ∀ D, N.Dep D → M.Dep D

infixl:50 " ≤q " => Matroid.Quotient

infixl:50 " ≤w " => Matroid.WeakLE
