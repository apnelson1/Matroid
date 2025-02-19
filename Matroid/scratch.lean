import Mathlib

structure MyType (α M : Type*) where
  a₀ : α
  to_fun : α → M

variable {α M : Type*}

def MyPred [FunLike M ℕ ℝ] (A : MyType α M) : Prop := A.to_fun A.a₀ 3 = 37

example (A : MyType α (ℕ →₀ ℝ)) : MyPred A := sorry
-- typechecks fine

example (A : MyType α (ℕ → ℝ)) : MyPred A := sorry
-- failed to synthesize `FunLike (ℕ → ℝ) ℕ ℝ`
