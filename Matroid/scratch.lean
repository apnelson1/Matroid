import Mathlib.Combinatorics.SimpleGraph.Coloring

variable {α : Type*} {P : ℕ → ℕ → Prop} (f : ℕ → ℕ)

theorem foo (h0 : P 0 0) (h : ∀ x y, P (f x) (y - 1) → P x y) (a b : ℕ) : P a b := by
  by_cases h' : a = 0 ∧ b = 0
  · rwa [h'.1, h'.2]
  apply h
  have h' : (f (a -1)) + (b - 1) < f a + b := sorry
  exact foo h0 h (a-1) (b - 1)
termination_by f a + b

  -- apply h (a - 1) (b-1)
