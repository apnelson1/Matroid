import Mathlib.Data.Real.Basic
import Mathlib.Data.Countable.Defs

theorem foo : ∃ f : ℝ → ℝ → Bool, ∀ x y, x < y → f x y = f y x ∧
  ∀ (S : Set ℝ), (∃ c, ∀ x < y, x ∈ S → y ∈ S → f x y = c) → Countable S := sorry
