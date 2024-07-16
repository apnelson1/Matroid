import Mathlib.Data.Finset.Basic

example : ∀ x y : ℕ, x < 5 → 7 < y → x < 5 := by
  simp (config := {contextual := true})
