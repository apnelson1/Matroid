import Mathlib.Tactic

structure pt where 
  (n : ℕ)
  (m : ℕ)

def pt.left (P : pt) : ℕ := P.n
pp_extended_field_notation pt.left

example (P : pt) : 0 ≤ P.left := by
  simp

