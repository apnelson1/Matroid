import Mathlib.Data.Nat.Basic

def add_five : ℕ → ℕ := fun x ↦ x+5 

postfix:max "*" => add_five

lemma star_succ (n : ℕ) : (n*).succ = n.succ* := by 
  simp [add_five]

-- lemma star_succ' (n : ℕ) : n*.succ = n.succ* := by sorry
-- breaks without parentheses