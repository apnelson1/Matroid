import Matroid.Matroid

open Matroid Set

-- theorem foo {α : Type _} {a₀ : α} {f : α → ℕ} {P : α → Prop} {g : α → α}
--     (hg : ∀ a, a ≠ a₀ → f (g a) < f a) (h₁ : P a₀) (h₂ : ∀ a, P (g a) → P a) (x : α) : P x := by
   
--   obtain (rfl | h) := eq_or_ne x a₀
--   · exact h₁
  
--   have _ : f (g x) < f x := hg _ h 
--   -- gives decreasing_by 

--   exact h₂ x (foo hg h₁ h₂ (g x))
-- termination_by _ => f x

-- theorem foo' {α : Type _} {a₀ : α} {f : α → ℕ} {P : α → Prop} {g : α → α}
--     (hg : ∀ a, a ≠ a₀ → f (g a) < f a) (h₁ : P a₀) (h₂ : ∀ a, P (g a) → P a) (x : α) : P x := by
   
--   obtain (rfl | h) := eq_or_ne x a₀
--   · exact h₁
  
--   have h' : f (g x) < f x
--   · exact hg _ h 
--   -- gives decreasing_by 

--   exact h₂ x (foo hg h₁ h₂ (g x))







theorem encard_diff_le_aux' {Base : Set α → Prop} (exch : exchange_property Base) 
    {B₁ B₂ : Set α} (hB₁ : Base B₁) (hB₂ : Base B₂) : (B₁ \ B₂).encard ≤ (B₂ \ B₁).encard := by
  obtain (hinf | hfin₂) := (B₂ \ B₁).finite_or_infinite.symm
  · rw [hinf.encard_eq]; apply le_top
  obtain (he | ⟨e,he⟩) := (B₂ \ B₁).eq_empty_or_nonempty
  · simp [antichain_of_exch exch hB₂ hB₁ (diff_eq_empty.mp he)] 
  obtain ⟨f, hf, hB'⟩ := exch B₂ B₁ hB₂ hB₁ e he
  
  have : ncard (insert f (B₂ \ {e}) \ B₁) < ncard (B₂ \ B₁) := by 
    ( rw [insert_diff_of_mem _ hf.1, diff_diff_comm]; 
      exact ncard_diff_singleton_lt_of_mem he hfin₂)

  have hencard := encard_diff_le_aux exch hB₁ hB'
  rw [insert_diff_of_mem _ hf.1, diff_diff_comm, ←union_singleton, ←diff_diff, diff_diff_right,
    inter_singleton_eq_empty.mpr he.2, union_empty] at hencard

  rw [←encard_diff_singleton_add_one he, ←encard_diff_singleton_add_one hf]
  exact add_le_add_right hencard 1
termination_by _ => (B₂ \ B₁).ncard