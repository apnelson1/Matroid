import Mathlib.Data.ENat.Basic
import Mathlib.Data.Nat.Cast.WithTop

-- this easy lemma is provable by well-founded induction  
theorem wf1 (P : ℕ∞ → Prop) (h0 : P 0) (h : ∀ k, 0 < k → ∃ t, t < k ∧ (P t → P k)) (n : ℕ∞) :
    P n := by 
  refine' WellFounded.induction (r := (· < ·)) IsWellFounded.wf _ (fun x h' ↦ _)
  obtain ((rfl : x = 0) | hpos) := eq_zero_or_pos 
  · exact h0
  obtain ⟨t, ht, hPt⟩ := h x hpos
  exact hPt (h' _ ht)



-- Same lemma statement; this time, we try to prove it by invoking itself on a smaller value. 
theorem wf2 (P : ℕ∞ → Prop) (h0 : P 0) (h : ∀ k, 0 < k → ∃ t, t < k ∧ (P t → P k)) (n : ℕ∞) :
    P n := by 
  obtain ((rfl : n = 0) | hn) := eq_zero_or_pos 
  · exact h0
  obtain ⟨t, _, hPt⟩ := h n hn  
  exact hPt (wf2 P h0 h t)

termination_by' instWellFoundedRelationWithTopNat
  






  
  -- goal should simplify to `t < n`, but instead simplifies to `False` ?? 