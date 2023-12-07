import Mathlib.Combinatorics.Colex

open Finset Colex Set Function



#check Finset.geomSum_lt_geomSum_iff_toColex_lt_toColex

theorem geomSum_two_surjective : Surjective (fun s : Finset ℕ ↦ s.sum (fun i ↦ 2^i)) := by
  intro n
  refine n.strong_induction_on (fun n h ↦ ?_)
  obtain (rfl | hpos) := n.eq_zero_or_pos
  · exact ⟨∅, by simp⟩
  obtain ⟨s,hs'⟩ := h (n/2) sorry
  obtain (he | ho) := n.even_or_odd
  ·


example : Colex ℕ ≃o ℕ where
  toFun s:= s.ofColex.sum (fun i ↦ 2 ^ i)
  invFun := _
  left_inv := _
  right_inv := _
  map_rel_iff' := _
