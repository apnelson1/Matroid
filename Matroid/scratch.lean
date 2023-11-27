import Mathlib.Data.Finset.Card

def P : Finset ℕ → Prop := sorry

theorem hP {s : Finset ℕ} (hs : ¬ P s) : ∃ t, t ⊂ s ∧ ¬ P t  := sorry

theorem foo1 (s : Finset ℕ) : P s := by
  by_contra h
  obtain ⟨t, ht, hPt⟩ := hP h

  have h_lt : t.card < s.card
  · exact Finset.card_lt_card ht

  exact hPt <| foo1 t
termination_by _ => s.card

-- failed to prove termination, possible solutions:
--   - Use `have`-expressions to prove the remaining goals
--   - Use `termination_by` to specify a different well-founded relation
--   - Use `decreasing_by` to specify your own tactic for discharging this kind of goal


theorem foo2 (s : Finset ℕ) : P s := by
  by_contra h
  obtain ⟨t, ht, hPt⟩ := hP h

  have h_lt : t.card < s.card := Finset.card_lt_card ht

  exact hPt <| foo2 t
termination_by _ => s.card

-- succeeds
