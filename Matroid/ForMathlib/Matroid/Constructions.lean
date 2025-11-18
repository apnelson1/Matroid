import Mathlib.Combinatorics.Matroid.Constructions

namespace Matroid

variable {α : Type*}

lemma exists_eq_loopyOn_or_rankPos (M : Matroid α) : (∃ E, M = loopyOn E) ∨ M.RankPos := by
  obtain h1 | h2 := M.eq_loopyOn_or_rankPos
  · exact .inl ⟨M.E, h1⟩
  exact .inr h2

lemma exists_eq_freeOn_or_rankPos_dual (M : Matroid α) : (∃ E, M = freeOn E) ∨ M✶.RankPos := by
  obtain ⟨E, h⟩ | h  := M✶.exists_eq_loopyOn_or_rankPos
  · exact .inl ⟨E, by simpa using dual_inj.2 h⟩
  exact .inr h
