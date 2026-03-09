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

@[simp]
lemma freeOn_rankPos_iff {E : Set α} : (freeOn E).RankPos ↔ E.Nonempty := by
  simp [rankPos_iff, Set.nonempty_iff_ne_empty, eq_comm]

@[simps! E IsBase] protected def ofExistsMatroidBase (E : Set α) (Base : Set α → Prop)
    (hM : ∃ (M : Matroid α), E = M.E ∧ ∀ I, M.IsBase I ↔ Base I) : Matroid α :=
  have hex : ∃ (M : Matroid α), E = M.E ∧ M.IsBase = Base := by
    obtain ⟨M, rfl, h⟩ := hM; refine ⟨_, rfl, funext (by simp [h])⟩
  Matroid.ofBase (E := E) (IsBase := Base)
  (exists_isBase := by obtain ⟨M, -, rfl⟩ := hex; exact M.exists_isBase)
  (isBase_exchange := by obtain ⟨M, -, rfl⟩ := hex; exact M.isBase_exchange)
  (maximality := by obtain ⟨M, rfl, rfl⟩ := hex; convert M.maximality with B hI I; rw [M.indep_iff])
  (subset_ground := by obtain ⟨M, rfl, rfl⟩ := hex; exact fun _ ↦ IsBase.subset_ground)
