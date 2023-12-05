import Mathlib.Data.Set.Card

open Set BigOperators

variable {s : Set α} {n : ℕ}

@[simp] theorem encard_pair_le (e f : α) : encard {e,f} ≤ 2 := by
  obtain (rfl | hne) := eq_or_ne e f
  · simp only [mem_singleton_iff, insert_eq_of_mem, encard_singleton]; norm_num
  rw [encard_pair hne]

theorem Set.coe_le_encard_iff : n ≤ s.encard ↔ (s.Finite → n ≤ s.ncard) := by
  obtain (hfin | hinf) := s.finite_or_infinite
  · rw [← hfin.cast_ncard_eq, iff_true_intro hfin, Nat.cast_le, true_imp_iff]
  rw [hinf.encard_eq, iff_true_intro le_top, true_iff, iff_false_intro hinf, false_imp_iff]
  trivial

theorem Fin.nonempty_embedding_iff_le_encard : Nonempty (Fin n ↪ s) ↔ n ≤ s.encard := by
  refine ⟨fun ⟨i⟩ ↦ ?_, fun h ↦ ?_⟩
  · convert ((Equiv.Set.univ (Fin n)).toEmbedding.trans i).enccard_le
    simp [encard_univ]
  obtain ⟨t, hts, hcard⟩ := exists_subset_encard_eq h
  have ht : t.Finite := finite_of_encard_eq_coe hcard
  rw [←ht.cast_ncard_eq, Nat.cast_inj, ncard_eq_toFinset_card t ht] at hcard
  refine ⟨(Finset.equivFinOfCardEq hcard).symm.toEmbedding.trans ?_ ⟩
  simp only [Finite.mem_toFinset]
  exact embeddingOfSubset t s hts

@[simp] theorem PartENat.card_option (α : Type*) :
    PartENat.card (Option α) = PartENat.card α + 1 := by
  obtain (hα | hα) := finite_or_infinite α
  · have _ := Fintype.ofFinite α; simp
  simp

#check Finset.card_biUnion

-- theorem encard_iUnion {ι : Type*} [Fintype ι] (s : ι → Set α) (hs : univ.PairwiseDisjoint s) :
--     encard (⋃ i, s i) = ∑ i, encard (s i) := by
--   obtain (⟨i, hi⟩ | h) := em <| ∃ i, (s i).Infinite
--   · rw [(hi.mono (subset_iUnion s i)).encard_eq]
--     rw [sum_compl]
