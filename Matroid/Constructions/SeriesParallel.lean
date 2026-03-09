import Matroid.Uniform
import Matroid.ForMathlib.Matroid.Constructions

namespace Matroid

open Set

variable {α : Type*} {M M' N : Matroid α} {e f : α} {I C J R B X Y Z K S P : Set α}

@[simps! E]
def seriesParallelDuo (S P : Set α) (hdj : Disjoint S P) :=
  Matroid.ofExistsMatroid (S ∪ P)
    (fun I ↦ (S = ∅ ∧ (unifOn P 1).Indep I) ∨ (P = ∅ ∧ (circuitOn S).Indep I) ∨
    (S.Nonempty ∧ P.Nonempty ∧ ((freeOn S).disjointSum (loopyOn P) hdj).freeLift.truncate.Indep I))
    (by
      obtain rfl | hPne := P.eq_empty_or_nonempty
      · exact ⟨circuitOn S, by simp, by by_cases hne : S = ∅ <;> simp [hne]⟩
      obtain rfl | hSne := S.eq_empty_or_nonempty
      · exact ⟨unifOn P 1, by simp, by simp⟩
      exact ⟨((freeOn S).disjointSum (loopyOn P) hdj).freeLift.truncate,
        by simp [hSne.ne_empty, hPne.ne_empty, hPne, hSne]⟩)

@[simp]
lemma seriesParallelDuo_empty_left : seriesParallelDuo ∅ P (by simp) = unifOn P 1 :=
  ext_indep (by simp) <| by simp +contextual [seriesParallelDuo, Matroid.ofExistsMatroid]

@[simp]
lemma seriesParallelDuo_empty_right : seriesParallelDuo S ∅ (by simp) = circuitOn S :=
  ext_indep (by simp) <| by simp +contextual [seriesParallelDuo, Matroid.ofExistsMatroid]

lemma seriesParallelDuo_nonempty_eq (hS : S.Nonempty) (hP : P.Nonempty) (hdj : Disjoint S P) :
    seriesParallelDuo S P hdj = ((freeOn S).disjointSum (loopyOn P) hdj).freeLift.truncate :=
  ext_indep (by simp) <| by
    simp [seriesParallelDuo, hS.ne_empty, hP.ne_empty, hS, hP, Matroid.ofExistsMatroid]

lemma seriesParallelDuo_rankPos (hP : P.Nonempty) (hdj : Disjoint S P) :
    (seriesParallelDuo S P hdj).RankPos := by
  obtain rfl | hne := S.eq_empty_or_nonempty
  · simp [rankPos_iff, unifOn_isBase_iff, one_le_encard_iff_nonempty.2 hP]
  have : (loopyOn P)✶.RankPos := by simp [freeOn_rankPos hP]
  suffices 2 ≤ S.encard + 1 by simpa [seriesParallelDuo_nonempty_eq hne hP]
  grw [← one_le_encard_iff_nonempty.2 hne, one_add_one_eq_two]

lemma seriesParallelDuo_dual_rankPos (hS : S.Nonempty) (hdj : Disjoint S P) :
    (seriesParallelDuo S P hdj)✶.RankPos := by
  obtain rfl | hne := P.eq_empty_or_nonempty
  · simpa [seriesParallelDuo_empty_right, circuitOn_dual]
  rw [seriesParallelDuo_nonempty_eq hS hne]
  have : (loopyOn S).Nonempty := ⟨hS⟩
  simp only [truncate_dual, freeLift_dual, disjointSum_dual, freeOn_dual_eq, loopyOn_dual_eq]
  infer_instance

@[simp]
lemma seriesParallelDuo_dual (hdj : Disjoint S P) :
    (seriesParallelDuo S P hdj)✶ = seriesParallelDuo P S hdj.symm := by
  obtain rfl | hSne := S.eq_empty_or_nonempty
  · simp [unifOn_one_dual]
  obtain rfl | hPne := P.eq_empty_or_nonempty
  · simp
  have hSp : (freeOn S).RankPos := freeOn_rankPos hSne
  have hPp : (loopyOn P)✶.RankPos := by simpa using freeOn_rankPos hPne
  rw [seriesParallelDuo_nonempty_eq hSne hPne hdj, ← truncate_freeLift,
    seriesParallelDuo_nonempty_eq hPne hSne, disjointSum_comm]
  simp

lemma seriesParallelDuo_indep_iff (hdj : Disjoint S P) (hS : S.Nonempty) (hP : P.Nonempty)
    {I : Set α} : (seriesParallelDuo S P hdj).Indep I ↔ I ⊆ S ∪ P ∧ (I ∩ P).Subsingleton ∧
      (S ⊆ I → S = I) := by
  obtain rfl | hne := I.eq_empty_or_nonempty
  · simp
  have : (loopyOn P)✶.RankPos := by simpa
  have : (loopyOn P).Nonempty := ⟨hP⟩
  -- have : (freeOn S)✶.RankPos := by
  --   simp
  rw [seriesParallelDuo_nonempty_eq hS hP, truncate_indep_iff, freeLift_indep_iff,
    freeLift_isBase_iff]
  simp only [hne, disjointSum_ground_eq, freeOn_ground, loopyOn_ground, mem_inter_iff, mem_union,
    disjointSum_indep_iff, diff_inter_right_comm, freeOn_indep_iff, diff_singleton_subset_iff,
    loopyOn_indep_iff, diff_eq_empty, subset_singleton_iff, and_imp, forall_const,
    disjointSum_isBase_iff, freeOn_isBase_iff, loopyOn_isBase_iff, not_and, forall_exists_index]

  refine ⟨fun ⟨⟨e, he, hdj, hI⟩, h2⟩ ↦ ⟨by grind, ?_, by grind⟩, fun ⟨hIss, hIP, hss⟩ ↦ ⟨?_, ?_⟩⟩
  ·
    exact subsingleton_singleton.anti hdj
  ·
    by_cases hSI : S ⊆ I
    · obtain rfl := hss hSI
      obtain ⟨f, hf⟩ := hne
      grind
    obtain hIP | ⟨f, hf⟩ := hIP.eq_empty_or_singleton
    · simp [diff_inter_right_comm, hIP]
      obtain ⟨x, hx⟩ := hne
      grind

    refine ⟨f, ?_, ?_⟩
    obtain ⟨f, hfS, hfI⟩ := not_subset.1 hSI



    -- have := h2 f hfI

  -- refine ⟨fun h hISP hIP hSI ↦ ?_, fun h ↦ ⟨?_, ?_⟩⟩
  -- · obtain ⟨⟨e, ⟨heI, heS | heP⟩, hdj, hxI⟩, hI⟩ := h
  --   · obtain rfl | hssu := hSI.eq_or_ssubset
  --     · rfl
  --     obtain ⟨f, hfI, hfS⟩ := exists_of_ssubset hssu
  --     grind
  --   grind
  -- ·

  -- obtain rfl | hPne := P.eq_empty_or_nonempty
  -- · simp only [seriesParallelDuo_empty_right, union_empty, inter_empty, subsingleton_empty,
  --     true_and, and_imp]
  --   obtain rfl | hSne := S.eq_empty_or_nonempty
  --   · sorry
  --   simp only [circuitOn_indep_iff hSne, ssubset_iff_subset_ne, ne_eq, ← and_imp,
  --     ← subset_antisymm_iff, eq_comm (a := I), imp_self, iff_true]
  --   refine ⟨fun h hIS hSI ↦ ?_, fun h ↦ ?_⟩
  --   ·

      -- rw [circuitOn_indep_iff h]

lemma seriesParallelDuo_isCircuit_iff (hS : S.Nonempty) (hP : P.Nonempty) (hdj : Disjoint S P)
    (C : Set α) : (seriesParallelDuo S P hdj).IsCircuit C ↔
        ∃ e ∈ P, C = insert e S ∨ (∃ e ∈ P, ∃ f ∈ P, e ≠ f ∧ C = {e, f}) := by
  rw [isCircuit_iff_dep_forall_diff_singleton_indep]

-- lemma seriesParallelDuo_two_two {a b c d : α} (hab : a ≠ b) (hcd : c ≠ d)
--     (hdj : Disjoint {a, b} {c, d}) {I : Set α} : (seriesParallelDuo {a, b} {c, d} hdj).Indep I
