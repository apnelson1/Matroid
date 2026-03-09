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
  rw [seriesParallelDuo_nonempty_eq hS hP, truncate_indep_iff, freeLift_indep_iff,
    freeLift_isBase_iff]
  simp only [hne, disjointSum_ground_eq, freeOn_ground, loopyOn_ground, mem_inter_iff, mem_union,
    disjointSum_indep_iff, diff_inter_right_comm, freeOn_indep_iff, diff_singleton_subset_iff,
    loopyOn_indep_iff, diff_eq_empty, subset_singleton_iff, and_imp, forall_const,
    disjointSum_isBase_iff, freeOn_isBase_iff, loopyOn_isBase_iff, not_and, forall_exists_index]
  refine ⟨fun ⟨⟨e, he, hdj, hI⟩, h2⟩ ↦ ?_, fun ⟨hIss, hIP, hss⟩ ↦ ⟨?_, by grind⟩⟩
  · have hISP : I ⊆ S ∪ P := by grind
    have hss : (I ∩ P).Subsingleton := fun a ↦ by grind
    refine ⟨by grind, hss, fun h ↦ h.antisymm fun f hf ↦ by_contra fun hfS ↦ ?_⟩
    simp_rw [inter_eq_self_of_subset_right h] at h2
    exact h2 f hf (by grind) (by grind) (by grind) (by grind)
  obtain hIP | ⟨x, hIPx⟩ := hIP.eq_empty_or_singleton
  · rw [← disjoint_iff_inter_eq_empty] at hIP
    exact Exists.imp (by grind) hne
  simp only [Set.ext_iff, mem_inter_iff, mem_singleton_iff] at hIPx
  use x; grind

lemma seriesParallelDuo_indep_insert_ssubset (hdj : Disjoint S P) (hI1 : I ⊂ S) (he : e ∈ P) :
    (seriesParallelDuo S P hdj).Indep (insert e I) := by
  grw [seriesParallelDuo_indep_iff hdj (nonempty_iff_ne_empty.2 (by grind)) ⟨e, he⟩,
    and_iff_right (by grind), insert_inter_of_mem he, (hdj.mono_left hI1.subset).inter_eq,
    and_iff_right (by simp), subset_insert_iff_of_notMem (by grind)]
  simp [hI1.not_subset]

-- lemma seriesParallelDuo_loopless (hdj : Disjoint S P) (seriesParallelDuo S P hdj).Parallel e f := by

-- lemma seriesParallelDuo_parallel (hdj : Disjoint S P) (he : e ∈ P) (hf : f ∈ P) :
--     (seriesParallelDuo S P hdj).Parallel e f := by
--   obtain rfl | hS := S.eq_empty_or_nonempty
--   · simp only [seriesParallelDuo_empty_left]
--     obtain rfl | hne := eq_or_ne e f
--     · rw [parallel_self_iff, ← indep_singleton, unifOn_indep_iff]
--       simpa
--     rw [parallel_iff_isCircuit hne, unifOn_isCircuit_iff, encard_pair hne]
--     grind
--   rw [parallel]
  -- rw [seriesParallelDuo_nonempty_eq hS ⟨e, he⟩ hdj]
  -- grw [seriesParallelDuo_indep_iff hdj (nonempty_iff_ne_empty.2 (by grind)) ⟨e, he⟩,
  --   and_iff_right (by grind), insert_inter_of_mem he, (hdj.mono_left hI1.subset).inter_eq,
  --   and_iff_right (by simp), subset_insert_iff_of_notMem (by grind)]
  -- simp [hI1.not_subset]

lemma seriesParallelDuo_isCircuit_iff (hS : S.Nonempty) (hP : P.Nonempty) (hdj : Disjoint S P)
    (C : Set α) (hCSP : C ⊆ S ∪ P) : (seriesParallelDuo S P hdj).IsCircuit C ↔
        (∃ e ∈ P, C = insert e S) ∨ (∃ e ∈ P, ∃ f ∈ P, e ≠ f ∧ C = {e, f}) := by

  obtain hss | hnt := (C ∩ P).subsingleton_or_nontrivial
  ·
    obtain he | ⟨x, hCPX⟩ := hss.eq_empty_or_singleton
    · refine iff_of_false (fun hC ↦ hC.not_indep ?_) ?_
      · refine Indep.subset (J := S) ?_ (by tauto_set)
        rw [seriesParallelDuo_indep_iff hdj hS hP]
        simp [hdj.inter_eq]
      rw [← disjoint_iff_inter_eq_empty] at he
      grind
    obtain rfl | hssu := (show C \ {x} ⊆ S by grind).eq_or_ssubset
    · sorry



  simp only [isCircuit_iff_dep_forall_diff_singleton_indep, dep_iff,
    seriesParallelDuo_indep_iff hdj hS hP, not_and, Classical.not_imp, seriesParallelDuo_E,
    diff_singleton_subset_iff, forall_mem_and, ne_eq]
  refine ⟨fun ⟨h1, h2, h3, h4⟩ ↦ ?_, fun h ↦ ?_⟩
  · obtain hss | hnt := (C ∩ P).subsingleton_or_nontrivial
    · obtain he | ⟨x, hCPX⟩ := hss.eq_empty_or_singleton
      ·


-- lemma seriesParallelDuo_two_two {a b c d : α} (hab : a ≠ b) (hcd : c ≠ d)
--     (hdj : Disjoint {a, b} {c, d}) {I : Set α} : (seriesParallelDuo {a, b} {c, d} hdj).Indep I
