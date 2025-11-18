import Mathlib.Combinatorics.Matroid.Closure

variable {α : Type*} {M : Matroid α}

open Set

namespace Matroid

lemma Spanning.rankFinite_of_finite {S : Set α} (hS : M.Spanning S) (hSfin : S.Finite) :
    M.RankFinite := by
  obtain ⟨B, hB⟩ := hS.exists_isBase_subset
  refine hB.1.rankFinite_of_finite <| hSfin.subset hB.2

lemma IsRestriction.closure_subset_closure {M N : Matroid α} (h : M ≤r N) (X : Set α) :
    M.closure X ⊆ N.closure X := by
  obtain ⟨R, h', rfl⟩ := h.exists_eq_restrict
  grw [← closure_inter_ground, restrict_closure_eq _, inter_subset_left]
  · exact closure_mono _ inter_subset_left
  exact inter_subset_right

lemma spanning_empty_iff_eq_loopyOn : M.Spanning ∅ ↔ ∃ E, M = loopyOn E := by
  refine ⟨fun h ↦ ⟨M.E, ?_⟩, ?_⟩
  · exact empty_isBase_iff.1 (M.empty_indep.isBase_of_spanning h)
  rintro ⟨E, rfl⟩
  simp only [loopyOn_spanning_iff, empty_subset]

lemma spanning_empty_iff : M.Spanning ∅ ↔ M = loopyOn M.E := by
  rw [spanning_empty_iff_eq_loopyOn]
  refine ⟨?_, fun h ↦ ⟨M.E, h⟩⟩
  rintro ⟨E, rfl⟩
  rfl

lemma dep_dual_iff_compl_not_spanning {X : Set α} (hXE : X ⊆ M.E := by aesop_mat) :
    M✶.Dep X ↔ ¬ M.Spanning (M.E \ X) := by
  rw [← not_indep_iff, ← coindep_iff_compl_spanning]

lemma dep_compl_dual_iff_not_spanning {X : Set α} (hXE : X ⊆ M.E := by aesop_mat) :
    M✶.Dep (M.E \ X) ↔ ¬ M.Spanning X := by
  rw [← not_indep_iff, ← coindep_def, spanning_iff_compl_coindep]

lemma spanning_dual_iff {X : Set α} (hXE : X ⊆ M.E := by aesop_mat) :
    M✶.Spanning X ↔ M.Indep (M.E \ X) := by
  rw [spanning_iff_compl_coindep, dual_coindep_iff, dual_ground]

lemma spanning_compl_dual_iff {X : Set α} (hXE : X ⊆ M.E := by aesop_mat) :
    M✶.Spanning (M.E \ X) ↔ M.Indep X := by
  rw [spanning_iff_compl_coindep, dual_coindep_iff, dual_ground, diff_diff_cancel_left hXE]
