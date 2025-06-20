import Matroid.Minor.Delete
import Mathlib.Data.Matroid.Minor.Contract

variable {α : Type*} {M M' N : Matroid α} {e f : α} {I J R B X Y Z K S : Set α}

open Set

namespace Matroid

@[simp] lemma freeOn_contract (E X : Set α) : (freeOn E) ／ X = freeOn (E \ X) := by
  rw [← loopyOn_dual_eq, ← dual_delete, loopyOn_delete, loopyOn_dual_eq]

@[simp]
lemma loopyOn_contract (E X : Set α) : (loopyOn E) ／ X = loopyOn (E \ X) := by
  rw [← dual_inj, dual_contract, loopyOn_dual_eq, freeOn_delete, loopyOn_dual_eq]

lemma contract_eq_loopyOn_of_spanning {C : Set α} (h : M.Spanning C) :
    M ／ C = loopyOn (M.E \ C) := by
  rw [eq_loopyOn_iff_loops, contract_ground, and_iff_left rfl, contract_loops_eq, h.closure_eq]


@[simp] lemma contract_ground_self (M : Matroid α) : M ／ M.E = emptyOn α := by
  simp [← ground_eq_empty_iff]

section project

/-- Contract a set `C`, then put the removed elements back in as loops. -/
def project (M : Matroid α) (C : Set α) : Matroid α := (M ／ C) ↾ M.E

@[simp]
lemma project_ground (M : Matroid α) (C : Set α) : (M.project C).E = M.E := rfl

@[simp]
lemma project_inter_ground (M : Matroid α) (C : Set α) : M.project (C ∩ M.E) = M.project C := by
  simp [project]

@[simp]
lemma project_closure (M : Matroid α) (C X : Set α) :
    (M.project C).closure X = M.closure (X ∪ C) := by
  wlog h : C ⊆ M.E ∧ X ⊆ M.E  with aux
  · rw [← project_inter_ground, ← closure_inter_ground, project_ground, aux _ _ _ (by simp),
      ← union_inter_distrib_right, closure_inter_ground]
  rw [project, restrict_closure_eq', inter_eq_self_of_subset_left h.2, contract_closure_eq,
    contract_ground, diff_diff_cancel_left h.1,
    inter_eq_self_of_subset_left (diff_subset.trans (M.closure_subset_ground _)),
    diff_union_self, union_eq_left]
  apply M.subset_closure_of_subset' subset_union_right h.1

@[simp]
lemma project_indep_iff {C I : Set α} : (M.project C).Indep I ↔ (M ／ C).Indep I := by
  simp only [project, restrict_indep_iff, and_iff_left_iff_imp]
  exact fun h ↦ h.of_contract.subset_ground

@[simp]
lemma project_delete_self (M : Matroid α) (C : Set α) : (M.project C) ＼ C = M ／ C :=
  ext_indep rfl <| by simp +contextual [subset_diff]

@[simp]
lemma project_loops (M : Matroid α) (C : Set α) : (M.project C).loops = M.closure C := by
  simp [loops]
