import Mathlib.Data.Matroid.Minor.Contract

variable {α : Type*} {M M' N : Matroid α} {e f : α} {I C J R B X Y Z K S : Set α}

open Set

namespace Matroid



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
lemma project_indep_iff : (M.project C).Indep I ↔ (M ／ C).Indep I := by
  simp only [project, restrict_indep_iff, and_iff_left_iff_imp]
  exact fun h ↦ h.of_contract.subset_ground

lemma Indep.of_project (hI : (M.project C).Indep I) : M.Indep I :=
  (project_indep_iff.1 hI).of_contract

@[simp]
lemma project_project (M : Matroid α) (C₁ C₂ : Set α) :
    (M.project C₁).project C₂ = M.project (C₁ ∪ C₂) :=
  ext_closure <| by simp [union_assoc, union_comm C₂]

@[simp]
lemma project_delete_self (M : Matroid α) (C : Set α) : (M.project C) ＼ C = M ／ C :=
  ext_indep rfl <| by simp +contextual [subset_diff]

@[simp]
lemma project_loops (M : Matroid α) (C : Set α) : (M.project C).loops = M.closure C := by
  simp [loops]

@[simp]
lemma project_spanning_iff {C : Set α} (hC : C ⊆ M.E := by aesop_mat) :
    (M.project C).Spanning X ↔ M.Spanning (X ∪ C) := by
  rw [spanning_iff, project_closure, spanning_iff, project_ground, union_subset_iff,
    and_iff_left hC]

lemma IsBasis'.project_eq_project (hI : M.IsBasis' I X) : M.project X = M.project I := by
  refine ext_indep rfl fun J hJ ↦ ?_
  simp only [project, restrict_indep_iff, hI.contract_indep_iff, and_comm,
    hI.indep.contract_indep_iff, and_congr_right_iff, and_congr_left_iff]
  refine fun _ hJI ↦ ⟨fun hdj ↦ hdj.symm.mono_right hI.subset,
    fun hdj ↦ disjoint_left.2 fun e heX heJ ↦ ?_⟩
  rw [hI.eq_of_subset_indep (J := insert e I)
    (hJI.subset (insert_subset (.inl heJ) subset_union_right)) (subset_insert _ _)
    (insert_subset heX hI.subset)] at hdj
  simp [heJ] at hdj

lemma IsBasis.project_eq_project (hI : M.IsBasis I X) : M.project X = M.project I :=
  hI.isBasis'.project_eq_project

@[simp]
lemma project_closure_eq (M : Matroid α) (X : Set α) : M.project (M.closure X) = M.project X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [hI.project_eq_project, hI.isBasis_closure_right.project_eq_project]

lemma project_restrict_comm (M : Matroid α) (hXR : X ⊆ R) : (M ↾ R).project X = (M.project X) ↾ R :=
  ext_closure fun Y ↦ by simp [union_inter_distrib_right, inter_eq_self_of_subset_left hXR]

lemma project_restrict_univ (M : Matroid α) : (M ↾ univ).project X = (M.project X) ↾ univ :=
  M.project_restrict_comm <| subset_univ X

lemma contract_restrict_univ (M : Matroid α) : (M ／ X) ↾ univ = (M.project X) ↾ univ :=
  ext_indep rfl fun _ ↦ by simp

/-- Turn the elements of `D` into loops. -/
def loopify (M : Matroid α) (D : Set α) : Matroid α := (M ＼ D) ↾ M.E

@[simp]
lemma loopify_ground (M : Matroid α) (D : Set α) : (M.loopify D).E = M.E := rfl

@[simp]
lemma loopify_inter_ground (M : Matroid α) (D : Set α) : M.loopify (D ∩ M.E) = M.loopify D := by
  rw [loopify, delete_inter_ground_eq, loopify]

lemma loopify_closure' (M : Matroid α) (D : Set α) :
    (M.loopify D).closure X = M.closure (X \ D) ∪ (D ∩ M.E) := by
  simp only [loopify, restrict_closure_eq', delete_closure_eq, delete_ground,
    sdiff_sdiff_right_self, inf_eq_inter]
  rw [inter_comm, ← inter_union_distrib_left, inter_comm, diff_union_self, inter_diff_right_comm,
    closure_inter_ground, union_inter_distrib_right,
    inter_eq_self_of_subset_left (closure_subset_ground ..)]

-- lemma IsBasis.project_eq (h : M.IsBasis I X) : M.project X = (M.project I).loopify X := by
--   _
