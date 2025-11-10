import Mathlib.Combinatorics.Matroid.Minor.Contract

variable {α : Type*} {M M' N : Matroid α} {e f : α} {I C J R B X Y Z K S : Set α}

open Set

namespace Matroid



/-- Contract a set `C`, then put the removed elements back in as loops. -/
def project (M : Matroid α) (C : Set α) : Matroid α := (M ／ C) ↾ M.E

@[simp, aesop unsafe 20% (rule_sets := [Matroid])]
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

lemma project_closure_eq_project_closure_union (M : Matroid α) (C X : Set α) :
    (M.project C).closure X = (M.project C).closure (X ∪ C) := by
  simp [union_assoc]

lemma project_indep_iff : (M.project C).Indep I ↔ (M ／ C).Indep I := by
  simp only [project, restrict_indep_iff, and_iff_left_iff_imp]
  exact fun h ↦ h.of_contract.subset_ground

lemma project_indep_eq : (M.project C).Indep = (M ／ C).Indep := by
  ext I
  rw [project_indep_iff]

lemma Indep.project_indep_iff (hI : M.Indep I) :
    (M.project I).Indep J ↔ Disjoint J I ∧ M.Indep (J ∪ I)  := by
  rw [Matroid.project_indep_iff, hI.contract_indep_iff]

@[simp]
lemma project_empty (M : Matroid α) : M.project ∅ = M := by
  simp [project]

lemma Indep.of_project (hI : (M.project C).Indep I) : M.Indep I :=
  (Matroid.project_indep_iff.1 hI).of_contract

@[simp]
lemma project_ground_self (M : Matroid α) : M.project M.E = loopyOn M.E := by
  refine ext_closure fun X ↦ ?_
  simp only [project_closure, loopyOn_closure_eq]
  rw [← closure_inter_ground, inter_eq_self_of_subset_right subset_union_right, closure_ground]

@[simp]
lemma project_project (M : Matroid α) (C₁ C₂ : Set α) :
    (M.project C₁).project C₂ = M.project (C₁ ∪ C₂) :=
  ext_closure <| by simp [union_assoc, union_comm C₂]

lemma Indep.of_project_subset {C' : Set α} (hI : (M.project C).Indep I) (hC' : C' ⊆ C) :
    (M.project C').Indep I := by
  rw [← union_eq_self_of_subset_left hC', ← project_project] at hI
  exact hI.of_project

@[simp]
lemma project_delete_self (M : Matroid α) (C : Set α) : (M.project C) ＼ C = M ／ C :=
  ext_indep rfl <| by simp +contextual [project_indep_iff, subset_diff]

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

lemma project_isBasis'_eq : (M.project C).IsBasis' = (M ／ C).IsBasis' := by
  ext I C
  simp_rw [IsBasis', project_indep_eq]

lemma project_isBasis_iff (hdj : Disjoint X C) :
    (M.project C).IsBasis I X ↔ (M ／ C).IsBasis I X := by
  rw [isBasis_iff_isBasis'_subset_ground, isBasis_iff_isBasis'_subset_ground, project_isBasis'_eq,
    project_ground, contract_ground, subset_diff, and_iff_left hdj]

lemma project_isBase_eq : (M.project C).IsBase = (M ／ C).IsBase := by
  ext B
  rw [← isBasis_ground_iff, project_ground, ← isBasis'_iff_isBasis, project_isBasis'_eq,
    isBasis'_iff_isBasis_inter_ground, contract_ground, inter_eq_self_of_subset_right diff_subset,
    ← contract_ground, isBasis_ground_iff]

@[simp]
lemma project_closure_eq (M : Matroid α) (X : Set α) : M.project (M.closure X) = M.project X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [hI.project_eq_project, hI.isBasis_closure_right.project_eq_project]

@[simp]
lemma project_loops_eq (M : Matroid α) : M.project M.loops = M := by
  simp [← closure_empty]

lemma project_eq_self (hX : X ⊆ M.loops) : M.project X = M := by
  rw [← project_closure_eq, closure_eq_loops_of_subset hX, project_loops_eq]

lemma project_project_eq_project (hXY : M.closure X ⊆ M.closure Y) :
    (M.project X).project Y = M.project Y := by
  rw [← project_closure_eq, project_closure, ← closure_closure_union_closure_eq_closure_union,
    union_eq_self_of_subset_right hXY, closure_closure, ← M.project_closure_eq, project_project,
    union_eq_self_of_subset_left hXY, project_closure_eq]

lemma project_restrict_comm (M : Matroid α) (hXR : X ⊆ R) : (M ↾ R).project X = (M.project X) ↾ R :=
  ext_closure fun Y ↦ by simp [union_inter_distrib_right, inter_eq_self_of_subset_left hXR]

lemma project_restrict_univ (M : Matroid α) : (M ↾ univ).project X = (M.project X) ↾ univ :=
  M.project_restrict_comm <| subset_univ X

lemma contract_restrict_univ (M : Matroid α) : (M ／ X) ↾ univ = (M.project X) ↾ univ :=
  ext_indep rfl fun _ ↦ by simp [project_indep_iff]

instance project_finitary [M.Finitary] : (M.project X).Finitary := by
  rw [project]
  infer_instance

lemma project_comap_image {β : Type*} (M : Matroid β) (f : α → β) (C : Set α) :
    (M.project (f '' C)).comap f = (M.comap f).project C :=
  ext_closure fun X ↦ by simp [image_union]

lemma project_comap {β : Type*} (M : Matroid β) (f : α → β) (C : Set β) (hC : C ⊆ range f) :
    (M.project C).comap f = (M.comap f).project (f ⁻¹' C) := by
  refine ext_closure fun X ↦ ?_
  obtain ⟨C, hC, rfl⟩ := subset_range_iff_exists_image_eq.1 hC
  have h' : M.closure (f '' C) = M.closure (f '' (f ⁻¹' (f '' C))) := by
    refine (M.closure_subset_closure (image_mono (subset_preimage_image ..))).antisymm ?_
    rw [image_preimage_eq_inter_range, inter_eq_self_of_subset_left hC]
  simp only [comap_closure_eq, project_closure, image_union, closure_union_congr_right h']

lemma Dep.project {D : Set α} (hD : M.Dep D) (C : Set α) : (M.project C).Dep D := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' C
  rw [dep_iff, project_ground, and_iff_left hD.subset_ground, hI.project_eq_project,
    hI.indep.project_indep_iff]
  exact fun h ↦ (h.2.subset subset_union_left).not_dep hD

-- lemma IsCircuit.project_subset_dep {C : Set α} (hC : M.IsCircuit C) (X : Set α) :
--     (M.project C).Dep D := by
--   obtain ⟨I, hI⟩ := M.exists_isBasis' C
--   rw [dep_iff, project_ground, and_iff_left hD.subset_ground, hI.project_eq_project,
--     hI.indep.project_indep_iff]
--   exact fun h ↦ (h.2.subset subset_union_left).not_dep hD


lemma Indep.project_isBasis'_iff (hI : M.Indep I) :
    (M.project I).IsBasis' J X ↔ M.IsBasis' (I ∪ J) (I ∪ X) ∧ Disjoint I J := by
  have hss : I ⊆ M.closure (I ∪ X) := M.subset_closure_of_subset' subset_union_left
  have hdj (h : Disjoint I J) : (J ⊆ I ∪ X ↔ J ⊆ X) := by rw [← diff_subset_iff, h.sdiff_eq_right]
  simp only [isBasis'_iff_isBasis_closure, project_closure, isBasis_iff_indep_subset_closure,
    hI.project_indep_iff, union_subset_iff, subset_union_left, disjoint_comm (a := J),
    union_comm (b := I)]
  tauto


lemma Indep.project_isBasis_iff (hI : M.Indep I) :
    (M.project I).IsBasis J X ↔ M.IsBasis (I ∪ J) (I ∪ X) ∧ Disjoint I J := by
  rw [isBasis_iff_isBasis'_subset_ground, isBasis_iff_isBasis'_subset_ground,
    hI.project_isBasis'_iff, union_subset_iff, project_ground, and_iff_right hI.subset_ground,
    and_assoc, and_right_comm, and_assoc]

lemma project_isBasis'_iff_contract_isBasis' :
    (M.project C).IsBasis' I X ↔ (M ／ C).IsBasis' I (X \ C) := by
  rw [project, isBasis'_restrict_iff, isBasis'_iff_isBasis_inter_ground, iff_comm,
     isBasis'_iff_isBasis_inter_ground, contract_ground, ← diff_inter_distrib_right,
     inter_assoc, inter_eq_self_of_subset_right diff_subset, inter_diff_assoc, iff_self_and]
  exact fun h ↦ h.indep.subset_ground.trans diff_subset

-- lemma project_isBasis_iff_contract_isBasis :
--     (M.project C).IsBasis I X ↔ (M ／ C).IsBasis I (X \ C) := by
--   -- wlog hXE : X ⊆ M.E
--   -- · refune iff_
--   -- convert M.project_isBasis'_iff_contract_isBasis' (I := I) (X := X ∩ M.E) (C := C) using 1
--   -- · sorry



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
