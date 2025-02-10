import Mathlib.Data.Matroid.Circuit
import Matroid.ForMathlib.Matroid.Sum

section OnUniv

namespace Matroid

variable {α : Type*} {M : Matroid α}

open Set

@[mk_iff]
class OnUniv (M : Matroid α) : Prop where
  ground_eq : M.E = univ

@[simp]
lemma ground_eq_univ (M : Matroid α) [OnUniv M] : M.E = univ :=
  OnUniv.ground_eq

@[simp, aesop safe (rule_sets := [Matroid])]
lemma OnUniv.subset_ground (M : Matroid α) [M.OnUniv] (X : Set α) : X ⊆ M.E := by
  simp [OnUniv.ground_eq]

lemma corestrict_univ_eq_disjointSum (M : Matroid α) :
    (M✶ ↾ univ)✶ = M.disjointSum (freeOn M.Eᶜ) disjoint_compl_right := by
  rw [← dual_inj, dual_dual, disjointSum_dual]
  simp only [freeOn_dual_eq]
  refine ext_indep (by simp) ?_
  simp only [restrict_ground_eq, subset_univ, restrict_indep_iff, and_true, disjointSum_indep_iff,
    dual_ground, inter_subset_right,  loopyOn_ground, loopyOn_indep_iff,
    union_compl_self, forall_const, ← disjoint_iff_inter_eq_empty, disjoint_compl_right_iff_subset]
  refine fun I ↦ ⟨fun h ↦
    ⟨by rwa [← dual_ground, inter_eq_self_of_subset_left h.subset_ground], h.subset_ground⟩,
    fun ⟨h1, h2⟩ ↦ by rwa [inter_eq_self_of_subset_left h2] at h1⟩

@[simp]
lemma corestrict_univ_indep_iff {I : Set α} : (M✶ ↾ univ)✶.Indep I ↔ M.Indep (I ∩ M.E) := by
  simp [corestrict_univ_eq_disjointSum]

lemma corestrict_univ_base_iff {B : Set α} : (M✶ ↾ univ)✶.Base B ↔ M.Base (B ∩ M.E) ∧ M.Eᶜ ⊆ B := by
  simp [corestrict_univ_eq_disjointSum, disjointSum_base_iff]

lemma corestrict_univ_basis_iff {I X : Set α} :
    (M✶ ↾ univ)✶.Basis I X ↔ M.Basis (I ∩ M.E) (X ∩ M.E) ∧ I ⊆ X ∧ X \ M.E ⊆ I := by
  simp only [corestrict_univ_eq_disjointSum, disjointSum_basis_iff, freeOn_ground, freeOn_basis_iff,
    subset_antisymm_iff, subset_inter_iff, inter_subset_right, and_true, union_compl_self,
    subset_univ, and_comm (a := I ⊆ X), true_and, and_congr_right_iff, and_congr_left_iff]
  intro hb hIX
  rw [and_iff_right (inter_subset_left.trans hIX), diff_eq]

lemma Basis'.corestrict_univ_basis {I X : Set α} (hIX : M.Basis' I X) :
    (M✶ ↾ univ)✶.Basis (I ∪ (X \ M.E)) X := by
  rwa [corestrict_univ_basis_iff, and_iff_left subset_union_right, union_subset_iff,
    and_iff_right hIX.subset, and_iff_left diff_subset, ← basis'_iff_basis_inter_ground,
    union_inter_distrib_right, inter_eq_self_of_subset_left hIX.indep.subset_ground,
    disjoint_sdiff_left.inter_eq, union_empty]

lemma Basis.corestrict_univ_basis {I X : Set α} (hIX : M.Basis I X) :
    (M✶ ↾ univ)✶.Basis I X := by
  simpa [diff_eq_empty.2 hIX.subset_ground, union_empty] using hIX.basis'.corestrict_univ_basis

lemma Basis'.corestrict_univ_union_basis_union {I X : Set α} (hIX : M.Basis' I X) :
    (M✶ ↾ univ)✶.Basis (I ∪ M.Eᶜ) (X ∪ M.Eᶜ) := by
  suffices (X ∪ M.Eᶜ) \ M.E ⊆ I ∪ M.Eᶜ by
    simpa [corestrict_univ_basis_iff, union_inter_distrib_right, hIX.subset.trans subset_union_left,
      inter_eq_self_of_subset_left hIX.indep.subset_ground, and_iff_right hIX.basis_inter_ground]
  rw [union_comm I, diff_subset_iff, ← union_assoc]
  simp

@[simp] lemma corestrict_univ_restrict_ground : (M✶ ↾ univ)✶ ↾ M.E = M := by
  refine ext_indep rfl ?_
  simp_rw [restrict_indep_iff, corestrict_univ_indep_iff]
  simp +contextual only [restrict_ground_eq, and_true]
  intro I hIE
  rw [inter_eq_self_of_subset_left hIE]
