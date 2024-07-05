import Mathlib.Data.Matroid.Restrict

namespace Matroid
open Set

variable {α : Type*} {I B J X : Set α} {M : Matroid α}

def coexpand (M : Matroid α) : Matroid α := (M✶ ↾ univ)✶

lemma coexpand_dual_base_iff : M✶.coexpand.Base B ↔ M.Base (M.E \ B) ∧ M.Eᶜ ⊆ B := by
  simp [coexpand, base_restrict_iff', Basis', mem_maximals_iff, compl_subset_comm]
  refine ⟨fun ⟨h1, h2⟩ ↦ ⟨?_, ?_⟩, fun ⟨hB, hBE⟩ ↦ ⟨hB.indep.subset ?_, fun J hJ hBJ ↦ ?_⟩⟩
  · rw [← show univ \ B = M.E \ B by
      refine subset_antisymm ?_ (diff_subset_diff_left (subset_univ _))
      simp [subset_diff, and_iff_right h1.subset_ground, disjoint_sdiff_left] ]
    exact h1.base_of_maximal h2
  · rw [compl_eq_univ_diff]
    exact h1.subset_ground
  · rwa [subset_diff, and_iff_left disjoint_sdiff_left, ← compl_eq_univ_diff]
  refine hBJ.antisymm ?_
  rw [← hB.eq_of_subset_indep hJ (subset_trans (diff_subset_diff_left (subset_univ _)) hBJ)]
  exact (diff_subset_diff_left (subset_univ _))

lemma coexpand_base_iff : M.coexpand.Base B ↔ M.Base (B ∩ M.E) ∧ M.Eᶜ ⊆ B := by
  rw [← dual_dual M, coexpand_dual_base_iff, dual_base_iff, dual_ground, dual_dual,
    and_congr_left_iff, compl_subset_comm, sdiff_sdiff_right_self]
  simp [inf_eq_inter, inter_comm B]

@[simp] lemma coexpand_indep_iff : M.coexpand.Indep I ↔ M.Indep (I ∩ M.E) := by
  simp_rw [indep_iff (M := M.coexpand), coexpand_base_iff, compl_subset_comm]
  refine ⟨fun ⟨B, ⟨hB, _⟩, hIB⟩ ↦ hB.indep.subset (inter_subset_inter_left _ hIB), fun h ↦ ?_⟩
  obtain ⟨B, hB, hIEB⟩ := h.exists_base_superset
  refine ⟨B ∪ M.Eᶜ, ?_⟩
  suffices I ⊆ B ∪ M.Eᶜ by simpa [inter_subset_right, union_inter_distrib_right,
    inter_eq_self_of_subset_left hB.subset_ground, hB]
  simp only [subset_def, mem_union, mem_compl_iff, or_iff_not_imp_right, not_not]
  exact fun x hxI hxE ↦ hIEB ⟨hxI, hxE⟩

@[simp] lemma coexpand_ground_eq : M.coexpand.E = univ := rfl
