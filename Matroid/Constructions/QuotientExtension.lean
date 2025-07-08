import Matroid.Rank.Skew
import Matroid.Order.Quotient
import Matroid.Extension

open Set BigOperators Set.Notation Function

namespace Matroid

variable {α : Type*} {ι : Type*} {η : Type*} {A : Set η} {M N : Matroid α}
    {B I J X X' Y Y' F : Set α} {e : α} {i j : ι} {Xs Ys Is Js : ι → Set α}

def Quotient.extension [N.Finitary] (h : N ≤q M) : M.ModularCut :=
    ModularCut.ofForallIsModularPairChainInter
    (M := M)
    (U := {F | M.IsFlat F ∧ M.project F = N.project F})
    (h_isFlat := by simp +contextual)
    (h_pair := by
      refine fun F F' ⟨hF, hFe⟩ ⟨hF', hF'e⟩ hmod ↦ ⟨hF.inter hF', ?_⟩
      obtain ⟨B, hBu, hBF, hBF', hBi⟩ := hmod.exists_common_isBasis
      -- rw [isBasis_iff_indep_subset_closure] at hBF hBF'
      have h1 : (M.project F).Indep (B \ F) := by
        rw [hBF.project_eq_project, project_indep_iff, (hBu.indep.inter_right _).contract_indep_iff,
          and_iff_right disjoint_sdiff_inter, diff_union_inter]
        exact hBu.indep
      have h1' : (M.project F').Indep (B \ F') := by
        rw [hBF'.project_eq_project, project_indep_iff, (hBu.indep.inter_right _).contract_indep_iff,
          and_iff_right disjoint_sdiff_inter, diff_union_inter]
        exact hBu.indep
      -- have hrw : (N.project (F ∩ F')).project F = N.project F := sorry
      -- have hrw' : (N.project (F ∩ F')).project F' = N.project F' := sorry
      set I := B ∩ (F' \ F) with hI_def
      have hI : (N.project (F ∩ F')).Indep I := sorry

      -- rw [hFe, ← hrw] at h1
      rw [hF'e] at h1'
      -- have ha0 := h1'.of_project_subset (C' := F ∩ F') inter_subset_right
      have h2 : ((N.project (F ∩ F')).project I).Indep (B \ F') := by
        rw [project_project]
        exact h1'.of_project_subset <| by (rw [hI_def]; tauto_set)

      rw [project_indep_iff, hI.contract_indep_iff, hI_def] at h2
      replace h2 := h2.2





    ) sorry sorry
