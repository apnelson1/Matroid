import Matroid.Rank.Skew
import Matroid.Order.Quotient
import Matroid.Extension

open Set BigOperators Set.Notation Function

namespace Matroid

variable {α : Type*} {ι : Type*} {η : Type*} {A : Set η} {M N : Matroid α}
    {B I J X X' Y Y' F : Set α} {e : α} {i j : ι} {Xs Ys Is Js : ι → Set α}

/-- If `N` is a finitary quotient of `M`, then the collection of all flats `F` of `M`
for which `M.project F = N.project F` is a modular cut. -/
def Quotient.modularCut [N.Finitary] (h : N ≤q M) : M.ModularCut :=
    ModularCut.ofForallIsModularPairChainInter
    (M := M)
    (U := {F | M.IsFlat F ∧ M.project F = N.project F})
    (h_isFlat := by simp +contextual)
    (h_superset := by
      refine fun F F' ⟨hF, hFe⟩ hF' hss ↦ ⟨hF', ?_⟩
      rw [← union_eq_self_of_subset_left hss, ← project_project, hFe, project_project])
    (h_pair := by
      refine fun F F' ⟨hF, hFe⟩ ⟨hF', hF'e⟩ hmod ↦ ⟨hF.inter hF', ?_⟩
      obtain ⟨B, hB, hBu, hBF, hBF', hBi⟩ := hmod.exists_isMutualBasis_isBase
      have hBi := hB.indep
      have h1 : (M.project F).Indep (B \ F) := by rwa [project_indep_iff,
        hBF.contract_indep_iff_of_disjoint disjoint_sdiff_right, inter_comm, diff_union_inter]
      have h1' : (M.project F').Indep (B \ F') := by rwa [project_indep_iff,
        hBF'.contract_indep_iff_of_disjoint disjoint_sdiff_right, inter_comm, diff_union_inter]
      set I := B ∩ (F' \ F) with hI_def
      rw [hF'e] at h1'
      have hI : (N.project (F ∩ F')).Indep I := by
        rw [hFe] at h1
        exact (h1.of_project_subset inter_subset_left).subset <| by tauto_set
      have h2 : ((N.project (F ∩ F')).project I).Indep (B \ F') := by
        rw [project_project]
        exact h1'.of_project_subset <| by (rw [hI_def]; tauto_set)
      rw [project_indep_iff, hI.contract_indep_iff, hI_def] at h2
      have hq := h.project_quotient_project (F ∩ F')
      refine Eq.symm <| hq.eq_of_isBase_indep ?_ h2.2
      refine (hq.weakLE.indep_of_indep h2.2).isBase_of_spanning ?_
      have hss : B ⊆ B \ F' ∪ B ∩ (F' \ F) ∪ (F ∩ F') := by tauto_set
      rw [spanning_iff_closure_eq ?_]
      · refine (closure_subset_ground ..).antisymm ?_
        grw [project_closure, ← M.closure_subset_closure hss, hB.closure_eq, project_ground]
      grw [project_ground, diff_subset, inter_subset_left, union_self]
      exact hBi.subset_ground )
    (h_chain := by
      refine fun Fs hFs hCne hmod hchain ↦ ⟨?_, ?_⟩
      · exact IsFlat.sInter hCne fun F hF ↦ (hFs hF).1
      obtain ⟨B, hB, hBmut⟩ := hmod.exists_isMutualBasis_isBase
      refine Eq.symm <| (h.project_quotient_project _).eq_of_isBase_indep (B := B \ ⋂₀ Fs) ?_ ?_
      sorry
      sorry
    )
