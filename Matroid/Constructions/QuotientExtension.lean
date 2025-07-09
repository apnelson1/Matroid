import Matroid.Rank.Skew
import Matroid.Order.Quotient
import Matroid.Extension
import Matroid.ForMathlib.Data.Set.Finite

open Set BigOperators Set.Notation Function

namespace Matroid

variable {α : Type*} {ι : Type*} {η : Type*} {A : Set η} {M N : Matroid α}
    {B I J X X' Y Y' F : Set α} {e : α} {i j : ι} {Xs Ys Is Js : ι → Set α}

/-- If `N` is a finitary quotient of `M`, then the collection of all flats `F` of `M`
for which `M.project F = N.project F` is a modular cut. -/
@[simps!]
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
      refine Eq.symm <| hq.eq_of_closure_indep ?_ h2.2
      grw [project_closure,
        ← M.closure_subset_closure (show B ⊆ _ by tauto_set), hB.closure_eq, project_ground])
    (h_chain := by
      refine fun Fs hFs hCne hmod hchain ↦ ⟨?_, ?_⟩
      · exact IsFlat.sInter hCne fun F hF ↦ (hFs hF).1
      simp only [subset_def, mem_setOf_eq] at hFs
      obtain ⟨B, hB, hBmut⟩ := hmod.exists_isMutualBasis_isBase
      simp only [isMutualBasis_iff, Subtype.forall] at hBmut
      refine Eq.symm <| (h.project_quotient_project _).eq_of_closure_indep (X := B \ ⋂₀ Fs) ?_ ?_
      · simp [hB.spanning.closure_eq_of_superset subset_union_left]
      rw [indep_iff_forall_subset_not_isCircuit', project_ground, h.ground_eq,
        and_iff_left (diff_subset.trans hB.subset_ground)]
      intro C hCss hC
      have aux (e) (he : e ∈ C) : ∃ F ∈ Fs, e ∉ F := by simpa using (hCss he).2
      choose! F' hF' using aux
      replace hchain : IsChain (fun a b ↦ b ≤ a) Fs := hchain.symm
      have hss' : F' '' C ⊆ Fs := by
        rw [image_subset_iff, subset_def]
        exact fun e heC ↦ (hF' e heC).1
      obtain ⟨F₀, hF₀, hF₀le : ∀ F ∈ F' '' C, F₀ ⊆ F⟩ :=
        hchain.directedOn.exists_forall_le hCne hss' (hC.finite.image F')
      have hCi : (N.project F₀).Indep C := by
        rw [← (hFs _ hF₀).2, (hBmut.2 F₀ hF₀).project_eq_project, project_indep_iff,
          (hBmut.1.inter_left F₀).contract_indep_iff, inter_comm, disjoint_left]
        refine ⟨?_, hBmut.1.subset (union_subset (hCss.trans diff_subset) inter_subset_left)⟩
        rintro e heC ⟨heB, heF₀⟩
        exact (hF' e heC).2 <| hF₀le (F' e) (mem_image_of_mem _ heC) heF₀
      refine hC.not_indep (hCi.of_project_subset (sInter_subset_of_mem hF₀)))

lemma Quotient.foo [N.Finitary] (h : N ≤q M) : N ≤q (M.projectBy h.modularCut) := by
  set U := h.modularCut with hU
  refine quotient_of_forall_closure_subset_closure h.ground_eq.symm fun I (hIE : I ⊆ M.E) ↦ ?_
  wlog hI : (M.projectBy U).Indep I generalizing I with aux
  · obtain ⟨J, hJ⟩ := (M.projectBy U).exists_isBasis I hIE
    grw [← hJ.closure_eq_closure, aux _ (hJ.subset.trans hIE) hJ.indep,
      N.closure_subset_closure hJ.subset]
