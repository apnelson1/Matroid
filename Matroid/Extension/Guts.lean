import Matroid.Modular.Flat
import Matroid.Connectivity.Separation
import Matroid.Constructions.Project

open Set BigOperators Set.Notation Function

namespace Matroid

variable {α : Type*} {ι : Type*} {η : Type*} {A : Set η} {M : Matroid α} {B I J X X' Y Y' F : Set α}
    {e : α} {i j : ι} {Xs Ys Is Js : ι → Set α}

/-- For any collection of sets with union `M.E`, the modular cut
comprising all flats whose projections make `X` a skew family in `M`. -/
def gutsModularCut (M : Matroid α) (X : ι → Set α) (Xu : ⋃ i, X i = M.E) : M.ModularCut where
  carrier := {F | M.IsFlat F ∧ (M.project F).IsSkewFamily X}
  forall_isFlat _ h := h.1
  forall_superset := by
    refine fun F F' ⟨hF, hFX⟩ hF' hss ↦ ⟨hF', ?_⟩
    have h' := hFX.project (C := F') (hF'.subset_ground.trans Xu.symm.subset)
    rwa [project_project, union_eq_self_of_subset_left hss] at h'
  forall_inter := by
    refine fun Gs hGs hne hmod ↦ ⟨IsFlat.sInter hne fun F hF ↦ (hGs hF).1, ?_⟩
    obtain ⟨B, hB, hBmut⟩ := hmod.exists_isMutualBasis_isBase
    have h₁ (i) (F) (hF : F ∈ Gs) : X i ⊆ M.closure (B ∩ (X i ∪ F))
    · obtain ⟨hF_flat, hFsk⟩ := hGs hF
      rw [inter_union_distrib_left, inter_comm _ F, closure_union_congr_right
        (show M.closure (F ∩ B) = M.closure F from hBmut.closure_inter_eq ⟨F, hF⟩),
        ← project_closure, ← inter_eq_right,
        ← (hFsk.skew_compl_singleton i).closure_union_right_inter_left inter_subset_right,
        inter_eq_right]
      have h' : X i ⊆ (M.project F).closure B := by
        rw [project_closure, hB.spanning.closure_eq_of_superset subset_union_left, ← Xu]
        apply subset_iUnion
      refine h'.trans <| closure_subset_closure _ ?_
      nth_rw 1 [← inter_eq_left.2 (hB.subset_ground.trans_eq Xu.symm), inter_iUnion]
      grw [← biUnion_mono rfl.subset (fun j hj ↦ inter_subset_right (s := B))]
      rw [← biUnion_insert (t := fun i ↦ B ∩ X i), ← union_singleton, compl_union_self,
        biUnion_univ]
    set G₀ := ⋂₀ Gs with G₀_def
    have h₂ : M.IsBasis (B ∩ G₀) G₀ := by
      have := hne.to_subtype
      simpa [iInter_coe_set, inter_comm _ B, ← sInter_eq_biInter] using hBmut.isBasis_iInter
    have h₃ (i) : X i ⊆ (M.project G₀).closure ((B \ G₀) ∩ (X i)) := by
      refine (subset_iInter₂_iff.2 (h₁ i)).trans ?_
      rw [← closure_biInter_eq_biInter_closure_of_biUnion_indep hne (hB.indep.subset (by simp)),
        project_closure, ← inter_distrib_biInter _ hne, ← union_iInter₂, ← sInter_eq_biInter,
        inter_union_distrib_left, closure_union_congr_right h₂.closure_eq_closure]
      exact M.closure_subset_closure (by tauto_set)
    refine IsSkewFamily.mono (IsSkewFamily.cls_isSkewFamily ?_) h₃
    rw [Indep.isSkewFamily_iff_pairwise_disjoint]
    · refine fun i j hne ↦ disjoint_left.2 fun x ⟨⟨hxB, hxG⟩, hxi⟩ ⟨_, hxj⟩ ↦ ?_
      obtain ⟨G₁, hG₁, hxG₁⟩ : ∃ G₁ ∈ Gs, x ∉ G₁ := by simpa [G₀_def] using hxG
      have hG₁B : M.IsBasis (G₁ ∩ B) G₁ := hBmut.isBasis_inter ⟨G₁, hG₁⟩
      refine ((hGs hG₁).2.disjoint_of_indep_subset (I := (B \ G₁) ∩ (X i))
        ?_ inter_subset_right hne).notMem_of_mem_left (a := x) ⟨⟨hxB, hxG₁⟩, hxi⟩ hxj
      refine Indep.inter_right ?_ _
      rw [project_indep_iff, hG₁B.contract_indep_iff_of_disjoint disjoint_sdiff_right,
        inter_comm, diff_union_inter]
      exact hB.indep
    rw [project_indep_iff, h₂.contract_indep_iff_of_disjoint]
    · exact hB.indep.subset <| by simpa using fun i ↦ inter_subset_left.trans diff_subset
    simpa using fun i ↦ disjoint_sdiff_right.mono_right inter_subset_left

@[simp]
lemma mem_gutsModularCut_iff (M : Matroid α) (X : ι → Set α) (Xu : ⋃ i, X i = M.E) {F : Set α} :
    F ∈ M.gutsModularCut X Xu ↔ M.IsFlat F ∧ (M.project F).IsSkewFamily X := Iff.rfl
