import Matroid.Modular.Flat
import Matroid.Connectivity.Separation


open Set BigOperators Set.Notation Function

namespace Matroid

variable {α : Type*} {ι : Type*} {η : Type*} {A : Set η} {M : Matroid α} {B I J X X' Y Y' F : Set α}
    {e : α} {i j : ι} {Xs Ys Is Js : ι → Set α}


lemma IsSkewFamily.project {C : Set α} (h : M.IsSkewFamily Xs) (hC : C ⊆ ⋃ i, Xs i) :
    (M.project C).IsSkewFamily Xs := by

  wlog hCE : C ⊆ M.E generalizing C with aux
  · rw [← project_inter_ground]
    exact aux (inter_subset_left.trans hC) inter_subset_right
  obtain ⟨⟨B, hB⟩, hloops⟩ := h
  obtain ⟨I, hI⟩ := M.exists_isBasis C
  obtain ⟨B', hB', rfl⟩ := hI.exists_isBasis_inter_eq_of_superset (subset_union_right (s := B))
    (union_subset hB.indep.subset_ground hCE)
  -- TODO : make this a lemma about projections
  have hBb : (M.project C).IsBase (B' \ C) := by
    refine Indep.isBase_of_spanning ?_ ?_
    · simpa [project_indep_iff, hI.contract_indep_iff_of_disjoint disjoint_sdiff_right,
        diff_union_inter] using hB'.indep
    rw [project_spanning_iff hCE, diff_union_self]
    exact (hB'.isBase_of_isBase_subset hB.isBase subset_union_left).spanning_of_superset
      subset_union_left (union_subset hB'.indep.subset_ground hCE)

  refine ⟨⟨B' \ C, ?_⟩, fun i j hne ↦ (hloops hne).trans (by simp [loops])⟩
  refine hBb.isModularBase_of_forall_subset_closure fun i ↦ (hB.subset_closure_inter i).trans ?_
  simp only [project_closure, isFlat_closure, inter_union_distrib_right, diff_union_self]
  refine M.closure_subset_closure ?_
  sorry

@[simp]
lemma project_project (M : Matroid α) (C₁ C₂ : Set α) :
    (M.project C₁).project C₂ = M.project (C₁ ∪ C₂) := sorry

/-- For any partition `X` of the ground set of a matroid `M`, the modular cut
comprising of all flats whose projections make `X` a skew family in `M`. -/
def partitionGutsModularCut (M : Matroid α) (X : ι → Set α) (dj : Pairwise (Disjoint on X))
  (Xu : ⋃ i, X i = M.E) : M.ModularCut where
  carrier := {F | M.IsFlat F ∧ (M.project F).IsSkewFamily X}
  forall_isFlat _ h := h.1
  forall_superset := by
    refine fun F F' ⟨hF, hFX⟩ hF' hss ↦ ⟨hF', ?_⟩
    have h' := hFX.project (C := F') (hF'.subset_ground.trans Xu.symm.subset)
    rwa [project_project, union_eq_self_of_subset_left hss] at h'
  forall_inter := by
    refine fun Gs hGs hne ⟨B, hB⟩ ↦ ⟨IsFlat.sInter hne fun F hF ↦ (hGs hF).1, ?_⟩
    have h₁ (i) (F) (hF : F ∈ Gs) : X i ⊆ M.closure (B ∩ (X i ∪ F))
    · obtain ⟨hF_flat, hFsk⟩ := hGs hF
      rw [inter_union_distrib_left, inter_comm _ F, closure_union_congr_right
        (show M.closure (F ∩ B) = M.closure F from hB.closure_inter_eq ⟨F, hF⟩),
        ← project_closure, ← inter_eq_right,
        ← (hFsk.skew_compl_singleton i).closure_union_right_inter_left inter_subset_right,
        inter_eq_right]
      have h' : X i ⊆ (M.project F).closure B := by
        rw [project_closure, hB.isBase.spanning.closure_eq_of_superset subset_union_left, ← Xu]
        apply subset_iUnion
      refine h'.trans <| closure_subset_closure _ ?_
      nth_rw 1 [← inter_eq_left.2 (hB.isBase.subset_ground.trans_eq Xu.symm), inter_iUnion]
      grw [← biUnion_mono rfl.subset (fun j hj ↦ inter_subset_right (s := B))]
      rw [← biUnion_insert (t := fun i ↦ B ∩ X i), ← union_singleton, compl_union_self,
        biUnion_univ]
    set G₀ := ⋂₀ Gs
    have h₂ : M.IsBasis (B ∩ G₀) G₀ := by
      have := hne.to_subtype
      simpa [iInter_coe_set, inter_comm _ B, ← sInter_eq_biInter] using hB.isBasis_iInter
    have h₃ (i) : X i ⊆ (M.project G₀).closure ((B \ G₀) ∩ (X i)) := by
      refine (subset_iInter₂_iff.2 (h₁ i)).trans ?_
      rw [← closure_biInter_eq_biInter_closure_of_biUnion_indep hne (hB.indep.subset (by simp)),
        project_closure, ← inter_distrib_biInter _ hne, ← union_iInter₂, ← sInter_eq_biInter,
        inter_union_distrib_left, closure_union_congr_right h₂.closure_eq_closure]
      exact M.closure_subset_closure (by tauto_set)
    refine IsSkewFamily.mono (IsSkewFamily.cls_isSkewFamily ?_) h₃
    rw [Indep.isSkewFamily_iff_pairwise_disjoint]
    · exact dj.mono fun i j h ↦ h.mono inter_subset_right inter_subset_right
    rw [project_indep_iff, h₂.contract_indep_iff_of_disjoint]
    · exact hB.indep.subset <| by simpa using fun i ↦ inter_subset_left.trans diff_subset
    simpa using fun i ↦ disjoint_sdiff_right.mono_right inter_subset_left
