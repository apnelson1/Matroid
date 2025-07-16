import Matroid.Modular.Flat
import Matroid.Connectivity.Multi
import Matroid.Constructions.Project
import Matroid.ForMathlib.Matroid.Closure

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

lemma closure_mem_gutsModularCut_iff (M : Matroid α) (X : ι → Set α) (Xu : ⋃ i, X i = M.E)
    {Y : Set α} : M.closure Y ∈ M.gutsModularCut X Xu ↔ (M.project Y).IsSkewFamily X := by
  rw [mem_gutsModularCut_iff, and_iff_right (M.closure_isFlat _), project_closure_eq]

lemma foo (M : Matroid α) (X : ι → Set α) (Xu : ⋃ i, X i = M.E) (hXsk : ¬ M.IsSkewFamily X) :
    M.multiConn X = (M.projectBy (M.gutsModularCut X Xu)).multiConn X + 1 := by

  obtain hι | hι := isEmpty_or_nonempty ι
  · simp at hXsk
  classical
  have hXE : ∀ i, X i ⊆ M.E := fun i ↦ (subset_iUnion ..).trans_eq Xu
  choose J hJ using fun i ↦ (M.project (⋃ j ∈ ({i} : Set ι)ᶜ, X j)).exists_isBasis (X i)
  have hJi := fun i ↦ (hJ i).indep.of_project
  choose I hI using fun i ↦ (hJi i).subset_isBasis_of_subset (hJ i).subset
  obtain ⟨hI, hJI⟩ := forall_and.1 hI
  -- by_cases hIsk : M.IsSkewFamily I
  -- · simp [(hIsk.cls_isSkewFamily.mono (fun i ↦ (hI i).subset_closure)).multiConn]
  have hul {i} {j} : J j ⊆ update J i (I i) j := sorry
  have huu {i} {j} : update J i (I i) j ⊆ I j := sorry
  /- The union of one `I i` and all the `J` is independent -/
  have h1 (i) : M.Indep ((I i) ∪ ⋃ j, J j)
  · suffices hsk : M.IsSkewFamily (update J i (I i))
    · rw [Indep.isSkewFamily_iff_pairwise_disjoint_union_indep] at hsk
      · refine hsk.2.subset ?_
        simp only [ne_eq, union_subset_iff, iUnion_subset_iff]
        exact ⟨subset_iUnion_of_subset i (by simp), fun j ↦ subset_iUnion_of_subset j hul⟩
      exact fun j ↦ (hI j).indep.subset huu
    rw [isSkewFamily_iff_nearly_forall_skew_compl_singleton (hJi i₀).subset_ground]
    intro j hji
    rw [update_of_ne hji, (hJi j).skew_iff_contract_indep, ← project_indep_iff]
    · exact (hJ j).indep.of_project_subset <| iUnion₂_mono fun k _ ↦ huu.trans <| (hI _).subset
    exact iUnion₂_subset fun i _ ↦ huu.trans (hI i).indep.subset_ground
  have hdj {i j : ι} (hij : i ≠ j) : Disjoint (J i) (I j) := by
    refine ((subset_diff.1 <| (project_indep_iff.1 (hJ i).indep).subset_ground).2).mono_right ?_
    grw [le_iff_subset, (hI j).subset, ← subset_biUnion_of_mem hij.symm]
  have hJi : M.Indep (⋃ j, J j) :=
    (h1 (Classical.arbitrary ι)).subset subset_union_right
  /- The union of all the `J i` does not belong to the guts cut -/
  have h2 : M.closure (⋃ i, J i) ∉ M.gutsModularCut X Xu
  · refine fun hcl ↦ hXsk ?_
    rw [closure_mem_gutsModularCut_iff] at hcl
    replace hcl : (M.project (⋃ i, J i)).IsSkewFamily fun i ↦ I i \ J i :=
      (hcl.mono fun i ↦ (diff_subset (t := J i)).trans (hI i).subset)
    rw [Indep.isSkewFamily_iff_pairwise_disjoint_union_indep, hJi.project_indep_iff,
      ← iUnion_union_distrib, iUnion_congr (fun i ↦ diff_union_of_subset (hJI i))] at hcl
    · simp_rw [isSkewFamily_iff_cls_isSkewFamily hXE, ← (hI _).closure_eq_closure,
        ← isSkewFamily_iff_cls_isSkewFamily (fun i ↦ (hI i).indep.subset_ground)]
      rw [Indep.isSkewFamily_iff_pairwise_disjoint_union_indep (fun i ↦ (hI i).indep),
        and_iff_left hcl.2.2]
      intro i j hij
      rw [Function.onFun, ← diff_union_of_subset (hJI i), disjoint_union_left,
        and_iff_left (hdj hij), ← diff_union_of_subset (hJI j), disjoint_union_right,
        and_iff_left ((hdj hij.symm).symm.mono_left diff_subset)]
      exact hcl.1 hij
    simp_rw [hJi.project_indep_iff, disjoint_iUnion_right]
    refine fun i ↦ ⟨fun j ↦ ?_, (h1 i).subset (union_subset_union_left _ diff_subset)⟩
    obtain rfl | hij := eq_or_ne i j
    · exact disjoint_sdiff_left
    exact (hdj hij.symm).symm.mono_left diff_subset

  have h3 (s : ι) : M.project (⋃ i ∈ ({s} : Set ι)ᶜ, X i)
      = (M.projectBy (M.gutsModularCut X Xu)).project (⋃ i ∈ ({s} : Set ι)ᶜ, X i) := by
    rw [ModularCut.projectby_eq_project_of_closure_mem]
    rw [closure_mem_gutsModularCut_iff]
    sorry







    -- refine (h1.subset)




        -- refine fun i j hij ↦ disjoint_left.2 fun e hei hej ↦ ?_
