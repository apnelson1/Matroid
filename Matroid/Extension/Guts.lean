import Matroid.Modular.Flat
import Matroid.Connectivity.Multi
import Matroid.Extension.Minor
import Matroid.Extension.ProjectionBy
import Matroid.Constructions.Project
import Matroid.ForMathlib.Matroid.Closure
import Matroid.ForMathlib.Data.ENat.Iterate

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

@[simp]
lemma gutsModularCut_eq_top_iff {X : ι → Set α} (Xu : ⋃ i, X i = M.E) :
    M.gutsModularCut X Xu = ⊤ ↔ M.IsSkewFamily X := by
  rw [ModularCut.eq_top_iff, loops, closure_mem_gutsModularCut_iff, project_empty]

/-- Projecting through the guts modular cut of a partition drops its dual connectivity by `1`. -/
lemma multiConn_projectBy_gutsModularCut_add_one (M : Matroid α) {X : ι → Set α}
    (hdj : Pairwise (Disjoint on X)) (Xu : ⋃ i, X i = M.E) (hXsk : ¬ M.IsSkewFamily X) :
    (M.projectBy (M.gutsModularCut X Xu))✶.multiConn X + 1 = M✶.multiConn X := by
  obtain hι | hι := isEmpty_or_nonempty ι
  · simp at hXsk
  rw [eq_comm, ModularCut.multiConn_dual_eq_multiConn_projectBy_dual_add_one_iff']
  suffices ∀ i, (M.project (M.E \ X i)).IsSkewFamily X
    from .inr <| by simpa [mem_gutsModularCut_iff, Xu, hXsk]
  refine fun i ↦ isSkewFamily_of_nearly_all_loops (i₀ := i) ?_ fun j hji ↦ ?_
  · grw [project_ground, ← Xu, ← subset_iUnion]
  grw [project_loops, ← Xu, ← subset_closure _ _ (by grw [Xu, diff_subset]),
    subset_diff, and_iff_left (hdj hji), ← subset_iUnion]

/-- Projecting through the guts modular cut of a partition drops its dual connectivity by `1`.
The truncated subtraction is really the right thing here, though there is no good API for it. -/
lemma multiConn_projectBy_gutsModularCut_eq_sub_one (M : Matroid α) {X : ι → Set α}
    (hdj : Pairwise (Disjoint on X)) (Xu : ⋃ i, X i = M.E) :
    (M.projectBy (M.gutsModularCut X Xu))✶.multiConn X = M✶.multiConn X - 1 := by
  by_cases hX : M.IsSkewFamily X
  · rw [(gutsModularCut_eq_top_iff Xu).2 hX, ModularCut.projectBy_top]
    rw [← dual_isSkewFamily_iff hdj Xu] at hX
    simp [hX.multiConn]
  rw [← M.multiConn_projectBy_gutsModularCut_add_one hdj Xu hX,
    show ∀ a : ℕ∞, a + 1 - 1 = a from fun a ↦ by cases a <;> norm_cast]

/-- The minimum number of guts projections required to make a set `X` skew in the dual matroid.
Equal to `⊤` if no finite number suffices. -/
noncomputable def gutsProjectDepth (M : Matroid α) (X : ι → Set α) (hX : ⋃ i, X i = M.E) : ℕ∞ :=
  ENat.iterateDepth
    (α := {N : Matroid α // N.E = M.E})
    (f := fun N ↦
      ⟨N.1.projectBy (N.1.gutsModularCut X (by simp_rw [hX, ← N.2])), by simpa using N.2⟩)
    (P := fun N ↦ N.1✶.multiConn X = 0)
    (a := ⟨M, rfl⟩)

lemma gutsProjectDepth_eq_zero' {M : Matroid α} {X : ι → Set α} {hX} :
    M.gutsProjectDepth X hX = 0 ↔ M✶.IsSkewFamily X := by
  simp only [gutsProjectDepth, ENat.iterateDepth_eq_zero]
  rw [← multiConn_eq_zero_iff (by simp [← hX, subset_iUnion])]

lemma gutsProjectDepth_eq_zero {M : Matroid α} {X : ι → Set α} {hX}
    (hdj : Pairwise (Disjoint on X)) : M.gutsProjectDepth X hX = 0 ↔ M.IsSkewFamily X := by
  rw [gutsProjectDepth_eq_zero', dual_isSkewFamily_iff hdj hX]

/-- The dual connectivity of a partition is equal to the minimum of guts projections
required to squash the partition into a skew family. -/
theorem gutsProjectDepth_eq_multiConn (M : Matroid α) (X : ι → Set α) (hX : ⋃ i, X i = M.E)
    (hdj : Pairwise (Disjoint on X)) : M.gutsProjectDepth X hX = M✶.multiConn X := by
  rw [gutsProjectDepth, ENat.iterateDepth_eq_self_of_forall_apply_eq_add_one]
  simp only [ne_eq, Subtype.forall]
  rintro N hN hmc
  rw [multiConn_projectBy_gutsModularCut_add_one _ hdj]
  rwa [multiConn_eq_zero_iff (by simp [hN, ← hX, subset_iUnion]),
    dual_isSkewFamily_iff hdj (by rwa [hN])] at hmc

/-- If `A` is a `Finset` with size equal to the dual `multiConn` of a partition `X`,
and `A` is disjoint from the ground set, then there is a major `P` of `M` so that `P ＼ A = M`
and `X` is skew in `P ／ A`. -/
theorem exists_contract_skew_delete_eq_of_card_eq_dual_multiConn (M : Matroid α) (X : ι → Set α)
    (hX : ⋃ i, X i = M.E) (hdj : Pairwise (Disjoint on X)) {A : Finset α}
    (hA : A.card = M✶.multiConn X) (hA_dj : Disjoint (A : Set α) M.E) :
    ∃ (P : Matroid α), (A : Set α) ⊆ P.E ∧ P ＼ A = M ∧ (P ／ A).IsSkewFamily X := by
  induction A using Finset.cons_induction generalizing M with
  | empty =>
  · rw [Finset.card_empty, Nat.cast_zero, eq_comm, M✶.multiConn_eq_zero_iff' hX,
      dual_isSkewFamily_iff hdj hX] at hA
    exact ⟨M, by simpa⟩
  | cons a A has IH =>
  · obtain ⟨haE : a ∉ M.E, hA_dj : Disjoint (A : Set α) M.E⟩ := by simpa using hA_dj
    have hnsk : ¬ M.IsSkewFamily X := by
      rw [← dual_isSkewFamily_iff hdj hX, ← multiConn_eq_zero_iff' (by simpa using hX), ← hA]
      simp
    specialize IH (M.projectBy (M.gutsModularCut X hX)) (by simpa) ?_ (by simpa)
    · rwa [← multiConn_projectBy_gutsModularCut_add_one _ hdj hX hnsk, Finset.card_cons,
        Nat.cast_add, Nat.cast_one, WithTop.add_right_inj (by simp)] at hA
    obtain ⟨Q, hAQ, hQd, hQc⟩ := IH
    rw [← ModularCut.extendBy_contractElem (e := a) _ haE] at hQd
    obtain ⟨P, haP, rfl, hPd⟩ :=
      exists_common_major_of_delete_eq_contractElem (by simpa) hAQ hQd
    refine ⟨P, ?_, ?_, ?_⟩
    · simp [insert_subset_iff, haP (by simp),
        show (A : Set α) ⊆ P.E from hAQ.trans diff_subset]
    · rw [Finset.coe_cons, ← union_singleton, ← delete_delete, hPd,
        ModularCut.extendBy_deleteElem _ haE]
    rwa [Finset.coe_cons, ← singleton_union, ← contract_contract]

theorem bar {M P : Matroid α} (X : ι → Set α) {A : Set α} (h_con : P ／ A = M)
    (h_del : (P ＼ A).IsSkewFamily X) : M.multiConn X ≤ A.encard := by
  rw [isSkewFamily_delete_iff_of_disjoint] at h_del
  · grw [← h_con, ← multiConn_project_eq_multiConn_contract, multiConn_project_le_multiConn_add,
      h_del.multiConn, zero_add, eRk_le_encard]
  exact fun i ↦ (subset_diff.1 <| h_del.subset_ground_of_mem i).2

theorem foo {M P : Matroid α} (X : ι → Set α) (hX : ⋃ i, X i = M.E)
    (hdj : Pairwise (Disjoint on X)) {A : Set α} (h_del : P ＼ A = M)
    (h_con : (P ／ A).IsSkewFamily X) : M✶.multiConn X ≤ A.encard := by
  grw [bar (M := M✶) (P := P✶) X]
  · rw [← h_del, dual_delete]
  rwa [← dual_contract, dual_isSkewFamily_iff hdj]
  rw [hX, contract_ground, ← h_del, delete_ground]
  -- ·
