import Matroid.Modular.Basic

universe u

variable {α η : Type*} {ι : Sort*} {M : Matroid α} {e f : α} {Xs Ys Is : ι → Set α} {i j : ι}
    {B I J X X' Y Y' F : Set α}

open Set Function

namespace Matroid

/-- A `SkewFamily` is a collection of sets having pairwise disjoint bases whose union is
  independent. -/
@[mk_iff]
structure SkewFamily (M : Matroid α) (Xs : ι → Set α) : Prop where
  modular : M.ModularFamily Xs
  disj : ∀ ⦃i j⦄, i ≠ j → Xs i ∩ Xs j ⊆ M.closure ∅

lemma SkewFamily.modularFamily (h : M.SkewFamily Xs) : M.ModularFamily Xs :=
  h.1

@[aesop unsafe 5% (rule_sets := [Matroid])]
lemma SkewFamily.subset_ground_of_mem (h : M.SkewFamily Xs) (i : ι) : Xs i ⊆ M.E :=
  h.modularFamily.subset_ground_of_mem i

lemma SkewFamily.loop_of_mem_inter (h : M.SkewFamily Xs) (hij : i ≠ j)
    (he : e ∈ Xs i ∩ Xs j) : M.Loop e :=
  h.2 hij he

lemma SkewFamily.subset_loops_of_ne (h : M.SkewFamily Xs) (hij : i ≠ j) :
    Xs i ∩ Xs j ⊆ M.closure ∅ :=
  h.2 hij

lemma SkewFamily.disjoint_inter_indep (h : M.SkewFamily Xs) (hI : M.Indep I) (hij : i ≠ j) :
    Disjoint (Xs i ∩ I) (Xs j) := by
  rw [disjoint_iff_forall_ne]
  rintro e ⟨hei, heI⟩ _ hej rfl
  exact (hI.nonloop_of_mem heI).not_loop <| h.loop_of_mem_inter hij ⟨hei,hej⟩

lemma SkewFamily.disjoint_of_indep_subset (h : M.SkewFamily Xs) (hI : M.Indep I) (hIX : I ⊆ Xs i)
    (hij : i ≠ j) : Disjoint I (Xs j) := by
  have hdj := h.disjoint_inter_indep hI hij
  rwa [inter_eq_self_of_subset_right hIX] at hdj

lemma SkewFamily.pairwise_disjoint_inter_of_indep {Xs : η → Set α} (h : M.SkewFamily Xs)
    (hI : M.Indep I) : Pairwise (Disjoint on (fun i ↦ Xs i ∩ I)) :=
  fun _ _ hij ↦ (h.disjoint_inter_indep hI hij).mono_right inter_subset_left

lemma SkewFamily.pairwise_disjoint_of_indep_subsets {Is Xs : η → Set α} (h : M.SkewFamily Xs)
    (hIX : ∀ i, Is i ⊆ Xs i) (hIs : ∀ i, M.Indep (Is i)) : Pairwise (Disjoint on Is) :=
  fun i j hij ↦ disjoint_iff_inter_eq_empty.2 <|
    ((hIs i).inter_right (Is j)).eq_empty_of_subset_loops
    ((inter_subset_inter (hIX i) (hIX j)).trans (h.2 hij).subset)

lemma SkewFamily.pairwise_disjoint_of_bases {Is Xs : η → Set α} (h : M.SkewFamily Xs)
    (hIX : ∀ i, M.Basis (Is i) (Xs i)) : Pairwise (Disjoint on Is) :=
  h.pairwise_disjoint_of_indep_subsets (fun i ↦ (hIX i).subset) (fun i ↦ (hIX i).indep)

lemma SkewFamily.cls_skewFamily (h : M.SkewFamily Xs) :
    M.SkewFamily (fun i ↦ M.closure (Xs i)) := by
  refine ⟨h.modularFamily.cls_modularFamily, fun i j hij ↦ ?_⟩
  have := M.closure_subset_closure_of_subset_closure <| h.subset_loops_of_ne hij
  rwa [← (h.modularFamily.modularPair i j).inter_closure_eq]

lemma Indep.skewFamily_of_disjoint_bases {Is Xs : η → Set α} (hI : M.Indep (⋃ i, Is i))
    (hdj : Pairwise (Disjoint on Is)) (hIs : ∀ i, M.Basis (Is i) (Xs i)) : M.SkewFamily Xs := by
  refine ⟨hI.modularFamily fun i ↦ ?_, fun i j hij ↦ ?_⟩
  · rw [hI.inter_basis_closure_iff_subset_closure_inter]
    exact (hIs i).subset_closure.trans
      (M.closure_subset_closure (subset_inter (hIs i).subset (subset_iUnion _ i)))
  refine (inter_subset_inter (M.subset_closure _ (hIs i).subset_ground)
    (M.subset_closure _ (hIs j).subset_ground)).trans ?_
  rw [← (hIs i).closure_eq_closure, ← (hIs j).closure_eq_closure,
    ← (hI.subset _).closure_inter_eq_inter_closure, Disjoint.inter_eq <| hdj hij]
  exact union_subset (subset_iUnion _ _) (subset_iUnion _ _)

lemma skewFamily_iff_exist_bases {Xs : η → Set α} : M.SkewFamily Xs ↔
    ∃ (Is : η → Set α), Pairwise (Disjoint on Is) ∧ M.Basis (⋃ i, Is i) (⋃ i, Xs i) ∧
      ∀ i, M.Basis (Is i) (Xs i) := by
  refine ⟨fun h ↦ ?_, fun ⟨Is, hdj, hIs, hb⟩ ↦ hIs.indep.skewFamily_of_disjoint_bases hdj hb⟩
  obtain ⟨B, hB⟩ := h.modularFamily
  refine ⟨_, ?_, ?_, hB.basis_inter⟩
  · exact h.pairwise_disjoint_of_indep_subsets (fun i ↦ inter_subset_left)
      (fun i ↦ hB.indep.inter_left _)
  rw [← iUnion_inter]
  exact hB.basis_iUnion

lemma Indep.skewFamily_iff_pairwise_disjoint {Is : η → Set α} (hI : M.Indep (⋃ i, Is i)) :
    M.SkewFamily Is ↔ Pairwise (Disjoint on Is) := by
  refine ⟨fun h ↦ h.pairwise_disjoint_of_indep_subsets
    (fun _ ↦ Subset.rfl) (fun i ↦ hI.subset (subset_iUnion _ _)),
    fun h ↦ hI.skewFamily_of_disjoint_bases ?_ (fun i ↦ (hI.subset (subset_iUnion _ _)).basis_self)⟩
  exact h

/--
  For a skew family `Xs`, the union of some independent subsets of the `Xs` is independent.
  Quite a nasty proof. Probably the right proof involves relating modularity to the
  lattice of Flats. -/
lemma SkewFamily.iUnion_indep_subset_indep {ι : Sort u} {Is Xs : ι → Set α} (h : M.SkewFamily Xs)
    (hIX : ∀ i, Is i ⊆ Xs i) (hIs : ∀ i, M.Indep (Is i)) : M.Indep (⋃ i, Is i) := by
  -- reduce to the case where `ι` is a type.
  suffices aux : ∀ (η : Type u) (Is Xs : η → Set α), M.SkewFamily Xs → (∀ i, Is i ⊆ Xs i) →
      (∀ i, M.Indep (Is i)) → M.Indep (⋃ i, Is i) by
    convert aux (PLift ι) (fun i ↦ Is i.down) (fun i ↦ Xs i.down) ?_
      (by simpa [PLift.forall]) (by simpa [PLift.forall])
    · exact (iUnion_plift_down Is).symm
    convert h
    simp [skewFamily_iff, ModularFamily, modularBase_iff, PLift.forall]

  clear! Is Xs
  intro η Is Xs h hIX hIs
  choose Js hJs using fun i ↦ (hIs i).subset_basis_of_subset (hIX i)
  refine Indep.subset ?_ <| iUnion_mono (fun i ↦ (hJs i).2)

  obtain ⟨J, hJ⟩ := M.exists_basis _ (iUnion_subset (fun i ↦ (hJs i).1.indep.subset_ground))

  by_contra hcon
  have ex_i : ∃ i e, e ∈ (Js i) \ J := by
    by_contra! h'
    rw [← hJ.subset.antisymm (iUnion_subset fun i e he ↦ by_contra fun heJ ↦ h' i e ⟨he, heJ⟩)]
      at hcon
    exact hcon hJ.indep

  obtain ⟨i₀, e, hei₀, heJ⟩ := ex_i

  obtain ⟨Ks, hdj, hKs, huKs⟩ := skewFamily_iff_exist_bases.1 h

  have hssE : Js i₀ ∪ (⋃ i ∈ ({i₀}ᶜ : Set η), Ks i) ⊆ M.E := by
    refine union_subset (hJs i₀).1.indep.subset_ground ?_
    simp only [mem_compl_iff, mem_singleton_iff, iUnion_subset_iff]
    exact fun i _ ↦ (huKs i).indep.subset_ground

  obtain ⟨K', hK', hss⟩ := (hJs i₀).1.indep.subset_basis_of_subset subset_union_left hssE

  have hK'' : ∀ i, i ≠ i₀ → Ks i ⊆ K' := by
    intro i hne f hf
    by_contra hfK'
    apply hKs.indep.not_mem_closure_diff_of_mem (mem_iUnion.2 ⟨i,hf⟩)
    have hclosure : f ∈ M.closure K' := by
      exact hK'.subset_closure (Or.inr <| mem_biUnion hne hf)

    refine mem_of_mem_of_subset
      (M.closure_subset_closure (subset_diff_singleton hK'.subset hfK') hclosure)
      (M.closure_subset_closure_of_subset_closure ?_)
    simp only [mem_compl_iff, mem_singleton_iff, mem_union, mem_iUnion, exists_prop, not_exists,
      diff_singleton_subset_iff, union_subset_iff, iUnion_subset_iff]
    refine ⟨(hJs i₀).1.subset.trans ?_, fun i _ ↦ ?_⟩
    · refine (huKs i₀).subset_closure.trans (subset_trans (M.closure_subset_closure ?_)
        (subset_insert _ _))
      refine subset_diff_singleton (subset_iUnion Ks i₀) (fun hf' ↦ ?_)
      exact (hdj hne).ne_of_mem hf hf' rfl

    refine subset_trans ?_ <|
      insert_subset_insert (M.subset_closure _ (diff_subset.trans hKs.indep.subset_ground))
    rw [insert_diff_singleton]
    exact (subset_iUnion Ks i).trans (subset_insert _ _)

  have he' : e ∈ M.closure (K' \ {e}) := by
    refine mem_of_mem_of_subset (hJ.subset_closure (mem_iUnion_of_mem _ hei₀)) ?_
    rw [closure_subset_closure_iff_subset_closure]
    rintro f hf
    obtain ⟨i, hfi⟩ := mem_iUnion.1 (hJ.subset hf)
    obtain (rfl | hi) := eq_or_ne i₀ i
    · apply M.subset_closure (K' \ {e}) (diff_subset.trans hK'.indep.subset_ground)
      exact ⟨hss hfi, fun (h : f = e) ↦ heJ <| h ▸ hf⟩
    refine mem_of_mem_of_subset ((hJs i).1.subset.trans (huKs i).subset_closure hfi)
      (M.closure_subset_closure ?_)
    refine subset_diff_singleton (hK'' i hi.symm) (fun heK ↦ ?_)
    apply Loop.not_nonloop <| h.loop_of_mem_inter hi ⟨(hJs i₀).1.subset hei₀, (huKs i).subset heK⟩
    exact (hK'.indep.subset hss).nonloop_of_mem hei₀

  exact hK'.indep.not_mem_closure_diff_of_mem (hss hei₀) he'

lemma SkewFamily.mono {ι : Sort u} {Xs Ys : ι → Set α} (h : M.SkewFamily Xs)
    (hYX : ∀ i, Ys i ⊆ Xs i) : M.SkewFamily Ys := by
  -- reduce to the case where `ι` is a type.
  suffices aux : ∀ (η : Type u) (Xs Ys : η → Set α), M.SkewFamily Xs → (∀ i, Ys i ⊆ Xs i) →
      M.SkewFamily Ys by
    convert aux (PLift ι) (fun i ↦ Xs i.down) (fun i ↦ Ys i.down) ?_ (by simpa [PLift.forall])
    · simp [skewFamily_iff, ModularFamily, modularBase_iff, PLift.forall]
    simpa [skewFamily_iff, ModularFamily, modularBase_iff, PLift.forall] using h
  clear! Xs Ys
  intro η Xs Ys h hYX
  choose Is hIs using fun i ↦ M.exists_basis (Ys i) ((hYX i).trans (h.subset_ground_of_mem i))
  refine Indep.skewFamily_of_disjoint_bases ?_ ?_ hIs
  · exact h.iUnion_indep_subset_indep (fun i ↦ (hIs i).subset.trans (hYX i)) (fun i ↦ (hIs i).indep)
  exact h.pairwise_disjoint_of_indep_subsets
    (fun i ↦ (hIs i).subset.trans (hYX i)) (fun i ↦ (hIs i).indep)

lemma SkewFamily.iUnion_basis_iUnion (h : M.SkewFamily Xs) (hIs : ∀ i, M.Basis (Is i) (Xs i)) :
    M.Basis (⋃ i, Is i) (⋃ i, Xs i) := by
  have hi := h.iUnion_indep_subset_indep (fun i ↦ (hIs i).subset) (fun i ↦ (hIs i).indep)
  exact hi.basis_of_subset_of_subset_closure (iUnion_mono (fun i ↦ (hIs i).subset)) <|
    iUnion_subset
      (fun i ↦ (hIs i).subset_closure.trans (M.closure_subset_closure (subset_iUnion _ _)))

lemma SkewFamily.sum_eRk_eq_eRk_iUnion [Fintype η] {Xs : η → Set α} (h : M.SkewFamily Xs) :
    ∑ i, M.eRk (Xs i) = M.eRk (⋃ i, Xs i) := by
  choose Is hIs using fun i ↦ M.exists_basis (Xs i) (h.subset_ground_of_mem i)
  have hdj := (h.pairwise_disjoint_of_bases hIs)
  rw [← pairwise_univ] at hdj
  rw [(h.iUnion_basis_iUnion hIs).eRk_eq_encard, encard_iUnion _ hdj]
  simp_rw [(hIs _).eRk_eq_encard]

lemma FinRk.skewFamily_iff_sum_eRk_eq_eRk_iUnion [Fintype η] {Xs : η → Set α}
    (hXs : ∀ i, M.FinRk (Xs i)) (hXE : ∀ i, Xs i ⊆ M.E) :
    M.SkewFamily Xs ↔ ∑ i, M.eRk (Xs i) = M.eRk (⋃ i, Xs i) := by
  refine ⟨SkewFamily.sum_eRk_eq_eRk_iUnion, fun hsum ↦ ?_⟩
  choose Is hIs using fun i ↦ M.exists_basis (Xs i) (hXE i)
  rw [← eRk_closure_eq , ← M.closure_iUnion_closure_eq_closure_iUnion] at hsum
  simp_rw [← (fun i ↦ M.eRk_closure_eq (Xs i)), ← (fun i ↦ (hIs i).closure_eq_closure),
    M.closure_iUnion_closure_eq_closure_iUnion, eRk_closure_eq, (fun i ↦ (hIs i).indep.eRk)] at hsum

  apply Indep.skewFamily_of_disjoint_bases ?_ ?_ hIs
  · exact FinRk.indep_of_encard_le_eRk
      ((FinRk.iUnion hXs).subset (iUnion_mono (fun i ↦ (hIs i).subset)))
      ((encard_iUnion_le _).trans hsum.le)
  rw [← pairwise_univ]
  exact pairwiseDisjoint_of_encard_sum_le_encard_iUnion
    (fun i ↦ (hXs i).finite_of_basis (hIs i)) (hsum.le.trans <| M.eRk_le_encard _)

lemma skewFamily_iff_sum_eRk_eq_eRk_iUnion [Fintype η] [FiniteRk M] {Xs : η → Set α}
    (hXs : ∀ i, Xs i ⊆ M.E) : M.SkewFamily Xs ↔ ∑ i, M.rk (Xs i) = M.rk (⋃ i, Xs i) := by
  simp_rw [FinRk.skewFamily_iff_sum_eRk_eq_eRk_iUnion (fun i ↦ M.to_finRk (Xs i)) hXs,
    ← M.cast_rk_eq, ← Nat.cast_sum, Nat.cast_inj]

lemma skewFamily_iff_forall_circuit {Xs : η → Set α} (hXs : ∀ i, Xs i ⊆ M.E)
    (hdj : Pairwise (Disjoint on Xs)) :
    M.SkewFamily Xs ↔ ∀ C, M.Circuit C → C ⊆ ⋃ i, Xs i → ∃ i, C ⊆ Xs i := by
  refine ⟨fun h C hC hCU ↦ ?_, fun h ↦ ?_⟩
  · have h : ∃ i, ¬ M.Indep (C ∩ Xs i) := by
      by_contra! hcon
      refine hC.dep.not_indep ?_
      refine (h.iUnion_indep_subset_indep (fun i ↦ inter_subset_right) hcon).subset ?_
      simp [← inter_iUnion, hCU, Subset.rfl]
    obtain ⟨i, hi⟩ := h
    rw [← hC.eq_of_not_indep_subset hi inter_subset_left]
    exact ⟨i, inter_subset_right⟩
  choose Is hIs using fun i ↦ M.exists_basis _ (hXs i)
  have hss := iUnion_mono (fun i ↦ (hIs i).subset)
  have hIe : ⋃ i, Is i ⊆ M.E := by simp [fun i ↦ (hIs i).subset.trans (hXs i)]
  have h_inter : ∀ i, Xs i ∩ ⋃ j, Is j = Is i := by
    intro i
    simp only [inter_iUnion, subset_antisymm_iff, iUnion_subset_iff]
    refine ⟨fun j ↦ ?_, subset_iUnion_of_subset i (subset_inter (hIs i).subset Subset.rfl)⟩
    obtain (rfl | hne) := eq_or_ne i j
    · apply inter_subset_right
    simp [((hdj hne).mono_right (hIs j).subset).inter_eq]
  refine Indep.skewFamily_of_disjoint_bases ?_ ?_ hIs
  · rw [indep_iff_forall_subset_not_circuit hIe]
    intro C hCss hC
    obtain ⟨i, hI⟩ := h C hC (hCss.trans hss)
    have hC' := subset_inter hI hCss
    rw [h_inter] at hC'
    exact hC.dep.not_indep ((hIs i).indep.subset hC')
  exact fun i j hne ↦ (hdj hne).mono ((hIs i).subset) ((hIs j).subset)

lemma SkewFamily.exists_subset_of_circuit {Xs : η → Set α} (h : M.SkewFamily Xs) {C : Set α}
    (hC : M.Circuit C) (hCss : C ⊆ ⋃ i, Xs i) : ∃ i, C ⊆ Xs i := by
  set Ys := fun i ↦ (Xs i) ∩ C
  have hYs := h.mono (Ys := Ys) (by simp [Ys])
  by_cases hdj : Pairwise (Disjoint on Ys)
  · rw [skewFamily_iff_forall_circuit (fun i ↦ inter_subset_right.trans hC.subset_ground) hdj] at hYs
    obtain ⟨i, h⟩ := hYs C hC (by rwa [← iUnion_inter, subset_inter_iff, and_iff_left rfl.subset])
    exact ⟨i, h.trans inter_subset_left⟩
  simp only [Pairwise, ne_eq, disjoint_iff_inter_eq_empty, not_forall, Classical.not_imp,
    exists_prop, eq_empty_iff_forall_not_mem, not_not] at hdj
  obtain ⟨i, j, hne, e, he⟩ := hdj
  have hel := hYs.loop_of_mem_inter hne he
  obtain rfl : C = {e} := hel.eq_of_circuit_mem hC
    (mem_of_mem_of_subset he (inter_subset_left.trans inter_subset_right))
  exact ⟨i, singleton_subset_iff.2 <| mem_of_mem_of_subset he
    (inter_subset_left.trans inter_subset_left)⟩

/-- Two sets are skew if they have disjoint bases with independent union. -/
def Skew (M : Matroid α) (X Y : Set α) := M.SkewFamily (fun i ↦ bif i then X else Y)

@[aesop unsafe 5% (rule_sets := [Matroid])]
lemma Skew.subset_ground_left (h : M.Skew X Y) : X ⊆ M.E :=
  h.subset_ground_of_mem true

@[aesop unsafe 5% (rule_sets := [Matroid])]
lemma Skew.subset_ground_right (h : M.Skew X Y) : Y ⊆ M.E :=
  h.subset_ground_of_mem false

lemma Skew.modularPair (h : M.Skew X Y) : M.ModularPair X Y :=
  h.modularFamily

lemma skew_iff_modularPair_inter_subset_loops :
    M.Skew X Y ↔ M.ModularPair X Y ∧ X ∩ Y ⊆ M.closure ∅ := by
  rw [Skew, skewFamily_iff, ModularPair, and_congr_right_iff]
  simp [inter_comm X Y]

lemma ModularPair.skew_of_inter_subset_loops (h : M.ModularPair X Y) (hss : X ∩ Y ⊆ M.closure ∅) :
    M.Skew X Y := by
  rwa [skew_iff_modularPair_inter_subset_loops, and_iff_right h]

lemma ModularPair.skew_of_disjoint (h : M.ModularPair X Y) (hdj : Disjoint X Y) :
    M.Skew X Y :=
  h.skew_of_inter_subset_loops (by simp [hdj.inter_eq])

lemma Skew.inter_subset_loops (h : M.Skew X Y) : X ∩ Y ⊆ M.closure ∅ :=
  (skew_iff_modularPair_inter_subset_loops.1 h).2

lemma Skew.disjoint [Loopless M] (h : M.Skew X Y) : Disjoint X Y := by
  rw [disjoint_iff_inter_eq_empty, ← subset_empty_iff]
  simpa using h.inter_subset_loops

lemma Skew.symm (h : M.Skew X Y) : M.Skew Y X := by
  rw [skew_iff_modularPair_inter_subset_loops] at h ⊢
  rwa [inter_comm, modularPair_comm]

lemma skew_comm : M.Skew X Y ↔ M.Skew Y X :=
  ⟨Skew.symm, Skew.symm⟩

lemma Skew.disjoint_of_indep_subset_left (h : M.Skew X Y) (hI : M.Indep I) (hIX : I ⊆ X) :
    Disjoint I Y :=
  SkewFamily.disjoint_of_indep_subset (i := true) (j := false) h hI hIX (by simp)

lemma Skew.disjoint_of_indep_subset_right (h : M.Skew X Y) (hJ : M.Indep J) (hJY : J ⊆ Y) :
    Disjoint X J :=
  (SkewFamily.disjoint_of_indep_subset (j := true) (i := false) h hJ hJY (by simp)).symm

lemma Skew.disjoint_of_basis_of_subset (h : M.Skew X Y) (hI : M.Basis I X) (hJ : J ⊆ Y) :
    Disjoint I J :=
  (h.disjoint_of_indep_subset_left hI.indep hI.subset).mono_right hJ

lemma Skew.disjoint_of_indep_left (h : M.Skew I X) (hI : M.Indep I) : Disjoint I X :=
  h.disjoint_of_indep_subset_left hI Subset.rfl

lemma Skew.disjoint_of_indep_right (h : M.Skew X I) (hI : M.Indep I) : Disjoint X I :=
  h.disjoint_of_indep_subset_right hI Subset.rfl

lemma Skew.diff_loops_disjoint_left (h : M.Skew X Y) : Disjoint (X \ M.closure ∅) Y := by
  rw [disjoint_iff_inter_eq_empty, ← inter_diff_right_comm, diff_eq_empty]
  exact h.inter_subset_loops

lemma Skew.mono (h : M.Skew X Y) (hX : X' ⊆ X) (hY : Y' ⊆ Y) : M.Skew X' Y' :=
  SkewFamily.mono h (Ys := fun i ↦ bif i then X' else Y') (Bool.rec (by simpa) (by simpa))

lemma Skew.mono_left (h : M.Skew X Y) (hX : X' ⊆ X) : M.Skew X' Y :=
  h.mono hX Subset.rfl

lemma Skew.mono_right (h : M.Skew X Y) (hY : Y' ⊆ Y) : M.Skew X Y' :=
  h.mono Subset.rfl hY

lemma skew_iff_exist_bases {X Y : Set α} :
    M.Skew X Y ↔ ∃ I J, Disjoint I J ∧ M.Basis (I ∪ J) (X ∪ Y) ∧ M.Basis I X ∧ M.Basis J Y := by
  simp only [Skew, skewFamily_iff_exist_bases, Bool.forall_bool, cond_false, cond_true,
    ← pairwise_disjoint_on_bool]
  refine ⟨fun ⟨Is, h1, h2, h3⟩ ↦ ?_, fun ⟨I, J, h1, h2, h3X, h3Y⟩ ↦ ?_⟩
  · refine ⟨Is true, Is false, ?_, ?_, h3.symm⟩
    · convert h1 with b
      cases b <;> rfl
    convert h2 <;> simp [Set.ext_iff, or_comm]
  refine ⟨fun i ↦ bif i then I else J, h1, ?_, by simpa, by simpa⟩
  convert h2 <;> simp [Set.ext_iff, or_comm]

lemma Skew.closure_skew (h : M.Skew X Y) : M.Skew (M.closure X) (M.closure Y) := by
  have h' := SkewFamily.cls_skewFamily h
  simp_rw [Bool.cond_eq_ite, apply_ite, ← Bool.cond_eq_ite] at h'
  exact h'

lemma skew_iff_closure_skew (hX : X ⊆ M.E := by aesop_mat) (hY : Y ⊆ M.E := by aesop_mat) :
    M.Skew X Y ↔ M.Skew (M.closure X) (M.closure Y) :=
  ⟨Skew.closure_skew, fun h ↦ h.mono (M.subset_closure X) (M.subset_closure Y)⟩

lemma skew_iff_closure_skew_left (hX : X ⊆ M.E := by aesop_mat) :
    M.Skew X Y ↔ M.Skew (M.closure X) Y := by
  by_cases hY : Y ⊆ M.E
  · rw [skew_iff_closure_skew, iff_comm, skew_iff_closure_skew, closure_closure]
  exact iff_of_false (fun h ↦ hY <| h.subset_ground_right) (fun h ↦ hY <| h.subset_ground_right)

lemma skew_iff_closure_skew_right (hY : Y ⊆ M.E := by aesop_mat) :
    M.Skew X Y ↔ M.Skew X (M.closure Y) := by
  rw [skew_comm, skew_iff_closure_skew_left, skew_comm]

lemma Skew.closure_skew_right (h : M.Skew X Y) : M.Skew X (M.closure Y) := by
  rwa [← skew_iff_closure_skew_right]

lemma Skew.closure_skew_left (h : M.Skew X Y) : M.Skew (M.closure X) Y := by
  rwa [← skew_iff_closure_skew_left]

lemma Skew.inter_closure_eq (h : M.Skew X Y) : M.closure X ∩ M.closure Y = M.closure ∅ :=
  h.closure_skew.inter_subset_loops.antisymm
    (subset_inter (M.closure_mono (empty_subset _)) (M.closure_mono (empty_subset _)))

lemma skew_iff_of_loopEquiv (hX : M.LoopEquiv X X') (hY : M.LoopEquiv Y Y') :
    M.Skew X Y ↔ M.Skew X' Y' := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rwa [skew_iff_closure_skew hX.subset_ground hY.subset_ground, ← hX.closure_eq_closure,
      ← hY.closure_eq_closure, ← skew_iff_closure_skew]
  rwa [skew_iff_closure_skew hX.symm.subset_ground hY.symm.subset_ground, hX.closure_eq_closure,
    hY.closure_eq_closure, ← skew_iff_closure_skew]

lemma skew_iff_diff_loops_skew : M.Skew X Y ↔ M.Skew (X \ M.closure ∅) (Y \ M.closure ∅) :=
  skew_iff_of_loopEquiv (M.loopEquiv_diff_loops X) (M.loopEquiv_diff_loops Y)

lemma skew_iff_diff_loops_skew_left : M.Skew X Y ↔ M.Skew (X \ M.closure ∅) Y :=
  skew_iff_of_loopEquiv (M.loopEquiv_diff_loops X) rfl

lemma skew_iff_bases_skew (hI : M.Basis I X) (hJ : M.Basis J Y) : M.Skew I J ↔ M.Skew X Y :=
  ⟨fun h ↦ h.closure_skew.mono hI.subset_closure hJ.subset_closure,
    fun h ↦ h.mono hI.subset hJ.subset⟩

lemma Skew.union_indep_of_indep_subsets (h : M.Skew X Y) (hI : M.Indep I) (hIX : I ⊆ X)
    (hJ : M.Indep J) (hJY : J ⊆ Y) : M.Indep (I ∪ J) := by
  rw [union_eq_iUnion]
  exact SkewFamily.iUnion_indep_subset_indep h (Is := fun i ↦ bif i then I else J)
    (Bool.rec (by simpa) (by simpa)) (Bool.rec (by simpa) (by simpa))

lemma Skew.union_basis_union (h : M.Skew X Y) (hI : M.Basis I X) (hJ : M.Basis J Y) :
    M.Basis (I ∪ J) (X ∪ Y) := by
  rw [union_eq_iUnion, union_eq_iUnion]
  exact SkewFamily.iUnion_basis_iUnion h (Bool.rec (by simpa) (by simpa))

lemma Indep.skew_iff_disjoint (h : M.Indep (I ∪ J)) : M.Skew I J ↔ Disjoint I J := by
  rw [← pairwise_disjoint_on_bool, Skew, Indep.skewFamily_iff_pairwise_disjoint]
  rwa [union_eq_iUnion] at h

lemma Indep.skew_iff_disjoint_union_indep (hI : M.Indep I) (hJ : M.Indep J) :
    M.Skew I J ↔ Disjoint I J ∧ M.Indep (I ∪ J) := by
  refine ⟨fun h ↦ ⟨h.disjoint_of_indep_left hI, ?_⟩, fun h ↦ h.2.skew_iff_disjoint.2 h.1⟩
  exact h.union_indep_of_indep_subsets hI Subset.rfl hJ Subset.rfl

lemma Indep.subset_skew_diff (h : M.Indep I) (hJI : J ⊆ I) : M.Skew J (I \ J) := by
  rw [Indep.skew_iff_disjoint]
  · exact disjoint_sdiff_right
  exact h.subset (union_subset hJI diff_subset)

lemma skew_iff_contract_restrict_eq_restrict (hX : X ⊆ M.E := by aesop_mat)
    (hY : Y ⊆ M.E := by aesop_mat) : M.Skew X Y ↔ (M ／ X) ↾ Y = M ↾ Y := by
  obtain ⟨I, hI⟩ := M.exists_basis X
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine ext_indep rfl fun J (hJ : J ⊆ Y) ↦ ?_
    simp_rw [restrict_indep_iff, hI.contract_indep_iff, and_iff_left hJ]
    refine ⟨fun h ↦ h.1.subset subset_union_left,
      fun hJi ↦ ⟨?_, h.disjoint_of_indep_subset_right hJi hJ⟩⟩
    exact h.symm.union_indep_of_indep_subsets hJi hJ hI.indep hI.subset
  obtain ⟨J, hJ⟩ := M.exists_basis Y
  have hi : (M ↾ Y).Indep J := restrict_indep_iff.2 ⟨hJ.indep, hJ.subset⟩
  rw [← h, hI.contract_eq_contract_delete, restrict_indep_iff, delete_indep_iff,
    hI.indep.contract_indep_iff, union_comm, disjoint_comm,
    ← hI.indep.skew_iff_disjoint_union_indep hJ.indep] at hi

  exact hi.1.1.closure_skew.mono hI.subset_closure hJ.subset_closure

lemma skew_insert_iff (he : e ∈ M.E) :
    M.Skew (insert e X) Y ↔ M.Skew X Y ∧ (e ∈ M.closure (X ∪ Y) → e ∈ M.closure X) := by
  wlog hXE : X ⊆ M.E
  · refine iff_of_false (fun hs ↦ hXE ((subset_insert _ _).trans hs.subset_ground_left))
      (fun h ↦ hXE h.1.subset_ground_left)
  wlog hYE : Y ⊆ M.E
  · exact iff_of_false (fun h ↦ hYE h.subset_ground_right) (fun h ↦ hYE h.1.subset_ground_right)
  obtain hl | hnl := M.loop_or_nonloop e
  · rw [skew_iff_diff_loops_skew_left, insert_diff_of_mem _ hl, ← skew_iff_diff_loops_skew_left]
    simp [hl.mem_closure X]

  by_cases heY : e ∈ Y
  · refine iff_of_false (fun hsk ↦ hnl.not_loop ?_) ?_
    · exact hsk.inter_subset_loops ⟨.inl rfl, by simpa using heY⟩
    rw [not_and, _root_.not_imp]
    refine fun hsk ↦ ⟨M.mem_closure_of_mem' <| .inr heY  , fun hcl ↦ hnl.not_loop ?_⟩
    exact hsk.inter_closure_eq.subset (show e ∈ _ from ⟨hcl, M.mem_closure_of_mem' heY⟩)

  by_cases heX : e ∈ M.closure X
  · rw [skew_iff_closure_skew_left, closure_insert_eq_of_mem_closure heX,
      ← skew_iff_closure_skew_left]
    simp [heX]

  simp only [heX, imp_false]
  refine ⟨fun h ↦ ⟨h.mono_left (subset_insert _ _), fun hecl ↦ ?_⟩, fun ⟨hsk, h⟩ ↦ ?_⟩
  · rw [skew_comm, skew_iff_contract_restrict_eq_restrict] at h
    have he' : e ∈ (M ／ Y).closure X
    · rwa [contract_closure_eq, mem_diff, and_iff_left heY]
    have he'' : e ∈ ((M ／ Y) ↾ (insert e X)).closure X
    · rw [restrict_closure_eq', inter_eq_self_of_subset_left (subset_insert _ _)]
      simp [hecl, heY]
    rw [h, restrict_closure_eq _ (subset_insert _ _)] at he''
    exact heX he''.1
  rw [skew_iff_exist_bases] at hsk ⊢
  obtain ⟨I, J, hdj, hIJ, hI, hJ⟩ := hsk

  refine ⟨insert e I, J, ?_⟩
  rw [← singleton_union, union_assoc, ← singleton_union, union_assoc, disjoint_union_left]
  simp only [disjoint_singleton_left, hdj, and_true, singleton_union, hJ]

  have heIJ : M.Indep (insert e (I ∪ J))
  · rw [hIJ.indep.insert_indep_iff, hIJ.closure_eq_closure]
    exact .inl ⟨he, h⟩
  exact ⟨not_mem_subset (hJ.subset.trans (M.subset_closure_of_subset' subset_union_right)) h,
    hIJ.insert_basis_insert heIJ,
    hI.insert_basis_insert (heIJ.subset (insert_subset_insert subset_union_left))⟩

lemma Skew.contract_restrict_eq (hXY : M.Skew X Y) : (M ／ X) ↾ Y = M ↾ Y :=
  (skew_iff_contract_restrict_eq_restrict hXY.subset_ground_left hXY.subset_ground_right).1 hXY

lemma empty_skew (hX : X ⊆ M.E) : M.Skew ∅ X := by
  rw [skew_iff_contract_restrict_eq_restrict, contract_empty]

lemma skew_empty (hX : X ⊆ M.E) : M.Skew X ∅ :=
  (empty_skew hX).symm

lemma exists_contract_indep_to_spanning (M : Matroid α) (X : Set α) (hX : X ⊆ M.E) :
    ∃ I, M.Indep I ∧ Disjoint I X ∧ (M ／ I) ↾ X = M ↾ X ∧ (M ／ I).Spanning X := by
  obtain ⟨J, hJ⟩ := M.exists_basis X
  obtain ⟨B, hB, rfl⟩ := hJ.exists_base
  refine ⟨B \ X, hB.indep.diff _, disjoint_sdiff_left, Skew.contract_restrict_eq ?_, ?_⟩
  · rw [skew_iff_closure_skew_right, ← hJ.closure_eq_closure, ← skew_iff_closure_skew_right]
    simpa using (hB.indep.subset_skew_diff (diff_subset (t := X)))
  rw [contract_spanning_iff (diff_subset.trans hB.subset_ground), union_diff_self,
    and_iff_left disjoint_sdiff_right]
  exact hB.spanning.superset subset_union_right

/-- For any set `X`, we can find a minor in which `X` is spanning and cospanning,
such that both the restrict and corestriction to `X` are unchanged.  -/
lemma exists_minor_restrict_corestrict_eq_spanning_cospanning (hX : X ⊆ M.E) :
    ∃ N, N ≤m M ∧ N ↾ X = M ↾ X ∧ N✶ ↾ X = M✶ ↾ X ∧ N.Spanning X ∧ N✶.Spanning X := by
  obtain ⟨I, hI, hIX, hI_eq, hIsp⟩ := M.exists_contract_indep_to_spanning X hX
  obtain ⟨J, hJ, hJX, hJ_eq, hJsp⟩ := (M ／ I)✶.exists_contract_indep_to_spanning X
    hIsp.subset_ground
  refine ⟨M ／ I ＼ J, contract_delete_minor _ _ _, ?_, ?_, ?_, ?_⟩
  · rw [← delete_compl _, delete_ground, contract_ground, delete_delete,
      diff_diff_comm (t := J), union_diff_self, union_comm, ← delete_delete,
      ← contract_ground, delete_compl _, hI_eq, ← delete_inter_ground_eq,
      restrict_ground_eq, hJX.inter_eq, delete_empty]
    · exact hIsp.subset_ground
    exact hJsp.subset_ground
  · rw [delete_dual_eq_dual_contract, hJ_eq, contract_dual_eq_dual_delete, delete_eq_restrict,
      restrict_restrict_eq _ (show X ⊆ M✶.E \ I from hIsp.subset_ground)]
  · rwa [Coindep.delete_spanning_iff hJ, and_iff_left hJX.symm]
  rwa [delete_dual_eq_dual_contract]

lemma SkewFamily.skew_compl {Xs : η → Set α} (h : M.SkewFamily Xs) (A : Set η) :
    M.Skew (⋃ i ∈ A, Xs i) (⋃ i ∈ Aᶜ, Xs i) := by
  rw [skew_iff_modularPair_inter_subset_loops]
  refine ⟨h.modularFamily.modularPair_compl_biUnion A, ?_⟩
  rintro e ⟨⟨_,⟨i,hi,rfl⟩,hi'⟩ ,⟨_,⟨j,hj,rfl⟩,hj'⟩⟩
  simp only [mem_iUnion, exists_prop] at hi' hj'
  exact h.loop_of_mem_inter (show i ≠ j from fun hij ↦ hj'.1 <| hij ▸ hi'.1) ⟨hi'.2, hj'.2⟩

lemma SkewFamily.skew_compl_singleton {Xs : η → Set α} (h : M.SkewFamily Xs) (i : η) :
    M.Skew (Xs i) (⋃ j ∈ ({i} : Set η)ᶜ, Xs j) := by
  convert h.skew_compl {i}; simp

lemma skew_iff_forall_circuit (hdj : Disjoint X Y) (hX : X ⊆ M.E := by aesop_mat)
    (hY : Y ⊆ M.E := by aesop_mat) : M.Skew X Y ↔ ∀ C, M.Circuit C → C ⊆ X ∪ Y → C ⊆ X ∨ C ⊆ Y := by
  rw [Skew, skewFamily_iff_forall_circuit]
  · simp [← union_eq_iUnion, or_comm]
  · simp [hX, hY]
  rwa [pairwise_disjoint_on_bool]

lemma Skew.subset_or_subset_of_circuit (h : M.Skew X Y) {C : Set α} (hC : M.Circuit C)
    (hCss : C ⊆ X ∪ Y) : C ⊆ X ∨ C ⊆ Y := by
  rw [Skew] at h
  obtain ⟨rfl | rfl, hi⟩ := h.exists_subset_of_circuit hC <| by simpa [← union_eq_iUnion]
  · right
    simpa using hi
  left
  simpa using hi

lemma skew_of_subset_loops {L : Set α} (hL : L ⊆ M.closure ∅) (hX : X ⊆ M.E) : M.Skew L X := by
  rw [skew_iff_diff_loops_skew_left, diff_eq_empty.2 hL]
  apply empty_skew hX

lemma Loop.skew (he : M.Loop e) (hX : X ⊆ M.E) : M.Skew {e} X :=
  skew_of_subset_loops (by simpa) hX

lemma skew_of_subset_coloops {K : Set α} (hK : K ⊆ M✶.closure ∅) (hX : X ⊆ M.E)
    (hdj : Disjoint K X) : M.Skew K X := by
  rw [skew_iff_contract_restrict_eq_restrict, contract_eq_delete_of_subset_coloops hK,
    delete_eq_restrict, restrict_restrict_eq]
  rwa [subset_diff, and_iff_left hdj.symm]

lemma Coloop.skew (he : M.Coloop e) (hX : X ⊆ M.E) (heX : e ∉ X) : M.Skew {e} X :=
  skew_of_subset_coloops (by simpa) hX (by simpa)

lemma Nonloop.skew_right_iff (he : M.Nonloop e) (hX : X ⊆ M.E := by aesop_mat) :
    M.Skew X {e} ↔ e ∉ M.closure X := by
  obtain ⟨I, hI⟩ := M.exists_basis X
  rw [← skew_iff_bases_skew hI he.indep.basis_self, ← hI.closure_eq_closure,
    Indep.skew_iff_disjoint_union_indep hI.indep he.indep, disjoint_singleton_right,
    hI.indep.not_mem_closure_iff, union_singleton, and_comm]

lemma Nonloop.skew_left_iff (he : M.Nonloop e) (hX : X ⊆ M.E := by aesop_mat) :
    M.Skew {e} X ↔ e ∉ M.closure X := by
  rw [← he.skew_right_iff, skew_comm]

lemma Skew.restrict (hXY : M.Skew X Y) (R : Set α) : (M ↾ R).Skew (X ∩ R) (Y ∩ R) := by
  rw [skew_iff_exist_bases]
  simp only [basis_restrict_iff', union_subset_iff, inter_subset_right, and_self, and_true]
  rw [← union_inter_distrib_right, inter_right_comm,
    inter_eq_self_of_subset_left (union_subset hXY.subset_ground_left hXY.subset_ground_right),
    inter_right_comm, inter_eq_self_of_subset_left hXY.subset_ground_left,
    inter_right_comm, inter_eq_self_of_subset_left hXY.subset_ground_right,
    union_inter_distrib_right]
  replace hXY := hXY.mono (inter_subset_left (t := R)) (inter_subset_left (t := R))
  rwa [skew_iff_exist_bases] at hXY

lemma Skew.restrict_of_subset {R : Set α} (hXY : M.Skew X Y) (hXR : X ⊆ R) (hYR : Y ⊆ R) :
    (M ↾ R).Skew X Y := by
  convert hXY.restrict R <;> simpa

lemma Skew.of_restrict {R : Set α} (h : (M ↾ R).Skew X Y) (hR : R ⊆ M.E := by aesop_mat) :
    M.Skew X Y := by
  rw [skew_iff_modularPair_inter_subset_loops] at h ⊢
  simp only [restrict_closure_eq', empty_inter, diff_eq_empty.2 hR, union_empty,
    subset_inter_iff] at h
  exact ⟨h.1.ofRestrict hR, h.2.1⟩

lemma skew_restrict_iff {R : Set α} (hRE : R ⊆ M.E := by aesop_mat) :
    (M ↾ R).Skew X Y ↔ M.Skew X Y ∧ X ⊆ R ∧ Y ⊆ R :=
  ⟨fun h ↦ ⟨h.of_restrict, h.subset_ground_left, h.subset_ground_right⟩,
    fun h ↦ h.1.restrict_of_subset h.2.1 h.2.2⟩

lemma Skew.delete (hXY : M.Skew X Y) (D : Set α) : (M ＼ D).Skew (X \ D) (Y \ D) := by
  convert hXY.restrict (M.E \ D) using 1
  · rw [← inter_diff_assoc, inter_eq_self_of_subset_left hXY.subset_ground_left]
  rw [← inter_diff_assoc, inter_eq_self_of_subset_left hXY.subset_ground_right]

lemma Skew.delete_of_disjoint {D : Set α} (hXY : M.Skew X Y) (hXD : Disjoint X D)
    (hYD : Disjoint Y D) : (M ＼ D).Skew X Y := by
  convert hXY.delete D
  · exact hXD.sdiff_eq_left.symm
  exact hYD.sdiff_eq_left.symm

lemma Skew.of_delete {D : Set α} (h : (M ＼ D).Skew X Y) : M.Skew X Y :=
  h.of_restrict

lemma skew_delete_iff {D : Set α} :
    (M ＼ D).Skew X Y ↔ M.Skew X Y ∧ Disjoint X D ∧ Disjoint Y D :=
  ⟨fun h ↦ ⟨h.of_delete, (subset_diff.1 h.subset_ground_left).2,
    (subset_diff.1 h.subset_ground_right).2⟩, fun h ↦ h.1.delete_of_disjoint h.2.1 h.2.2⟩

lemma Skew.contract_subset_left {C : Set α} (hXY : M.Skew X Y) (hCX : C ⊆ X) :
    (M ／ C).Skew (X \ C) (Y \ C) := by
  obtain ⟨J, hJ⟩ := M.exists_basis C (hCX.trans hXY.subset_ground_left)
  obtain ⟨I, hI, rfl⟩ := hJ.exists_basis_inter_eq_of_superset hCX
  obtain ⟨K, hK⟩ := M.exists_basis Y
  have hdj : Disjoint X K := (hXY.mono_right hK.subset).disjoint_of_indep_right hK.indep
  have hi' : (M ／ C).Indep ((I \ C) ∪ K)
  · rw [hJ.contract_indep_iff, disjoint_union_right, and_iff_right disjoint_sdiff_right,
      union_right_comm, diff_union_inter]
    exact ⟨(hXY.union_basis_union hI hK).indep, hdj.mono_left hCX⟩
  have hsk := hi'.skew_iff_disjoint.2 (hdj.mono_left (diff_subset.trans hI.subset))
  refine hsk.closure_skew.mono ?_ ?_
  · rw [contract_closure_eq, diff_union_self, closure_union_congr_left hI.closure_eq_closure,
      union_eq_self_of_subset_right hCX]
    exact diff_subset_diff_left (M.subset_closure X)
  rw [contract_closure_eq, closure_union_congr_left hK.closure_eq_closure]
  exact diff_subset_diff_left (M.subset_closure_of_subset subset_union_left)

lemma Skew.contract_subset_left_of_disjoint_loops {C : Set α} (hXY : M.Skew X Y) (hCX : C ⊆ X)
    (hY : Disjoint Y (M.closure ∅)) : (M ／ C).Skew (X \ C) Y := by
  convert hXY.contract_subset_left hCX
  rw [eq_comm, sdiff_eq_left, ← hY.sdiff_eq_left]
  exact hXY.symm.diff_loops_disjoint_left.mono_right hCX

lemma Skew.contract_subset_right_of_disjoint_loops {C : Set α} (hXY : M.Skew X Y) (hCY : C ⊆ Y)
    (hX : Disjoint X (M.closure ∅)) : (M ／ C).Skew X (Y \ C) :=
  (hXY.symm.contract_subset_left_of_disjoint_loops hCY hX).symm

lemma Skew.contract_subset_right {C : Set α} (hXY : M.Skew X Y) (hCX : C ⊆ Y) :
    (M ／ C).Skew (X \ C) (Y \ C) :=
  (hXY.symm.contract_subset_left hCX).symm

lemma Skew.contract_subset_union {C : Set α} (hXY : M.Skew X Y) (hC : C ⊆ X ∪ Y) :
    (M ／ C).Skew (X \ C) (Y \ C) := by
  have h := (hXY.contract_subset_left (C := X ∩ C) inter_subset_left).contract_subset_right
    (C := (Y \ X) ∩ C) ?_
  · rwa [contract_contract, ← union_inter_distrib_right, union_diff_self,
      inter_eq_self_of_subset_right hC, diff_self_inter, (sdiff_eq_left (x := X \ C)).2,
      diff_diff, ← union_inter_distrib_right, union_diff_self,
      inter_eq_self_of_subset_right hC] at h
    exact disjoint_sdiff_left.mono_right inter_subset_right
  rw [subset_diff, and_iff_right (inter_subset_left.trans diff_subset)]
  exact disjoint_sdiff_left.mono inter_subset_left inter_subset_left

lemma modularPair_iff_skew_contract_inter (hXY : X ∩ Y ⊆ M.E) :
    M.ModularPair X Y ↔ (M ／ (X ∩ Y)).Skew (X \ Y) (Y \ X) := by

  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [skew_iff_modularPair_inter_subset_loops, disjoint_sdiff_sdiff.inter_eq,
      and_iff_left (empty_subset _)]
    convert h.contract (C := X ∩ Y) inter_subset_left inter_subset_right using 1 <;> simp

  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ Y)

  obtain ⟨IX, hIX⟩ := (M ／ (X ∩ Y)).exists_basis (X \ Y) h.subset_ground_left
  obtain ⟨IY, hIY⟩ := (M ／ (X ∩ Y)).exists_basis (Y \ X) h.subset_ground_right

  have hi : M.Indep ((I ∪ IX) ∪ (I ∪ IY))
  · rw [← union_union_distrib_left]
    have hb := (h.union_basis_union hIX hIY).indep
    rw [hI.contract_indep_iff, union_comm] at hb
    exact hb.1

  refine hi.modularPair_of_union.of_basis_of_basis ?_ ?_
  · refine (hi.subset subset_union_left).basis_of_subset_of_subset_closure ?_ ?_
    · exact union_subset (hI.subset.trans inter_subset_left) (hIX.subset.trans diff_subset)
    have h := union_subset_union hIX.subset_closure hI.subset_closure
    rw [diff_union_inter, contract_closure_eq, ← closure_union_congr_right hI.closure_eq_closure,
      union_comm IX] at h
    exact h.trans (union_subset diff_subset (M.closure_subset_closure subset_union_left))
  refine (hi.subset subset_union_right).basis_of_subset_of_subset_closure ?_ ?_
  · exact union_subset (hI.subset.trans inter_subset_right) (hIY.subset.trans diff_subset)
  have h := union_subset_union hIY.subset_closure hI.subset_closure
  rw [inter_comm, diff_union_inter, contract_closure_eq, inter_comm,
    ← closure_union_congr_right hI.closure_eq_closure, union_comm IY] at h
  exact h.trans (union_subset diff_subset (M.closure_subset_closure subset_union_left))

lemma ModularPair.contract_subset_left {C : Set α} (hXY : M.ModularPair X Y) (hCX : C ⊆ X) :
    (M ／ C).ModularPair (X \ C) (Y \ C) := by
  rw [modularPair_iff_skew_contract_inter
    (inter_subset_left.trans (diff_subset_diff_left hXY.subset_ground_left))]
  rw [modularPair_iff_skew_contract_inter (inter_subset_left.trans hXY.subset_ground_left)] at hXY
  simp only [diff_inter_diff_right, contract_contract, union_diff_self, diff_diff_right,
    diff_diff_comm (s := X), diff_inter_self, union_empty, diff_diff_comm (s := Y)]
  rw [union_comm, ← contract_contract]
  have h' := hXY.contract_subset_left (C := C \ Y) (diff_subset_diff_left hCX)
  nth_rewrite 1 [← inter_eq_self_of_subset_left hCX, contract_contract]
  have hrw : X ∩ Y ∪ C ∩ X = X ∩ Y ∪ (C \ Y)
  · rw [inter_eq_self_of_subset_left hCX]
    refine subset_antisymm ?_ (union_subset_union_right _ diff_subset)
    rw [union_subset_iff, and_iff_right subset_union_left]
    nth_rewrite 1 [← diff_union_inter C Y, union_comm]
    exact union_subset_union_left _ (inter_subset_inter_left _ hCX)
  rw [hrw, ← contract_contract]
  exact h'.mono (diff_subset_diff_right diff_subset) (diff_subset_diff_right diff_subset)

lemma ModularPair.skew_contract_inter (hXY : M.ModularPair X Y) :
    (M ／ (X ∩ Y)).Skew (X \ Y) (Y \ X) := by
  rwa [← modularPair_iff_skew_contract_inter (inter_subset_left.trans hXY.subset_ground_left)]



section ModularCompl


section ModularCompl

variable {F₀ F₁ F F' : Set α}

/-- `M.ModularCompl F₀ F₁ F F'` means that `F,F'` are a modular pair of flats with intersection
`F₀` and whose union has closure `F₁`.
Every `F` with `F₀ ⊆ F ⊆ F₁` has a `ModularCompl`.   -/
@[mk_iff] structure ModularCompl (M : Matroid α) (F₀ F₁ F F' : Set α) : Prop where
  flat_left : M.Flat F
  flat_right : M.Flat F'
  inter_eq : F ∩ F' = F₀
  closure_union_eq : M.closure (F ∪ F') = F₁
  modularPair : M.ModularPair F F'

lemma ModularCompl.symm (h : M.ModularCompl F₀ F₁ F F') : M.ModularCompl F₀ F₁ F' F where
  flat_left := h.flat_right
  flat_right := h.flat_left
  inter_eq := by rw [← h.inter_eq, inter_comm]
  closure_union_eq := by rw [← h.closure_union_eq, union_comm]
  modularPair := h.modularPair.symm

lemma modularCompl_comm :
    M.ModularCompl F₀ F₁ F F' ↔ M.ModularCompl F₀ F₁ F' F :=
  ⟨ModularCompl.symm, ModularCompl.symm⟩

@[aesop unsafe 24% (rule_sets := [Matroid])]
lemma ModularCompl.left_subset_ground (h : M.ModularCompl F₀ F₁ F F') : F ⊆ M.E :=
  h.flat_left.subset_ground

@[aesop unsafe 25% (rule_sets := [Matroid])]
lemma ModularCompl.right_subset_ground (h : M.ModularCompl F₀ F₁ F F') : F' ⊆ M.E :=
  h.flat_right.subset_ground

lemma ModularCompl.flat_top (h : M.ModularCompl F₀ F₁ F F') : M.Flat F₁ := by
  simp [← h.closure_union_eq]

@[aesop unsafe 25% (rule_sets := [Matroid])]
lemma ModularCompl.top_subset_ground (h : M.ModularCompl F₀ F₁ F F') : F₁ ⊆ M.E :=
  h.flat_top.subset_ground

lemma ModularCompl.flat_bot (h : M.ModularCompl F₀ F₁ F F') : M.Flat F₀ := by
  rw [← h.inter_eq]
  exact h.flat_left.inter h.flat_right

@[aesop unsafe 25% (rule_sets := [Matroid])]
lemma ModularCompl.bot_subset_ground (h : M.ModularCompl F₀ F₁ F F') : F₀ ⊆ M.E :=
  h.flat_bot.subset_ground

lemma ModularCompl.subset_left (h : M.ModularCompl F₀ F₁ F F') : F₀ ⊆ F := by
  simp [← h.inter_eq]

lemma ModularCompl.subset_right (h : M.ModularCompl F₀ F₁ F F') : F₀ ⊆ F' := by
  simp [← h.inter_eq]

lemma ModularCompl.left_subset (h : M.ModularCompl F₀ F₁ F F') : F ⊆ F₁ := by
  rw [← h.closure_union_eq]
  refine M.subset_closure_of_subset' subset_union_left h.flat_left.subset_ground

lemma ModularCompl.right_subset (h : M.ModularCompl F₀ F₁ F F') : F' ⊆ F₁ :=
  h.symm.left_subset

lemma ModularCompl.subset (h : M.ModularCompl F₀ F₁ F F') : F₀ ⊆ F₁ :=
  h.subset_left.trans h.left_subset

lemma Flat.exists_modularCompl (hF₀ : M.Flat F₀) (hF₁ : M.Flat F₁) (hF : M.Flat F) (hF₀F : F₀ ⊆ F)
    (hFF₁ : F ⊆ F₁) : ∃ F', M.ModularCompl F₀ F₁ F F' := by
  obtain ⟨I, hI⟩ := M.exists_basis F₀
  obtain ⟨J, hJ, rfl⟩ := hI.exists_basis_inter_eq_of_superset hF₀F
  obtain ⟨K, hK, rfl⟩ := hJ.exists_basis_inter_eq_of_superset hFF₁
  rw [inter_assoc, inter_eq_self_of_subset_right hF₀F] at hI

  have hi : M.Indep (K ∩ F ∪ (K ∩ F₀ ∪ K \ F)) :=
    hK.indep.subset (union_subset inter_subset_left (union_subset inter_subset_left diff_subset))

  have hmod : M.ModularPair F (M.closure (F₀ ∪ K \ F))
  · refine hi.modularPair_of_union.of_basis_of_basis hJ ?_
    rw [← closure_union_congr_left hI.closure_eq_closure]
    exact Indep.basis_closure (hK.indep.subset (union_subset inter_subset_left diff_subset))

  use M.closure (F₀ ∪ (K \ F))
  rw [modularCompl_iff, and_iff_right hF, and_iff_right (M.closure_flat _),
    closure_union_closure_right_eq, union_comm F, union_assoc, diff_union_self, union_comm K,
    ← union_assoc, closure_union_congr_right hK.closure_eq_closure,
    union_eq_self_of_subset_left (union_subset (hF₀F.trans hFF₁) hFF₁), hF₁.closure,
    and_iff_right rfl, and_iff_left hmod]

  rw [← (hF.inter (M.closure_flat _)).closure,  hmod.inter_closure_eq, ← hJ.closure_eq_closure,
    closure_closure, ← closure_union_congr_left hI.closure_eq_closure,
     ← Indep.closure_inter_eq_inter_closure, inter_union_distrib_left, ← inter_inter_distrib_left,
     inter_eq_self_of_subset_right hF₀F,
     (disjoint_sdiff_right.mono_left inter_subset_right).inter_eq, union_empty,
    hI.closure_eq_closure, hF₀.closure]

  exact hK.indep.subset (union_subset inter_subset_left
    (union_subset inter_subset_left diff_subset))

/-- Two flats are `ModularCompl` in the interval `[M.closure ∅, M.E]` iff they are skew
with spanning union. -/
lemma modularCompl_loops_ground_iff {F F' : Set α} (hF : M.Flat F) (hF' : M.Flat F'):
    M.ModularCompl (M.closure ∅) M.E F F' ↔ M.Skew F F' ∧ M.Spanning (F ∪ F') := by
  rw [modularCompl_iff, and_iff_right hF, and_iff_right hF', spanning_iff_closure_eq,
    and_comm (b := M.ModularPair _ _), ← and_assoc, and_congr_left_iff]
  refine fun hcl ↦ ⟨fun ⟨h, hmod⟩ ↦ ?_, fun h ↦ ⟨?_, h.modularPair ⟩⟩
  · rw [skew_iff_modularPair_inter_subset_loops, and_iff_right hmod, h]
  rw [← h.inter_closure_eq, hF.closure, hF'.closure]

lemma ModularCompl.basis_inter_basis_eq {J' : Set α} (h : M.ModularCompl F₀ F₁ F F')
    (hI : M.Basis I F₀) (hJ : M.Basis J F) (hJ' : M.Basis J' F') (hIJ : I ⊆ J) (hIJ' : I ⊆ J') :
    J ∩ J' = I := by
  have hcl := h.modularPair.inter_closure_eq
  rw [h.inter_eq, ← hI.closure_eq_closure, ← hJ.closure_eq_closure,
    ← hJ'.closure_eq_closure] at hcl
  rw [← (hJ.indep.inter_right J').closure_inter_eq_self_of_subset (subset_inter hIJ hIJ'),
    eq_comm, inter_eq_right, hcl]
  exact inter_subset_inter (M.subset_closure J) (M.subset_closure J')

lemma ModularCompl.basis_inter_right_eq (h : M.ModularCompl F₀ F₁ F F')
    (hI : M.Basis I F₀) (hJ : M.Basis J F) (hIJ : I ⊆ J) : J ∩ F' = I := by
  rw [inter_comm, hI.eq_of_subset_indep (hJ.indep.inter_left F')
    (subset_inter (hI.subset.trans h.subset_right) hIJ)]
  rw [← h.inter_eq, inter_comm]
  exact inter_subset_inter_left _ hJ.subset

lemma ModularCompl.union_basis_top {J' : Set α} (h : M.ModularCompl F₀ F₁ F F') (hI : M.Basis I F₀)
    (hJ : M.Basis J F) (hJ' : M.Basis J' F') (hIJ : I ⊆ J) (hIJ' : I ⊆ J') :
    M.Basis (J ∪ J') F₁ := by
  refine Indep.basis_of_subset_of_subset_closure ?_
    (union_subset (hJ.subset.trans h.left_subset) (hJ'.subset.trans h.right_subset))
    (by rw [closure_union_congr_left hJ.closure_eq_closure,
      closure_union_congr_right hJ'.closure_eq_closure, h.closure_union_eq])
  have hp := h.modularPair
  rw [modularPair_iff_skew_contract_inter (inter_subset_left.trans hp.subset_ground_left),
    h.inter_eq, hI.contract_eq_contract_delete] at hp
  replace hp := hp.of_delete

  have hwin := hp.union_indep_of_indep_subsets (I := J \ I) (J := J' \ I)
  rw [hI.indep.contract_indep_iff, and_iff_right disjoint_sdiff_left, diff_union_of_subset hIJ,
    hI.indep.contract_indep_iff, diff_union_of_subset hIJ', and_iff_right disjoint_sdiff_left,
    imp_iff_right hJ.indep, imp_iff_right hJ'.indep, hI.indep.contract_indep_iff,
    ← union_diff_distrib, diff_union_self] at hwin
  refine (hwin ?_ ?_).2.subset subset_union_left
  · rw [← h.basis_inter_right_eq hI hJ hIJ, diff_self_inter]
    exact diff_subset_diff_left hJ.subset
  rw [← h.symm.basis_inter_right_eq hI hJ' hIJ', diff_self_inter]
  exact diff_subset_diff_left hJ'.subset

end ModularCompl

end ModularCompl
