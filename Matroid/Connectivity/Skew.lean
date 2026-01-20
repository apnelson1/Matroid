import Mathlib.Algebra.BigOperators.Ring.Finset
import Matroid.Modular.Basic
import Matroid.Order.Quotient
import Matroid.Constructions.Project
import Matroid.ForMathlib.Set

universe u

variable {α η : Type*} {ι : Sort*} {M : Matroid α} {e f : α} {Xs Ys Is : ι → Set α} {i j : ι}
    {B I J X X' Y Y' F : Set α}

open Set Function

namespace Matroid

/-- A `SkewFamily` in a matroid is a collection of sets having pairwise disjoint bases
whose union is independent. -/
@[mk_iff]
structure IsSkewFamily (M : Matroid α) (Xs : ι → Set α) : Prop where
  isModularFamily : M.IsModularFamily Xs
  disj : ∀ ⦃i j⦄, i ≠ j → Xs i ∩ Xs j ⊆ M.loops

@[aesop unsafe 5% (rule_sets := [Matroid])]
lemma IsSkewFamily.subset_ground_of_mem (h : M.IsSkewFamily Xs) (i : ι) : Xs i ⊆ M.E :=
  h.isModularFamily.subset_ground_of_mem i

lemma IsSkewFamily.isLoop_of_mem_inter (h : M.IsSkewFamily Xs) (hij : i ≠ j)
    (he : e ∈ Xs i ∩ Xs j) : M.IsLoop e :=
  h.2 hij he

lemma IsSkewFamily.subset_loops_of_ne (h : M.IsSkewFamily Xs) (hij : i ≠ j) :
    Xs i ∩ Xs j ⊆ M.loops :=
  h.2 hij

lemma IsSkewFamily.pairwise_subset_loops {Xs : η → Set α} (h : M.IsSkewFamily Xs) :
    Pairwise (fun i j ↦ Xs i ∩ Xs j ⊆ M.loops) :=
  fun _ _ ↦ h.subset_loops_of_ne

lemma IsSkewFamily.comp {ζ : Sort*} (h : M.IsSkewFamily Xs) (t : ζ → ι) (ht : Injective t) :
    M.IsSkewFamily (Xs ∘ t) :=
  ⟨h.isModularFamily.comp t, fun _ _ hne ↦ h.subset_loops_of_ne fun h' ↦ hne <| ht h'⟩

@[simp]
lemma isSkewFamily_iff_of_subsingleton [Subsingleton ι] : M.IsSkewFamily Xs ↔ ∀ i, Xs i ⊆ M.E := by
  rw [isSkewFamily_iff]
  simp only [isModularFamily_iff_of_subsingleton, ne_eq, and_iff_left_iff_imp]
  refine fun _ i j hne ↦ ?_
  simp [Subsingleton.elim i j] at hne

lemma IsSkewFamily.disjoint_inter_indep (h : M.IsSkewFamily Xs) (hI : M.Indep I) (hij : i ≠ j) :
    Disjoint (Xs i ∩ I) (Xs j) := by
  rw [disjoint_iff_forall_ne]
  rintro e ⟨hei, heI⟩ _ hej rfl
  exact (hI.isNonloop_of_mem heI).not_isLoop <| h.isLoop_of_mem_inter hij ⟨hei,hej⟩

lemma IsSkewFamily.diff_loops_pairwise_disjoint {Xs : η → Set α} (h : M.IsSkewFamily Xs) :
    Pairwise (Disjoint on (fun i ↦ (Xs i \ M.loops))) :=
  fun _ _ hij ↦ disjoint_left.2 fun _ hai haj ↦ hai.2 <| (h.disj hij) ⟨hai.1, haj.1⟩

lemma IsSkewFamily.disjoint_of_indep_subset (h : M.IsSkewFamily Xs) (hI : M.Indep I)
    (hIX : I ⊆ Xs i) (hij : i ≠ j) : Disjoint I (Xs j) := by
  have hdj := h.disjoint_inter_indep hI hij
  rwa [inter_eq_self_of_subset_right hIX] at hdj

lemma IsSkewFamily.pairwise_disjoint_inter_of_indep {Xs : η → Set α} (h : M.IsSkewFamily Xs)
    (hI : M.Indep I) : Pairwise (Disjoint on (fun i ↦ Xs i ∩ I)) :=
  fun _ _ hij ↦ (h.disjoint_inter_indep hI hij).mono_right inter_subset_left

lemma IsSkewFamily.pairwise_disjoint_of_indep_subsets {Is Xs : η → Set α} (h : M.IsSkewFamily Xs)
    (hIX : ∀ i, Is i ⊆ Xs i) (hIs : ∀ i, M.Indep (Is i)) : Pairwise (Disjoint on Is) :=
  fun i j hij ↦ disjoint_iff_inter_eq_empty.2 <|
    ((hIs i).inter_right (Is j)).eq_empty_of_subset_loops
    ((inter_subset_inter (hIX i) (hIX j)).trans (h.2 hij).subset)

lemma IsSkewFamily.pairwise_disjoint_of_isBases {Is Xs : η → Set α} (h : M.IsSkewFamily Xs)
    (hIX : ∀ i, M.IsBasis (Is i) (Xs i)) : Pairwise (Disjoint on Is) :=
  h.pairwise_disjoint_of_indep_subsets (fun i ↦ (hIX i).subset) (fun i ↦ (hIX i).indep)

lemma IsSkewFamily.cls_isSkewFamily (h : M.IsSkewFamily Xs) :
    M.IsSkewFamily (fun i ↦ M.closure (Xs i)) := by
  refine ⟨h.isModularFamily.cls_isModularFamily, fun i j hij ↦ ?_⟩
  have := M.closure_subset_closure_of_subset_closure <| h.subset_loops_of_ne hij
  rwa [← (h.isModularFamily.isModularPair i j).inter_closure_eq]

lemma Indep.isSkewFamily_of_disjoint_isBases {Is Xs : η → Set α} (hI : M.Indep (⋃ i, Is i))
    (hdj : Pairwise (Disjoint on Is)) (hIs : ∀ i, M.IsBasis (Is i) (Xs i)) : M.IsSkewFamily Xs := by
  refine ⟨hI.isModularFamily fun i ↦ ?_, fun i j hij ↦ ?_⟩
  · rw [hI.inter_isBasis_closure_iff_subset_closure_inter]
    exact (hIs i).subset_closure.trans
      (M.closure_subset_closure (subset_inter (hIs i).subset (subset_iUnion _ i)))
  refine (inter_subset_inter (M.subset_closure _ (hIs i).subset_ground)
    (M.subset_closure _ (hIs j).subset_ground)).trans ?_
  rw [← (hIs i).closure_eq_closure, ← (hIs j).closure_eq_closure, loops,
    ← (hI.subset _).closure_inter_eq_inter_closure, Disjoint.inter_eq <| hdj hij]
  exact union_subset (subset_iUnion _ _) (subset_iUnion _ _)

lemma isSkewFamily_iff_exist_isBases {Xs : η → Set α} : M.IsSkewFamily Xs ↔
    ∃ (Is : η → Set α), Pairwise (Disjoint on Is) ∧ M.IsBasis (⋃ i, Is i) (⋃ i, Xs i) ∧
      ∀ i, M.IsBasis (Is i) (Xs i) := by
  refine ⟨fun h ↦ ?_, fun ⟨Is, hdj, hIs, hb⟩ ↦ hIs.indep.isSkewFamily_of_disjoint_isBases hdj hb⟩
  obtain ⟨B, hB⟩ := h.isModularFamily
  refine ⟨_, ?_, ?_, hB.isBasis_inter⟩
  · exact h.pairwise_disjoint_of_indep_subsets (fun i ↦ inter_subset_left)
      (fun i ↦ hB.indep.inter_left _)
  rw [← iUnion_inter]
  exact hB.isBasis_iUnion

lemma IsSkewFamily.restrict {Xs : η → Set α} {R : Set α} (hXs : M.IsSkewFamily Xs)
    (h : ∀ i, Xs i ⊆ R) : (M ↾ R).IsSkewFamily Xs := by
  simp_rw [isSkewFamily_iff, ← closure_empty, restrict_closure_eq', empty_inter]
  exact ⟨hXs.isModularFamily.restrict h, fun i j hij ↦
    subset_trans (subset_inter (hXs.2 hij) (inter_subset_left.trans (h i))) subset_union_left⟩

lemma isSkewFamily_restrict_iff' {Xs : η → Set α} {R : Set α} :
    (M ↾ R).IsSkewFamily Xs ↔ M.IsSkewFamily (fun i ↦ Xs i ∩ M.E) ∧ ∀ i, Xs i ⊆ R := by
  refine ⟨fun ⟨hmod, hdj⟩ ↦ ⟨⟨hmod.ofRestrict', fun i j hne ↦ ?_⟩, hmod.subset_ground_of_mem⟩,
    fun ⟨⟨⟨B, hB, hBmod⟩, hss⟩, hXR⟩ ↦ ⟨⟨B ∩ R, ⟨?_, fun i ↦ ?_⟩⟩, fun i j hij ↦ ?_⟩⟩
  · grw [← inter_inter_distrib_right, hdj hne, restrict_loops_eq', union_inter_distrib_right,
      diff_inter_self, union_empty, inter_subset_left, inter_subset_left]
  · simp [hB.inter_right]
  · simp only [isBasis_restrict_iff', hXR, and_true]
    rw [inter_comm B, ← inter_assoc, inter_eq_self_of_subset_left (hXR i),
      ← inter_eq_self_of_subset_right hB.subset_ground, ← inter_assoc]
    exact hBmod i
  grw [restrict_loops_eq', diff_eq, inter_comm R, ← union_inter_distrib_right, subset_inter_iff,
    and_iff_left (inter_subset_left.trans (hXR i)), union_comm, ← diff_subset_iff, diff_compl,
    inter_inter_distrib_right]
  exact hss hij

lemma isSkewFamily_restrict_iff {Xs : η → Set α} {R : Set α} (hXs : ∀ i, Xs i ⊆ M.E) :
    (M ↾ R).IsSkewFamily Xs ↔ M.IsSkewFamily Xs ∧ ∀ i, Xs i ⊆ R := by
  simp_rw [isSkewFamily_restrict_iff', inter_eq_self_of_subset_left (hXs _)]

lemma isSkewFamily_dual_iff_isModularFamily_compl {X : η → Set α} (hX : ∀ i, X i ⊆ M.E)
    (hdj : Pairwise (Disjoint on X)) :
    M✶.IsSkewFamily X ↔ M.IsModularFamily (fun i ↦ M.E \ (X i)) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨B, hB, hBX⟩ := h.isModularFamily.exists_isMutualBasis_isBase
    exact (hBX.isMutualBasis_compl_ofDual hB).isModularFamily
  obtain ⟨B, hB, hBX⟩ := h.exists_isMutualBasis_isBase
  refine ⟨(hBX.isMutualBasis_of_compl hX hB).isModularFamily,
    fun i j hne ↦ by simp [(hdj hne).inter_eq]⟩

lemma Indep.isSkewFamily_iff_pairwise_disjoint {Is : η → Set α} (hI : M.Indep (⋃ i, Is i)) :
    M.IsSkewFamily Is ↔ Pairwise (Disjoint on Is) := by
  refine ⟨fun h ↦ h.pairwise_disjoint_of_indep_subsets
    (fun _ ↦ Subset.rfl) (fun i ↦ hI.subset (subset_iUnion _ _)),
    fun h ↦ hI.isSkewFamily_of_disjoint_isBases ?_
      (fun i ↦ (hI.subset (subset_iUnion _ _)).isBasis_self)⟩
  exact h

lemma Indep.isSkewFamily_iff_pairwise_disjoint_union_indep {Is : η → Set α}
    (hI : ∀ i, M.Indep (Is i)) :
    M.IsSkewFamily Is ↔ Pairwise (Disjoint on Is) ∧ M.Indep (⋃ i, Is i) := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ h.2.isSkewFamily_iff_pairwise_disjoint.2 h.1⟩
  · exact h.pairwise_disjoint_of_indep_subsets (fun _ ↦ rfl.subset) hI
  obtain ⟨B, hB, hBI⟩ := h.isModularFamily.exists_isMutualBasis_isBase
  refine hB.indep.subset <| iUnion_subset fun i ↦ ?_
  grw [← (hBI.isBasis_inter i).eq_of_subset_indep (hI i) inter_subset_left rfl.subset,
    inter_subset_right]

  /--
  For a skew family `Xs`, the union of some independent subsets of the `Xs` is independent.
  Quite a nasty proof. Probably the right proof involves relating modularity to the
  lattice of Flats. -/
lemma IsSkewFamily.iUnion_indep_subset_indep {ι : Sort u} {Is Xs : ι → Set α}
    (h : M.IsSkewFamily Xs) (hIX : ∀ i, Is i ⊆ Xs i) (hIs : ∀ i, M.Indep (Is i)) :
    M.Indep (⋃ i, Is i) := by
  -- reduce to the case where `ι` is a type.
  suffices aux : ∀ (η : Type u) (Is Xs : η → Set α), M.IsSkewFamily Xs → (∀ i, Is i ⊆ Xs i) →
      (∀ i, M.Indep (Is i)) → M.Indep (⋃ i, Is i) by
    convert aux (PLift ι) (fun i ↦ Is i.down) (fun i ↦ Xs i.down) ?_
      (by simpa [PLift.forall]) (by simpa [PLift.forall])
    · exact (iUnion_plift_down Is).symm
    convert h
    simp [isSkewFamily_iff, IsModularFamily, isMutualBasis_iff, PLift.forall]
  clear! Is Xs
  intro η Is Xs h hIX hIs
  -- extend each `I i` to a basis `J i` of `X i`, and let `J` be a basis for the union of the `J i`.
  choose Js hJs using fun i ↦ (hIs i).subset_isBasis_of_subset (hIX i)
  refine Indep.subset ?_ <| iUnion_mono (fun i ↦ (hJs i).2)
  obtain ⟨J, hJ⟩ := M.exists_isBasis _ (iUnion_subset (fun i ↦ (hJs i).1.indep.subset_ground))
  -- We may assume that `J` is a strict subset of the union, so there is some `e ∈ (J i₀) \ J`
  -- for some `i₀`.
  by_contra hcon
  have ex_i : ∃ i e, e ∈ (Js i) \ J := by
    by_contra! h'
    rw [← hJ.subset.antisymm (iUnion_subset fun i e he ↦ by_contra fun heJ ↦ h' i e ⟨he, heJ⟩)]
      at hcon
    exact hcon hJ.indep
  obtain ⟨i₀, e, hei₀, heJ⟩ := ex_i
  -- Let `K i` be a modular collection of bases.
  obtain ⟨Ks, hdj, hKs, huKs⟩ := isSkewFamily_iff_exist_isBases.1 h

  have hssE : Js i₀ ∪ (⋃ i ∈ ({i₀}ᶜ : Set η), Ks i) ⊆ M.E := by
    refine union_subset (hJs i₀).1.indep.subset_ground ?_
    simp only [mem_compl_iff, mem_singleton_iff, iUnion_subset_iff]
    exact fun i _ ↦ (huKs i).indep.subset_ground

  obtain ⟨K', hK', hss⟩ := (hJs i₀).1.indep.subset_isBasis_of_subset subset_union_left hssE

  have hK'' : ∀ i, i ≠ i₀ → Ks i ⊆ K' := by
    intro i hne f hf
    by_contra hfK'
    apply hKs.indep.notMem_closure_diff_of_mem (mem_iUnion.2 ⟨i,hf⟩)
    have hclosure : f ∈ M.closure K' := by
      exact hK'.subset_closure (Or.inr <| mem_biUnion hne hf)

    refine mem_of_mem_of_subset
      (M.closure_subset_closure (subset_diff_singleton hK'.subset hfK') hclosure)
      (M.closure_subset_closure_of_subset_closure ?_)
    simp only [mem_compl_iff, mem_singleton_iff, diff_singleton_subset_iff, union_subset_iff,
      iUnion_subset_iff]
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
    apply IsLoop.not_isNonloop <| h.isLoop_of_mem_inter hi ⟨(hJs i₀).1.subset hei₀,
      (huKs i).subset heK⟩
    exact (hK'.indep.subset hss).isNonloop_of_mem hei₀

  exact hK'.indep.notMem_closure_diff_of_mem (hss hei₀) he'

lemma IsSkewFamily.mono {ι : Sort u} {Xs Ys : ι → Set α} (h : M.IsSkewFamily Xs)
    (hYX : ∀ i, Ys i ⊆ Xs i) : M.IsSkewFamily Ys := by
  -- reduce to the case where `ι` is a type.
  suffices aux : ∀ (η : Type u) (Xs Ys : η → Set α), M.IsSkewFamily Xs → (∀ i, Ys i ⊆ Xs i) →
      M.IsSkewFamily Ys by
    convert aux (PLift ι) (fun i ↦ Xs i.down) (fun i ↦ Ys i.down) ?_ (by simpa [PLift.forall])
    · simp [isSkewFamily_iff, IsModularFamily, isMutualBasis_iff, PLift.forall]
    simpa [isSkewFamily_iff, IsModularFamily, isMutualBasis_iff, PLift.forall] using h
  clear! Xs Ys
  intro η Xs Ys h hYX
  choose Is hIs using fun i ↦ M.exists_isBasis (Ys i) ((hYX i).trans (h.subset_ground_of_mem i))
  refine Indep.isSkewFamily_of_disjoint_isBases ?_ ?_ hIs
  · exact h.iUnion_indep_subset_indep (fun i ↦ (hIs i).subset.trans (hYX i)) (fun i ↦ (hIs i).indep)
  exact h.pairwise_disjoint_of_indep_subsets
    (fun i ↦ (hIs i).subset.trans (hYX i)) (fun i ↦ (hIs i).indep)

lemma isSkewFamily_delete_iff {Xs : η → Set α} {D : Set α} :
    (M ＼ D).IsSkewFamily Xs ↔ M.IsSkewFamily (fun i ↦ Xs i \ D) ∧ ∀ i, Disjoint (Xs i) D := by
  simp only [← restrict_compl, isSkewFamily_restrict_iff', subset_diff,
    forall_and, ← and_assoc, and_congr_left_iff]
  intro hdj
  simp_rw [(hdj _).sdiff_eq_left]
  refine ⟨fun ⟨h, h'⟩ ↦ ?_, fun h ↦ ⟨h.mono fun _ ↦ inter_subset_left, h.subset_ground_of_mem⟩⟩
  simp_rw [inter_eq_self_of_subset_left (h' _)] at h
  exact h

lemma isSkewFamily_delete_iff_of_disjoint {Xs : η → Set α} {D : Set α}
    (hdj : ∀ i, Disjoint (Xs i) D) :
    (M ＼  D).IsSkewFamily Xs ↔ M.IsSkewFamily Xs := by
  simp_rw [isSkewFamily_delete_iff, and_iff_left hdj, (hdj _).sdiff_eq_left]

lemma isSkewFamily_iff_cls_isSkewFamily (hX : ∀ i, Xs i ⊆ M.E) :
    M.IsSkewFamily Xs ↔ M.IsSkewFamily (fun i ↦ M.closure (Xs i)) :=
  ⟨fun h ↦ h.cls_isSkewFamily, fun h ↦ h.mono fun i ↦ M.subset_closure _⟩

lemma isSkewFamily_iff_diff_loops_isSkewFamily :
    M.IsSkewFamily Xs ↔ M.IsSkewFamily (fun i ↦ (Xs i) \ M.loops) := by
  refine ⟨fun h ↦ h.mono fun _ ↦ diff_subset, fun h ↦ h.cls_isSkewFamily.mono fun i ↦ ?_⟩
  nth_rw 1 [← diff_union_inter (Xs i) M.loops, union_subset_iff]
  refine ⟨M.subset_closure _ (h.subset_ground_of_mem i), inter_subset_right.trans ?_⟩
  exact M.closure_subset_closure (empty_subset _)

lemma IsSkewFamily.iUnion_isBasis_iUnion (h : M.IsSkewFamily Xs)
    (hIs : ∀ i, M.IsBasis (Is i) (Xs i)) : M.IsBasis (⋃ i, Is i) (⋃ i, Xs i) := by
  have hi := h.iUnion_indep_subset_indep (fun i ↦ (hIs i).subset) (fun i ↦ (hIs i).indep)
  exact hi.isBasis_of_subset_of_subset_closure (iUnion_mono (fun i ↦ (hIs i).subset)) <|
    iUnion_subset
      (fun i ↦ (hIs i).subset_closure.trans (M.closure_subset_closure (subset_iUnion _ _)))

lemma IsSkewFamily.isModularFamily_union_of_subset {Xs : η → Set α} {Z : Set α}
    (hX : M.IsSkewFamily Xs) (hZ : Z ⊆ ⋃ i, Xs i) : M.IsModularFamily (fun i ↦ Xs i ∪ Z) := by
  choose I J hI using fun i ↦ M.exists_isBasis_subset_isBasis
    (show Xs i ∩ Z ⊆ Xs i from inter_subset_left)
  have hJu := hX.iUnion_isBasis_iUnion (fun i ↦ (hI i).2.1)
  refine ⟨⋃ i, J i, hJu.indep, fun i ↦ ?_⟩
  refine (hJu.indep.inter_left _).isBasis_of_subset_of_subset_closure inter_subset_left <|
    union_subset ?_ ?_
  · nth_grw 1 [(hI i).2.1.subset_closure]
    exact M.closure_subset_closure <| subset_inter ((hI i).2.1.subset.trans subset_union_left) <|
      subset_iUnion ..
  rw [← inter_eq_self_of_subset_left hZ, inter_comm, iUnion_inter, iUnion_subset_iff]
  intro j
  nth_grw 1 [(hI j).1.subset_closure, ← subset_union_right,
    ← subset_iUnion_of_subset j (hI j).1.subset, ← subset_iUnion_of_subset j (hI j).2.2, inter_self]

lemma IsSkewFamily.sum_eRk_eq_eRk_iUnion [Fintype η] {Xs : η → Set α} (h : M.IsSkewFamily Xs) :
    ∑ i, M.eRk (Xs i) = M.eRk (⋃ i, Xs i) := by
  choose Is hIs using fun i ↦ M.exists_isBasis (Xs i) (h.subset_ground_of_mem i)
  have hdj := (h.pairwise_disjoint_of_isBases hIs)
  rw [(h.iUnion_isBasis_iUnion hIs).eRk_eq_encard, encard_iUnion _ hdj]
  simp_rw [(hIs _).eRk_eq_encard]

lemma IsRkFinite.isSkewFamily_iff_sum_eRk_eq_eRk_iUnion [Fintype η] {Xs : η → Set α}
    (hXs : ∀ i, M.IsRkFinite (Xs i)) (hXE : ∀ i, Xs i ⊆ M.E) :
    M.IsSkewFamily Xs ↔ ∑ i, M.eRk (Xs i) = M.eRk (⋃ i, Xs i) := by
  refine ⟨IsSkewFamily.sum_eRk_eq_eRk_iUnion, fun hsum ↦ ?_⟩
  choose Is hIs using fun i ↦ M.exists_isBasis (Xs i) (hXE i)
  rw [← eRk_closure_eq , ← M.closure_iUnion_closure_eq_closure_iUnion] at hsum
  simp_rw [← (fun i ↦ M.eRk_closure_eq (Xs i)), ← (fun i ↦ (hIs i).closure_eq_closure),
    M.closure_iUnion_closure_eq_closure_iUnion, eRk_closure_eq,
      (fun i ↦ (hIs i).indep.eRk_eq_encard)] at hsum

  apply Indep.isSkewFamily_of_disjoint_isBases ?_ ?_ hIs
  · exact IsRkFinite.indep_of_encard_le_eRk
      ((IsRkFinite.iUnion hXs).subset (iUnion_mono (fun i ↦ (hIs i).subset)))
      ((encard_iUnion_le _).trans hsum.le)
  exact pairwiseDisjoint_of_sum_encard_le_encard_iUnion
    (fun i ↦ (hXs i).finite_of_isBasis (hIs i)) (hsum.le.trans <| M.eRk_le_encard _)

lemma isSkewFamily_iff_sum_eRk_eq_eRk_iUnion [Fintype η] [RankFinite M] {Xs : η → Set α}
    (hXs : ∀ i, Xs i ⊆ M.E) : M.IsSkewFamily Xs ↔ ∑ i, M.rk (Xs i) = M.rk (⋃ i, Xs i) := by
  simp_rw [IsRkFinite.isSkewFamily_iff_sum_eRk_eq_eRk_iUnion (fun i ↦ M.isRkFinite_set (Xs i)) hXs,
    ← M.cast_rk_eq, ← Nat.cast_sum, Nat.cast_inj]

/-- If a family of sets contains at most one set without loops, then the family is skew. -/
lemma isSkewFamily_of_nearly_all_loops {i₀ : η} {Xs : η → Set α} (hi₀ : Xs i₀ ⊆ M.E)
    (hX : ∀ i ≠ i₀, Xs i ⊆ M.loops) : M.IsSkewFamily Xs := by
  obtain ⟨I, hI⟩ := M.exists_isBasis (Xs i₀)
  rw [isSkewFamily_iff, IsModularFamily]
  refine ⟨⟨I, hI.indep, fun i ↦ ?_⟩, ?_⟩
  · obtain rfl | hne := eq_or_ne i i₀
    · rwa [inter_eq_self_of_subset_right hI.subset]
    rw [(hI.indep.inter_left _).eq_empty_of_subset_loops (inter_subset_left.trans (hX _ hne))]
    simpa using hX _ hne
  intro i j hne
  obtain rfl | hne := eq_or_ne i i₀
  · grw [inter_subset_right, hX j hne.symm]
  grw [inter_subset_left, hX _ hne]

@[simp]
lemma isSkewFamily_loopyOn_iff {E : Set α} {Xs : η → Set α} :
    (loopyOn E).IsSkewFamily Xs ↔ ∀ i, Xs i ⊆ E := by
  obtain hη | ⟨⟨i⟩⟩ := isEmpty_or_nonempty η
  · simp
  refine ⟨fun h i ↦ h.subset_ground_of_mem i, fun h ↦ ?_⟩
  apply isSkewFamily_of_nearly_all_loops (h i) <| by simp +contextual [loops, h]

lemma isSkewFamily_iff_forall_isCircuit {Xs : η → Set α} (hXs : ∀ i, Xs i ⊆ M.E)
    (hdj : Pairwise (Disjoint on Xs)) :
    M.IsSkewFamily Xs ↔ ∀ C, M.IsCircuit C → C ⊆ ⋃ i, Xs i → ∃ i, C ⊆ Xs i := by
  refine ⟨fun h C hC hCU ↦ ?_, fun h ↦ ?_⟩
  · have h : ∃ i, ¬ M.Indep (C ∩ Xs i) := by
      by_contra! hcon
      refine hC.dep.not_indep ?_
      refine (h.iUnion_indep_subset_indep (fun i ↦ inter_subset_right) hcon).subset ?_
      simp [← inter_iUnion, hCU]
    obtain ⟨i, hi⟩ := h
    rw [← hC.eq_of_not_indep_subset hi inter_subset_left]
    exact ⟨i, inter_subset_right⟩
  choose Is hIs using fun i ↦ M.exists_isBasis _ (hXs i)
  have hss := iUnion_mono (fun i ↦ (hIs i).subset)
  have hIe : ⋃ i, Is i ⊆ M.E := by simp [fun i ↦ (hIs i).subset.trans (hXs i)]
  have h_inter : ∀ i, Xs i ∩ ⋃ j, Is j = Is i := by
    intro i
    simp only [inter_iUnion, subset_antisymm_iff, iUnion_subset_iff]
    refine ⟨fun j ↦ ?_, subset_iUnion_of_subset i (subset_inter (hIs i).subset Subset.rfl)⟩
    obtain (rfl | hne) := eq_or_ne i j
    · apply inter_subset_right
    simp [((hdj hne).mono_right (hIs j).subset).inter_eq]
  refine Indep.isSkewFamily_of_disjoint_isBases ?_ ?_ hIs
  · rw [indep_iff_forall_subset_not_isCircuit hIe]
    intro C hCss hC
    obtain ⟨i, hI⟩ := h C hC (hCss.trans hss)
    have hC' := subset_inter hI hCss
    rw [h_inter] at hC'
    exact hC.dep.not_indep ((hIs i).indep.subset hC')
  exact fun i j hne ↦ (hdj hne).mono ((hIs i).subset) ((hIs j).subset)

lemma IsSkewFamily.exists_subset_of_isCircuit {Xs : η → Set α} (h : M.IsSkewFamily Xs) {C : Set α}
    (hC : M.IsCircuit C) (hCss : C ⊆ ⋃ i, Xs i) : ∃ i, C ⊆ Xs i := by
  set Ys := fun i ↦ (Xs i) ∩ C
  have hYs := h.mono (Ys := Ys) (by simp [Ys])
  by_cases hdj : Pairwise (Disjoint on Ys)
  · rw [isSkewFamily_iff_forall_isCircuit (fun i ↦ inter_subset_right.trans hC.subset_ground) hdj]
      at hYs
    obtain ⟨i, h⟩ := hYs C hC (by rwa [← iUnion_inter, subset_inter_iff, and_iff_left rfl.subset])
    exact ⟨i, h.trans inter_subset_left⟩
  simp only [Pairwise, ne_eq, disjoint_iff_inter_eq_empty, not_forall, exists_prop,
    eq_empty_iff_forall_notMem, not_not] at hdj
  obtain ⟨i, j, hne, e, he⟩ := hdj
  have hel := hYs.isLoop_of_mem_inter hne he
  obtain rfl : C = {e} := hel.eq_of_isCircuit_mem hC
    (mem_of_mem_of_subset he (inter_subset_left.trans inter_subset_right))
  exact ⟨i, singleton_subset_iff.2 <| mem_of_mem_of_subset he
    (inter_subset_left.trans inter_subset_left)⟩

lemma IsSkewFamily.subset_of_isCircuit_of_mem {Xs : η → Set α} (h : M.IsSkewFamily Xs) {C : Set α}
    {i : η} (hC : M.IsCircuit C) (hCss : C ⊆ ⋃ i, Xs i) (he : e ∈ C) (hei : e ∈ Xs i) :
    C ⊆ Xs i := by
  obtain ⟨j, hj⟩ := h.exists_subset_of_isCircuit hC hCss
  obtain rfl | hne := eq_or_ne i j
  · assumption
  obtain rfl := (h.isLoop_of_mem_inter hne ⟨hei, hj he⟩).eq_of_isCircuit_mem hC he
  simpa

lemma isSkewFamily_iff_restrict_iUnion_eq_disjointSigma {ι : Type*} {Xs : ι → Set α}
    (hdj : Pairwise (Disjoint on Xs)) (hss : ∀ i, Xs i ⊆ M.E) :
    M.IsSkewFamily Xs ↔ M ↾ ⋃ i, Xs i = Matroid.disjointSigma (fun i ↦ (M ↾ Xs i)) (by simpa) := by
  have hrw {C} : (C ⊆ ⋃ i, Xs i ↔ ∃ i, C ⊆ Xs i) ↔ (C ⊆ ⋃ i, Xs i → ∃ i, C ⊆ Xs i) :=
    ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun ⟨i, hi⟩ ↦ hi.trans <| subset_iUnion ..⟩⟩
  simp [isSkewFamily_iff_forall_isCircuit hss hdj, ext_iff_isCircuit,
    restrict_isCircuit_iff (iUnion_subset hss), restrict_isCircuit_iff (hss _), hrw]

lemma IsSkewFamily.restrict_iUnion_eq_disjointSigma {ι : Type*} {Xs : ι → Set α}
    (h : M.IsSkewFamily Xs) (hdj : Pairwise (Disjoint on Xs)) :
    M ↾ ⋃ i, Xs i = Matroid.disjointSigma (fun (i : ι) ↦ (M ↾ Xs i)) (by simpa) := by
  rwa [← isSkewFamily_iff_restrict_iUnion_eq_disjointSigma hdj h.subset_ground_of_mem]

lemma contract_isSkewFamily_iff_project_isSkewFamily {C : Set α} {Xs : η → Set α}
    (hXC : ∀ i, Disjoint (Xs i) C) : (M ／ C).IsSkewFamily Xs ↔ (M.project C).IsSkewFamily Xs := by
  rwa [← project_delete_self, isSkewFamily_delete_iff_of_disjoint]

lemma project_isSkewFamily_iff {C : Set α} {Xs : ι → Set α} (hC : C ⊆ M.E := by aesop_mat) :
    (M.project C).IsSkewFamily Xs ↔ M.IsModularFamily (fun i ↦ Xs i ∪ C) ∧
    ∀ ⦃i j⦄, i ≠ j → Xs i ∩ Xs j ⊆ M.closure C := by
  obtain ⟨I, hI⟩ := M.exists_isBasis C
  refine ⟨fun h ↦ ⟨?_, fun _ _ hne ↦ by simpa using h.subset_loops_of_ne hne⟩,
    fun ⟨h, h'⟩ ↦ ⟨?_, fun _ _ hne ↦ by simpa using h' hne⟩⟩
  · obtain ⟨B, hB, hBX⟩ := h.isModularFamily.exists_isMutualBasis_isBase
    rw [hI.project_eq_project] at hBX
    obtain ⟨hdj : Disjoint B I, hi : M.Indep (B ∪ I)⟩ := (hI.indep.project_indep_iff.1 hBX.indep)
    refine ⟨B ∪ I, hi, fun i ↦ ?_⟩
    have hb := hBX.isBasis_inter i
    replace hB := project_indep_iff.1 hB.indep
    have hdj' : Disjoint B C := (subset_diff.1 hB.subset_ground).2
    rw [show (Xs i ∪ C) ∩ (B ∪ I) = I ∪ (Xs i ∩ B) by grind [hI.subset]]
    rw [hI.indep.project_isBasis_iff] at hb
    refine hb.1.indep.isBasis_of_subset_of_subset_closure (by grind [hI.subset]) ?_
    have hXE : Xs i ⊆ M.E := h.subset_ground_of_mem i
    grw [hb.1.closure_eq_closure, closure_union_congr_left hI.closure_eq_closure, union_comm,
      ← M.subset_closure _]
  obtain ⟨B, hB, hIB⟩ := h.exists_isMutualBasis_superset_of_indep_of_subset_inter hI.indep
    (by grw [← iInter_union, hI.subset, ← subset_union_right])
  refine ⟨B \ I, ?_, fun i ↦ ?_⟩
  · rw [hI.project_eq_project, hI.indep.project_indep_iff]
    exact ⟨disjoint_sdiff_left, hB.indep.subset (by grind)⟩
  rw [hI.project_eq_project, hI.indep.project_isBasis_iff, and_iff_left (by grind)]
  obtain rfl : B ∩ C = I := (hI.eq_of_subset_indep (hB.indep.inter_right _)
    (subset_inter hIB hI.subset) inter_subset_right).symm
  convert (hB.isBasis_inter i).isBasis_closure_right.isBasis_subset ?_ ?_ using 1
  · grind
  · grind
  grw [inter_subset_right, union_comm C, ← M.subset_closure _ (hB.subset_ground i)]

lemma contract_isSkewFamily_iff {C : Set α} {Xs : η → Set α} (hXC : ∀ i, Disjoint (Xs i) C)
    (hC : C ⊆ M.E := by aesop_mat) :
    (M ／ C).IsSkewFamily Xs ↔ M.IsModularFamily (fun i ↦ Xs i ∪ C) ∧
      ∀ ⦃i j⦄, i ≠ j → Xs i ∩ Xs j ⊆ M.closure C := by
  rw [contract_isSkewFamily_iff_project_isSkewFamily hXC, project_isSkewFamily_iff]

/-- Two sets are skew if they have disjoint bases with independent union. -/
def Skew (M : Matroid α) (X Y : Set α) := M.IsSkewFamily (fun i ↦ bif i then X else Y)

@[aesop unsafe 5% (rule_sets := [Matroid])]
lemma Skew.subset_ground_left (h : M.Skew X Y) : X ⊆ M.E :=
  h.subset_ground_of_mem true

@[aesop unsafe 5% (rule_sets := [Matroid])]
lemma Skew.subset_ground_right (h : M.Skew X Y) : Y ⊆ M.E :=
  h.subset_ground_of_mem false

lemma Skew.isModularPair (h : M.Skew X Y) : M.IsModularPair X Y :=
  h.isModularFamily

lemma skew_iff_isModularPair_inter_subset_loops :
    M.Skew X Y ↔ M.IsModularPair X Y ∧ X ∩ Y ⊆ M.loops := by
  rw [Skew, isSkewFamily_iff, IsModularPair, and_congr_right_iff]
  simp [inter_comm X Y]

lemma IsModularPair.skew_of_inter_subset_loops (h : M.IsModularPair X Y)
    (hss : X ∩ Y ⊆ M.loops) : M.Skew X Y := by
  rwa [skew_iff_isModularPair_inter_subset_loops, and_iff_right h]

lemma IsModularPair.skew_of_disjoint (h : M.IsModularPair X Y) (hdj : Disjoint X Y) :
    M.Skew X Y :=
  h.skew_of_inter_subset_loops (by simp [hdj.inter_eq])

lemma Skew.inter_subset_loops (h : M.Skew X Y) : X ∩ Y ⊆ M.loops :=
  (skew_iff_isModularPair_inter_subset_loops.1 h).2

lemma Skew.disjoint [Loopless M] (h : M.Skew X Y) : Disjoint X Y := by
  rw [disjoint_iff_inter_eq_empty, ← subset_empty_iff]
  simpa using h.inter_subset_loops

lemma Skew.symm (h : M.Skew X Y) : M.Skew Y X := by
  rw [skew_iff_isModularPair_inter_subset_loops] at h ⊢
  rwa [inter_comm, isModularPair_comm]

lemma skew_comm : M.Skew X Y ↔ M.Skew Y X :=
  ⟨Skew.symm, Skew.symm⟩

lemma IsSkewFamily.skew_of_ne (h : M.IsSkewFamily Xs) (hij : i ≠ j) : M.Skew (Xs i) (Xs j) := by
  rw [Skew]
  convert h.comp (t := fun b ↦ bif b then i else j) <| Bool.injective_iff.2 hij.symm
  grind

lemma Skew.disjoint_of_indep_subset_left (h : M.Skew X Y) (hI : M.Indep I) (hIX : I ⊆ X) :
    Disjoint I Y :=
  IsSkewFamily.disjoint_of_indep_subset (i := true) (j := false) h hI hIX (by simp)

lemma Skew.disjoint_of_indep_subset_right (h : M.Skew X Y) (hJ : M.Indep J) (hJY : J ⊆ Y) :
    Disjoint X J :=
  (IsSkewFamily.disjoint_of_indep_subset (j := true) (i := false) h hJ hJY (by simp)).symm

lemma Skew.disjoint_of_isBasis_of_subset (h : M.Skew X Y) (hI : M.IsBasis I X) (hJ : J ⊆ Y) :
    Disjoint I J :=
  (h.disjoint_of_indep_subset_left hI.indep hI.subset).mono_right hJ

lemma Skew.disjoint_of_indep_left (h : M.Skew I X) (hI : M.Indep I) : Disjoint I X :=
  h.disjoint_of_indep_subset_left hI Subset.rfl

lemma Skew.disjoint_of_indep_right (h : M.Skew X I) (hI : M.Indep I) : Disjoint X I :=
  h.disjoint_of_indep_subset_right hI Subset.rfl

lemma Skew.diff_loops_disjoint_left (h : M.Skew X Y) : Disjoint (X \ M.loops) Y := by
  rw [disjoint_iff_inter_eq_empty, ← inter_diff_right_comm, diff_eq_empty]
  exact h.inter_subset_loops

lemma Skew.diff_loops_disjoint_right (h : M.Skew X Y) : Disjoint X (Y \ M.loops) :=
  h.symm.diff_loops_disjoint_left.symm

lemma Skew.diff_loops_disjoint (h : M.Skew X Y) : Disjoint (X \ M.loops) (Y \ M.loops) :=
  h.diff_loops_disjoint_left.mono_right diff_subset

lemma Skew.mono (h : M.Skew X Y) (hX : X' ⊆ X) (hY : Y' ⊆ Y) : M.Skew X' Y' :=
  IsSkewFamily.mono h (Ys := fun i ↦ bif i then X' else Y') (Bool.rec (by simpa) (by simpa))

lemma Skew.mono_left (h : M.Skew X Y) (hX : X' ⊆ X) : M.Skew X' Y :=
  h.mono hX Subset.rfl

lemma Skew.mono_right (h : M.Skew X Y) (hY : Y' ⊆ Y) : M.Skew X Y' :=
  h.mono Subset.rfl hY

@[gcongr]
lemma skew_anti_left {M : Matroid α} {Y : Set α} : Antitone (fun X ↦ M.Skew X Y) :=
  fun A B (hAB : A ⊆ B) h ↦ h.mono_left hAB

@[gcongr]
lemma skew_anti_right {M : Matroid α} {X : Set α} : Antitone (fun Y ↦ M.Skew X Y) :=
  fun A B (hAB : A ⊆ B) h ↦ h.mono_right hAB

lemma skew_iff_exist_isBases {X Y : Set α} :
    M.Skew X Y ↔
    ∃ I J, Disjoint I J ∧ M.IsBasis (I ∪ J) (X ∪ Y) ∧ M.IsBasis I X ∧ M.IsBasis J Y := by
  simp only [Skew, isSkewFamily_iff_exist_isBases, Bool.forall_bool, cond_false, cond_true,
    pairwise_disjoint_on_bool', iUnion_bool]
  exact ⟨fun ⟨Is, h1, h2, h3⟩ ↦ ⟨Is true, Is false, h1, h2, h3.symm⟩,
    fun ⟨I, J, h1, h2, h3X, h3Y⟩ ↦ ⟨fun i ↦ bif i then I else J, h1, h2, by simpa, by simpa⟩⟩

lemma Skew.closure_skew (h : M.Skew X Y) : M.Skew (M.closure X) (M.closure Y) := by
  have h' := IsSkewFamily.cls_isSkewFamily h
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

lemma Skew.inter_closure_eq (h : M.Skew X Y) : M.closure X ∩ M.closure Y = M.loops :=
  h.closure_skew.inter_subset_loops.antisymm
    (subset_inter (M.closure_mono (empty_subset _)) (M.closure_mono (empty_subset _)))

lemma skew_iff_of_isLoopEquiv (hX : M.IsLoopEquiv X X') (hY : M.IsLoopEquiv Y Y') :
    M.Skew X Y ↔ M.Skew X' Y' := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rwa [skew_iff_closure_skew hX.subset_ground hY.subset_ground, ← hX.closure_eq_closure,
      ← hY.closure_eq_closure, ← skew_iff_closure_skew]
  rwa [skew_iff_closure_skew hX.symm.subset_ground hY.symm.subset_ground, hX.closure_eq_closure,
    hY.closure_eq_closure, ← skew_iff_closure_skew]

lemma skew_iff_diff_loops_skew : M.Skew X Y ↔ M.Skew (X \ M.loops) (Y \ M.loops) :=
  skew_iff_of_isLoopEquiv (M.isLoopEquiv_diff_loops X) (M.isLoopEquiv_diff_loops Y)

lemma skew_iff_diff_loops_skew_left : M.Skew X Y ↔ M.Skew (X \ M.loops) Y :=
  skew_iff_of_isLoopEquiv (M.isLoopEquiv_diff_loops X) rfl

lemma skew_iff_skew_diff_left : M.Skew X Y ↔ M.Skew (X \ Y) Y ∧ X ∩ Y ⊆ M.loops := by
  by_cases h : X ∩ Y ⊆ M.loops
  · rw [skew_iff_diff_loops_skew_left, iff_comm, skew_iff_diff_loops_skew_left, and_iff_left h]
    convert Iff.rfl using 2; grind
  exact iff_of_false (fun hs ↦ h hs.inter_subset_loops) (by simp [h])

lemma skew_iff_skew_diff_diff : M.Skew X Y ↔ M.Skew (X \ Y) (Y \ X) ∧ X ∩ Y ⊆ M.loops := by
  by_cases h : X ∩ Y ⊆ M.loops
  · rw [skew_iff_diff_loops_skew, iff_comm, skew_iff_diff_loops_skew, and_iff_left h]
    convert Iff.rfl using 2 <;> grind
  exact iff_of_false (fun hs ↦ h hs.inter_subset_loops) (by simp [h])

lemma skew_iff_isBases_skew (hI : M.IsBasis I X) (hJ : M.IsBasis J Y) : M.Skew I J ↔ M.Skew X Y :=
  ⟨fun h ↦ h.closure_skew.mono hI.subset_closure hJ.subset_closure,
    fun h ↦ h.mono hI.subset hJ.subset⟩

lemma skew_dual_iff (hXY : Disjoint X Y) (hX : X ⊆ M.E := by aesop_mat)
    (hY : Y ⊆ M.E := by aesop_mat) : M✶.Skew X Y ↔ M.IsModularPair (M.E \ X) (M.E \ Y) := by
  rw [Skew, isSkewFamily_dual_iff_isModularFamily_compl (by grind) (by grind [Pairwise]),
    IsModularPair]
  simp [Bool.apply_cond (f := fun X ↦ M.E \ X)]

lemma isModularPair_dual_iff (hXY : X ∪ Y = M.E) :
    M✶.IsModularPair X Y ↔ M.Skew (M.E \ X) (M.E \ Y) := by
  nth_rw 2 [← dual_dual M]
  rw [← dual_ground, skew_dual_iff, dual_ground, ← hXY, diff_diff_cancel_left subset_union_left,
    diff_diff_cancel_left subset_union_right]
  rw [dual_ground, disjoint_iff_inter_eq_empty, diff_inter_diff, hXY, diff_self]

lemma Coindep.skew_dual_iff (hX : M.Coindep X) (hXY : Disjoint X Y)
    (hYE : Y ⊆ M.E := by aesop_mat) : M✶.Skew X Y ↔ X ⊆ M.closure (M.E \ (X ∪ Y)) := by
  rw [Matroid.skew_dual_iff hXY, hX.compl_spanning.isModularPair_iff, diff_inter_diff,
    ← diff_union_of_subset (subset_diff.2 ⟨hX.subset_ground, hXY⟩), union_subset_iff,
    diff_diff, union_comm, and_iff_right (M.subset_closure ..)]

/-- Can we just lose this one by the below? -/
lemma Skew.union_indep_of_indep_subsets (h : M.Skew X Y) (hI : M.Indep I) (hIX : I ⊆ X)
    (hJ : M.Indep J) (hJY : J ⊆ Y) : M.Indep (I ∪ J) := by
  rw [union_eq_iUnion]
  exact IsSkewFamily.iUnion_indep_subset_indep h (Is := fun i ↦ bif i then I else J)
    (Bool.rec (by simpa) (by simpa)) (Bool.rec (by simpa) (by simpa))

lemma Skew.union_indep (h : M.Skew I J) (hI : M.Indep I) (hJ : M.Indep J) : M.Indep (I ∪ J) :=
  h.union_indep_of_indep_subsets hI rfl.subset hJ rfl.subset

lemma Skew.union_isBasis_union (h : M.Skew X Y) (hI : M.IsBasis I X) (hJ : M.IsBasis J Y) :
    M.IsBasis (I ∪ J) (X ∪ Y) := by
  rw [union_eq_iUnion, union_eq_iUnion]
  exact IsSkewFamily.iUnion_isBasis_iUnion h (Bool.rec (by simpa) (by simpa))

lemma Indep.skew_iff_disjoint (h : M.Indep (I ∪ J)) : M.Skew I J ↔ Disjoint I J := by
  rw [← pairwise_disjoint_on_bool, Skew, Indep.isSkewFamily_iff_pairwise_disjoint]
  rwa [union_eq_iUnion] at h

-- lemma Skew.union_isBasis_union_iff (h : M.Skew X Y) (hIX : I ⊆ X) (hJY : J ⊆ Y) :
--     M.IsBasis (I ∪ J) (X ∪ Y) ↔ M.IsBasis I X ∧ M.IsBasis J Y := by
--   _

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
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine ext_indep rfl fun J (hJ : J ⊆ Y) ↦ ?_
    simp_rw [restrict_indep_iff, hI.contract_indep_iff, and_iff_left hJ]
    refine ⟨fun h ↦ h.1.subset subset_union_left,
      fun hJi ↦ ⟨?_, h.disjoint_of_indep_subset_right hJi hJ⟩⟩
    exact h.symm.union_indep_of_indep_subsets hJi hJ hI.indep hI.subset
  obtain ⟨J, hJ⟩ := M.exists_isBasis Y
  have hi : (M ↾ Y).Indep J := restrict_indep_iff.2 ⟨hJ.indep, hJ.subset⟩
  rw [← h, hI.contract_eq_contract_delete, restrict_indep_iff, delete_indep_iff,
    hI.indep.contract_indep_iff, union_comm, disjoint_comm,
    ← hI.indep.skew_iff_disjoint_union_indep hJ.indep] at hi

  exact hi.1.1.closure_skew.mono hI.subset_closure hJ.subset_closure

lemma Indep.skew_iff_contract_indep (hI : M.Indep I) (hX : X ⊆ M.E) :
    M.Skew I X ↔ (M ／ X).Indep I := by
  rw [skew_comm, skew_iff_contract_restrict_eq_restrict, hI.restrict_eq_freeOn,
    ← restrict_eq_freeOn_iff]

lemma skew_insert_iff (he : e ∈ M.E) :
    M.Skew (insert e X) Y ↔ M.Skew X Y ∧ (e ∈ M.closure (X ∪ Y) → e ∈ M.closure X) := by
  wlog hXE : X ⊆ M.E
  · refine iff_of_false (fun hs ↦ hXE ((subset_insert _ _).trans hs.subset_ground_left))
      (fun h ↦ hXE h.1.subset_ground_left)
  wlog hYE : Y ⊆ M.E
  · exact iff_of_false (fun h ↦ hYE h.subset_ground_right) (fun h ↦ hYE h.1.subset_ground_right)
  obtain hl | hnl := M.isLoop_or_isNonloop e
  · rw [skew_iff_diff_loops_skew_left, insert_diff_of_mem _ hl, ← skew_iff_diff_loops_skew_left]
    simp [hl.mem_closure X]

  by_cases heY : e ∈ Y
  · refine iff_of_false (fun hsk ↦ hnl.not_isLoop ?_) ?_
    · exact hsk.inter_subset_loops ⟨.inl rfl, by simpa using heY⟩
    rw [not_and, _root_.not_imp]
    refine fun hsk ↦ ⟨M.mem_closure_of_mem' <| .inr heY  , fun hcl ↦ hnl.not_isLoop ?_⟩
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
  rw [skew_iff_exist_isBases] at hsk ⊢
  obtain ⟨I, J, hdj, hIJ, hI, hJ⟩ := hsk

  refine ⟨insert e I, J, ?_⟩
  rw [← singleton_union, union_assoc, ← singleton_union, union_assoc, disjoint_union_left]
  simp only [disjoint_singleton_left, hdj, and_true, singleton_union, hJ]

  have heIJ : M.Indep (insert e (I ∪ J))
  · rw [hIJ.indep.insert_indep_iff, hIJ.closure_eq_closure]
    exact .inl ⟨he, h⟩
  exact ⟨notMem_subset (hJ.subset.trans (M.subset_closure_of_subset' subset_union_right)) h,
    hIJ.insert_isBasis_insert heIJ,
    hI.insert_isBasis_insert (heIJ.subset (insert_subset_insert subset_union_left))⟩

lemma Skew.contract_restrict_eq (hXY : M.Skew X Y) : (M ／ X) ↾ Y = M ↾ Y :=
  (skew_iff_contract_restrict_eq_restrict hXY.subset_ground_left hXY.subset_ground_right).1 hXY

lemma empty_skew (hX : X ⊆ M.E) : M.Skew ∅ X := by
  rw [skew_iff_contract_restrict_eq_restrict, contract_empty]

lemma skew_empty (hX : X ⊆ M.E) : M.Skew X ∅ :=
  (empty_skew hX).symm

lemma Skew.closure_union_right_inter_left {S : Set α} (h : M.Skew X Y) (hS : S ⊆ X) :
    M.closure (S ∪ Y) ∩ X = M.closure S ∩ X := by
  refine subset_antisymm ?_ <| inter_subset_inter_left _ <| M.closure_mono subset_union_left
  rw [← M.restrict_closure_eq hS, ← h.symm.contract_restrict_eq, restrict_closure_eq',
    contract_closure_eq, inter_eq_self_of_subset_left hS, contract_ground]
  tauto_set

lemma Skew.closure_union_left_inter_right {S : Set α} (h : M.Skew X Y) (hS : S ⊆ Y) :
    M.closure (S ∪ X) ∩ Y = M.closure S ∩ Y :=
  h.symm.closure_union_right_inter_left hS

lemma exists_contract_indep_to_spanning (M : Matroid α) (X : Set α) (hX : X ⊆ M.E) :
    ∃ I, M.Indep I ∧ Disjoint I X ∧ (M ／ I) ↾ X = M ↾ X ∧ (M ／ I).Spanning X := by
  obtain ⟨J, hJ⟩ := M.exists_isBasis X
  obtain ⟨B, hB, rfl⟩ := hJ.exists_isBase
  refine ⟨B \ X, hB.indep.diff _, disjoint_sdiff_left, Skew.contract_restrict_eq ?_, ?_⟩
  · rw [skew_iff_closure_skew_right, ← hJ.closure_eq_closure, ← skew_iff_closure_skew_right]
    simpa using (hB.indep.subset_skew_diff (diff_subset (t := X)))
  rw [contract_spanning_iff (diff_subset.trans hB.subset_ground), union_diff_self,
    and_iff_left disjoint_sdiff_right]
  exact hB.spanning.superset subset_union_right

/-- For any set `X`, we can find a minor in which `X` is spanning and cospanning,
such that both the restrict and corestriction to `X` are unchanged.  -/
lemma exists_isMinor_restrict_corestrict_eq_spanning_cospanning (hX : X ⊆ M.E) :
    ∃ N, N ≤m M ∧ N ↾ X = M ↾ X ∧ N✶ ↾ X = M✶ ↾ X ∧ N.Spanning X ∧ N✶.Spanning X := by
  obtain ⟨I, hI, hIX, hI_eq, hIsp⟩ := M.exists_contract_indep_to_spanning X hX
  obtain ⟨J, hJ, hJX, hJ_eq, hJsp⟩ := (M ／ I)✶.exists_contract_indep_to_spanning X
    hIsp.subset_ground
  refine ⟨M ／ I ＼ J, contract_delete_isMinor _ _ _, ?_, ?_, ?_, ?_⟩
  · rw [← delete_compl _, delete_ground, contract_ground, delete_delete,
      diff_diff_comm (t := J), union_diff_self, union_comm, ← delete_delete,
      ← contract_ground, delete_compl _, hI_eq, ← delete_inter_ground_eq,
      restrict_ground_eq, hJX.inter_eq, delete_empty]
    · exact hIsp.subset_ground
    exact hJsp.subset_ground
  · rw [dual_delete, hJ_eq, dual_contract, delete_eq_restrict,
      restrict_restrict_eq _ (show X ⊆ M✶.E \ I from hIsp.subset_ground)]
  · rwa [Coindep.delete_spanning_iff hJ, and_iff_left hJX.symm]
  rwa [dual_delete]

lemma IsSkewFamily.skew_compl {Xs : η → Set α} (h : M.IsSkewFamily Xs) (A : Set η) :
    M.Skew (⋃ i ∈ A, Xs i) (⋃ i ∈ Aᶜ, Xs i) := by
  rw [skew_iff_isModularPair_inter_subset_loops]
  refine ⟨h.isModularFamily.isModularPair_compl_biUnion A, ?_⟩
  rintro e ⟨⟨_,⟨i,hi,rfl⟩,hi'⟩ ,⟨_,⟨j,hj,rfl⟩,hj'⟩⟩
  simp only [mem_iUnion, exists_prop] at hi' hj'
  exact h.isLoop_of_mem_inter (show i ≠ j from fun hij ↦ hj'.1 <| hij ▸ hi'.1) ⟨hi'.2, hj'.2⟩

lemma IsSkewFamily.skew_compl_singleton {Xs : η → Set α} (h : M.IsSkewFamily Xs) (i : η) :
    M.Skew (Xs i) (⋃ j ∈ ({i} : Set η)ᶜ, Xs j) := by
  convert h.skew_compl {i}; simp

/-- Can this be moved up? -/
lemma IsSkewFamily.isMutualBasis_of_indep {Xs : η → Set α} (h : M.IsSkewFamily Xs) (hB : M.Indep B)
    (hBX : B ⊆ ⋃ i, Xs i) (hX : ∀ i, Xs i ⊆ M.closure B) : M.IsMutualBasis B Xs := by
  refine hB.isMutualBasis_of_forall_subset_closure fun i ↦ ?_
  rw [← inter_eq_right,
    ← (h.skew_compl_singleton i).closure_union_right_inter_left (S := Xs i ∩ B) inter_subset_left,
    inter_eq_right, inter_comm]
  grw [← biUnion_mono rfl.subset (fun j hj ↦ inter_subset_right (s := B))]
  rw [← biUnion_insert (t := fun i ↦ B ∩ Xs i), ← union_singleton, compl_union_self,
    ← inter_iUnion₂, biUnion_univ, inter_eq_self_of_subset_left hBX]
  apply hX


lemma IsSkewFamily.project {Xs : η → Set α} {C : Set α} (h : M.IsSkewFamily Xs)
    (hC : C ⊆ ⋃ i, Xs i) : (M.project C).IsSkewFamily Xs := by
  wlog hCi : M.Indep C generalizing C with aux
  · obtain ⟨I, hI⟩ := M.exists_isBasis' C
    rw [hI.project_eq_project]
    exact aux (hI.subset.trans hC) hI.indep
  have huss : ⋃ i, Xs i ⊆ (M.project C).E := by simp [h.subset_ground_of_mem]
  obtain ⟨I, hI⟩ := (M.project C).exists_isBasis _ huss
  have hIC : M.Indep (I ∪ C) := by
    have hi := hI.indep
    simp only [project_indep_iff, hCi.contract_indep_iff] at hi
    exact hi.2
  have hmut := h.isMutualBasis_of_indep hIC (union_subset hI.subset hC) fun i ↦ ?_
  · refine ⟨⟨_, hI.indep.isMutualBasis_of_forall_subset_closure (fun i ↦ ?_)⟩, ?_⟩
    · rw [project_closure, ← closure_subset_closure_iff_subset_closure, ← hmut.closure_inter_eq]
      refine M.closure_subset_closure <| by tauto_set
    exact fun i j hij ↦ (h.2 hij).trans (by simp [loops])
  exact (subset_iUnion ..).trans (hI.subset_closure.trans (by simp))

lemma dual_isSkewFamily_iff {X : η → Set α} (hdj : Pairwise (Disjoint on X)) (hu : ⋃ i, X i = M.E) :
    M✶.IsSkewFamily X ↔ M.IsSkewFamily X := by
  wlog h : M.IsSkewFamily X generalizing M with aux
  · refine ⟨fun h' ↦ ?_, fun h' ↦ by contradiction⟩
    rwa [← M.dual_dual, aux (by simpa) h']
  simp only [h, iff_true]
  obtain ⟨B, hB, hBmod⟩ := h.isModularFamily.exists_isMutualBasis_isBase
  refine ⟨⟨M.E \ B, hB.compl_isBase_dual.indep, ?_⟩, fun _ _ hne ↦ by simp [(hdj hne).inter_eq]⟩
  intro i
  rw [inter_comm, hB.compl_isBase_dual.inter_isBasis_iff_compl_inter_isBasis_dual,
    dual_ground, diff_diff_cancel_left hB.subset_ground, dual_dual, inter_comm]
  have hrw : ⋃ j ∈ ({i}ᶜ : Set η), X j = M.E \ X i := by
    ext e
    simp only [mem_compl_iff, mem_singleton_iff, mem_iUnion, exists_prop, mem_diff, ← hu]
    exact ⟨fun ⟨j, hji, hej⟩ ↦ ⟨⟨_, hej⟩, (hdj hji).notMem_of_mem_left hej⟩,
      fun ⟨⟨j, hej⟩, hei⟩ ↦ ⟨j, by rintro rfl; contradiction, hej⟩⟩
  have := hBmod.isBasis_biUnion ({i}ᶜ : Set η)
  rwa [hrw] at this

lemma skew_iff_forall_isCircuit (hdj : Disjoint X Y) (hX : X ⊆ M.E := by aesop_mat)
    (hY : Y ⊆ M.E := by aesop_mat) :
    M.Skew X Y ↔ ∀ C, M.IsCircuit C → C ⊆ X ∪ Y → C ⊆ X ∨ C ⊆ Y := by
  rw [Skew, isSkewFamily_iff_forall_isCircuit]
  · simp [or_comm]
  · simp [hX, hY]
  rwa [pairwise_disjoint_on_bool]

lemma Skew.subset_or_subset_of_isCircuit (h : M.Skew X Y) {C : Set α} (hC : M.IsCircuit C)
    (hCss : C ⊆ X ∪ Y) : C ⊆ X ∨ C ⊆ Y := by
  rw [Skew] at h
  obtain ⟨rfl | rfl, hi⟩ := h.exists_subset_of_isCircuit hC <| by simpa [← union_eq_iUnion]
  · right
    simpa using hi
  left
  simpa using hi

lemma Skew.subset_of_isCircuit_of_mem_left (h : M.Skew X Y) {C : Set α} (hC : M.IsCircuit C)
    (hCXY : C ⊆ X ∪ Y) (he : e ∈ C) (heX : e ∈ X) : C ⊆ X := by
  simpa using h.subset_of_isCircuit_of_mem hC (i := true) (e := e) (by simpa) he (by simpa)

lemma isSkewFamily_iff_forall_skew_compl_singleton {Xs : η → Set α} :
    M.IsSkewFamily Xs ↔ ∀ i, M.Skew (Xs i) (⋃ j ∈ ({i} : Set η)ᶜ, Xs j) := by
  refine ⟨IsSkewFamily.skew_compl_singleton, fun h ↦ ?_⟩
  rw [isSkewFamily_iff_diff_loops_isSkewFamily, isSkewFamily_iff_forall_isCircuit]
  · refine fun C hC hCss ↦ ?_
    obtain ⟨e, he⟩ := hC.nonempty
    obtain ⟨i, hi, hel⟩ := mem_iUnion.1 <| hCss he
    replace h := (h i).mono (diff_subset (t := M.loops)) (diff_subset (t := M.loops))
    have h_or := h.subset_or_subset_of_isCircuit hC ?_; swap
    · rw [← union_diff_distrib]
      simp_rw [← biUnion_insert, ← union_singleton, compl_union_self, biUnion_univ, iUnion_diff]
      assumption
    refine h_or.elim (fun h ↦ ⟨i,h⟩) fun h' ↦ ?_
    simpa [hi, hel] using h.diff_loops_disjoint_left.notMem_of_mem_right (h' he)
  · exact fun i ↦ diff_subset.trans (h i).subset_ground_left
  refine fun i j hij ↦ disjoint_left.2 fun a hai haj ↦ ?_
  apply (h i).diff_loops_disjoint_left.notMem_of_mem_left hai
  simp only [mem_compl_iff, mem_singleton_iff, mem_iUnion, exists_prop]
  exact ⟨j, hij.symm, haj.1⟩

lemma isSkewFamily_set_coe_iff_forall_skew_compl_singleton {I : Set η} (Xs : η → Set α) :
    M.IsSkewFamily (fun i : I ↦ Xs i) ↔ ∀ j ∈ I, M.Skew (Xs j) (⋃ i ∈ I \ {j}, Xs i) := by
  simp only [isSkewFamily_iff_forall_skew_compl_singleton, mem_compl_iff, mem_singleton_iff,
    iUnion_coe_set, Subtype.forall, Subtype.mk.injEq, mem_diff]
  convert Iff.rfl using 4 with i hi
  ext e
  aesop

/-- If `X i` is skew to the union of the other `X j` for all but one `i`,
then the `X i` are skew. -/
lemma isSkewFamily_iff_nearly_forall_skew_compl_singleton
    {Xs : η → Set α} {i₀ : η} (hi₀ : Xs i₀ ⊆ M.E) :
    M.IsSkewFamily Xs ↔ ∀ i ≠ i₀, M.Skew (Xs i) (⋃ j ∈ ({i} : Set η)ᶜ, Xs j) := by
  obtain hss | hnt := subsingleton_or_nontrivial η
  · simp [Subsingleton.elim _ i₀, hi₀]
  classical
  rw [isSkewFamily_iff_forall_skew_compl_singleton]
  refine ⟨fun h i _ ↦ h i, fun h i ↦ ?_⟩
  obtain hne | rfl := (eq_or_ne i i₀).symm
  · apply h _ hne
  wlog hdj : Pairwise (Disjoint on Xs) generalizing Xs with aux
  · simp_rw [skew_iff_diff_loops_skew (X := Xs i), iUnion_diff]
    apply aux (diff_subset.trans hi₀)
    · intro i₁ i₂ hne
      obtain rfl | hne' := eq_or_ne i₁ i
      · refine (h _ hne.symm).symm.diff_loops_disjoint.mono_left ?_
        exact diff_subset_diff_left (subset_biUnion_of_mem hne)
      refine (h _ hne').diff_loops_disjoint.mono_right <| diff_subset_diff_left ?_
      exact subset_biUnion_of_mem hne.symm
    exact fun j hne ↦ (h j hne).mono diff_subset <| iUnion₂_mono fun i h ↦ diff_subset
  obtain ⟨j₀, hj₀i⟩ := exists_ne i
  rw [skew_iff_forall_isCircuit _ ?_ ?_]
  · intro C hC hCss
    by_contra! hnot
    obtain ⟨e, he⟩ := not_subset.1 hnot.1
    apply hnot.2
    obtain ⟨j, hji : j ≠ i, hej⟩ := mem_iUnion₂.1 <| (diff_subset_iff.2 hCss) ⟨he.1, he.2⟩
    grw [(h j hji).subset_of_isCircuit_of_mem_left hC  ?_ he.1 hej, ← subset_biUnion_of_mem hji]
    rwa [← biUnion_insert, ← union_singleton, compl_union_self] at hCss ⊢
  · simpa using fun j hne ↦ hdj (Ne.symm hne)
  · grw [← (h j₀ hj₀i).subset_ground_right]
    apply subset_biUnion_of_mem hj₀i.symm
  simp only [mem_compl_iff, mem_singleton_iff, iUnion_subset_iff]
  exact fun j hji ↦ (h j hji).subset_ground_left

lemma skew_of_subset_loops {L : Set α} (hL : L ⊆ M.loops) (hX : X ⊆ M.E) : M.Skew L X := by
  rw [skew_iff_diff_loops_skew_left, diff_eq_empty.2 hL]
  apply empty_skew hX

lemma IsLoop.skew (he : M.IsLoop e) (hX : X ⊆ M.E) : M.Skew {e} X :=
  skew_of_subset_loops (by simpa) hX

lemma skew_of_subset_coloops {K : Set α} (hK : K ⊆ M.coloops) (hX : X ⊆ M.E)
    (hdj : Disjoint K X) : M.Skew K X := by
  rw [skew_iff_contract_restrict_eq_restrict, contract_eq_delete_of_subset_coloops hK,
    delete_eq_restrict, restrict_restrict_eq]
  rwa [subset_diff, and_iff_left hdj.symm]

lemma IsColoop.skew (he : M.IsColoop e) (hX : X ⊆ M.E) (heX : e ∉ X) : M.Skew {e} X :=
  skew_of_subset_coloops (by simpa) hX (by simpa)

lemma IsNonloop.skew_right_iff (he : M.IsNonloop e) (hX : X ⊆ M.E := by aesop_mat) :
    M.Skew X {e} ↔ e ∉ M.closure X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  rw [← skew_iff_isBases_skew hI he.indep.isBasis_self, ← hI.closure_eq_closure,
    Indep.skew_iff_disjoint_union_indep hI.indep he.indep, disjoint_singleton_right,
    hI.indep.notMem_closure_iff, union_singleton, and_comm]

lemma IsNonloop.skew_left_iff (he : M.IsNonloop e) (hX : X ⊆ M.E := by aesop_mat) :
    M.Skew {e} X ↔ e ∉ M.closure X := by
  rw [← he.skew_right_iff, skew_comm]

lemma Skew.isModularPair_union_right_of_subset_left {Z : Set α} (hXY : M.Skew X Y) (hZX : Z ⊆ X) :
    M.IsModularPair X (Y ∪ Z) := by
  obtain ⟨I, J, hI, hJ, hIJ⟩ := M.exists_isBasis_subset_isBasis hZX
  obtain ⟨K, hK⟩ := M.exists_isBasis Y
  rw [isModularPair_iff_exists_isBasis_isBasis]
  have hbas : M.IsBasis (I ∪ K) (Y ∪ Z) :=
    union_comm _ _ ▸ Skew.union_isBasis_union (hXY.symm.mono_right hZX) hK hI
  refine ⟨J, I ∪ K, hJ, hbas, ?_⟩
  rw [← union_assoc, union_eq_self_of_subset_right hIJ]
  exact Skew.union_indep (hXY.mono hJ.subset hK.subset) hJ.indep hK.indep

lemma Skew.isModularPair_union_union_of_subset {Z : Set α} (hXY : M.Skew X Y) (hZX : Z ⊆ X ∪ Y) :
    M.IsModularPair (X ∪ Z) (Y ∪ Z) := by
  rw [Skew] at hXY
  rw [IsModularPair]
  convert hXY.isModularFamily_union_of_subset (Z := Z) (by simpa) using 2 with i
  grind

lemma Skew.restrict (hXY : M.Skew X Y) (R : Set α) : (M ↾ R).Skew (X ∩ R) (Y ∩ R) := by
  rw [skew_iff_exist_isBases]
  simp only [isBasis_restrict_iff', union_subset_iff, inter_subset_right, and_self, and_true]
  rw [← union_inter_distrib_right, inter_right_comm,
    inter_eq_self_of_subset_left (union_subset hXY.subset_ground_left hXY.subset_ground_right),
    inter_right_comm, inter_eq_self_of_subset_left hXY.subset_ground_left,
    inter_right_comm, inter_eq_self_of_subset_left hXY.subset_ground_right,
    union_inter_distrib_right]
  replace hXY := hXY.mono (inter_subset_left (t := R)) (inter_subset_left (t := R))
  rwa [skew_iff_exist_isBases] at hXY

lemma Skew.restrict_of_subset {R : Set α} (hXY : M.Skew X Y) (hXR : X ⊆ R) (hYR : Y ⊆ R) :
    (M ↾ R).Skew X Y := by
  convert hXY.restrict R <;> simpa

lemma Skew.of_restrict {R : Set α} (h : (M ↾ R).Skew X Y) (hR : R ⊆ M.E := by aesop_mat) :
    M.Skew X Y := by
  rw [skew_iff_isModularPair_inter_subset_loops, loops] at h ⊢
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

lemma isModularPair_iff_skew_contract_inter (hXY : X ∩ Y ⊆ M.E) :
    M.IsModularPair X Y ↔ (M ／ (X ∩ Y)).Skew (X \ Y) (Y \ X) := by
  rw [Skew, contract_isSkewFamily_iff (by grind), IsModularPair, and_iff_left (by grind)]
  convert Iff.rfl using 3 with i
  cases i <;> grind

lemma contract_skew_iff_project_skew {C : Set α} (hXC : Disjoint X C) (hYC : Disjoint Y C) :
    (M ／ C).Skew X Y ↔ (M.project C).Skew X Y := by
  rw [← project_delete_self, skew_delete_iff, and_iff_left hYC, and_iff_left hXC]

lemma contract_skew_iff {C : Set α} (hXC : Disjoint X C) (hYC : Disjoint Y C)
    (hC : C ⊆ M.E := by aesop_mat) :
    (M ／ C).Skew X Y ↔ M.IsModularPair (X ∪ C) (Y ∪ C) ∧ X ∩ Y ⊆ M.closure C := by
  rw [Skew, contract_isSkewFamily_iff (by grind), IsModularPair]
  convert Iff.rfl using 4 with i
  · grind
  simp [inter_comm]

lemma Skew.contract_subset_left {C : Set α} (hXY : M.Skew X Y) (hCX : C ⊆ X) :
    (M ／ C).Skew (X \ C) (Y \ C) := by
  grw [contract_skew_iff disjoint_sdiff_left disjoint_sdiff_left (hCX.trans hXY.subset_ground_left),
    diff_union_of_subset hCX, diff_union_self, diff_inter_diff_right, hXY.inter_subset_loops,
    diff_subset, loops, and_iff_left (M.closure_subset_closure (empty_subset C))]
  exact hXY.isModularPair_union_right_of_subset_left hCX

lemma Skew.contract_subset_left_of_disjoint_loops {C : Set α} (hXY : M.Skew X Y) (hCX : C ⊆ X)
    (hY : Disjoint Y (M.loops)) : (M ／ C).Skew (X \ C) Y := by
  convert hXY.contract_subset_left hCX
  rw [eq_comm, sdiff_eq_left, ← hY.sdiff_eq_left]
  exact hXY.symm.diff_loops_disjoint_left.mono_right hCX

lemma Skew.contract_subset_right_of_disjoint_loops {C : Set α} (hXY : M.Skew X Y) (hCY : C ⊆ Y)
    (hX : Disjoint X (M.loops)) : (M ／ C).Skew X (Y \ C) :=
  (hXY.symm.contract_subset_left_of_disjoint_loops hCY hX).symm

lemma Skew.contract_subset_right {C : Set α} (hXY : M.Skew X Y) (hCX : C ⊆ Y) :
    (M ／ C).Skew (X \ C) (Y \ C) :=
  (hXY.symm.contract_subset_left hCX).symm

lemma Skew.contract_subset_union {C : Set α} (hXY : M.Skew X Y) (hC : C ⊆ X ∪ Y) :
    (M ／ C).Skew (X \ C) (Y \ C) := by
  have hCE : C ⊆ M.E := by grw [hC, hXY.subset_ground_left, hXY.subset_ground_right, union_self]
  grw [contract_skew_iff disjoint_sdiff_left disjoint_sdiff_left, diff_union_self, diff_union_self,
    diff_inter_diff_right, hXY.inter_subset_loops, diff_subset,
    and_iff_left (M.loops_subset_closure C)]
  exact hXY.isModularPair_union_union_of_subset hC

lemma IsModularPair.contract_subset_union {C : Set α} (hXY : M.IsModularPair X Y) (hC : C ⊆ X ∪ Y) :
    (M ／ C).IsModularPair (X \ C) (Y \ C) := by
  have hXE := hXY.subset_ground_left
  have hYE := hXY.subset_ground_left
  rw [isModularPair_iff_skew_contract_inter] at ⊢ hXY
  · rw [diff_inter_diff_right, contract_contract, union_diff_self, union_comm,
      ← union_diff_self, ← contract_contract]
    exact (hXY.contract_subset_union (by grind)).mono (by grind) (by grind)
  · grind [contract_ground]
  grind

lemma IsModularPair.skew_contract_inter (hXY : M.IsModularPair X Y) :
    (M ／ (X ∩ Y)).Skew (X \ Y) (Y \ X) := by
  rwa [← isModularPair_iff_skew_contract_inter (inter_subset_left.trans hXY.subset_ground_left)]

lemma skew_iff_restrict_union_eq (hXE : X ⊆ M.E) (hYE : Y ⊆ M.E) (hdj : Disjoint X Y) :
    M.Skew X Y ↔ M ↾ (X ∪ Y) = (M ↾ X).disjointSum (M ↾ Y) hdj := by
  rw [disjointSum_eq_disjointSigma, union_eq_iUnion, Skew,
    isSkewFamily_iff_restrict_iUnion_eq_disjointSigma]
  · simp [Bool.apply_cond]
  · simpa [pairwise_on_bool Disjoint.symm]
  simp [hXE, hYE]

lemma skew_disjointSum {M₁ M₂ : Matroid α} (hdj : Disjoint M₁.E M₂.E) :
    (disjointSum M₁ M₂ hdj).Skew M₁.E M₂.E := by
  rw [skew_iff_forall_isCircuit hdj]
  simp_rw [disjointSum_isCircuit_iff]
  rintro C (h | h) -
  · exact .inl h.subset_ground
  exact .inr h.subset_ground

lemma contract_eq_delete_iff_skew_compl (hX : X ⊆ M.E := by aesop_mat) :
    M ／ X = M ＼ X ↔ M.Skew X (M.E \ X) := by
  rw [skew_iff_contract_restrict_eq_restrict, restrict_compl, ← contract_ground,
    restrict_ground_eq_self]

lemma Coindep.skew_compl_iff_subset_loops (hX : M.Coindep X) :
    M.Skew X (M.E \ X) ↔ X ⊆ M.loops := by
  refine ⟨fun h ↦ ?_, fun h ↦ skew_of_subset_loops h diff_subset⟩
  obtain ⟨B, hB⟩ := M.exists_isBasis (M.E \ X)
  have hBM := hB.isBase_of_spanning hX.compl_spanning
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  have hIB : B \ B = (I ∪ B) \ B := by rw [← hBM.eq_of_subset_indep
    ((h.mono hI.subset hB.subset).union_indep hI.indep hB.indep) subset_union_right]
  rw [union_diff_cancel_right (disjoint_sdiff_right.mono hI.subset hB.subset).inter_eq.subset,
    diff_self] at hIB
  rwa [← hIB, empty_isBasis_iff] at hI

lemma Indep.skew_compl_iff_subset_coloops (hI : M.Indep I) :
    M.Skew I (M.E \ I) ↔ I ⊆ M.coloops := by
  rw [← dual_loops, ← hI.coindep.skew_compl_iff_subset_loops, ← contract_eq_delete_iff_skew_compl,
    ← contract_eq_delete_iff_skew_compl, ← dual_inj, dual_contract, dual_delete, eq_comm]

section ModularCompl

variable {F₀ F₁ F F' : Set α}

/-- `M.ModularCompl F₀ F₁ F F'` means that `F,F'` are a modular pair of flats with intersection
`F₀` and whose union has closure `F₁`.
Every `F` with `F₀ ⊆ F ⊆ F₁` has a `ModularCompl`.   -/
@[mk_iff] structure ModularCompl (M : Matroid α) (F₀ F₁ F F' : Set α) : Prop where
  isFlat_left : M.IsFlat F
  isFlat_right : M.IsFlat F'
  inter_eq : F ∩ F' = F₀
  closure_union_eq : M.closure (F ∪ F') = F₁
  isModularPair : M.IsModularPair F F'

lemma ModularCompl.symm (h : M.ModularCompl F₀ F₁ F F') : M.ModularCompl F₀ F₁ F' F where
  isFlat_left := h.isFlat_right
  isFlat_right := h.isFlat_left
  inter_eq := by rw [← h.inter_eq, inter_comm]
  closure_union_eq := by rw [← h.closure_union_eq, union_comm]
  isModularPair := h.isModularPair.symm

lemma modularCompl_comm :
    M.ModularCompl F₀ F₁ F F' ↔ M.ModularCompl F₀ F₁ F' F :=
  ⟨ModularCompl.symm, ModularCompl.symm⟩

@[aesop unsafe 24% (rule_sets := [Matroid])]
lemma ModularCompl.left_subset_ground (h : M.ModularCompl F₀ F₁ F F') : F ⊆ M.E :=
  h.isFlat_left.subset_ground

@[aesop unsafe 25% (rule_sets := [Matroid])]
lemma ModularCompl.right_subset_ground (h : M.ModularCompl F₀ F₁ F F') : F' ⊆ M.E :=
  h.isFlat_right.subset_ground

lemma ModularCompl.isFlat_top (h : M.ModularCompl F₀ F₁ F F') : M.IsFlat F₁ := by
  simp [← h.closure_union_eq]

@[aesop unsafe 25% (rule_sets := [Matroid])]
lemma ModularCompl.top_subset_ground (h : M.ModularCompl F₀ F₁ F F') : F₁ ⊆ M.E :=
  h.isFlat_top.subset_ground

lemma ModularCompl.isFlat_bot (h : M.ModularCompl F₀ F₁ F F') : M.IsFlat F₀ := by
  rw [← h.inter_eq]
  exact h.isFlat_left.inter h.isFlat_right

@[aesop unsafe 25% (rule_sets := [Matroid])]
lemma ModularCompl.bot_subset_ground (h : M.ModularCompl F₀ F₁ F F') : F₀ ⊆ M.E :=
  h.isFlat_bot.subset_ground

lemma ModularCompl.subset_left (h : M.ModularCompl F₀ F₁ F F') : F₀ ⊆ F := by
  simp [← h.inter_eq]

lemma ModularCompl.subset_right (h : M.ModularCompl F₀ F₁ F F') : F₀ ⊆ F' := by
  simp [← h.inter_eq]

lemma ModularCompl.left_subset (h : M.ModularCompl F₀ F₁ F F') : F ⊆ F₁ := by
  rw [← h.closure_union_eq]
  refine M.subset_closure_of_subset' subset_union_left h.isFlat_left.subset_ground

lemma ModularCompl.right_subset (h : M.ModularCompl F₀ F₁ F F') : F' ⊆ F₁ :=
  h.symm.left_subset

lemma ModularCompl.subset (h : M.ModularCompl F₀ F₁ F F') : F₀ ⊆ F₁ :=
  h.subset_left.trans h.left_subset

lemma IsFlat.exists_modularCompl (hF₀ : M.IsFlat F₀) (hF₁ : M.IsFlat F₁) (hF : M.IsFlat F)
    (hF₀F : F₀ ⊆ F) (hFF₁ : F ⊆ F₁) : ∃ F', M.ModularCompl F₀ F₁ F F' := by
  obtain ⟨I, hI⟩ := M.exists_isBasis F₀
  obtain ⟨J, hJ, rfl⟩ := hI.exists_isBasis_inter_eq_of_superset hF₀F
  obtain ⟨K, hK, rfl⟩ := hJ.exists_isBasis_inter_eq_of_superset hFF₁
  rw [inter_assoc, inter_eq_self_of_subset_right hF₀F] at hI

  have hi : M.Indep (K ∩ F ∪ (K ∩ F₀ ∪ K \ F)) :=
    hK.indep.subset (union_subset inter_subset_left (union_subset inter_subset_left diff_subset))

  have hmod : M.IsModularPair F (M.closure (F₀ ∪ K \ F))
  · refine hi.isModularPair_of_union.of_isBasis_of_isBasis hJ ?_
    rw [← closure_union_congr_left hI.closure_eq_closure]
    exact Indep.isBasis_closure (hK.indep.subset (union_subset inter_subset_left diff_subset))

  use M.closure (F₀ ∪ (K \ F))
  rw [modularCompl_iff, and_iff_right hF, and_iff_right (M.closure_isFlat _),
    closure_union_closure_right_eq, union_comm F, union_assoc, diff_union_self, union_comm K,
    ← union_assoc, closure_union_congr_right hK.closure_eq_closure,
    union_eq_self_of_subset_left (union_subset (hF₀F.trans hFF₁) hFF₁), hF₁.closure,
    and_iff_right rfl, and_iff_left hmod]

  rw [← (hF.inter (M.closure_isFlat _)).closure,  hmod.inter_closure_eq, ← hJ.closure_eq_closure,
    closure_closure, ← closure_union_congr_left hI.closure_eq_closure,
     ← Indep.closure_inter_eq_inter_closure, inter_union_distrib_left, ← inter_inter_distrib_left,
     inter_eq_self_of_subset_right hF₀F,
     (disjoint_sdiff_right.mono_left inter_subset_right).inter_eq, union_empty,
    hI.closure_eq_closure, hF₀.closure]

  exact hK.indep.subset (union_subset inter_subset_left
    (union_subset inter_subset_left diff_subset))

/-- Two flats are `ModularCompl` in the interval `[M.loops, M.E]` iff they are skew
with spanning union. -/
lemma modularCompl_loops_ground_iff {F F' : Set α} (hF : M.IsFlat F) (hF' : M.IsFlat F'):
    M.ModularCompl (M.loops) M.E F F' ↔ M.Skew F F' ∧ M.Spanning (F ∪ F') := by
  rw [modularCompl_iff, and_iff_right hF, and_iff_right hF', spanning_iff_closure_eq,
    and_comm (b := M.IsModularPair _ _), ← and_assoc, and_congr_left_iff]
  refine fun hcl ↦ ⟨fun ⟨h, hmod⟩ ↦ ?_, fun h ↦ ⟨?_, h.isModularPair ⟩⟩
  · rw [skew_iff_isModularPair_inter_subset_loops, and_iff_right hmod, h]
  rw [← h.inter_closure_eq, hF.closure, hF'.closure]

lemma ModularCompl.isBasis_inter_isBasis_eq {J' : Set α} (h : M.ModularCompl F₀ F₁ F F')
    (hI : M.IsBasis I F₀) (hJ : M.IsBasis J F) (hJ' : M.IsBasis J' F') (hIJ : I ⊆ J)
    (hIJ' : I ⊆ J') : J ∩ J' = I := by
  have hcl := h.isModularPair.inter_closure_eq
  rw [h.inter_eq, ← hI.closure_eq_closure, ← hJ.closure_eq_closure,
    ← hJ'.closure_eq_closure] at hcl
  rw [← (hJ.indep.inter_right J').closure_inter_eq_self_of_subset (subset_inter hIJ hIJ'),
    eq_comm, inter_eq_right, hcl]
  exact inter_subset_inter (M.subset_closure J) (M.subset_closure J')

lemma ModularCompl.isBasis_inter_right_eq (h : M.ModularCompl F₀ F₁ F F')
    (hI : M.IsBasis I F₀) (hJ : M.IsBasis J F) (hIJ : I ⊆ J) : J ∩ F' = I := by
  rw [inter_comm, hI.eq_of_subset_indep (hJ.indep.inter_left F')
    (subset_inter (hI.subset.trans h.subset_right) hIJ)]
  rw [← h.inter_eq, inter_comm]
  exact inter_subset_inter_left _ hJ.subset

lemma ModularCompl.union_isBasis_top {J' : Set α} (h : M.ModularCompl F₀ F₁ F F')
    (hI : M.IsBasis I F₀) (hJ : M.IsBasis J F) (hJ' : M.IsBasis J' F') (hIJ : I ⊆ J)
    (hIJ' : I ⊆ J') : M.IsBasis (J ∪ J') F₁ := by
  refine Indep.isBasis_of_subset_of_subset_closure ?_
    (union_subset (hJ.subset.trans h.left_subset) (hJ'.subset.trans h.right_subset))
    (by rw [closure_union_congr_left hJ.closure_eq_closure,
      closure_union_congr_right hJ'.closure_eq_closure, h.closure_union_eq])
  have hp := h.isModularPair
  rw [isModularPair_iff_skew_contract_inter (inter_subset_left.trans hp.subset_ground_left),
    h.inter_eq, hI.contract_eq_contract_delete] at hp
  replace hp := hp.of_delete

  have hwin := hp.union_indep_of_indep_subsets (I := J \ I) (J := J' \ I)
  rw [hI.indep.contract_indep_iff, and_iff_right disjoint_sdiff_left, diff_union_of_subset hIJ,
    hI.indep.contract_indep_iff, diff_union_of_subset hIJ', and_iff_right disjoint_sdiff_left,
    imp_iff_right hJ.indep, imp_iff_right hJ'.indep, hI.indep.contract_indep_iff,
    ← union_diff_distrib, diff_union_self] at hwin
  refine (hwin ?_ ?_).2.subset subset_union_left
  · rw [← h.isBasis_inter_right_eq hI hJ hIJ, diff_self_inter]
    exact diff_subset_diff_left hJ.subset
  rw [← h.symm.isBasis_inter_right_eq hI hJ' hIJ', diff_self_inter]
  exact diff_subset_diff_left hJ'.subset

end ModularCompl
