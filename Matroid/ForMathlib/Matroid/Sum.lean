import Mathlib.Combinatorics.Matroid.Closure
import Mathlib.Combinatorics.Matroid.Sum
import Matroid.ForMathlib.Matroid.Map

namespace Matroid

open Set Sum
-- variable {M N : Matroid α}

@[simp] lemma preimage_image_sigmaMk {ι : Type*} {α : ι → Type*} (i : ι) (s : Set (α i)) :
    Sigma.mk i ⁻¹' (Sigma.mk i '' s) = s :=
  preimage_image_eq _ sigma_mk_injective

@[simp] lemma iUnion_preimage_image_sigma_mk_eq_self {ι : Type*} {α : ι → Type*}
    {s : ∀ i, Set (α i)} {i₀ : ι} : ⋃ i, Sigma.mk i₀ ⁻¹' (Sigma.mk i '' s i) = s i₀ := by
  refine subset_antisymm (iUnion_subset fun i ↦ ?_) <| ?_
  · obtain rfl | hne := eq_or_ne i₀ i
    · simp
    simp [preimage_image_sigmaMk_of_ne hne]
  convert subset_iUnion _ i₀
  simp

@[simp]
lemma Sum.preimage_image_inl (α β : Type*) (X : Set α) : (inl : α → α ⊕ β) ⁻¹' (inl '' X) = X := by
  rw [preimage_image_eq _ inl_injective]

@[simp]
lemma Sum.preimage_image_inr (α β : Type*) (X : Set β) : (inr : β → α ⊕ β) ⁻¹' (inr '' X) = X := by
  rw [preimage_image_eq _ inr_injective]

@[simp]
lemma Sum.preimage_inl_insert_inl (α β : Type*) (X : Set (α ⊕ β)) (e : α) :
    inl ⁻¹' (insert (inl e) X) = insert e (inl ⁻¹' X) := by
  grind

@[simp]
lemma Sum.preimage_inr_insert_inr (α β : Type*) (X : Set (α ⊕ β)) (e : β) :
    inr ⁻¹' (insert (inr e) X) = insert e (inr ⁻¹' X) := by
  grind

@[simp]
lemma Sum.preimage_inl_insert_inr (α β : Type*) (X : Set (α ⊕ β)) (e : β) :
    inl ⁻¹' (insert (inr e) X) = inl ⁻¹' X := by
  grind

@[simp]
lemma Sum.preimage_inr_insert_inl (α β : Type*) (X : Set (α ⊕ β)) (e : α) :
    inr ⁻¹' (insert (inl e) X) = inr ⁻¹' X := by
  grind


section sigma

variable {ι : Type*} {α : ι → Type*} {M : (i : ι) → Matroid (α i)} {I B X : ∀ i, Set (α i)}

lemma Indep.sigma (h : ∀ i, (M i).Indep (I i)) :
    (Matroid.sigma M).Indep (⋃ i, Sigma.mk i '' I i) := by
  simpa

lemma sigma_dep_iff {X : Set ((i : ι) × α i)} :
    (Matroid.sigma M).Dep X ↔
      ∃ i, (M i).Dep (Sigma.mk i ⁻¹' X) ∧ ∀ i, Sigma.mk i ⁻¹' X ⊆ (M i).E := by
  simp only [Dep, sigma_indep_iff, not_forall, sigma_ground_eq, subset_def, mem_sigma_iff, mem_univ,
    true_and, mem_preimage, exists_and_right]
  exact ⟨fun ⟨⟨i, hii⟩, hiss⟩ ↦ ⟨⟨i, hii, fun e he ↦ hiss _ he⟩, fun i e he ↦ hiss _ he⟩,
    fun ⟨⟨i, hi1, hi2⟩, h⟩ ↦ ⟨⟨i, hi1⟩, fun ⟨x,j⟩ hx ↦ h _ _ hx⟩⟩

lemma sigma_image_indep_iff {i : ι} {I : Set (α i)} :
    (Matroid.sigma M).Indep (Sigma.mk i '' I) ↔ (M i).Indep I := by
  simp only [sigma_indep_iff]
  refine ⟨fun h ↦ by simpa using h i, fun h ↦ ?_⟩
  rintro j
  obtain rfl | hne := eq_or_ne j i
  · simpa
  simp [preimage_image_sigmaMk_of_ne hne]

lemma sigma_image_dep_iff {i : ι} {D : Set (α i)} :
    (Matroid.sigma M).Dep (Sigma.mk i '' D) ↔ (M i).Dep D := by
  rw [Dep, sigma_image_indep_iff, Dep]
  simp

lemma IsBase.sigma (h : ∀ i, (M i).IsBase (B i)) :
    (Matroid.sigma M).IsBase (⋃ i, Sigma.mk i '' B i) := by
  simpa

lemma IsBasis.sigma (h : ∀ i, (M i).IsBasis (I i) (X i)) :
    (Matroid.sigma M).IsBasis (⋃ i, Sigma.mk i '' (I i)) (⋃ i, Sigma.mk i '' (X i)) := by
  refine Indep.isBasis_of_maximal_subset (Indep.sigma (fun i ↦ (h i).indep)) ?_ ?_
  · exact iUnion_subset fun i ↦ (subset_iUnion_of_subset i (image_mono (h i).subset))
  simp only [sigma_indep_iff, iUnion_subset_iff, image_subset_iff]
  intro Js hJ hIJ hJX
  rw [← iUnion_image_preimage_sigma_mk_eq_self (s := Js), iUnion_subset_iff]
  refine fun i ↦ subset_iUnion_of_subset i (image_mono ?_)
  rw [(h i).eq_of_subset_indep (hJ i) (hIJ i)]
  simpa using preimage_mono (f := Sigma.mk i) hJX

lemma sigma_isBasis_iff' {I X} :
    (Matroid.sigma M).IsBasis I X ↔ ∀ i, (M i).IsBasis (Sigma.mk i ⁻¹' I) (Sigma.mk i ⁻¹' X) := by
  refine ⟨fun h ↦ ?_,
    fun h ↦ by simpa only [iUnion_image_preimage_sigma_mk_eq_self] using IsBasis.sigma h⟩
  have hi : ∀ (i : ι), (M i).Indep (Sigma.mk i ⁻¹' I) := by simpa using h.indep
  refine fun i ↦ (hi i).isBasis_of_maximal_subset (preimage_mono h.subset) fun J hJ hIJ hJX ↦ ?_
  rw [h.eq_of_subset_indep (J := I ∪ Sigma.mk i '' J) ?_ subset_union_left
    (union_subset h.subset (by rwa [image_subset_iff])), preimage_union, preimage_image_sigmaMk]
  · simp
  simp only [sigma_indep_iff, preimage_union]
  intro j
  obtain rfl | hne := eq_or_ne i j
  · exact hJ.subset <| by simpa
  simp [preimage_image_sigmaMk_of_ne hne.symm, hi]

lemma sigma_isBasis'_iff' {I X} :
    (Matroid.sigma M).IsBasis' I X ↔ ∀ i, (M i).IsBasis' (Sigma.mk i ⁻¹' I) (Sigma.mk i ⁻¹' X) := by
  simp [isBasis'_iff_isBasis_inter_ground]

lemma sigma_closure_eq (X) :
    (Matroid.sigma M).closure X = ⋃ i, Sigma.mk i '' (M i).closure (Sigma.mk i ⁻¹' X) := by
  obtain ⟨I, hI⟩ := (Matroid.sigma M).exists_isBasis' X
  have hI' := sigma_isBasis'_iff'.1 hI
  ext ⟨i, e⟩
  simp only [← hI.closure_eq_closure, hI.indep.mem_closure_iff', sigma_ground_eq, mem_sigma_iff,
    mem_univ, true_and, sigma_indep_iff, mem_iUnion, mem_image, Sigma.mk.inj_iff]
  constructor
  · refine fun h ↦ ⟨i, e, ?_, rfl, heq_of_eq rfl⟩
    rw [← (hI' i).closure_eq_closure, (hI' i).indep.mem_closure_iff', and_iff_right h.1]
    refine fun h' ↦ h.2 fun j ↦ ?_
    obtain rfl | hne := eq_or_ne i j
    · exact h'.subset <| by simp [subset_def]
    refine (hI' j).indep.subset ?_
    rw [← singleton_union, preimage_union, preimage_eq_empty (by simpa), empty_union]
  rintro ⟨j, f, hf, rfl, h'⟩
  obtain rfl : f = e := by simpa using h'
  refine ⟨mem_ground_of_mem_closure hf, fun h ↦ ?_⟩
  rw [← (hI' j).closure_eq_closure, (hI' j).indep.mem_closure_iff'] at hf
  exact hf.2 <| (h j).subset <| by simp [insert_subset_iff, preimage_mono (subset_insert ..)]

lemma sigma_dual_eq : (Matroid.sigma M)✶ = Matroid.sigma (fun i ↦ (M i)✶) := by
  refine ext_isBase rfl fun B hB ↦ ?_
  simp only [dual_isBase_iff', sigma_ground_eq, sigma_isBase_iff, preimage_diff, mem_univ,
    mk_preimage_sigma, forall_and, and_congr_right_iff]
  exact fun _ ↦ ⟨fun h i ↦ (preimage_mono h).trans <| by simp, fun _ ↦ by simpa using hB⟩

end sigma

section disjointSigma

variable {ι α : Type*} {M : ι → Matroid α} {I J B X : ι → Set α}

lemma Indep.disjointSigma_iUnion h (hI : ∀ i, (M i).Indep (I i)) :
    (Matroid.disjointSigma M h).Indep (⋃ i, I i) := by
  rw [disjointSigma_indep_iff, and_iff_left <| iUnion_mono (fun i ↦ (hI i).subset_ground)]
  refine fun i ↦ (hI i).subset ?_
  rw [iUnion_inter, iUnion_subset_iff]
  intro j
  obtain rfl | hne := eq_or_ne i j
  · simp
  simp [((h hne.symm).mono_left (hI j).subset_ground).inter_eq]

lemma IsBase.disjointSigma_iUnion h (hB : ∀ i, (M i).IsBase (B i)) :
    (Matroid.disjointSigma M h).IsBase (⋃ i, B i) := by
  rw [disjointSigma_isBase_iff, and_iff_left <| iUnion_mono (fun i ↦ (hB i).subset_ground)]
  suffices aux : ∀ i, (⋃ j, B j) ∩ (M i).E = B i by
    simp_rw [aux]; assumption
  refine fun i ↦ subset_antisymm ?_ (subset_inter (subset_iUnion _ _) (hB i).subset_ground)
  rw [iUnion_inter, iUnion_subset_iff]
  intro j
  obtain rfl | hne := eq_or_ne i j
  · simp
  simp [((h hne.symm).mono_left (hB j).subset_ground).inter_eq]

lemma IsBasis.disjointSigma_iUnion h (hI : ∀ i, (M i).IsBasis (I i) (X i)) :
    (Matroid.disjointSigma M h).IsBasis (⋃ i, I i) (⋃ i, X i) := by
  have aux : ∀ (j : ι) {Y : ι → Set α}, (∀ i, Y i ⊆ (M i).E) → (⋃ i, Y i) ∩ (M j).E = Y j := by
    refine fun j Y hj ↦ subset_antisymm ?_ (subset_inter (subset_iUnion _ _) (hj j))
    rw [iUnion_inter, iUnion_subset_iff]
    intro i
    obtain rfl | hne := eq_or_ne i j
    · simp
    simp [((h hne).mono_left (hj i)).inter_eq]
  rw [disjointSigma_isBasis_iff, and_iff_right (iUnion_mono (fun i ↦ (hI i).subset)),
    and_iff_left (iUnion_mono (fun i ↦ (hI i).subset_ground))]
  intro i
  rw [aux _ (fun i ↦ (hI i).subset_ground), aux _ (fun i ↦ (hI i).indep.subset_ground)]
  apply hI

lemma isRestriction_disjointSigma h (i : ι) : (M i).IsRestriction (Matroid.disjointSigma M h) := by
  refine ⟨(M i).E, ?_, ext_indep rfl fun I ↦ ?_⟩
  · simp only [disjointSigma_ground_eq]
    exact subset_iUnion (fun i ↦ (M i).E) i
  simp only [restrict_indep_iff, disjointSigma_indep_iff]
  refine fun hss ↦ ⟨fun hI ↦ ⟨⟨?_, subset_iUnion_of_subset _ hI.subset_ground⟩, hI.subset_ground⟩,
    fun h ↦ (h.1.1 i).subset (by simpa)⟩
  intro j
  obtain rfl | hne := eq_or_ne i j
  · apply hI.inter_right
  simp [((h hne).mono_left hI.subset_ground).inter_eq]

lemma disjointSigma_closure h X :
    (Matroid.disjointSigma M h).closure X = ⋃ i, (M i).closure (X ∩ (M i).E) := by
  simp [Matroid.disjointSigma, mapEmbedding, Function.Embedding.sigmaSet, sigma_closure_eq,
    image_iUnion, image_image, preimage_preimage, inter_comm _ X]

end disjointSigma

section disjointSum

variable {α : Type*} {M N : Matroid α} {I J B B' : Set α}

lemma Indep.disjointSum_indep_union {h} (hI : M.Indep I) (hJ : N.Indep J) :
    (M.disjointSum N h).Indep (I ∪ J) := by
  rw [disjointSum_indep_iff, union_inter_distrib_right, union_inter_distrib_right,
    (h.mono_left hI.subset_ground).inter_eq, (h.symm.mono_left hJ.subset_ground).inter_eq,
    union_empty, empty_union]
  exact ⟨hI.subset inter_subset_left, hJ.subset inter_subset_left,
    union_subset_union hI.subset_ground hJ.subset_ground⟩

lemma IsBase.disjointSum_isBase_union {h} (hB : M.IsBase B) (hB' : N.IsBase B') :
    (M.disjointSum N h).IsBase (B ∪ B') := by
  rw [disjointSum_isBase_iff, union_inter_distrib_right, union_inter_distrib_right,
    (h.mono_left hB.subset_ground).inter_eq, (h.symm.mono_left hB'.subset_ground).inter_eq,
    union_empty, empty_union, inter_eq_self_of_subset_left hB.subset_ground,
    inter_eq_self_of_subset_left hB'.subset_ground]
  exact ⟨hB, hB', union_subset_union hB.subset_ground hB'.subset_ground⟩

lemma IsBasis.disjointSum_isBasis_union {I J X Y : Set α} {M N : Matroid α} (hIX : M.IsBasis I X)
    (hJY : N.IsBasis J Y) (h) : (M.disjointSum N h).IsBasis (I ∪ J) (X ∪ Y) := by

  rw [disjointSum_isBasis_iff, union_inter_distrib_right, union_inter_distrib_right,
    (h.symm.mono_left hJY.indep.subset_ground).inter_eq, union_empty,
    (h.symm.mono_left hJY.subset_ground).inter_eq, union_empty,
    inter_eq_self_of_subset_left hIX.subset_ground,
    inter_eq_self_of_subset_left hIX.indep.subset_ground,
    union_inter_distrib_right, union_inter_distrib_right,
    (h.mono_left hIX.indep.subset_ground).inter_eq, empty_union,
    (h.mono_left hIX.subset_ground).inter_eq, empty_union,
    inter_eq_self_of_subset_left hJY.subset_ground,
    inter_eq_self_of_subset_left hJY.indep.subset_ground]
  exact ⟨hIX, hJY, union_subset_union hIX.subset hJY.subset,
    union_subset_union hIX.subset_ground hJY.subset_ground⟩

-- TODO - generalize this to other sums.
@[simp]
lemma disjointSum_dual (M N : Matroid α) (hMN : Disjoint M.E N.E) :
    (M.disjointSum N hMN)✶ = M✶.disjointSum N✶ hMN := by
  refine ext_isBase (by simp) fun B hB ↦ ?_
  rw [disjointSum_isBase_iff, dual_isBase_iff, disjointSum_isBase_iff]
  simp only [disjointSum_ground_eq, dual_ground, inter_subset_right, dual_isBase_iff]
  simp only [dual_ground, disjointSum_ground_eq] at hB
  rw [union_diff_distrib, union_inter_distrib_right, inter_eq_self_of_subset_left diff_subset,
      (hMN.symm.mono_left diff_subset).inter_eq, union_empty, union_inter_distrib_right,
      inter_eq_self_of_subset_left diff_subset, (hMN.mono_left diff_subset).inter_eq, empty_union,
      and_iff_left (union_subset_union diff_subset diff_subset)]
  simp [hB]

lemma disjointSum_eq_disjointSigma (M N : Matroid α) (hMN : Disjoint M.E N.E) :
    M.disjointSum N hMN = Matroid.disjointSigma (fun b ↦ bif b then M else N)
    (by simp [Function.onFun, Pairwise, hMN, hMN.symm]) := by
  refine ext_indep (by simp [Set.ext_iff, or_comm]) fun I hI ↦ ?_
  simp [union_eq_iUnion, Bool.apply_cond, and_comm, and_assoc]

lemma isRestriction_disjointSum_left (hMN : Disjoint M.E N.E) : M ≤r (disjointSum M N hMN) := by
  rw [disjointSum_eq_disjointSigma]
  exact isRestriction_disjointSigma _ true

lemma isRestriction_disjointSum_right (hMN : Disjoint M.E N.E) : N ≤r (disjointSum M N hMN) := by
  rw [disjointSum_eq_disjointSigma]
  exact isRestriction_disjointSigma _ false

@[simp]
lemma disjointSum_restrict_left (hMN : Disjoint M.E N.E) : (disjointSum M N hMN) ↾ M.E = M :=
  (isRestriction_disjointSum_left hMN).eq_restrict

@[simp]
lemma disjointSum_restrict_right (hMN : Disjoint M.E N.E) : (disjointSum M N hMN) ↾ N.E = N :=
  (isRestriction_disjointSum_right hMN).eq_restrict

end disjointSum

variable {α β : Type*} {M : Matroid α} {N : Matroid β}

lemma sum_dep_iff (M : Matroid α) (N : Matroid β) (X : Set (α ⊕ β)) :
    (M.sum N).Dep X ↔ (M.Dep (.inl ⁻¹' X) ∨ N.Dep (.inr ⁻¹' X))
      ∧ .inl ⁻¹' X ⊆ M.E ∧ .inr ⁻¹' X ⊆ N.E := by
  by_cases hXE : X ⊆ (M.sum N).E
  · have hXM : inl ⁻¹' X ⊆ M.E := by grw [hXE]; simp
    have hXN : inr ⁻¹' X ⊆ N.E := by grw [hXE]; simp
    simp_rw [dep_iff, and_iff_left hXE, and_iff_left hXM, and_iff_left hXN, and_iff_left hXM,
      sum_indep_iff, Classical.not_and_iff_not_or_not]
  refine iff_of_false (mt Dep.subset_ground hXE) fun ⟨_, h⟩ ↦ hXE ?_
  rintro (x | x) hx
  · simp [h.1 hx]
  simp [h.2 hx]

lemma sum_closure_eq (M : Matroid α) (N : Matroid β) (X : Set (α ⊕ β)) :
    (M.sum N).closure X = inl '' (M.closure (inl ⁻¹' X)) ∪ inr '' (N.closure (inr ⁻¹' X)) := by
  wlog hX : (M.sum N).Indep X generalizing X with aux
  · obtain ⟨I, hI⟩ := (M.sum N).exists_isBasis' X
    have hI' := sum_isBasis_iff.1 hI.isBasis_inter_ground
    rw [← hI.closure_eq_closure, aux _ hI.indep, hI'.1.closure_eq_closure,
      hI'.2.closure_eq_closure, sum_ground]
    simp [preimage_image_eq _ inl_injective, preimage_image_eq _ inr_injective]
  have hX' := (sum_indep_iff ..).1 hX
  ext e
  simp [hX.mem_closure_iff, hX'.1.mem_closure_iff, hX'.2.mem_closure_iff, sum_dep_iff]
  obtain e | e := e
  · simp only [Sum.preimage_inl_insert_inl, Sum.preimage_inr_insert_inl, hX'.2.not_dep, or_false,
      insert_subset_iff, hX'.1.subset_ground, and_true, hX'.2.subset_ground, inl.injEq]
    rw [and_iff_left_of_imp (fun h ↦ h.subset_ground <| mem_insert ..)]
    simp
  simp only [Sum.preimage_inr_insert_inr, Sum.preimage_inl_insert_inr, hX'.1.not_dep, false_or,
      insert_subset_iff, hX'.1.subset_ground, and_true, hX'.2.subset_ground, inr.injEq, true_and]
  rw [and_iff_left_of_imp (fun h ↦ h.subset_ground <| mem_insert ..)]
  simp

@[simp]
lemma inl_mem_sum_closure_iff {e : α} {X : Set (α ⊕ β)} :
    inl e ∈ (M.sum N).closure X ↔ e ∈ M.closure (.inl ⁻¹' X) := by
  grind [sum_closure_eq]

@[simp]
lemma inr_mem_sum_closure_iff {e : β} {X : Set (α ⊕ β)} :
    inr e ∈ (M.sum N).closure X ↔ e ∈ N.closure (.inr ⁻¹' X) := by
  grind [sum_closure_eq]
