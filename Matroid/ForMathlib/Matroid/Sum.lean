import Mathlib.Data.Matroid.Sum

namespace Matroid

open Set
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

variable {α : Type*} {ι : Type*}

lemma Indep.sigma {α : ι → Type*} {M : (i : ι) → Matroid (α i)} {I : ∀ i, Set (α i)}
    (h : ∀ i, (M i).Indep (I i)) : (Matroid.sigma M).Indep (⋃ i, Sigma.mk i '' I i) := by
  simpa

lemma Base.sigma {α : ι → Type*} {M : (i : ι) → Matroid (α i)} {B : ∀ i, Set (α i)}
    (h : ∀ i, (M i).Base (B i)) : (Matroid.sigma M).Base (⋃ i, Sigma.mk i '' B i) := by
  simpa

lemma Basis.sigma {α : ι → Type*} {M : (i : ι) → Matroid (α i)} {I X : ∀ i, Set (α i)}
    (h : ∀ i, (M i).Basis (I i) (X i)) :
    (Matroid.sigma M).Basis (⋃ i, Sigma.mk i '' (I i)) (⋃ i, Sigma.mk i '' (X i)) := by
  refine Indep.basis_of_maximal_subset (Indep.sigma (fun i ↦ (h i).indep)) ?_ ?_
  · exact iUnion_subset fun i ↦ (subset_iUnion_of_subset i (image_subset _ (h i).subset))
  simp only [sigma_indep_iff, iUnion_subset_iff, image_subset_iff]
  intro Js hJ hIJ hJX
  rw [← iUnion_image_preimage_sigma_mk_eq_self (s := Js), iUnion_subset_iff]
  refine fun i ↦ subset_iUnion_of_subset i (image_subset _ ?_)
  rw [(h i).eq_of_subset_indep (hJ i) (hIJ i)]
  simpa using preimage_mono (f := Sigma.mk i) hJX

lemma sigma_basis_iff' {ι : Type*} {α : ι → Type*} {M : (i : ι) → Matroid (α i)} {I X} :
    (Matroid.sigma M).Basis I X ↔ ∀ i, (M i).Basis (Sigma.mk i ⁻¹' I) (Sigma.mk i ⁻¹' X) := by
  refine ⟨fun h ↦ ?_,
    fun h ↦ by simpa only [iUnion_image_preimage_sigma_mk_eq_self] using Basis.sigma h⟩
  have hi : ∀ (i : ι), (M i).Indep (Sigma.mk i ⁻¹' I) := by simpa using h.indep
  refine fun i ↦ (hi i).basis_of_maximal_subset (preimage_mono h.subset) fun J hJ hIJ hJX ↦ ?_
  rw [h.eq_of_subset_indep (J := I ∪ Sigma.mk i '' J) ?_ subset_union_left
    (union_subset h.subset (by rwa [image_subset_iff])), preimage_union, preimage_image_sigmaMk]
  · simp
  simp only [sigma_indep_iff, preimage_union]
  intro j
  obtain rfl | hne := eq_or_ne i j
  · exact hJ.subset <| by simpa
  simp [preimage_image_sigmaMk_of_ne hne.symm, hi]

lemma Indep.disjointSigma_iUnion {M : ι → Matroid α} {I : ι → Set α} h
    (hI : ∀ i, (M i).Indep (I i)) : (Matroid.disjointSigma M h).Indep (⋃ i, I i) := by
  rw [disjointSigma_indep_iff, and_iff_left <| iUnion_mono (fun i ↦ (hI i).subset_ground)]
  refine fun i ↦ (hI i).subset ?_
  rw [iUnion_inter, iUnion_subset_iff]
  intro j
  obtain rfl | hne := eq_or_ne i j
  · simp
  simp [((h hne.symm).mono_left (hI j).subset_ground).inter_eq]

lemma Base.disjointSigma_iUnion {M : ι → Matroid α} {B : ι → Set α} h
    (hB : ∀ i, (M i).Base (B i)) : (Matroid.disjointSigma M h).Base (⋃ i, B i) := by
  rw [disjointSigma_base_iff, and_iff_left <| iUnion_mono (fun i ↦ (hB i).subset_ground)]
  suffices aux : ∀ i, (⋃ j, B j) ∩ (M i).E = B i by
    simp_rw [aux]; assumption
  refine fun i ↦ subset_antisymm ?_ (subset_inter (subset_iUnion _ _) (hB i).subset_ground)
  rw [iUnion_inter, iUnion_subset_iff]
  intro j
  obtain rfl | hne := eq_or_ne i j
  · simp
  simp [((h hne.symm).mono_left (hB j).subset_ground).inter_eq]

lemma Basis.disjointSigma_iUnion {M : ι → Matroid α} {I X : ι → Set α} h
    (hI : ∀ i, (M i).Basis (I i) (X i)) :
    (Matroid.disjointSigma M h).Basis (⋃ i, I i) (⋃ i, X i) := by
  have aux : ∀ (j : ι) {Y : ι → Set α}, (∀ i, Y i ⊆ (M i).E) → (⋃ i, Y i) ∩ (M j).E = Y j := by
    refine fun j Y hj ↦ subset_antisymm ?_ (subset_inter (subset_iUnion _ _) (hj j))
    rw [iUnion_inter, iUnion_subset_iff]
    intro i
    obtain rfl | hne := eq_or_ne i j
    · simp
    simp [((h hne).mono_left (hj i)).inter_eq]
  rw [disjointSigma_basis_iff, and_iff_right (iUnion_mono (fun i ↦ (hI i).subset)),
    and_iff_left (iUnion_mono (fun i ↦ (hI i).subset_ground))]
  intro i
  rw [aux _ (fun i ↦ (hI i).subset_ground), aux _ (fun i ↦ (hI i).indep.subset_ground)]
  apply hI


lemma Indep.disjointSum_indep_union {I J : Set α} {M N : Matroid α} {h} (hI : M.Indep I)
    (hJ : N.Indep J) : (M.disjointSum N h).Indep (I ∪ J) := by
  rw [disjointSum_indep_iff, union_inter_distrib_right, union_inter_distrib_right,
    (h.mono_left hI.subset_ground).inter_eq, (h.symm.mono_left hJ.subset_ground).inter_eq,
    union_empty, empty_union]
  exact ⟨hI.subset inter_subset_left, hJ.subset inter_subset_left,
    union_subset_union hI.subset_ground hJ.subset_ground⟩

lemma Base.disjointSum_base_union {B B' : Set α} {M N : Matroid α} {h} (hB : M.Base B)
    (hB' : N.Base B') : (M.disjointSum N h).Base (B ∪ B') := by
  rw [disjointSum_base_iff, union_inter_distrib_right, union_inter_distrib_right,
    (h.mono_left hB.subset_ground).inter_eq, (h.symm.mono_left hB'.subset_ground).inter_eq,
    union_empty, empty_union, inter_eq_self_of_subset_left hB.subset_ground,
    inter_eq_self_of_subset_left hB'.subset_ground]
  exact ⟨hB, hB', union_subset_union hB.subset_ground hB'.subset_ground⟩

lemma Basis.disjointSum_basis_union {I J X Y : Set α} {M N : Matroid α} (hIX : M.Basis I X)
    (hJY : N.Basis J Y) (h) : (M.disjointSum N h).Basis (I ∪ J) (X ∪ Y) := by
  rw [disjointSum_basis_iff, union_inter_distrib_right, union_inter_distrib_right,
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
