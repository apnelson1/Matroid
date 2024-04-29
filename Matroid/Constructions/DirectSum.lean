import Matroid.Map

open Set BigOperators Set.Notation

universe u v

variable {α β ι : Type*}

-- a little API for mathlib.

/-- For disjoint `s t : Set α`, the natural injection from `↑s ⊕ ↑t` to `α`. -/
@[simps] def Disjoint.sumSubtypeEmbedding {s t : Set α} (h : Disjoint s t) : s ⊕ t ↪ α where
  toFun := Sum.elim Subtype.val Subtype.val
  inj' := by
    rintro (⟨a,ha⟩ | ⟨a,ha⟩) (⟨b,hb⟩ | ⟨b,hb⟩)
    · simp [Subtype.val_inj]
    · simpa using h.ne_of_mem ha hb
    · simpa using h.symm.ne_of_mem ha hb
    simp [Subtype.val_inj]

@[simp] theorem Disjoint.sumSubtypeEmbedding_preimage_inl {s t r : Set α} (h : Disjoint s t) :
    .inl ⁻¹' (h.sumSubtypeEmbedding ⁻¹' r) = r ∩ s := by
  ext; simp

@[simp] theorem Disjoint.sumSubtypeEmbedding_preimage_inr {s t r : Set α} (h : Disjoint s t) :
    .inr ⁻¹' (h.sumSubtypeEmbedding ⁻¹' r) = r ∩ t := by
  ext; simp

@[simp] theorem Disjoint.sumSubtypeEmbedding_range {s t : Set α} (h : Disjoint s t) :
    range h.sumSubtypeEmbedding = s ∪ t := by
  ext; simp

/-- For an indexed family `s` of disjoint sets in `α`, the natural injection from the
sigma-type `(i : ι) × ↑(s i)` to `α`. -/
@[simps] def Set.PairwiseDisjoint.sigmaSubtypeEmbedding {s : ι → Set α}
    (h : PairwiseDisjoint univ s) : ((i : ι) × (s i)) ↪ α where
      toFun := fun ⟨i, x⟩ ↦ x.1
      inj' := by
        rintro ⟨i,x⟩ ⟨j,y⟩ (hxy : x.1 = y.1)
        obtain rfl : i = j := Set.PairwiseDisjoint.elim h (mem_univ i) (mem_univ j)
          (not_disjoint_iff.2 ⟨x.1,x.2, by rw [hxy]; exact y.2⟩)
        rw [Subtype.val_inj] at hxy
        rw [hxy]

@[simp] theorem Set.PairwiseDisjoint.sigmaSubtypeEmbedding_preimage {s : ι → Set α}
    (h : PairwiseDisjoint univ s) (i : ι) (r : Set α) :
    Sigma.mk i ⁻¹' (h.sigmaSubtypeEmbedding ⁻¹' r) = r ∩ (s i) := by
  ext; simp

@[simp] theorem Set.PairwiseDisjoint.sigmaSubtypeEmbedding_range {s : ι → Set α}
    (h : PairwiseDisjoint univ s) : Set.range h.sigmaSubtypeEmbedding = ⋃ i : ι, s i := by
  ext; simp

namespace Matroid

section Sigma

/-- We prove that the direct sum of an indexed collection of matroids is a matroid
  by constructing an `IndepMatroid`.
  (Probably proving this is actually easier than defining the direct sum of matroids on two types,
  since it lets you abstract 'left' and 'right'.) -/
private def sigmaIndepMatroid {α : ι → Type*} (M : (i : ι) → Matroid (α i)) :
    IndepMatroid ((i : ι) × α i) where
      E := ⋃ (i : ι), (Sigma.mk i '' (M i).E)
      Indep I := ∀ i, (M i).Indep (Sigma.mk i ⁻¹' I)
      indep_empty := by simp
      indep_subset := sorry
      indep_aug := sorry
      indep_maximal := sorry
      subset_ground := sorry

/-- An indexed collection of matroids on arbitrary types determines a 'direct sum' matroid
on the sigma-type. -/
def sigma {α : ι → Type*} (M : (i : ι) → Matroid (α i)) : Matroid ((i : ι) × α i) :=
  (sigmaIndepMatroid M).matroid

@[simp] theorem sigma_indep_iff {α : ι → Type*} {M : (i : ι) → Matroid (α i)}
    {I : Set ((i : ι) × α i)} : (sigma M).Indep I ↔ ∀ i, (M i).Indep (Sigma.mk i ⁻¹' I) := by
  simp [sigma, sigmaIndepMatroid]

@[simp] theorem sigma_ground_eq {α : ι → Type*} {M : (i : ι) → Matroid (α i)} :
  (sigma M).E = ⋃ (i : ι), (Sigma.mk i '' (M i).E) := rfl

/-- The direct sum of an indexed collection of matroids on `α` with disjoint ground sets. -/
def sigma' (M : ι → Matroid α) (h : PairwiseDisjoint univ (fun i ↦ (M i).E)) : Matroid α :=
  (sigma (fun i ↦ (M i).restrictSubtype (M i).E)).mapEmbedding h.sigmaSubtypeEmbedding

@[simp] theorem sigma'_ground_eq {M : ι → Matroid α} (h : PairwiseDisjoint univ (fun i ↦ (M i).E)) :
    (sigma' M h).E = ⋃ i : ι, (M i).E := by
  ext; simp [sigma', mapEmbedding, restrictSubtype]

@[simp] theorem sigma'_indep_iff {M : ι → Matroid α} {h : PairwiseDisjoint univ (fun i ↦ (M i).E)}
    {I : Set α} :
    (sigma' M h).Indep I ↔ (∀ i, (M i).Indep (I ∩ (M i).E)) ∧ I ⊆ ⋃ i : ι, (M i).E := by
  simp [sigma', h.sigmaSubtypeEmbedding_preimage]

end Sigma

section Sum

/-- The direct sum of two matroids. Defined in terms of `Matroid.sigma` and
``Equiv.sumEquivSigmaBool`, which requires handling some universe issues with `ULift`. -/
def directSum {α : Type u} {β : Type v} (M : Matroid α) (N : Matroid β) : Matroid (α ⊕ β) :=
  let S := Matroid.sigma (Bool.rec (M.mapEquiv Equiv.ulift.symm) (N.mapEquiv Equiv.ulift.symm))
  let e := Equiv.sumEquivSigmaBool (ULift.{v} α) (ULift.{u} β)
  let S' := S.mapEquiv e.symm
  S'.mapEquiv (Equiv.sumCongr Equiv.ulift Equiv.ulift)

/-- Because of this simp lemma, the ugly universe stuff in the implementation of `directSum`
doesn't matter. -/
@[simp] theorem directSum_indep_iff {M : Matroid α} {N : Matroid β} {I : Set (α ⊕ β)} :
    (M.directSum N).Indep I ↔ M.Indep (.inl ⁻¹' I) ∧ N.Indep (.inr ⁻¹' I) := by
  simp only [directSum, mapEquiv_indep_iff, Equiv.sumCongr_symm, Equiv.sumCongr_apply,
    Equiv.symm_symm, sigma_indep_iff, Bool.forall_bool, Equiv.ulift_apply]
  convert Iff.rfl <;> ext <;> simp [Equiv.ulift, Equiv.sumEquivSigmaBool]

@[simp] theorem directSum_ground_eq (M : Matroid α) (N : Matroid β) :
    (M.directSum N).E = (.inl '' M.E) ∪ (.inr '' N.E) := by
  ext; simp [directSum, mapEquiv, mapEmbedding, Equiv.ulift, Equiv.sumEquivSigmaBool]

/-- The direct sum of two matroids on `α` with disjoint ground sets, as a `Matroid α`.
Implemented by mapping a matroid on `M.E ⊕ N.E` into `α`.  -/
def directSum' (M N : Matroid α) (h : Disjoint M.E N.E) : Matroid α :=
  ((M.restrictSubtype M.E).directSum (N.restrictSubtype N.E)).mapEmbedding h.sumSubtypeEmbedding

@[simp] theorem directSum'_ground_eq {M N : Matroid α} {h : Disjoint M.E N.E} :
    (M.directSum' N h).E = M.E ∪ N.E := by
  simp [directSum', restrictSubtype, mapEmbedding]

@[simp] theorem directSum'_indep_iff {M N : Matroid α} {h : Disjoint M.E N.E} {I : Set α} :
    (M.directSum' N h).Indep I ↔ M.Indep (I ∩ M.E) ∧ N.Indep (I ∩ N.E) ∧ I ⊆ M.E ∪ N.E := by
  simp [directSum', and_assoc]

theorem Indep.eq_union_image_of_directSum {M N : Matroid α} {h : Disjoint M.E N.E}
    {I : Set α} (hI : (directSum' M N h).Indep I) :
    ∃ IM IN, M.Indep IM ∧ N.Indep IN ∧ Disjoint IM IN ∧ I = IM ∪ IN := by
  rw [directSum'_indep_iff] at hI
  refine ⟨I ∩ M.E, I ∩ N.E, hI.1, hI.2.1, h.mono inf_le_right inf_le_right, ?_⟩
  rw [← inter_union_distrib_left, inter_eq_self_of_subset_left hI.2.2]

end Sum

end Matroid
