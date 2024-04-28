import Matroid.Constructions.Map

open Set BigOperators Set.Notation

universe u v

variable {α β ι : Type*}

-- a little API for mathlib.

/-- If `s` and `t` are disjoint sets in `α`, there is a natural injection from `s ⊕ t` to `α`. -/
@[simps] def Disjoint.sumElimValEmbedding {s t : Set α} (h : Disjoint s t) : s ⊕ t ↪ α where
  toFun := Sum.elim Subtype.val Subtype.val
  inj' := by
    rintro (⟨a,ha⟩ | ⟨a,ha⟩) (⟨b,hb⟩ | ⟨b,hb⟩)
    · simp [Subtype.val_inj]
    · simpa using h.ne_of_mem ha hb
    · simpa using h.symm.ne_of_mem ha hb
    simp [Subtype.val_inj]

@[simp] theorem Disjoint.sumElimValEmbedding_preimage_inl {s t r : Set α} (h : Disjoint s t) :
    .inl ⁻¹' (h.sumElimValEmbedding ⁻¹' r) = r ∩ s := by
  ext; simp

@[simp] theorem Disjoint.sumElimValEmbedding_preimage_inr {s t r : Set α} (h : Disjoint s t) :
    .inr ⁻¹' (h.sumElimValEmbedding ⁻¹' r) = r ∩ t := by
  ext; simp

@[simp] theorem Disjoint.sumElimValEmbedding_range {s t : Set α} (h : Disjoint s t) :
    range h.sumElimValEmbedding = s ∪ t := by
  ext; simp

namespace Matroid

/-- We prove that the direct sum of an indexed collection of matroids is a matroid
  by constructing an `IndepMatroid`.
  (Probably proving this is actually easier than defining the direct sum of matroids on two types,
  since it lets you abstract 'left' and right.) -/
private def sigmaIndepMatroid {α : ι → Type*} (M : (i : ι) → Matroid (α i)) :
    IndepMatroid ((i : ι) × α i) where
      E := ⋃ (i : ι), (Sigma.mk i '' (M i).E)
      Indep I := ∀ i, (M i).Indep (Sigma.mk i ⁻¹' I)
      indep_empty := by simp
      indep_subset := sorry
      indep_aug := sorry
      indep_maximal := sorry
      subset_ground := sorry

/-- An indexed collection of matroids on arbitrary types determines a
  'direct sum' matroid on the sigma-type. -/
def sigma {α : ι → Type*} (M : (i : ι) → Matroid (α i)) : Matroid ((i : ι) × α i) :=
  (sigmaIndepMatroid M).matroid

@[simp] theorem sigma_indep_iff {α : ι → Type*} {M : (i : ι) → Matroid (α i)}
    {I : Set ((i : ι) × α i)} : (sigma M).Indep I ↔ ∀ i, (M i).Indep (Sigma.mk i ⁻¹' I) := by
  simp [sigma, sigmaIndepMatroid]

@[simp] theorem sigma_ground_eq {α : ι → Type*} {M : (i : ι) → Matroid (α i)} :
  (sigma M).E = ⋃ (i : ι), (Sigma.mk i '' (M i).E) := rfl

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

/-- Applying this map to the direct sum of the 'subtype' version of `M` and `N` gives a
  direct sum within the type `α`, provided `M` and `N` have disjoint ground sets.   -/
def directSum' (M N : Matroid α) (h : Disjoint M.E N.E) : Matroid α :=
  ((M.onSubtype M.E).directSum (N.onSubtype N.E)).mapEmbedding h.sumElimValEmbedding

@[simp] theorem directSum'_ground_eq {M N : Matroid α} {h : Disjoint M.E N.E} :
    (M.directSum' N h).E = M.E ∪ N.E := by
  simp [directSum', onSubtype, mapEmbedding]

@[simp] theorem directSum'_indep_iff {M N : Matroid α} {h : Disjoint M.E N.E} {I : Set α} :
    (M.directSum' N h).Indep I ↔ M.Indep (I ∩ M.E) ∧ N.Indep (I ∩ N.E) ∧ I ⊆ M.E ∪ N.E := by
  simp [directSum', and_assoc]

-- TODO - direct sum of arbitrary indexed collections of matroids on the same type
-- with `PairwiseDisjoint` ground sets.

end Matroid
