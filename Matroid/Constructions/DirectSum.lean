import Mathlib.Data.Matroid.Map

open Set

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

#check Disjoint.sumSubtypeEmbedding

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

@[simp] lemma iUnion_preimage_image_sigma_mk_eq {ι : Type*} {α : ι → Type*}
    {f : (i : ι) → Set (α i)} {j : ι} : ⋃ i, Sigma.mk j ⁻¹' (Sigma.mk i '' (f i)) = f j := by
  aesop

/-- An indexed collection of matroids on determines a 'direct sum' matroid on the sigma-type. -/
protected def sigma {α : ι → Type*} (M : (i : ι) → Matroid (α i)) : Matroid ((i : ι) × α i) where
  E := ⋃ (i : ι), (Sigma.mk i '' (M i).E)
  Indep I := ∀ i, (M i).Indep (Sigma.mk i ⁻¹' I)
  Base B := ∀ i, (M i).Base (Sigma.mk i ⁻¹' B)

  indep_iff' I := by
    refine ⟨fun h ↦ ?_, fun ⟨B, hB, hIB⟩ i ↦ (hB i).indep.subset (preimage_mono hIB) ⟩
    choose Bs hBs using fun i ↦ (h i).exists_base_superset
    exact ⟨⋃ i, Sigma.mk i '' Bs i, fun i ↦ by simpa using (hBs i).1,
      fun ⟨i, e⟩ he ↦ mem_iUnion.2 ⟨i, mem_image_of_mem (Sigma.mk i) ((hBs i).2 he)⟩⟩

  exists_base := by
    choose B hB using fun i ↦ (M i).exists_base
    refine ⟨⋃ i, Sigma.mk i '' B i, by simpa⟩

  base_exchange B₁ B₂ h₁ h₂ := by
    simp only [mem_diff, Sigma.exists, and_imp, Sigma.forall]
    intro i e he₁ he₂
    have hf_ex := (h₁ i).exchange (h₂ i) ⟨he₁, by simpa⟩
    obtain ⟨f, ⟨hf₁, hf₂⟩, hfB⟩ := hf_ex
    refine ⟨i, f, ⟨hf₁, hf₂⟩, fun j ↦ ?_⟩
    rw [← union_singleton, preimage_union, preimage_diff]
    obtain (rfl | hne) := eq_or_ne i j
    · simpa only [ show ∀ x, {⟨i,x⟩} = Sigma.mk i '' {x} by simp,
        preimage_image_eq _ sigma_mk_injective, union_singleton]
    rw [preimage_singleton_eq_empty.2 (by simpa), preimage_singleton_eq_empty.2 (by simpa),
      diff_empty, union_empty]
    exact h₁ j

  maximality X _ I hI hIX := by
    choose Js hJs using
      fun i ↦ (hI i).subset_basis'_of_subset (preimage_mono (f := Sigma.mk i) hIX)
    refine ⟨⋃ i, Sigma.mk i '' Js i, ?_⟩
    simp only [mem_maximals_setOf_iff, preimage_iUnion, iUnion_preimage_image_sigma_mk_eq,
      iUnion_subset_iff, image_subset_iff, and_imp]
    refine ⟨⟨fun i ↦ (hJs i).1.indep,?_, fun i ↦ (hJs i).1.subset⟩, fun K hK _ hKX hJK ↦ ?_⟩
    · rw [← iUnion_image_preimage_sigma_mk_eq_self (s := I)]
      exact iUnion_mono (fun i ↦ image_subset _ (hJs i).2)
    simp_rw [fun i ↦ (hJs i).1.eq_of_subset_indep (hK i) (hJK i) (preimage_mono hKX)]
    rw [iUnion_image_preimage_sigma_mk_eq_self]

  subset_ground := by
    intro B hB
    rw [← iUnion_image_preimage_sigma_mk_eq_self (s := B)]
    exact iUnion_mono (fun i ↦ image_subset _ (hB i).subset_ground)

@[simp] theorem sigma_indep_iff {α : ι → Type*} {M : (i : ι) → Matroid (α i)}
    {I : Set ((i : ι) × α i)} :
    (Matroid.sigma M).Indep I ↔ ∀ i, (M i).Indep (Sigma.mk i ⁻¹' I) := Iff.rfl

@[simp] theorem sigma_base_iff {α : ι → Type*} {M : (i : ι) → Matroid (α i)}
    {B : Set ((i : ι) × α i)} :
    (Matroid.sigma M).Base B ↔ ∀ i, (M i).Base (Sigma.mk i ⁻¹' B) := Iff.rfl

@[simp] theorem sigma_ground_eq {α : ι → Type*} {M : (i : ι) → Matroid (α i)} :
  (Matroid.sigma M).E = ⋃ (i : ι), (Sigma.mk i '' (M i).E) := rfl

/-- The direct sum of an indexed collection of matroids on `α` with disjoint ground sets,
itself a matroid on `α` -/
protected def sigmaDisjoint (M : ι → Matroid α) (h : PairwiseDisjoint univ (fun i ↦ (M i).E)) :
    Matroid α :=
  (Matroid.sigma (fun i ↦ (M i).restrictSubtype (M i).E)).mapEmbedding h.sigmaSubtypeEmbedding

@[simp] theorem sigmaDisjoint_ground_eq {M : ι → Matroid α}
    (h : PairwiseDisjoint univ (fun i ↦ (M i).E)) :
    (Matroid.sigmaDisjoint M h).E = ⋃ i : ι, (M i).E := by
  ext; simp [Matroid.sigmaDisjoint, mapEmbedding, restrictSubtype]

@[simp] theorem sigma'_indep_iff {M : ι → Matroid α} {h : PairwiseDisjoint univ (fun i ↦ (M i).E)}
    {I : Set α} : (Matroid.sigmaDisjoint M h).Indep I ↔
      (∀ i, (M i).Indep (I ∩ (M i).E)) ∧ I ⊆ ⋃ i : ι, (M i).E := by
  simp [Matroid.sigmaDisjoint, h.sigmaSubtypeEmbedding_preimage]

end Sigma

section Sum

/-- The direct sum of two matroids. -/
@[simps!] def directSum {α : Type u} {β : Type v} (M : Matroid α) (N : Matroid β) :
    Matroid (α ⊕ β) := Matroid.ofExistsMatroid
  (E := (.inl '' M.E) ∪ (.inr '' N.E))
  (Indep := fun I ↦ M.Indep (Sum.inl ⁻¹' I) ∧ N.Indep (Sum.inr ⁻¹' I))
  (hM :=
    let S := Matroid.sigma (Bool.rec (M.mapEquiv Equiv.ulift.symm) (N.mapEquiv Equiv.ulift.symm))
    let e := Equiv.sumEquivSigmaBool (ULift.{v} α) (ULift.{u} β)
    let MS := (S.mapEquiv e.symm).mapEquiv (Equiv.sumCongr Equiv.ulift Equiv.ulift)
    by
    refine ⟨MS, ?_, fun I ↦ ?_⟩
    · simp [Set.ext_iff, MS, e, S, mapEquiv, mapEmbedding, Equiv.ulift, Equiv.sumEquivSigmaBool]
    simp only [MS, e, S, mapEquiv_indep_iff, Equiv.sumCongr_symm, Equiv.sumCongr_apply,
      Equiv.symm_symm, sigma_indep_iff, Bool.forall_bool, Equiv.ulift_apply]
    convert Iff.rfl <;>
    simp [Set.ext_iff, Equiv.ulift, Equiv.sumEquivSigmaBool] )

/-- The direct sum of two matroids on `α` with disjoint ground sets, as a `Matroid α`.
Implemented by mapping a matroid on `M.E ⊕ N.E` into `α`.  -/
@[simps!] def disjointSum (M N : Matroid α) (h : Disjoint M.E N.E) : Matroid α :=
  ((M.restrictSubtype M.E).directSum (N.restrictSubtype N.E)).mapEmbedding h.sumSubtypeEmbedding

@[simp] theorem disjointSum_ground_eq {M N : Matroid α} {h : Disjoint M.E N.E} :
    (M.disjointSum N h).E = M.E ∪ N.E := by
  simp [disjointSum, restrictSubtype, mapEmbedding]

@[simp] theorem disjointSum_indep_iff {M N : Matroid α} {h : Disjoint M.E N.E} {I : Set α} :
    (M.disjointSum N h).Indep I ↔ M.Indep (I ∩ M.E) ∧ N.Indep (I ∩ N.E) ∧ I ⊆ M.E ∪ N.E := by
  simp [disjointSum, and_assoc]

theorem Indep.eq_union_image_of_disjointSum {M N : Matroid α} {h : Disjoint M.E N.E}
    {I : Set α} (hI : (disjointSum M N h).Indep I) :
    ∃ IM IN, M.Indep IM ∧ N.Indep IN ∧ Disjoint IM IN ∧ I = IM ∪ IN := by
  rw [disjointSum_indep_iff] at hI
  refine ⟨I ∩ M.E, I ∩ N.E, hI.1, hI.2.1, h.mono inf_le_right inf_le_right, ?_⟩
  rw [← inter_union_distrib_left, inter_eq_self_of_subset_left hI.2.2]

end Sum

end Matroid
