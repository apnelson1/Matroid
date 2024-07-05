import Mathlib.Data.Matroid.Map
import Matroid.ForMathlib.MatroidBasic

open Set Set.Notation

universe u v

variable {α β ι : Type*}

-- a little API for mathlib.

section Disjoint

variable {α ι : Type*} {s t r : Set α}

/-- For disjoint `s t : Set α`, the natural injection from `↑s ⊕ ↑t` to `α`. -/
@[simps] def Disjoint.sumSubtypeEmbedding (h : Disjoint s t) : s ⊕ t ↪ α where
  toFun := Sum.elim (↑) (↑)
  inj' := by
    rintro (⟨a, ha⟩ | ⟨a, ha⟩) (⟨b, hb⟩ | ⟨b, hb⟩)
    · simp [Subtype.val_inj]
    · simpa using h.ne_of_mem ha hb
    · simpa using h.symm.ne_of_mem ha hb
    simp [Subtype.val_inj]

@[simp] theorem Disjoint.sumSubtypeEmbedding_preimage_inl (h : Disjoint s t) :
    .inl ⁻¹' (h.sumSubtypeEmbedding ⁻¹' r) = r ∩ s := by
  ext
  simp

@[simp] theorem Disjoint.sumSubtypeEmbedding_preimage_inr {s t r : Set α} (h : Disjoint s t) :
    .inr ⁻¹' (h.sumSubtypeEmbedding ⁻¹' r) = r ∩ t := by
  ext
  simp

@[simp] theorem Disjoint.sumSubtypeEmbedding_range {s t : Set α} (h : Disjoint s t) :
    range h.sumSubtypeEmbedding = s ∪ t := by
  ext
  simp



/-- For an indexed family `s : ι → Set α` of disjoint sets,
the natural injection from the sigma-type `(i : ι) × ↑(s i)` to `α`. -/
@[simps] def Pairwise.disjointSigmaSubtypeEmbedding {s : ι → Set α} (h : Pairwise (Disjoint on s)) :
    (i : ι) × s i ↪ α where
  toFun x := x.2.1
  inj' := by
    rintro ⟨i,⟨x,hx⟩⟩ ⟨j,⟨-,hx'⟩⟩ rfl
    obtain rfl : i = j := h.eq (not_disjoint_iff.2 ⟨_, hx, hx'⟩)
    rfl

@[simp] theorem Pairwise.disjointSigmaSubtypeEmbedding_preimage {s : ι → Set α}
    (h : Pairwise (Disjoint on s)) (i : ι) (r : Set α) :
    Sigma.mk i ⁻¹' (h.disjointSigmaSubtypeEmbedding ⁻¹' r) = r ∩ s i := by
  ext
  simp

@[simp] theorem Pairwise.dijsointSigmaSubtypeEmbedding_range {s : ι → Set α}
    (h : Pairwise (Disjoint on s)) : Set.range h.disjointSigmaSubtypeEmbedding = ⋃ i, s i := by
  ext
  simp

end Disjoint
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
  (Matroid.sigma M).E = ⋃ i, (Sigma.mk i '' (M i).E) := rfl

theorem sigma_basis_iff {α : ι → Type*} {M : (i : ι) → Matroid (α i)} {I X : Set ((i : ι) × α i)} :
    (Matroid.sigma M).Basis I X ↔ ∀ i, (M i).Basis (Sigma.mk i ⁻¹' I) (Sigma.mk i ⁻¹' X) := by
  simp only [Basis, sigma_indep_iff, mem_maximals_iff, mem_setOf_eq, and_imp, and_assoc,
    sigma_ground_eq, forall_and, and_congr_right_iff]
  refine fun hI ↦ ⟨fun ⟨hIX, h, h'⟩ ↦ ⟨fun i ↦ preimage_mono hIX, fun i I₀ hI₀ hI₀X hII₀ ↦ ?_, ?_⟩,
    fun ⟨hIX, h', h''⟩ ↦ ⟨?_, ?_, ?_⟩⟩
  · refine hII₀.antisymm ?_
    specialize h (y := I ∪ Sigma.mk i '' I₀)
    simp only [preimage_union, union_subset_iff, hIX, image_subset_iff, hI₀X, and_self,
      subset_union_left, true_implies] at h
    rw [h, preimage_union, sigma_mk_preimage_image_eq_self]
    · exact subset_union_right
    intro j
    obtain (rfl | hij) := eq_or_ne i j
    · rwa [sigma_mk_preimage_image_eq_self, union_eq_self_of_subset_left hII₀]
    rw [sigma_mk_preimage_image' hij, union_empty]
    apply hI
  · exact fun i ↦ by simpa using preimage_mono (f := Sigma.mk i) h'
  · exact fun ⟨i, x⟩ hx ↦ by simpa using hIX i hx
  · refine fun J hJ hJX hIJ ↦ hIJ.antisymm fun ⟨i,x⟩ hx ↦ ?_
    simpa using (h' i (hJ i) (preimage_mono hJX) (preimage_mono hIJ)).symm.subset hx
  exact fun ⟨i,x⟩ hx ↦ mem_iUnion_of_mem i <| by simpa using h'' i hx

theorem Finitary.sigma {α : ι → Type*} {M : (i : ι) → Matroid (α i)} (h : ∀ i, (M i).Finitary) :
    (Matroid.sigma M).Finitary := by
  refine ⟨fun I hI ↦ ?_⟩
  simp only [sigma_indep_iff] at hI ⊢
  intro i
  apply indep_of_forall_finite_subset_indep
  intro J hJI hJ
  convert hI (Sigma.mk i '' J) (by simpa) (hJ.image _) i
  rw [sigma_mk_preimage_image_eq_self]

/-- Given an indexed family `Ms : ι → Matroid α` of matroids on the same type, the direct
sum of these matroids as a matroid on the product type `ι × α`. -/
protected def prod {α ι : Type*} (Ms : ι → Matroid α) : Matroid (ι × α) :=
  (Matroid.sigma Ms).mapEquiv <| Equiv.sigmaEquivProd ι α

@[simp] theorem prod_indep_iff {α ι : Type*} (Ms : ι → Matroid α) (I : Set (ι × α)) :
    (Matroid.prod Ms).Indep I ↔ ∀ i, (Ms i).Indep (Prod.mk i ⁻¹' I) := by
  simp only [Matroid.prod, mapEquiv_indep_iff, Equiv.sigmaEquivProd_symm_apply, sigma_indep_iff]
  convert Iff.rfl
  ext
  simp

@[simp] theorem prod_ground_eq {α ι : Type*} (Ms : ι → Matroid α) :
    (Matroid.prod Ms).E = ⋃ i, Prod.mk i '' (Ms i).E := by
  ext
  simp [Matroid.prod]

theorem Finitary.prod {α ι : Type*} (Ms : ι → Matroid α) (h : ∀ i, (Ms i).Finitary) :
    (Matroid.prod Ms).Finitary := by
  have := Finitary.sigma h
  rw [Matroid.prod]
  infer_instance

/-- The direct sum of an indexed collection of matroids on `α` with disjoint ground sets,
itself a matroid on `α` -/
protected def sigmaDisjoint (M : ι → Matroid α) (h : Pairwise (Disjoint on fun i ↦ (M i).E)) :
    Matroid α :=
  (Matroid.sigma (fun i ↦ (M i).restrictSubtype (M i).E)).mapEmbedding
    h.disjointSigmaSubtypeEmbedding

@[simp] theorem sigmaDisjoint_ground_eq {M : ι → Matroid α} (h) :
    (Matroid.sigmaDisjoint M h).E = ⋃ i : ι, (M i).E := by
  ext; simp [Matroid.sigmaDisjoint, mapEmbedding, restrictSubtype]

@[simp] theorem sigma'_indep_iff {M : ι → Matroid α} {h}
    {I : Set α} : (Matroid.sigmaDisjoint M h).Indep I ↔
      (∀ i, (M i).Indep (I ∩ (M i).E)) ∧ I ⊆ ⋃ i : ι, (M i).E := by
  simp [Matroid.sigmaDisjoint, h.disjointSigmaSubtypeEmbedding_preimage]


end Sigma

section Sum

variable {α : Type u} {β : Type v}

/-- An auxiliary matroid that is propositionally but not definitionally equal to the direct sum. -/
def directSum_aux (M : Matroid α) (N : Matroid β) : Matroid (α ⊕ β) :=
  let S := Matroid.sigma (Bool.rec (M.mapEquiv Equiv.ulift.symm) (N.mapEquiv Equiv.ulift.symm))
  let e := Equiv.sumEquivSigmaBool (ULift.{v} α) (ULift.{u} β)
  (S.mapEquiv e.symm).mapEquiv (Equiv.sumCongr Equiv.ulift Equiv.ulift)

lemma directSum_ground_aux (M : Matroid α) (N : Matroid β) :
    (directSum_aux M N).E = (.inl '' M.E) ∪ (.inr '' N.E) := by
  simp [directSum_aux, Set.ext_iff, mapEquiv, mapEmbedding, Equiv.ulift, Equiv.sumEquivSigmaBool]

lemma directSum_indep_aux (M : Matroid α) (N : Matroid β) {I : Set (α ⊕ β)} :
    (directSum_aux M N).Indep I ↔ M.Indep (Sum.inl ⁻¹' I) ∧ N.Indep (Sum.inr ⁻¹' I) := by
  simp only [directSum_aux, mapEquiv_indep_iff, Equiv.sumCongr_symm, Equiv.sumCongr_apply,
    Equiv.symm_symm, sigma_indep_iff, Bool.forall_bool, Equiv.ulift_apply]
  convert Iff.rfl <;>
    simp [Set.ext_iff, Equiv.ulift, Equiv.sumEquivSigmaBool]

/-- The direct sum of two matroids. -/
@[simps!] def directSum (M : Matroid α) (N : Matroid β) : Matroid (α ⊕ β) :=
  Matroid.ofExistsMatroid
  (E := (.inl '' M.E) ∪ (.inr '' N.E))
  (Indep := fun I ↦ M.Indep (Sum.inl ⁻¹' I) ∧ N.Indep (Sum.inr ⁻¹' I))
  (hM := ⟨_, (directSum_ground_aux M N).symm, fun _ ↦ directSum_indep_aux M N⟩)

lemma directSum_eq_aux (M : Matroid α) (N : Matroid β) : directSum M N = directSum_aux M N :=
  eq_of_indep_iff_indep_forall (by simp [directSum, directSum_ground_aux])
    (fun I _ ↦ by simp [directSum, directSum_indep_aux, Matroid.ofExistsMatroid])

lemma directSum_basis_iff {M : Matroid α} {N : Matroid β} {I X : Set (α ⊕ β)} :
    (M.directSum N).Basis I X ↔
      (M.Basis (Sum.inl ⁻¹' I) (Sum.inl ⁻¹' X) ∧ N.Basis (Sum.inr ⁻¹' I) (Sum.inr ⁻¹' X)) := by
  simp only [directSum_eq_aux, directSum_aux, mapEquiv_basis_iff, Equiv.sumCongr_symm,
    Equiv.sumCongr_apply, Equiv.symm_symm, sigma_basis_iff, Bool.forall_bool, Equiv.ulift_apply,
    Equiv.sumEquivSigmaBool, Equiv.coe_fn_mk, Equiv.ulift]
  convert Iff.rfl
  all_goals
  · ext; simp

/-- The direct sum of two matroids on `α` with disjoint ground sets, as a `Matroid α`.
Implemented by mapping a matroid on `M.E ⊕ N.E` into `α`.  -/
def disjointSum (M N : Matroid α) (h : Disjoint M.E N.E) : Matroid α :=
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

lemma disjointSum_basis_iff {M N : Matroid α} {hdj : Disjoint M.E N.E} {I X : Set α} :
    (M.disjointSum N hdj).Basis I X ↔ M.Basis (I ∩ M.E) (X ∩ M.E) ∧ N.Basis (I ∩ N.E) (X ∩ N.E)
      ∧ I ⊆ M.E ∪ N.E ∧ X ⊆ M.E ∪ N.E := by
  simp only [disjointSum, mapEmbedding, restrictSubtype, restrict_ground_eq_self, map_basis_iff',
    directSum_basis_iff, comap_basis_iff, and_iff_right (Subtype.val_injective.injOn)]

  refine ⟨fun h ↦ ?_, fun ⟨hl, hr, hI, hX⟩ ↦ ?_⟩
  · obtain ⟨I, X, ⟨⟨hl, -⟩,⟨hr, -⟩⟩, rfl, rfl⟩ := h
    simp_rw [← hdj.sumSubtypeEmbedding_preimage_inl, ← hdj.sumSubtypeEmbedding_preimage_inr]
    simp_rw [preimage_image_eq _ hdj.sumSubtypeEmbedding.injective]
    refine ⟨hl, hr, ?_⟩
    simp only [Disjoint.sumSubtypeEmbedding_apply, image_subset_iff, preimage_union]
    constructor
    all_goals
    · rintro (⟨x, h⟩ | ⟨y, h⟩)
      <;> simp [h]
  have hIX : I ⊆ X := by
    convert union_subset_union hl.subset hr.subset <;>
    rwa [← inter_union_distrib_left, eq_comm, inter_eq_left]
  use (Sum.inl '' (M.E ↓∩ I) ∪ Sum.inr '' (N.E ↓∩ I))
  use (Sum.inl '' (M.E ↓∩ X) ∪ Sum.inr '' (N.E ↓∩ X))
  simp only [preimage_union, preimage_image_eq _ Sum.inl_injective, preimage_inl_image_inr,
    union_empty, Subtype.image_preimage_coe, inter_comm M.E, hl, preimage_mono hIX, and_self,
    preimage_inr_image_inl, preimage_image_eq _ Sum.inr_injective, empty_union, inter_comm N.E, hr,
    Disjoint.sumSubtypeEmbedding_apply, true_and]
  simp [image_union, image_image, ← union_inter_distrib_right, hX, hIX.trans hX]













end Sum

end Matroid
