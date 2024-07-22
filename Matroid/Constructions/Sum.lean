import Mathlib.Data.Matroid.Map
import Matroid.ForMathlib.MatroidMap
import Mathlib.Logic.Embedding.Set
-- import Matroid.ForMathlib.Logic_Embedding_Set

open Set

universe u v

namespace Matroid

section Sigma

variable {ι : Type*} {α : ι → Type*} {M : (i : ι) → Matroid (α i)}


theorem sigma_subset_sigma_iff {s t : (i : ι) → Set (α i)} {a b : Set ι} :
    a.sigma s ⊆ b.sigma t ↔ ∀ i ∈ a, (s i).Nonempty → i ∈ b ∧ s i ⊆ t i := by
  simp only [subset_def, mem_sigma_iff, and_imp, Sigma.forall, Set.Nonempty, forall_exists_index]
  exact ⟨fun h i hia x hx ↦ ⟨(h _ _ hia hx).1, fun y hy ↦ (h _ _ hia hy).2⟩,
    fun h i x hi hx ↦ ⟨(h i hi x hx).1, (h i hi x hx).2 x hx⟩⟩

theorem sigma_subset_sigma_iff' {s t : (i : ι) → Set (α i)} {a b : Set ι} (hab : a ⊆ b) :
    a.sigma s ⊆ b.sigma t ↔ ∀ i ∈ a, s i ⊆ t i := by
  simp_rw [sigma_subset_sigma_iff]
  refine ⟨fun h i hia ↦ ?_, fun h i hia _ ↦ ⟨hab hia, h i hia⟩⟩
  obtain hi | hi := (s i).eq_empty_or_nonempty
  · simp [hi]
  exact ((h i hia) hi).2

@[simp] theorem univ_sigma_preimage (s : Set (Σ i, α i)) :
    (@univ ι).sigma (fun i ↦ Sigma.mk i ⁻¹' s) = s :=
  ext <| by simp

/-- An indexed collection of matroids on determines a 'direct sum' matroid on the sigma-type. -/
protected def sigma (M : (i : ι) → Matroid (α i)) : Matroid ((i : ι) × α i) where
  E := univ.sigma (fun i ↦ (M i).E)
  Indep I := ∀ i, (M i).Indep (Sigma.mk i ⁻¹' I)
  Base B := ∀ i, (M i).Base (Sigma.mk i ⁻¹' B)

  indep_iff' I := by
    refine ⟨fun h ↦ ?_, fun ⟨B, hB, hIB⟩ i ↦ (hB i).indep.subset (preimage_mono hIB)⟩
    choose Bs hBs using fun i ↦ (h i).exists_base_superset
    refine ⟨univ.sigma Bs, fun i ↦ by simpa using (hBs i).1, ?_⟩
    rw [← univ_sigma_preimage I, sigma_subset_sigma_iff' Subset.rfl]
    exact fun i _ ↦ (hBs i).2

  exists_base := by
    choose B hB using fun i ↦ (M i).exists_base
    exact ⟨univ.sigma B, by simpa⟩

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

    use univ.sigma Js

    simp only [mem_maximals_setOf_iff, mem_univ, mk_preimage_sigma, and_imp,
      sigma_subset_sigma_iff' Subset.rfl, true_implies]
    refine ⟨⟨fun i ↦ (hJs i).1.indep, ⟨?_, ?_⟩⟩, fun S hS _ hSX h ↦ ?_⟩
    · rw [← univ_sigma_preimage I, sigma_subset_sigma_iff' Subset.rfl]
      exact fun i _ ↦ (hJs i).2
    · rw [← univ_sigma_preimage X, sigma_subset_sigma_iff' Subset.rfl]
      exact fun i _ ↦ (hJs i).1.subset
    rw [← univ_sigma_preimage S] at h ⊢
    rw [sigma_subset_sigma_iff' rfl.subset] at h
    convert rfl with i
    rw [(hJs i).1.eq_of_subset_indep (hS i) (h i <| mem_univ i)]
    exact preimage_mono hSX

  subset_ground B hB := by
    rw [← univ_sigma_preimage B]
    apply sigma_mono Subset.rfl fun i ↦ (hB i).subset_ground

@[simp] lemma sigma_indep_iff {I} :
    (Matroid.sigma M).Indep I ↔ ∀ i, (M i).Indep (Sigma.mk i ⁻¹' I) := Iff.rfl

@[simp] lemma sigma_base_iff {B} :
    (Matroid.sigma M).Base B ↔ ∀ i, (M i).Base (Sigma.mk i ⁻¹' B) := Iff.rfl

@[simp] lemma sigma_ground_eq : (Matroid.sigma M).E = univ.sigma fun i ↦ (M i).E := rfl

@[simp] lemma sigma_basis_iff {I X} :
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
  exact fun ⟨i,x⟩ hx ↦ by simpa using h'' i hx

lemma Finitary.sigma (h : ∀ i, (M i).Finitary) : (Matroid.sigma M).Finitary := by
  refine ⟨fun I hI ↦ ?_⟩
  simp only [sigma_indep_iff] at hI ⊢
  intro i
  apply indep_of_forall_finite_subset_indep
  intro J hJI hJ
  convert hI (Sigma.mk i '' J) (by simpa) (hJ.image _) i
  rw [sigma_mk_preimage_image_eq_self]

end Sigma

section Prod

variable {α ι : Type*} {Ms : ι → Matroid α}

/-- Given an indexed family `Ms : ι → Matroid α` of matroids on the same type, the direct
sum of these matroids as a matroid on the product type `ι × α`. -/
protected def prod (Ms : ι → Matroid α) : Matroid (ι × α) :=
  (Matroid.sigma Ms).mapEquiv <| Equiv.sigmaEquivProd ι α

@[simp] lemma prod_indep_iff {I} :
    (Matroid.prod Ms).Indep I ↔ ∀ i, (Ms i).Indep (Prod.mk i ⁻¹' I) := by
  simp only [Matroid.prod, mapEquiv_indep_iff, Equiv.sigmaEquivProd_symm_apply, sigma_indep_iff]
  convert Iff.rfl
  ext
  simp

@[simp] lemma prod_ground_eq (Ms : ι → Matroid α) :
    (Matroid.prod Ms).E = ⋃ i, Prod.mk i '' (Ms i).E := by
  ext
  simp [Matroid.prod]

lemma Finitary.prod (h : ∀ i, (Ms i).Finitary) : (Matroid.prod Ms).Finitary := by
  have := Finitary.sigma h
  rw [Matroid.prod]
  infer_instance

/-- The direct sum of an indexed collection of matroids on `α` with disjoint ground sets,
itself a matroid on `α` -/
protected def sigmaDisjoint (Ms : ι → Matroid α) (h : Pairwise (Disjoint on fun i ↦ (Ms i).E)) :
    Matroid α :=
  (Matroid.sigma (fun i ↦ (Ms i).restrictSubtype (Ms i).E)).mapEmbedding
    (Function.Embedding.sigmaSet h)

@[simp] lemma sigmaDisjoint_ground_eq {h} : (Matroid.sigmaDisjoint Ms h).E = ⋃ i : ι, (Ms i).E := by
  ext; simp [Matroid.sigmaDisjoint, mapEmbedding, restrictSubtype]

@[simp] lemma sigmaDisjoint_indep_iff {h I} :
    (Matroid.sigmaDisjoint Ms h).Indep I ↔
      (∀ i, (Ms i).Indep (I ∩ (Ms i).E)) ∧ I ⊆ ⋃ i, (Ms i).E := by
  simp [Matroid.sigmaDisjoint, (Function.Embedding.sigmaSet_preimage h)]

@[simp] lemma sigmaDisjoint_base_iff {h B} :
    (Matroid.sigmaDisjoint Ms h).Base B ↔
      (∀ i, (Ms i).Base (B ∩ (Ms i).E)) ∧ B ⊆ ⋃ i, (Ms i).E := by
  simp [Matroid.sigmaDisjoint, (Function.Embedding.sigmaSet_preimage h)]

@[simp] lemma sigmaDisjoint_basis_iff {h I X} :
    (Matroid.sigmaDisjoint Ms h).Basis I X ↔
      (∀ i, (Ms i).Basis (I ∩ (Ms i).E) (X ∩ (Ms i).E)) ∧ I ⊆ X ∧ X ⊆ ⋃ i, (Ms i).E := by
  simp [Matroid.sigmaDisjoint, Function.Embedding.sigmaSet_preimage h]

end Prod

section Sum

variable {α : Type u} {β : Type v} {M N : Matroid α}

/-- The direct sum of two matroids as a matroid on the sum type. -/
protected def sum (M : Matroid α) (N : Matroid β) : Matroid (α ⊕ β) :=
  let S := Matroid.sigma (Bool.rec (M.mapEquiv Equiv.ulift.symm) (N.mapEquiv Equiv.ulift.symm))
  let e := Equiv.sumEquivSigmaBool (ULift.{v} α) (ULift.{u} β)
  (S.mapEquiv e.symm).mapEquiv (Equiv.sumCongr Equiv.ulift Equiv.ulift)

@[simp] lemma sum_ground (M : Matroid α) (N : Matroid β) :
    (M.sum N).E = (.inl '' M.E) ∪ (.inr '' N.E) := by
  simp [Matroid.sum, Set.ext_iff, mapEquiv, mapEmbedding, Equiv.ulift, Equiv.sumEquivSigmaBool]

@[simp] lemma sum_indep_iff (M : Matroid α) (N : Matroid β) {I : Set (α ⊕ β)} :
    (M.sum N).Indep I ↔ M.Indep (.inl ⁻¹' I) ∧ N.Indep (.inr ⁻¹' I) := by
  simp only [Matroid.sum, mapEquiv_indep_iff, Equiv.sumCongr_symm, Equiv.sumCongr_apply,
    Equiv.symm_symm, sigma_indep_iff, Bool.forall_bool, Equiv.ulift_apply]
  convert Iff.rfl <;>
    simp [Set.ext_iff, Equiv.ulift, Equiv.sumEquivSigmaBool]

@[simp] lemma sum_base_iff {M : Matroid α} {N : Matroid β} {B : Set (α ⊕ β)} :
    (M.sum N).Base B ↔ M.Base (.inl ⁻¹' B) ∧ N.Base (.inr ⁻¹' B) := by
  simp only [Matroid.sum, mapEquiv_base_iff, Equiv.sumCongr_symm, Equiv.sumCongr_apply,
    Equiv.symm_symm, sigma_base_iff, Bool.forall_bool, Equiv.ulift_apply]
  convert Iff.rfl <;>
    simp [Set.ext_iff, Equiv.ulift, Equiv.sumEquivSigmaBool]

@[simp] lemma sum_basis_iff {M : Matroid α} {N : Matroid β} {I X : Set (α ⊕ β)} :
    (M.sum N).Basis I X ↔
      (M.Basis (Sum.inl ⁻¹' I) (Sum.inl ⁻¹' X) ∧ N.Basis (Sum.inr ⁻¹' I) (Sum.inr ⁻¹' X)) := by
  simp only [Matroid.sum, mapEquiv_basis_iff, Equiv.sumCongr_symm,
    Equiv.sumCongr_apply, Equiv.symm_symm, sigma_basis_iff, Bool.forall_bool, Equiv.ulift_apply,
    Equiv.sumEquivSigmaBool, Equiv.coe_fn_mk, Equiv.ulift]
  convert Iff.rfl <;>
  · ext; simp

end Sum

section disjointSum

variable {α : Type*} {M N : Matroid α}

/-- The direct sum of two matroids on `α` with disjoint ground sets, as a `Matroid α`.
Implemented by mapping a matroid on `↑(M.E) ⊕ ↑(N.E)` into `α`.  -/
@[simps!] def disjointSum (M N : Matroid α) (h : Disjoint M.E N.E) : Matroid α :=
  ((M.restrictSubtype M.E).sum (N.restrictSubtype N.E)).mapEmbedding
    (Function.Embedding.sumSet h)

@[simp] lemma disjointSum_ground_eq {h} : (M.disjointSum N h).E = M.E ∪ N.E := by
  simp [disjointSum, restrictSubtype, mapEmbedding]

@[simp] lemma disjointSum_indep_iff {h I} :
    (M.disjointSum N h).Indep I ↔ M.Indep (I ∩ M.E) ∧ N.Indep (I ∩ N.E) ∧ I ⊆ M.E ∪ N.E := by
  simp [disjointSum, and_assoc]

@[simp] lemma disjointSum_base_iff {h B} :
    (M.disjointSum N h).Base B ↔ M.Base (B ∩ M.E) ∧ N.Base (B ∩ N.E) ∧ B ⊆ M.E ∪ N.E := by
  simp [disjointSum, and_assoc]

@[simp] lemma disjointSum_basis_iff {h I X} :
    (M.disjointSum N h).Basis I X ↔ M.Basis (I ∩ M.E) (X ∩ M.E) ∧
      N.Basis (I ∩ N.E) (X ∩ N.E) ∧ I ⊆ X ∧ X ⊆ M.E ∪ N.E := by
  simp [disjointSum, and_assoc]

lemma Indep.eq_union_image_of_disjointSum {h I} (hI : (disjointSum M N h).Indep I) :
    ∃ IM IN, M.Indep IM ∧ N.Indep IN ∧ Disjoint IM IN ∧ I = IM ∪ IN := by
  rw [disjointSum_indep_iff] at hI
  refine ⟨_, _, hI.1, hI.2.1, h.mono inter_subset_right inter_subset_right, ?_⟩
  rw [← inter_union_distrib_left, inter_eq_self_of_subset_left hI.2.2]

lemma Base.eq_union_image_of_disjointSum {h B} (hB : (disjointSum M N h).Base B) :
    ∃ BM BN, M.Base BM ∧ N.Base BN ∧ Disjoint BM BN ∧ B = BM ∪ BN := by
  rw [disjointSum_base_iff] at hB
  refine ⟨_, _, hB.1, hB.2.1, h.mono inter_subset_right inter_subset_right, ?_⟩
  rw [← inter_union_distrib_left, inter_eq_self_of_subset_left hB.2.2]

end disjointSum

end Matroid
