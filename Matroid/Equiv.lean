import Matroid.Map
import Matroid.ForMathlib.Function

variable {α β : Type*} {M : Matroid α} {N : Matroid β}

open Set Set.Notation
namespace Matroid

/-- An isomorphism between two matroids. -/
@[pp_nodot] structure Iso (M : Matroid α) (N : Matroid β) where
  toEquiv : M.E ≃ N.E
  indep_image_iff' : ∀ (I : Set M.E), M.Indep I ↔ N.Indep (↑(toEquiv '' I))

infixl:65  " ≂ " => Iso

instance : EquivLike (M ≂ N) M.E N.E where
  coe f := f.toEquiv
  inv f := f.toEquiv.symm
  left_inv f := f.1.leftInverse_symm
  right_inv f := f.1.rightInverse_symm
  coe_injective' := by
    rintro ⟨f, -⟩ ⟨g, -⟩
    simp only [DFunLike.coe_fn_eq, Iso.mk.injEq]
    exact fun h _ ↦ h

theorem Iso.indep_image_iff (e : M ≂ N) {I : Set M.E} : M.Indep ↑I ↔ N.Indep ↑(e '' I) :=
  e.indep_image_iff' I

theorem Iso.image_indep (e : M ≂ N) {I : Set M.E} (hI : M.Indep I) : N.Indep (↑(e '' I)) :=
  e.indep_image_iff.1 hI

theorem Iso.dep_image_iff (e : M ≂ N) {D : Set M.E} : M.Dep ↑D ↔ N.Dep ↑(e '' D) := by
  rw [← not_indep_iff, e.indep_image_iff, not_indep_iff]

theorem Iso.image_dep (e : M ≂ N) {D : Set M.E} (hD : M.Dep ↑D) : N.Dep ↑(e '' D) :=
  e.dep_image_iff.1 hD

@[simps] def Iso.refl {M : Matroid α} : Iso M M where
  toEquiv := Equiv.refl _
  indep_image_iff' := by simp

@[simps] def Iso.symm (e : M ≂ N) : Iso N M where
  toEquiv := e.toEquiv.symm
  indep_image_iff' := by
    intro I
    have : I = e '' (Equiv.symm e '' I) := by
      exact Eq.symm <| Equiv.image_symm_image e.toEquiv I
    rw [← Equiv.image_symm_image e.toEquiv I]
    convert (e.indep_image_iff (I := e.toEquiv.symm '' I)).symm
    simp

@[simp] theorem Iso.apply_symm_apply (e : M ≂ N) (x : N.E) : e (e.symm x) = x :=
  Equiv.apply_symm_apply e.toEquiv x

@[simp] theorem Iso.symm_apply_apply (e : M ≂ N) (x : M.E) : e.symm (e x) = x :=
  Equiv.symm_apply_apply e.toEquiv x

theorem Iso.symm_image_image (e : M ≂ N) (X : Set M.E) : e.symm '' (e '' X) = X :=
  Equiv.symm_image_image e.toEquiv X

theorem Iso.image_symm_image (e : M ≂ N) (X : Set N.E) : e '' (e.symm '' X) = X :=
  Equiv.image_symm_image e.toEquiv X

@[simp] theorem Iso.image_symm_eq_preimage (e : M ≂ N) (X : Set N.E) : e.symm '' X = e ⁻¹' X :=
  Eq.symm <| preimage_equiv_eq_image_symm X e.toEquiv

@[simp] theorem Iso.preimage_symm_eq_image (e : M ≂ N) (X : Set M.E) : e.symm ⁻¹' X = e '' X :=
  (e.toEquiv.image_eq_preimage X).symm

@[simp] theorem Iso.preimage_image (e : M ≂ N) (X : Set M.E) : e ⁻¹' (e '' X) = X := by
  rw [← e.image_symm_eq_preimage, e.symm_image_image]

@[simp] theorem Iso.image_preimage (e : M ≂ N) (X : Set N.E) : e '' (e ⁻¹' X) = X := by
  rw [← e.image_symm_eq_preimage, e.image_symm_image]

@[simp] theorem Iso.preimage_subset_iff (e : M ≂ N) {X : Set N.E} {Y : Set M.E} :
    e ⁻¹' X ⊆ Y ↔ X ⊆ e '' Y := by
  rw [← e.image_symm_eq_preimage, image_subset_iff, e.preimage_symm_eq_image]

@[simp] theorem Iso.range_eq (e : M ≂ N) : range e = univ :=
  Equiv.range_eq_univ (e : M.E ≃ N.E)

@[simps] def Iso.trans {γ : Type*} {M : Matroid α} {N : Matroid β} {R : Matroid γ}
    (e : M ≂ N) (f : N ≂ R) : M ≂ R where
  toEquiv := (e : M.E ≃ N.E).trans f
  indep_image_iff' I := by
    rw [e.indep_image_iff', f.indep_image_iff']
    simp only [image_image, Equiv.trans_apply, EquivLike.coe_coe]
    rfl

@[simps] def Iso.ofEq {M N : Matroid α} (hMN : M = N) : M ≂ N where
  toEquiv := Equiv.setCongr (congr_arg Matroid.E hMN)
  indep_image_iff' := by subst hMN; simp

@[simps] def Iso.ofForallDep (e : M.E ≃ N.E) (he : ∀ (D : Set M.E), M.Dep D ↔ N.Dep ↑(e '' D)) :
    M ≂ N where
  toEquiv := e
  indep_image_iff' I := by rw [← not_dep_iff, he, not_dep_iff]

@[simps] def Iso.ofForallBase (e : M.E ≃ N.E)
    (he : ∀ (B : Set M.E), M.Base B ↔ N.Base (↑(e '' B))) : M ≂ N where
  toEquiv := e
  indep_image_iff' := by
    intro I
    rw [indep_iff, indep_iff]
    refine ⟨fun ⟨B, hB, hIB⟩ ↦ ?_, fun ⟨B, hB, hIB⟩ ↦ ?_⟩
    · obtain ⟨B, rfl⟩ := eq_image_val_of_subset hB.subset_ground
      refine ⟨↑(e '' B), (he B).1 hB, ?_⟩
      rw [image_subset_image_iff Subtype.val_injective] at hIB ⊢
      exact image_subset e hIB
    obtain ⟨B, rfl⟩ := eq_image_val_of_subset hB.subset_ground
    refine ⟨↑(e.symm '' B), by rwa [he, e.image_symm_image] , ?_⟩
    rw [image_subset_image_iff Subtype.val_injective] at hIB ⊢
    simpa using hIB

theorem Iso.base_image (e : M ≂ N) {B : Set M.E} (hB : M.Base B) : N.Base (↑(e '' B)) := by
  rw [base_iff_maximal_indep, ← e.indep_image_iff, and_iff_right hB.indep]
  intro I hI h'
  obtain ⟨I, rfl⟩ := eq_image_val_of_subset hI.subset_ground
  replace hB := hB.eq_of_subset_indep (e.symm.image_indep hI)
  simp only [image_subset_iff, preimage_val_image_val_eq_self, image_val_inj,
    image_symm_eq_preimage] at hB
  simp only [image_subset_iff, preimage_val_image_val_eq_self] at h'
  simp [hB h', image_image]

theorem Iso.base_image_iff (e : M ≂ N) {B : Set M.E} : M.Base B ↔ N.Base (↑(e '' B)) :=
  ⟨e.base_image, fun h ↦ by simpa using e.symm.base_image h⟩
section map

noncomputable def isoMap (M : Matroid α) (f : α → β) (hf : M.E.InjOn f) : M ≂ (M.map f hf) where
  toEquiv := Equiv.Set.imageOfInjOn _ _ hf
  indep_image_iff' := by
    intro I
    simp only [Equiv.Set.imageOfInjOn, map_ground, Equiv.coe_fn_mk, image_val_image_val_eq]
    rw [map_image_indep_iff <| Subtype.coe_image_subset M.E I]

noncomputable def isoComapOn (M : Matroid β) (f : α → β) {E : Set α} (hf : BijOn f E M.E) :
    (M.comapOn E f) ≂ M where
  toEquiv := BijOn.equiv f hf
  indep_image_iff' I := by
    rw [comapOn_indep_iff, and_iff_right (hf.injOn.mono <| Subtype.coe_image_subset _ I),
      image_image, image_image]
    simp [BijOn.equiv]

noncomputable def isoComap (M : Matroid β) (f : α → β) (hf : BijOn f (f ⁻¹' M.E) M.E) :
    M.comap f ≂ M :=
  (Iso.ofEq <| (comapOn_preimage_eq M f).symm).trans (isoComapOn M f hf)

noncomputable def isoMapSetEmbedding (M : Matroid α) (f : M.E ↪ β) : M ≂ M.mapSetEmbedding f where
  toEquiv := (Equiv.ofInjective f f.injective)
  indep_image_iff' I := by simp [preimage_image_eq _ f.injective, image_image]

noncomputable def isoMapSetEquiv (M : Matroid α) {E : Set β} (f : M.E ≃ E) :
    M ≂ M.mapSetEquiv f where
  toEquiv := f
  indep_image_iff' := by simp

end map

section dual

def Iso.dual (e : M ≂ N) : M✶ ≂ N✶ :=
  let e' : M✶.E ≃ N✶.E := ((Equiv.setCongr rfl).trans (e : M.E ≃ N.E)).trans (Equiv.setCongr rfl)
  Iso.ofForallBase e' (by
    simp only [dual_ground, image_subset_iff, Subtype.coe_preimage_self, subset_univ, dual_base_iff]
    intro B
    simp_rw [show M.E = Subtype.val '' (univ : Set M.E) by simp,
      show N.E = Subtype.val '' (univ : Set N.E) by simp]
    rw [← image_val_diff, ← image_val_diff, e.base_image_iff, image_diff, image_univ, e.range_eq]
    · rfl
    exact (Equiv.injective (e : M.E ≃ N.E)))

@[simp] theorem Iso.dual_image (e : M ≂ N) (X : Set α) :
    Subtype.val '' (e.dual '' (M✶.E ↓∩ X)) = e '' (M.E ↓∩ X) := rfl

def Iso.dual_comm (e : M ≂ N✶) : M✶ ≂ N :=
  e.dual.trans <| Iso.ofEq N.dual_dual

end dual

section restrict

def Iso.restrict (e : M ≂ N) {R : Set α} {S : Set β} (hR : R ⊆ M.E) (hS : S ⊆ N.E)
    (hRS : ∀ x : M.E, (e x).1 ∈ S ↔ x.1 ∈ R) : (M ↾ R) ≂ (N ↾ S) where
  toEquiv := Equiv.subsetEquivSubset (e : M.E ≃ N.E) hR hS hRS
  indep_image_iff' := by
    simp only [restrict_ground_eq, restrict_indep_iff, image_subset_iff, Subtype.coe_preimage_self,
      subset_univ, and_true]
    intro I
    convert e.indep_image_iff (I := (embeddingOfSubset _ _ hR) '' I) using 2 <;> simp

end restrict
