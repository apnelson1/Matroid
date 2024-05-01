import Matroid.Map
import Matroid.ForMathlib.Function

variable {α β : Type*} {M : Matroid α} {N : Matroid β}

open Set Function Set.Notation

attribute [simp] Set.preimage_val_image_val_eq_self

@[simp] theorem image_val_image_val_eq (f : α → β) (s : Set α) (x : Set s) :
    (↑) '' ((fun x : s ↦ (⟨f x, mem_image_of_mem _ x.2⟩ : f '' s)) '' x) = f '' x := by
  aesop

@[simp] theorem image_val_image_eq_image_image_val (s : Set α) (t : Set β) (f : s → t) (x : Set s) :
    ↑((f '' (s ↓∩ x))) = f '' ↑(s ↓∩ x) := by
  aesop

@[simp] theorem image_val_eq (s : Set α) (x : Set s) : Subtype.val '' x = ↑x := rfl

theorem image_val_image_eq (s : Set α) (t : Set s) (f : α → β) :
    (fun (x : s) ↦ f ↑x) '' t = f '' (↑t) := by
  ext; simp

theorem eq_image_val_of_subset {s x : Set α} (hsx : x ⊆ s) : ∃ (y : Set s), x = ↑y :=
  ⟨s ↓∩ x, by simpa⟩

theorem image_val_preimage_val_of_subset {s x : Set α} (hsx : x ⊆ s) : ↑(s ↓∩ x) = x := by
  simpa


namespace Matroid

structure Iso (M : Matroid α) (N : Matroid β) where
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

theorem Iso.indep_image_iff {e : M ≂ N} {I : Set α} :
    M.Indep (M.E ↓∩ I) ↔ N.Indep ↑(e '' (M.E ↓∩ I)) :=
  e.indep_image_iff' (M.E ↓∩ I)

theorem Iso.indep_image_val_iff {e : M ≂ N} {I : Set M.E} :
    M.Indep ↑I ↔ N.Indep (↑(e '' I)) :=
  e.indep_image_iff' I

theorem Iso.image_indep (e : M ≂ N) {I : Set M.E} (hI : M.Indep I) : N.Indep (↑(e '' I)) :=
  Iso.indep_image_val_iff.1 hI

@[simps] def Iso.symm (e : M ≂ N) : Iso N M where
  toEquiv := e.toEquiv.symm
  indep_image_iff' := by
    intro I
    have : I = e '' (Equiv.symm e '' I) := by
      exact Eq.symm <| Equiv.image_symm_image e.toEquiv I
    rw [← Equiv.image_symm_image e.toEquiv I]
    convert (e.indep_image_val_iff (I := e.toEquiv.symm '' I)).symm
    simp

-- I don't actually know what the simp normal form should be with these.
-- In particular, how should `e '' X ⊆ Y` simplify?
-- Should we get `X ⊆ e.symm '' Y` or `X ⊆ e ⁻¹' Y`?

theorem Iso.symm_image_image (e : M ≂ N) (X : Set M.E) : e.symm '' (e '' X) = X :=
  Equiv.symm_image_image e.toEquiv X

theorem Iso.image_symm_image (e : M ≂ N) (X : Set N.E) : e '' (e.symm '' X) = X :=
  Equiv.image_symm_image e.toEquiv X

@[simp] theorem Iso.image_symm_eq_preimage (e : M ≂ N) (X : Set N.E) : e.symm '' X = e ⁻¹' X :=
  Eq.symm <| preimage_equiv_eq_image_symm X e.toEquiv

@[simp] theorem Iso.preimage_image (e : M ≂ N) (X : Set M.E) : e ⁻¹' (e '' X) = X := by
  rw [← e.image_symm_eq_preimage, e.symm_image_image]

@[simp] theorem Iso.image_preimage (e : M ≂ N) (X : Set N.E) : e '' (e ⁻¹' X) = X := by
  rw [← e.image_symm_eq_preimage, e.image_symm_image]

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

-- @[simp] theorem Iso.toFun_symm (e : M ≂ N) : (e.symm : N.E → M.E) = (e : M.E ≃ N.E).symm := rfl

noncomputable def iso_map (M : Matroid α) (f : α → β) (hf : M.E.InjOn f) : M.Iso (M.map f hf) where
  toEquiv := Equiv.Set.imageOfInjOn _ _ hf
  indep_image_iff' := by
    intro I
    simp only [Equiv.Set.imageOfInjOn, map_ground, Equiv.coe_fn_mk, image_val_image_val_eq]
    rw [map_image_indep_iff <| Subtype.coe_image_subset M.E I]

noncomputable def iso_comapOn (M : Matroid β) (f : α → β) {E : Set α} (hf : BijOn f E M.E) :
    (M.comapOn E f) ≂ M where
  toEquiv := BijOn.equiv f hf
  indep_image_iff' I := by
    rw [comapOn_indep_iff, and_iff_right (hf.injOn.mono <| Subtype.coe_image_subset _ I)]
    simp [BijOn.equiv, image_image]

@[simps!] noncomputable def iso_comap (M : Matroid β) (f : α → β) (hf : BijOn f (f ⁻¹' M.E) M.E) :
    M.comap f ≂ M :=
  (Iso.ofEq <| (comapOn_preimage_eq M f).symm).trans (iso_comapOn M f hf)

@[simps] def iso_of_base_iff_base (e : M.E ≃ N.E)
    (he : ∀ (B : Set M.E), M.Base B ↔ N.Base (↑(e '' B))) : M ≂ N where
  toEquiv := e
  indep_image_iff' := by
    intro I
    rw [indep_iff_subset_base, indep_iff_subset_base]
    refine ⟨fun ⟨B, hB, hIB⟩ ↦ ?_, fun ⟨B, hB, hIB⟩ ↦ ?_⟩
    · obtain ⟨B, rfl⟩ := eq_image_val_of_subset hB.subset_ground
      refine ⟨↑(e '' B), (he B).1 hB, ?_⟩
      rw [image_subset_image_iff Subtype.val_injective] at hIB ⊢
      exact image_subset e hIB
    obtain ⟨B, rfl⟩ := eq_image_val_of_subset hB.subset_ground
    refine ⟨↑(e.symm '' B), by rwa [he, e.image_symm_image] , ?_⟩
    rw [image_subset_image_iff Subtype.val_injective] at hIB ⊢
    simpa using hIB

theorem Iso.base_image_subtype (e : M ≂ N) {B : Set M.E} (hB : M.Base B) : N.Base (↑(e '' B)) := by
  rw [base_iff_maximal_indep, ← e.indep_image_val_iff, and_iff_right hB.indep]
  intro I hI h'
  obtain ⟨I, rfl⟩ := eq_image_val_of_subset hI.subset_ground
  replace hB := hB.eq_of_subset_indep (e.symm.image_indep hI)
  simp only [image_subset_iff, preimage_val_image_val_eq_self, image_val_inj,
    image_symm_eq_preimage] at hB
  simp only [image_subset_iff, preimage_val_image_val_eq_self] at h'
  simp [hB h', image_image]

theorem Iso.base_image {B : Set α} (e : M ≂ N) (hB : M.Base B) : N.Base (↑(e '' (M.E ↓∩ B))) :=
  e.base_image_subtype <| by simpa [inter_eq_self_of_subset_right hB.subset_ground]

theorem Iso.base_image_subtype_iff (e : M ≂ N) {B : Set M.E} : M.Base B ↔ N.Base (↑(e '' B)) :=
  ⟨e.base_image_subtype, fun h ↦ by simpa using e.symm.base_image_subtype h⟩
