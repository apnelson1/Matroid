import Matroid.Closure
import Matroid.ForMathlib.PreimageVal
import Matroid.ForMathlib.Logic_Embedding_Set
import Matroid.ForMathlib.MatroidBasic

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

lemma Iso.indep_image_iff (e : M ≂ N) {I : Set M.E} : M.Indep ↑I ↔ N.Indep ↑(e '' I) :=
  e.indep_image_iff' I

lemma Iso.image_indep (e : M ≂ N) {I : Set M.E} (hI : M.Indep I) : N.Indep ↑(e '' I) :=
  e.indep_image_iff.1 hI

lemma Iso.dep_image_iff (e : M ≂ N) {D : Set M.E} : M.Dep ↑D ↔ N.Dep ↑(e '' D) := by
  rw [← not_indep_iff, e.indep_image_iff, not_indep_iff]

lemma Iso.image_dep (e : M ≂ N) {D : Set M.E} (hD : M.Dep ↑D) : N.Dep ↑(e '' D) :=
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

@[simp] lemma Iso.apply_symm_apply (e : M ≂ N) (x : N.E) : e (e.symm x) = x :=
  Equiv.apply_symm_apply e.toEquiv x

@[simp] lemma Iso.symm_apply_apply (e : M ≂ N) (x : M.E) : e.symm (e x) = x :=
  Equiv.symm_apply_apply e.toEquiv x

lemma Iso.symm_image_image (e : M ≂ N) (X : Set M.E) : e.symm '' (e '' X) = X :=
  Equiv.symm_image_image e.toEquiv X

lemma Iso.image_symm_image (e : M ≂ N) (X : Set N.E) : e '' (e.symm '' X) = X :=
  Equiv.image_symm_image e.toEquiv X

@[simp] lemma Iso.image_symm_eq_preimage (e : M ≂ N) (X : Set N.E) : e.symm '' X = e ⁻¹' X :=
  Eq.symm <| preimage_equiv_eq_image_symm X e.toEquiv

@[simp] lemma Iso.preimage_symm_eq_image (e : M ≂ N) (X : Set M.E) : e.symm ⁻¹' X = e '' X :=
  (e.toEquiv.image_eq_preimage X).symm

@[simp] lemma Iso.preimage_image (e : M ≂ N) (X : Set M.E) : e ⁻¹' (e '' X) = X := by
  rw [← e.image_symm_eq_preimage, e.symm_image_image]

@[simp] lemma Iso.image_preimage (e : M ≂ N) (X : Set N.E) : e '' (e ⁻¹' X) = X := by
  rw [← e.image_symm_eq_preimage, e.image_symm_image]

@[simp] lemma Iso.preimage_subset_iff (e : M ≂ N) {X : Set N.E} {Y : Set M.E} :
    e ⁻¹' X ⊆ Y ↔ X ⊆ e '' Y := by
  rw [← e.image_symm_eq_preimage, image_subset_iff, e.preimage_symm_eq_image]

@[simp] lemma Iso.range_eq (e : M ≂ N) : range e = univ :=
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
    · obtain ⟨B, rfl⟩ := Subset.eq_image_val hB.subset_ground
      refine ⟨↑(e '' B), (he B).1 hB, ?_⟩
      rw [image_subset_image_iff Subtype.val_injective] at hIB ⊢
      exact image_subset e hIB
    obtain ⟨B, rfl⟩ := Subset.eq_image_val hB.subset_ground
    refine ⟨↑(e.symm '' B), by rwa [he, e.image_symm_image] , ?_⟩
    rw [image_subset_image_iff Subtype.val_injective] at hIB ⊢
    simpa using hIB

lemma Iso.base_image (e : M ≂ N) {B : Set M.E} (hB : M.Base B) : N.Base (↑(e '' B)) := by
  rw [base_iff_maximal_indep, ← e.indep_image_iff, and_iff_right hB.indep]
  intro I hI h'
  obtain ⟨I, rfl⟩ := Subset.eq_image_val hI.subset_ground
  replace hB := hB.eq_of_subset_indep (e.symm.image_indep hI)
  simp only [image_subset_iff, preimage_val_image_val_eq_self, image_val_inj,
    image_symm_eq_preimage] at hB
  simp only [image_subset_iff, preimage_val_image_val_eq_self] at h'
  simp [hB h', image_image]

lemma Iso.base_image_iff (e : M ≂ N) {B : Set M.E} : M.Base B ↔ N.Base (↑(e '' B)) :=
  ⟨e.base_image, fun h ↦ by simpa using e.symm.base_image h⟩

lemma Iso.nonempty_right (e : M ≂ N) [M.Nonempty] : N.Nonempty := by
  obtain ⟨x,hx⟩ := M.ground_nonempty
  exact ⟨e ⟨x,hx⟩, Subtype.coe_prop (e ⟨x, hx⟩)⟩

lemma Iso.right_eq_empty (e : emptyOn α ≂ N) : N = emptyOn β := by
  rw [← ground_eq_empty_iff]
  have h := e.toEquiv
  simp only [emptyOn_ground] at h
  exact isEmpty_coe_sort.mp h.symm.isEmpty

section map

lemma Iso.basis_image_iff (e : M ≂ N) {I X : Set M.E} :
    M.Basis I X ↔ N.Basis ↑(e '' I) ↑(e '' X) := by
  simp only [image_subset_iff, Subtype.coe_preimage_self, subset_univ, basis_iff_mem_maximals,
    mem_maximals_iff, mem_setOf_eq, ← e.indep_image_iff, preimage_val_image_val_eq_self, and_imp,
    preimage_image, and_congr_right_iff]
  intro hI hIX
  refine ⟨fun h J hJ hJX hIJ ↦ ?_, fun h J hJ hJX hIJ ↦ ?_⟩
  · specialize h (y := ↑(e.symm '' (N.E ↓∩ J)))
    simp only [image_symm_eq_preimage, e.indep_image_iff, image_preimage,
      Subtype.image_preimage_coe, inter_eq_self_of_subset_right hJ.subset_ground, hJ,
      image_subset_iff, preimage_val_image_val_eq_self, preimage_subset_iff, image_val_inj,
      true_implies] at h

    specialize h <| by simpa [Set.preimage_val_image_val_eq_self]
      using (show N.E ↓∩ J ⊆ _ from preimage_mono (f := Subtype.val) hJX)
    obtain rfl := h (by convert hIJ)
    simp [hJ.subset_ground]
  specialize h (y := ↑(e '' (M.E ↓∩ J)))
  simp only [← e.indep_image_iff, Subtype.image_preimage_coe,
    inter_eq_self_of_subset_right hJ.subset_ground, hJ, image_subset_iff,
    preimage_val_image_val_eq_self, preimage_image, image_val_inj, true_implies] at h
  rw [← image_subset_image_iff Subtype.val_injective] at h
  simp only [Subtype.image_preimage_coe, inter_eq_self_of_subset_right hJ.subset_ground] at h
  specialize h hJX (by convert hIJ)
  rw [← e.symm_image_image I, h]
  simp [hJ.subset_ground]

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
  indep_image_iff' := by simp [Set.preimage_val_image_val_eq_self]

/-- If `M` and `N` are isomorphic and `α → β` is nonempty, then `N` is a map of `M`.
Useful for getting out of subtype hell. -/
lemma Iso.exists_eq_map (e : M ≂ N) [Nonempty (α → β)] : ∃ (f : α → β) (h : _), N = M.map f h := by
  classical
  set f : α → β := fun x ↦ if hx : x ∈ M.E then e ⟨x,hx⟩ else Classical.arbitrary (α → β) x
  have hf_im' : ∀ X ⊆ M.E, f '' X = e '' (M.E ↓∩ X) := by
    simp [← Subtype.forall_set_subtype, preimage_image_eq _ Subtype.val_injective,
      image_image, show ∀ x : M.E, f x = e x from fun x ↦ by simp [f, x.2]]
  have hf_im : ∀ X : Set M.E, f '' X = e '' X := fun X ↦ by
    rw [hf_im' _ (by simp), preimage_image_eq _ Subtype.val_injective]
  refine ⟨f, fun _ hx _ hy ↦ by simp [f, hx, hy, Subtype.val_inj],
    eq_of_indep_iff_indep_forall ?_ ?_⟩
  · simp [map_ground, hf_im' _ Subset.rfl]
  simp_rw [map_indep_iff, ← Subtype.forall_set_subtype]
  refine fun I ↦ ⟨fun hI ↦ ⟨↑(e.symm '' I), ?_⟩, fun ⟨I₀, hI₀, h⟩ ↦ ?_⟩
  · rw [hf_im, image_symm_image, and_iff_left rfl]
    rwa [← e.symm.indep_image_iff]
  rwa [h, hf_im' _ hI₀.subset_ground, ← e.indep_image_iff,
    Subset.image_val_preimage_val_eq hI₀.subset_ground]

lemma Iso.exists_eq_map' (e : M ≂ N) [M.Nonempty] :
    ∃ (f : α → β) (hf : InjOn f M.E), N = M.map f hf :=
  have := e.nonempty_right
  have := N.nonempty_type
  e.exists_eq_map

lemma Iso.empty_empty_or_exists_eq_map (e : M ≂ N) :
    (M = emptyOn α ∧ N = emptyOn β) ∨ ∃ (f : α → β) (hf : InjOn f M.E), N = M.map f hf := by
  obtain (rfl | hne) := M.eq_emptyOn_or_nonempty
  · simp [e.right_eq_empty]
  exact .inr e.exists_eq_map'

lemma Finite.of_iso (hM : M.Finite) (e : M ≂ N) : N.Finite := by
  have h := e.toEquiv.finite_iff.mp
  simp_rw [finite_coe_iff] at h
  exact ⟨h M.ground_finite⟩

lemma Finitary.of_iso (hM : M.Finitary) (e : M ≂ N) : N.Finitary := by
  obtain (h | h) := isEmpty_or_nonempty β
  · rw [eq_emptyOn N]; infer_instance
  obtain ⟨f,hf,rfl⟩ := e.exists_eq_map
  infer_instance

lemma Iso.finite_iff (e : M ≂ N) : M.Finite ↔ N.Finite :=
  ⟨fun h ↦ h.of_iso e, fun h ↦ h.of_iso e.symm⟩

lemma Iso.finitary_iff (e : M ≂ N) : M.Finitary ↔ N.Finitary :=
  ⟨fun h ↦ h.of_iso e, fun h ↦ h.of_iso e.symm⟩


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

@[simp] lemma Iso.dual_image (e : M ≂ N) (X : Set α) :
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


/-- If an equivalence between `M.E` and `N.E` respects the closure function, it is an isomorphism-/
def isoOfForallImageCl {β : Type*} {N : Matroid β} (e : M.E ≃ N.E)
    (h : ∀ X : Set M.E, N.cl ↑(e '' X) = e '' (M.E ↓∩ M.cl ↑X)) : M ≂ N where
  toEquiv := e
  indep_image_iff' I := by
    rw [indep_iff_not_mem_cl_diff_forall, indep_iff_not_mem_cl_diff_forall]
    simp only [mem_image, Subtype.exists, exists_and_right, exists_eq_right, forall_exists_index,
      mem_image_equiv]
    refine ⟨fun h' x hx y hy ⟨hyI, hyx⟩ hxI ↦ h' y hy hyI ?_, fun h' x hx hxI h'' ↦
      h' (e ⟨x,hx⟩).1 (e ⟨x,hx⟩).2 x hx ⟨hxI, rfl⟩ ?_⟩
    · have h_eq : (↑(e '' I) : Set β) \ {x} = ↑(e '' ((M.E ↓∩ I) \ {⟨y,hy⟩})) := by
        simp [image_diff e.injective, hyx, Set.preimage_val_image_val_eq_self]
      have h'' : ∃ hx', ↑(e.symm ⟨x, hx'⟩) ∈ M.cl (↑I \ {y}) := by simpa [h_eq, h] using hxI
      simpa [← hyx, Equiv.symm_apply_apply, exists_prop, and_iff_right hx] using h''
    have h_eq : ((↑(e '' I) : Set β) \ {↑(e ⟨x, hx⟩)}) = ↑(e '' (I \ {⟨x,hx⟩})) := by
      simp [image_diff e.injective]
    rw [h_eq, h]
    simpa

@[simp] lemma isoOfForallImageCl_apply {β : Type*} {N : Matroid β} (e : M.E ≃ N.E) (h) (x : M.E) :
  (isoOfForallImageCl e h) x = e x := rfl
