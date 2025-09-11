import Mathlib.Combinatorics.Matroid.Constructions
import Mathlib.Combinatorics.Matroid.Map
import Matroid.ForMathlib.PartialEquiv
import Matroid.ForMathlib.Other

open Set

variable {α β γ : Type*} {M : Matroid α} {N : Matroid β} {R : Matroid γ} {e : PartialEquiv α β}
  {f : PartialEquiv β γ}


namespace Matroid

theorem Nonempty.nonempty_type {M : Matroid α} (hM : M.Nonempty) : Nonempty α := by
  obtain ⟨e,-⟩ := hM; exact ⟨e⟩

section GroundEquiv

/-- `GroundEquiv e M N` means that `e : PartialEquiv α β` puts `M.E` and `N.E` in bijection.
The API here is to combine some of `PartialEquiv`'s API with `aesop_mat`.  -/
def GroundEquiv (e : PartialEquiv α β) (M : Matroid α) (N : Matroid β) :=
  e.source = M.E ∧ e.target = N.E

theorem GroundEquiv.refl (M : Matroid α) : GroundEquiv (PartialEquiv.ofSet M.E) M M := ⟨rfl,rfl⟩

theorem GroundEquiv.source_eq (h : GroundEquiv e M N) : e.source = M.E := h.1

theorem GroundEquiv.target_eq (h : GroundEquiv e M N) : e.target = N.E := h.2

theorem GroundEquiv.injOn (h : GroundEquiv e M N) : InjOn e M.E := by
  rw [← h.source_eq]; exact e.injOn

theorem GroundEquiv.bijOn (h : GroundEquiv e M N) : BijOn e M.E N.E := by
  rw [← h.source_eq, ← h.target_eq]; exact e.bijOn

theorem GroundEquiv.dual (h : GroundEquiv e M N) : GroundEquiv e M✶ N✶ := h

theorem GroundEquiv.of_dual (h : GroundEquiv e M✶ N✶) : GroundEquiv e M N := h

theorem GroundEquiv.symm (h : GroundEquiv e M N) : GroundEquiv e.symm N M := by
  rwa [GroundEquiv, e.symm_source, e.symm_target, and_comm]

theorem GroundEquiv.trans {f : PartialEquiv β γ} (he : GroundEquiv e M N) (hf : GroundEquiv f N R) :
    GroundEquiv (e.trans f) M R := by
  refine ⟨?_, ?_⟩
  · rw [e.trans_source, ← he.source_eq, hf.source_eq, ← he.target_eq,
      inter_eq_self_of_subset_left e.source_subset_preimage_target]
  rw [e.trans_target, ← hf.target_eq, he.target_eq, ← hf.source_eq,
    inter_eq_self_of_subset_left f.target_subset_preimage_source]

theorem GroundEquiv.image_ground (h : GroundEquiv e M N) : e '' M.E = N.E := by
  rw [← h.source_eq, e.image_source_eq_target, h.target_eq]

theorem GroundEquiv.image_subset_ground (h : GroundEquiv e M N) (X : Set α)
    (hX : X ⊆ M.E := by aesop_mat) : e '' X ⊆ N.E := by
  replace hX := image_mono hX
  rwa [← h.source_eq, e.image_source_eq_target, h.target_eq] at hX

theorem GroundEquiv.symm_image_subset_ground (h : GroundEquiv e M N) (X : Set β)
    (hX : X ⊆ N.E := by aesop_mat) : e.symm '' X ⊆ M.E :=
  h.symm.image_subset_ground X

theorem GroundEquiv.symm_image_image (h : GroundEquiv e M N) (X : Set α)
    (hX : X ⊆ M.E := by aesop_mat) : e.symm '' (e '' X) = X := by
  rw [e.symm_image_image_of_subset_source]
  rwa [h.source_eq]

theorem GroundEquiv.image_symm_image (h : GroundEquiv e M N) (X : Set β)
    (hX : X ⊆ N.E := by aesop_mat) : e '' (e.symm '' X) = X := by
  rw [e.image_symm_image_of_subset_target]
  rwa [h.target_eq]

theorem GroundEquiv.subset_symm_image_of_image_subset (h : GroundEquiv e M N) {X : Set α}
    {Y : Set β} (hX : X ⊆ M.E := by aesop_mat) (hXY : e '' X ⊆ Y) : X ⊆ e.symm '' Y := by
  replace hXY := image_subset e.symm hXY
  rwa [h.symm_image_image X] at hXY

theorem GroundEquiv.image_subset_of_subset_symm_image (h : GroundEquiv e M N) {X : Set α}
    {Y : Set β} (hY : Y ⊆ N.E := by aesop_mat) (hXY : X ⊆ e.symm '' Y) : e '' X ⊆ Y := by
  replace hXY := image_mono hXY
  rwa [h.image_symm_image Y] at hXY

theorem GroundEquiv.image_subset_iff (h : GroundEquiv e M N) {X : Set α} {Y : Set β}
    (hX : X ⊆ M.E := by aesop_mat) (hY : Y ⊆ N.E := by aesop_mat) :
    e '' X ⊆ Y ↔ X ⊆ e.symm '' Y :=
  ⟨h.subset_symm_image_of_image_subset, h.image_subset_of_subset_symm_image⟩

theorem GroundEquiv.restrict (h : GroundEquiv e M N) {M' : Matroid α} {N' : Matroid β}
    (hM' : M'.E ⊆ M.E) (hN' : N'.E ⊆ N.E) (h_image : e.IsImage M'.E N'.E) :
    GroundEquiv h_image.restr M' N' := by
  rwa [GroundEquiv, PartialEquiv.IsImage.restr_source, inter_eq_right,
    PartialEquiv.IsImage.restr_target, inter_eq_right, h.source_eq, h.target_eq,
    and_iff_right hM']

theorem GroundEquiv.image_isImage (h : GroundEquiv e M N) (X : Set α)
    (hX : X ⊆ M.E := by aesop_mat) : e.IsImage X (e '' X) :=
  e.image_isImage_of_subset_source (by rwa [h.source_eq])

theorem GroundEquiv.symm_image_isImage (h : GroundEquiv e M N) (Y : Set β)
    (hX : Y ⊆ N.E := by aesop_mat) : e.IsImage (e.symm '' Y) Y :=
  e.symm_image_isImage_of_subset_target (by rwa [h.target_eq])

theorem GroundEquiv.eq_emptyOn (h : GroundEquiv e M (emptyOn β)) : M = emptyOn α := by
  rw [← ground_eq_empty_iff, ← h.source_eq, ← e.symm_image_target_eq_source, h.target_eq]; simp

theorem GroundEquiv.of_empty [Nonempty α] [Nonempty β] :
    GroundEquiv PartialEquiv.empty (emptyOn α) (emptyOn β) := by
  simp [GroundEquiv]

end GroundEquiv

section WeakMap

/-- `IsWeakMap e M N` means that `e` is a bijection from `M.E` to `N.E` for which the image of
each dependent set is dependent
(or equivalently the preimage of each independent set is independent) -/
structure IsWeakMap (e : PartialEquiv α β) (M : Matroid α) (N : Matroid β) : Prop :=
  (groundEquiv : GroundEquiv e M N)
  (image_dep : ∀ ⦃D⦄, M.Dep D → N.Dep (e '' D))

theorem isWeakMap_def : IsWeakMap e M N ↔ (GroundEquiv e M N ∧ ∀ ⦃D⦄, M.Dep D → N.Dep (e '' D)) :=
  ⟨fun h ↦ ⟨h.1,h.2⟩, fun h ↦ ⟨h.1,h.2⟩⟩

theorem IsWeakMap.refl (M : Matroid α) : IsWeakMap (PartialEquiv.ofSet M.E) M M :=
  ⟨GroundEquiv.refl M, by simp⟩

theorem IsWeakMap.trans (h : IsWeakMap e M N) (h' : IsWeakMap f N R) :
    IsWeakMap (e.trans f) M R := ⟨h.groundEquiv.trans h'.groundEquiv,
    fun _ hD ↦ by simpa [image_image] using h'.image_dep (h.image_dep hD)⟩

theorem IsWeakMap.symm_image_indep (h : IsWeakMap e M N) {I : Set β} (hI : N.Indep I) :
    M.Indep (e.symm '' I) := by
  rw [indep_iff_not_dep, and_iff_left (h.groundEquiv.symm_image_subset_ground I)]
  refine fun hD ↦ hI.not_dep ?_
  replace hD := h.image_dep hD
  rwa [h.groundEquiv.image_symm_image I] at hD

theorem IsWeakMap.indep_of_image (h : IsWeakMap e M N) {I : Set α} (hI : N.Indep (e '' I))
    (hIE : I ⊆ M.E := by aesop_mat) : M.Indep I := by
  rw [← h.groundEquiv.symm_image_image I]
  exact h.symm_image_indep hI

theorem GroundEquiv.isWeakMap_iff_symm_image_indep (h : GroundEquiv e M N) :
    IsWeakMap e M N ↔ ∀ ⦃I⦄, N.Indep I → M.Indep (e.symm '' I) := by
  refine ⟨fun h' I ↦ h'.symm_image_indep, fun h' ↦ ⟨h, fun D hD ↦ ?_⟩⟩
  rw [dep_iff, and_iff_left (h.image_subset_ground D)]
  exact fun hI ↦  (h' hI).not_dep (by rwa [h.symm_image_image D])

theorem GroundEquiv.isWeakMap_of_symm_image_isBase (h : GroundEquiv e M N)
    (h_isBase : ∀ ⦃B⦄, N.IsBase B → M.IsBase (e.symm '' B)) : IsWeakMap e M N :=
  h.isWeakMap_iff_symm_image_indep.2 fun _ ⟨_, hB, hIB⟩ ↦
    (h_isBase hB).indep.subset (image_mono hIB)

theorem IsWeakMap.restrict (h : IsWeakMap e M N) {X : Set α} (hX : X ⊆ M.E) {Y : Set β}
    (hY : Y ⊆ N.E) (hXY : e.IsImage X Y) :
    IsWeakMap hXY.restr (M ↾ X) (N ↾ Y) := by
  refine ⟨h.groundEquiv.restrict (M' := M ↾ X) (N' := N ↾ Y) hX hY hXY, ?_⟩
  simp only [restrict_dep_iff, PartialEquiv.IsImage.restr_apply, and_imp]
  refine fun D hD hDX ↦ ⟨fun hi ↦ hD (h.indep_of_image hi), ?_⟩
  have := image_mono hDX
  rwa [← inter_eq_self_of_subset_right hY, ← h.groundEquiv.target_eq, ← hXY.image_eq,
    h.groundEquiv.source_eq, inter_eq_self_of_subset_right hX]

theorem IsWeakMap.of_empty [Nonempty α] [Nonempty β] :
    IsWeakMap PartialEquiv.empty (emptyOn α) (emptyOn β) where
  groundEquiv := GroundEquiv.of_empty
  image_dep := by simp [dep_iff]


end WeakMap

def IsIso (e : PartialEquiv α β) (M : Matroid α) (N : Matroid β) : Prop :=
  IsWeakMap e M N ∧ IsWeakMap e.symm N M

theorem IsIso.refl (M : Matroid α) : IsIso (PartialEquiv.ofSet M.E) M M := by
  rw [IsIso, PartialEquiv.ofSet_symm, and_self]
  exact IsWeakMap.refl M

theorem IsIso.symm (h : IsIso e M N) : IsIso e.symm N M := by
  simpa [IsIso, and_comm]

theorem IsIso.isWeakMap (h : IsIso e M N) : IsWeakMap e M N := h.1

theorem IsIso.trans (h : IsIso e M N) (h' : IsIso f N R) : IsIso (e.trans f) M R :=
  ⟨h.isWeakMap.trans h'.isWeakMap, h'.symm.isWeakMap.trans h.symm.isWeakMap⟩

theorem IsIso.groundEquiv (h : IsIso e M N) : GroundEquiv e M N := h.1.1

theorem GroundEquiv.isIso_of_map_indep_map_indep (he : GroundEquiv e M N)
    (hMN : ∀ ⦃I⦄, M.Indep I → N.Indep (e '' I)) (hNM : ∀ ⦃I⦄, N.Indep I → M.Indep (e.symm '' I)) :
    IsIso e M N :=
  ⟨he.isWeakMap_iff_symm_image_indep.2 hNM, he.symm.isWeakMap_iff_symm_image_indep.2 (by simpa)⟩

theorem GroundEquiv.isIso_of_map_isBase_map_isBase (he : GroundEquiv e M N)
    (hMN : ∀ ⦃B⦄, M.IsBase B → N.IsBase (e '' B)) (hNM : ∀ ⦃B⦄, N.IsBase B → M.IsBase (e.symm '' B)) :
      IsIso e M N :=
  ⟨he.isWeakMap_of_symm_image_isBase hNM, he.symm.isWeakMap_of_symm_image_isBase (by simpa)⟩

theorem IsIso.image_indep (h : IsIso e M N) {I : Set α} (hI : M.Indep I) : N.Indep (e '' I) := by
  simpa using h.symm.isWeakMap.symm_image_indep hI

theorem IsIso.indep_iff_image_indep (h : IsIso e M N) {I : Set α} (hIE : I ⊆ M.E := by aesop_mat) :
    M.Indep I ↔ N.Indep (e '' I) :=
  ⟨h.image_indep, fun hI ↦ h.isWeakMap.indep_of_image hI⟩

theorem IsIso.image_isBase (h : IsIso e M N) {B : Set α} (hB : M.IsBase B) : N.IsBase (e '' B) := by
  refine Indep.isBase_of_maximal (h.image_indep hB.indep) (fun J hJ heJ ↦ ?_)
  rw [hB.eq_of_subset_indep (h.isWeakMap.symm_image_indep hJ)
    (h.groundEquiv.subset_symm_image_of_image_subset hB.subset_ground heJ),
    h.groundEquiv.image_symm_image J]

theorem IsIso.image_dual_isBase (h : IsIso e M N) {B : Set α} (hB : M✶.IsBase B) :
    N✶.IsBase (e '' B) := by
  rw [dual_isBase_iff', and_iff_left <| h.groundEquiv.image_subset_ground B hB.subset_ground,
    ← h.groundEquiv.image_ground, ← h.groundEquiv.injOn.image_diff hB.subset_ground]
  exact (h.image_isBase <| hB.compl_isBase_of_dual)

theorem IsIso.dual (h : IsIso e M N) : IsIso e M✶ N✶ :=
  h.groundEquiv.dual.isIso_of_map_isBase_map_isBase (fun _ ↦ h.image_dual_isBase)
    (fun _ ↦ h.symm.image_dual_isBase)

def IsIso.restrict (h : IsIso e M N) {X : Set α} {Y : Set β} (hX : X ⊆ M.E := by aesop_mat)
    (hY : Y ⊆ N.E := by aesop_mat) (hXY : e.IsImage X Y) : IsIso hXY.restr (M ↾ X) (N ↾ Y) :=
  ⟨h.isWeakMap.restrict hX hY hXY, h.symm.isWeakMap.restrict hY hX hXY.symm⟩

def IsIso.restrict_left (h : IsIso e M N) (R : Set α) (hR : R ⊆ M.E := by aesop_mat) :
    IsIso (e.restr R) (M ↾ R) (N ↾ (e '' R)) := by
  have hR' := h.groundEquiv.image_isImage R
  rw [← hR'.restr_eq_restr_set]
  exact h.restrict hR (h.groundEquiv.image_subset_ground R) _

theorem IsIso.of_empty [Nonempty α] [Nonempty β] :
    IsIso PartialEquiv.empty (emptyOn α) (emptyOn β) :=
  ⟨IsWeakMap.of_empty,by simpa using IsWeakMap.of_empty⟩

section Iso

/-- We write `M ≃ N` if there is an isomorphism from `M` to `N`. This is defined as a disjunction
so it behaves mathematically correctly even when `α` or `β` is empty,
even though there may be no `e` with `IsIso e M N` in such cases.
(The aim is to save on unneccessary `Nonempty` assumptions in applications,
but perhaps this isn't worth the hassle) -/
def Iso : Matroid α → Matroid β → Prop := fun M N ↦
  (M = emptyOn α ∧ N = emptyOn β) ∨ ∃ e, IsIso e M N

infixl:65  " ≃ " => Iso

theorem Iso.empty_or_exists_isIso (h : M ≃ N) :
    (M = emptyOn α ∧ N = emptyOn β) ∨ ∃ e, IsIso e M N := h

@[simp] theorem iso_emptyOn_iff {M : Matroid α} {β : Type*} :
    M ≃ emptyOn β ↔ M = emptyOn α := by
  constructor
  · rintro (⟨rfl,-⟩ | ⟨⟨e, he⟩⟩ ); rfl
    exact he.groundEquiv.eq_emptyOn
  rintro rfl
  exact Or.inl ⟨rfl, rfl⟩

theorem Iso.symm {M : Matroid α} {N : Matroid β} (h : M ≃ N) : N ≃ M := by
  obtain (⟨hM,hN⟩ | ⟨⟨e,he⟩⟩)  := h
  · exact Or.inl ⟨hN, hM⟩
  exact Or.inr ⟨e.symm, he.symm⟩

theorem Iso.comm {M : Matroid α} {N : Matroid β} : M ≃ N ↔ N ≃ M :=
  ⟨Iso.symm, Iso.symm⟩

theorem Iso.refl (M : Matroid α) : M ≃ M :=
  Or.inr <| ⟨_, IsIso.refl M⟩

theorem IsIso.iso (h : IsIso e M N) : M ≃ N :=
  Or.inr ⟨e,h⟩

theorem Iso.trans {O : Matroid γ}
    (h1 : M ≃ N) (h2 : N ≃ O) : M ≃ O := by
  obtain (⟨rfl,rfl⟩ | ⟨⟨i1, hi1⟩⟩) := h1
  · rwa [Iso.comm, iso_emptyOn_iff] at h2 ⊢
  obtain (⟨rfl,rfl⟩ | ⟨⟨i2, hi2⟩⟩) := h2
  · rw [iso_emptyOn_iff]
    exact iso_emptyOn_iff.1 hi1.iso
  have := hi1.trans hi2
  exact Or.inr ⟨_, hi1.trans hi2⟩

theorem Iso.exists_isIso [Nonempty α] [Nonempty β] (h : M ≃ N) :
    ∃ e, IsIso e M N := by
  obtain (⟨rfl, rfl⟩ | ⟨⟨e, he⟩⟩) := h
  · exact ⟨_, IsIso.of_empty⟩
  exact ⟨e,he⟩

theorem Nonempty.iso_iff_exists_isIso (hM : M.Nonempty) : M ≃ N ↔ ∃ e, IsIso e M N := by
  rw [Iso, ← ground_eq_empty_iff, or_iff_right]
  exact not_and.2 fun a _ ↦ hM.ground_nonempty.ne_empty a

theorem Iso.finite_iff (h : M ≃ N) : M.Finite ↔ N.Finite := by
  obtain (⟨rfl,rfl⟩ | ⟨⟨e,he⟩⟩) := h
  · exact iff_of_true (finite_emptyOn α) (finite_emptyOn β)
  refine ⟨fun ⟨hfin⟩ ↦ ⟨?_⟩, fun ⟨hfin⟩ ↦ ⟨?_⟩⟩
  · rw [← he.groundEquiv.image_ground]
    exact hfin.image e
  rw [← he.symm.groundEquiv.image_ground]
  exact hfin.image _

theorem Iso.rankFinite_iff (h : M ≃ N) : M.RankFinite ↔ N.RankFinite := by
  obtain (⟨rfl,rfl⟩ | ⟨⟨e,he⟩⟩) := h
  · apply iff_of_true <;> infer_instance
  exact ⟨fun ⟨B, hB, hBfin⟩ ↦ ⟨e '' B, he.image_isBase hB, hBfin.image _⟩,
    fun ⟨B, hB, hBfin⟩ ↦ ⟨e.symm '' B, he.symm.image_isBase hB, hBfin.image _⟩⟩

theorem Iso.dual (h : M ≃ N) : M✶ ≃ N✶ := by
  obtain (⟨rfl, rfl⟩ | ⟨⟨e,he⟩⟩) := h
  · exact Or.inl ⟨by simp, by simp⟩
  exact Or.inr ⟨_,he.dual⟩

theorem isIso_dual_iff : M✶ ≃ N✶ ↔ M ≃ N := by
  refine ⟨fun h ↦ ?_, Iso.dual⟩
  rw [← dual_dual M, ← dual_dual N]
  exact h.dual

theorem iso_emptyOn_emptyOn (α β : Type*) : emptyOn α ≃ emptyOn β := by
  rw [iso_emptyOn_iff]

@[simp] theorem emptyOn_iso_iff {M : Matroid α} (β : Type*) : emptyOn β ≃ M ↔ M = emptyOn α := by
  rw [Iso.comm, iso_emptyOn_iff]

theorem iso_loopyOn_iff {M : Matroid α} {β : Type*} {E : Set β} :
    M ≃ loopyOn E ↔ M = loopyOn M.E ∧ Nonempty (M.E ≃ E) := by
  classical
  obtain (rfl | hM) := M.eq_emptyOn_or_nonempty
  · simp only [emptyOn_iso_iff, emptyOn_ground, loopyOn_empty, true_and]
    rw [← ground_eq_empty_iff, loopyOn_ground]
    exact ⟨by rintro rfl; exact ⟨Equiv.equivOfIsEmpty _ _⟩,
      fun ⟨e⟩ ↦ eq_empty_of_forall_notMem fun x hx ↦ by simpa using (e.symm ⟨x,hx⟩).2⟩

  simp only [hM.iso_iff_exists_isIso, eq_loopyOn_iff, true_and]
  refine ⟨fun ⟨e, he⟩ ↦ ⟨fun I _ hI ↦ by simpa using he.image_indep hI, ?_⟩, fun ⟨h,⟨e⟩⟩ ↦ ?_⟩
  · have h_e := e.toEquiv
    rw [he.groundEquiv.source_eq, he.groundEquiv.target_eq, loopyOn_ground] at h_e
    exact ⟨h_e⟩
  obtain ⟨x,hx⟩ := hM.ground_nonempty
  have _ : Nonempty α := ⟨x⟩
  have _ : Nonempty β := ⟨(e ⟨x,hx⟩)⟩
  refine ⟨PartialEquiv.ofSetEquiv e,
    GroundEquiv.isIso_of_map_indep_map_indep ⟨rfl,rfl⟩ ?_ (by simp)⟩
  · simp only [PartialEquiv.ofSetEquiv_apply, loopyOn_indep_iff, image_eq_empty]
    exact fun I hI ↦ h I hI.subset_ground hI

theorem iso_freeOn_iff {M : Matroid α} {β : Type*} {E : Set β} :
    M ≃ freeOn E ↔ M = freeOn M.E ∧ Nonempty (M.E ≃ E) := by
  rw [← isIso_dual_iff, freeOn_dual_eq, iso_loopyOn_iff, ← eq_dual_iff_dual_eq, dual_ground,
    loopyOn_dual_eq]

end Iso

section Map

theorem iso_map (M : Matroid α) (f : α → β) (hf : InjOn f M.E) : M ≃ M.map f hf := by
  obtain (rfl | hM) := M.eq_emptyOn_or_nonempty; simp
  have := hM.nonempty_type
  rw [hM.iso_iff_exists_isIso]
  have hg : GroundEquiv hf.toPartialEquiv M (M.map f hf) := ⟨by simp, by simp⟩
  refine ⟨_, hg.isIso_of_map_indep_map_indep ?_ ?_⟩
  · simp only [InjOn.toPartialEquiv, BijOn.toPartialEquiv_apply, map_indep_iff]
    exact fun I hI ↦ ⟨I,hI,rfl⟩
  simp only [map_indep_iff, InjOn.toPartialEquiv, BijOn.toPartialEquiv_symm_apply,
    forall_exists_index, and_imp]
  rintro _ I hI rfl
  rwa [hf.invFunOn_image hI.subset_ground]

theorem iso_comap (f : α ↪ β) {M : Matroid β} (hfE : range f = M.E) : M.comap f ≃ M := by
  obtain (rfl | hM) := M.eq_emptyOn_or_nonempty; simp
  obtain ⟨x,hx⟩ := hM.ground_nonempty
  obtain ⟨y, rfl⟩ := hfE.symm.subset hx
  have hf : BijOn f univ M.E := by
    suffices SurjOn (⇑f) univ (range ⇑f) by simpa [BijOn, f.injective.injOn univ, ← hfE]
    rintro y ⟨x,hx,rfl⟩; simp
  have _ : Nonempty α := ⟨y⟩
  have hg : GroundEquiv hf.toPartialEquiv (M.comap f) M := ⟨by simp [← hf.image_eq], by simp⟩
  refine Or.inr ⟨_, hg.isIso_of_map_indep_map_indep ?_ ?_⟩
  · simp only [comap_indep_iff, BijOn.toPartialEquiv_apply, and_imp]
    exact fun I hI _ ↦ hI
  simp only [BijOn.toPartialEquiv_symm_apply, comap_indep_iff, f.injective.injOn _, and_true]
  intro I hI
  rwa [hf.surjOn.image_invFun_image_subset_eq hI.subset_ground]

/-


/-- `M` is isomorphic to its image -/
noncomputable def iso_image [Nonempty α] (M : Matroid α) (f : α → β) (hf : InjOn f M.E) :
    Iso M (M.map f hf)  :=
  iso_of_forall_indep' hf.toPartialEquiv ( by simp ) ( by simp )
  ( by
    simp only [InjOn.toPartialEquiv, BijOn.toPartialEquiv_apply, image_indep_iff]
    refine fun I hIE ↦ ⟨fun hI ↦ ⟨I, hI, rfl⟩, fun ⟨I₀, hI₀, (h_eq : f '' _ = _)⟩ ↦ ?_⟩
    rw [hf.image_eq_image_iff_of_subset hIE hI₀.subset_ground] at h_eq
    rwa [h_eq] )

noncomputable def comap_iso [Nonempty α] {M : Matroid β} (hf : f.Injective)
    (hfE : range f = M.E) : Iso (M.comap f) M :=
  iso_of_forall_indep' (hf.injOn univ).toPartialEquiv (by simp [← hfE]) (by simpa)
    ( by simp [← hfE, hf.injOn _] )

@[simp] theorem comap_iso_coeFun [Nonempty α] {M : Matroid β} (hf : f.Injective)
    (hfE : range f = M.E) : (comap_iso hf hfE : α → β) = fun x ↦ f x := rfl


noncomputable def iso_onSubtype' (hX : X ⊆ M.E) (hne : X.Nonempty) : Iso (M.onSubtype X) (M ↾ X) :=
  have _ := nonempty_coe_sort.2 hne
  iso_of_forall_indep' (Subtype.coe_injective.injOn univ).toPartialEquiv
    (by simp [onSubtype_ground hX]) (by simp)
  ( by
    simp only [onSubtype_ground hX, subset_univ, InjOn.toPartialEquiv, image_univ,
      Subtype.range_coe_subtype, setOf_mem_eq, BijOn.toPartialEquiv_apply, restrict_indep_iff,
      image_subset_iff, Subtype.coe_preimage_self, and_true, forall_true_left]
    simp only [onSubtype._eq_1, comap_indep_iff, and_iff_left_iff_imp]
    intro I
    simp [Subtype.val_injective.injOn I] )

noncomputable def iso_onSubtype [M.Nonempty] (hE : M.E = E) : Iso M (M.onSubtype E) := by
  have hne : Nonempty E := by subst hE; exact nonempty_coe_sort.mpr M.ground_nonempty
  exact (comap_iso Subtype.val_injective (by rw [Subtype.range_val, ← hE])).symm

theorem isIso_onSubtype (M : Matroid α) (hE : M.E = E) : M ≃ M.onSubtype E := by
  obtain (rfl | hM) := M.eq_emptyOn_or_nonempty
  · simp only [emptyOn_ground] at hE; subst hE; simp
  exact (iso_onSubtype hE).isIso


/-- If `f` is locally a bijection, then `M` is isomorphic to its comap. -/
noncomputable def iso_comapOn [_root_.Nonempty α] (M : Matroid β) {f : α → β} {E : Set α}
    (hf : BijOn f E M.E) : Iso (M.comapOn E f) M :=
  iso_of_forall_indep'
  hf.toPartialEquiv
  ( by rw [BijOn.toPartialEquiv_source, comapOn_ground_eq] )
  hf.toPartialEquiv_target
  ( by
    simp only [comapOn_ground_eq, comapOn_indep_iff, BijOn.toPartialEquiv_apply,
      and_iff_left_iff_imp]
    exact fun I hIE _ ↦ ⟨hf.injOn.mono hIE, hIE⟩ )

theorem Iso.eq_comap {M : Matroid α} {N : Matroid β} (e : Iso M N) : M = N.comapOn M.E e := by
  simp only [ext_iff_indep, comapOn_ground_eq, comapOn_indep_iff, true_and]
  intro I hIE
  rw [and_iff_left hIE, ← e.on_indep_iff, iff_self_and]
  exact fun _ ↦ e.toPartialEquiv.bijOn.injOn.mono (by simpa)

-/

end Map





end Matroid
