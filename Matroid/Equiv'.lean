import Matroid.Constructions.Basic
import Matroid.ForMathlib.PartialEquiv
import Matroid.ForMathlib.Other


open Set


variable {α β γ : Type*} {M : Matroid α} {N : Matroid β} {R : Matroid γ} {e : PartialEquiv α β}
  {f : PartialEquiv β γ}

theorem PartialEquiv.image_isImage_of_subset_source (e : PartialEquiv α β) {s : Set α}
    (h : s ⊆ e.source) : e.IsImage s (e '' s) := by
  apply PartialEquiv.IsImage.of_image_eq
  rw [inter_eq_self_of_subset_right h, eq_comm, inter_eq_right]
  exact image_subset_target e h

theorem PartialEquiv.symm_image_isImage_of_subset_source (e : PartialEquiv α β) {s : Set β}
    (h : s ⊆ e.target) : e.IsImage (e.symm '' s) s := by
  simpa using e.symm.image_isImage_of_subset_source (s := s) (by simpa)

theorem PartialEquiv.IsImage.restr_eq_restr_set {s : Set α} {t : Set β} (h : e.IsImage s t) :
    h.restr = e.restr s := by
  ext <;> simp

namespace Matroid

section GroundEquiv

/-- `GroundEquiv e M N` means that `e : PartialEquiv` puts `M.E` and `N.E` in bijection.  -/
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
  replace hX := image_subset e hX
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
  replace hXY := image_subset e hXY
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

end GroundEquiv

section WeakMap

/-- `IsWeakMap e M N` means that `e` is a bijection mapping dependent sets to dependent sets. -/
structure IsWeakMap (e : PartialEquiv α β) (M : Matroid α) (N : Matroid β) : Prop :=
  (groundEquiv : GroundEquiv e M N)
  (image_dep : ∀ ⦃D⦄, M.Dep D → N.Dep (e '' D))

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

theorem GroundEquiv.isWeakMap_of_symm_image_base (h : GroundEquiv e M N)
    (h_base : ∀ ⦃B⦄, N.Base B → M.Base (e.symm '' B)) : IsWeakMap e M N :=
  h.isWeakMap_iff_symm_image_indep.2 fun _ ⟨_, hB, hIB⟩ ↦
    (h_base hB).indep.subset (image_subset _ hIB)

theorem IsWeakMap.restrict (h : IsWeakMap e M N) {X : Set α} (hX : X ⊆ M.E) {Y : Set β}
    (hY : Y ⊆ N.E) (hXY : e.IsImage X Y) :
    IsWeakMap hXY.restr (M ↾ X) (N ↾ Y) := by
  refine ⟨h.groundEquiv.restrict (M' := M ↾ X) (N' := N ↾ Y) hX hY hXY, ?_⟩
  simp only [restrict_dep_iff, PartialEquiv.IsImage.restr_apply, and_imp]
  refine fun D hD hDX ↦ ⟨fun hi ↦ hD (h.indep_of_image hi), ?_⟩
  have := image_subset e hDX
  rwa [← inter_eq_self_of_subset_right hY, ← h.groundEquiv.target_eq, ← hXY.image_eq,
    h.groundEquiv.source_eq, inter_eq_self_of_subset_right hX]

  -- exact fun D hD hDR ↦ ⟨fun hi ↦ hD (h.indep_of_image hi), hDR.trans <| subset_preimage_image e X⟩

-- theorem IsWeakMap.restrict_left (h : IsWeakMap e M N) (R : Set α) (hR : R ⊆ M.E := by aesop_mat) :
--     IsWeakMap (e.restr R) (M ↾ R) (N ↾ (e '' R)) := by
--   refine ⟨?_,?_⟩
--   · have he' : e.IsImage R (e '' R) :=
--       e.image_isImage_of_subset_source (by rwa [h.groundEquiv.source_eq])
--     have h' := h.groundEquiv.restrict (M' := M ↾ R) (N' := N ↾ (e '' R)) hR ?_ he'
--     · rwa [← e.isImage_restr_eq_restr] at h'
--     apply h.groundEquiv.image_subset_ground _
--   simp only [restrict_dep_iff, PartialEquiv.restr_coe, image_subset_iff, and_imp]
--   exact fun D hD hDR ↦ ⟨fun hi ↦ hD (h.indep_of_image hi), hDR.trans <| subset_preimage_image e R⟩

-- theorem IsWeakMap.restrict_right (h : IsWeakMap e M N) (R : Set β) (hR : R ⊆ N.E := by aesop_mat) :
--     IsWeakMap (e.symm.restr R).symm (M ↾ (e.symm '' R)) (N ↾ R) := by
--   refine ⟨?_, ?_⟩
--   ·

end WeakMap

def IsIso (e : PartialEquiv α β) (M : Matroid α) (N : Matroid β) : Prop :=
  IsWeakMap e M N ∧ IsWeakMap e.symm N M

theorem IsIso.symm (h : IsIso e M N) : IsIso e.symm N M := by
  simpa [IsIso, and_comm]

theorem IsIso.isWeakMap (h : IsIso e M N) : IsWeakMap e M N := h.1

theorem IsIso.groundEquiv (h : IsIso e M N) : GroundEquiv e M N := h.1.1

theorem GroundEquiv.isIso_of_map_base_map_base (he : GroundEquiv e M N)
    (hMN : ∀ ⦃B⦄, M.Base B → N.Base (e '' B)) (hNM : ∀ ⦃B⦄, N.Base B → M.Base (e.symm '' B)) :
      IsIso e M N :=
  ⟨he.isWeakMap_of_symm_image_base hNM, he.symm.isWeakMap_of_symm_image_base (by simpa)⟩

theorem IsIso.image_indep (h : IsIso e M N) {I : Set α} (hI : M.Indep I) : N.Indep (e '' I) := by
  simpa using h.symm.isWeakMap.symm_image_indep hI

theorem IsIso.indep_iff_image_indep (h : IsIso e M N) {I : Set α} (hIE : I ⊆ M.E := by aesop_mat) :
    M.Indep I ↔ N.Indep (e '' I) :=
  ⟨h.image_indep, fun hI ↦ h.isWeakMap.indep_of_image hI⟩

theorem IsIso.image_base (h : IsIso e M N) {B : Set α} (hB : M.Base B) : N.Base (e '' B) := by
  refine Indep.base_of_maximal (h.image_indep hB.indep) (fun J hJ heJ ↦ ?_)
  rw [hB.eq_of_subset_indep (h.isWeakMap.symm_image_indep hJ)
    (h.groundEquiv.subset_symm_image_of_image_subset hB.subset_ground heJ),
    h.groundEquiv.image_symm_image J]

theorem IsIso.image_dual_base (h : IsIso e M N) {B : Set α} (hB : M✶.Base B) :
    N✶.Base (e '' B) := by
  rw [dual_base_iff', and_iff_left <| h.groundEquiv.image_subset_ground B hB.subset_ground,
    ← h.groundEquiv.image_ground, ← h.groundEquiv.injOn.image_diff hB.subset_ground]
  exact (h.image_base <| hB.compl_base_of_dual)

theorem IsIso.dual (h : IsIso e M N) : IsIso e M✶ N✶ :=
  h.groundEquiv.dual.isIso_of_map_base_map_base (fun _ ↦ h.image_dual_base)
    (fun _ ↦ h.symm.image_dual_base)

def IsIso.restrict_left (h : IsIso e M N) (R : Set α) (hR : R ⊆ M.E := by aesop_mat) :
    IsIso (e.restr R) (M ↾ R) (N ↾ (e '' R)) := by
  have hRN := h.groundEquiv.image_subset_ground R
  have hR' : e.IsImage R (e '' R) :=
    e.image_isImage_of_subset_source (by rwa [h.groundEquiv.source_eq])
  rw [← hR'.restr_eq_restr_set]
  refine ⟨h.isWeakMap.restrict hR hRN hR', h.symm.isWeakMap.restrict hRN hR hR'.symm ⟩


  -- refine ⟨?_, ?_⟩
  -- · apply h.iseqk
  -- have := h.isWeakMap
    -- Iso (M ↾ R) (N ↾ (e '' R)


  -- have := h.symm.imagehB.compl_base_of_dual





-- /-- A `PartialEquiv` is a weak map from `M` to `N` if the preimage of every independent set is
--   independent-/
-- structure IsWeakMap (e : PartialEquiv α β) (M : Matroid α) (N : Matroid β) : Prop :=
--   (source_eq : e.source = M.E)
--   (target_eq : e.target = N.E)
--   (symm_image_indep : ∀ ⦃I⦄, N.Indep I → M.Indep (e.symm '' I))

-- theorem IsWeakMap.subset_source (h : IsWeakMap e M N) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
--     X ⊆ e.source :=
--   hX.trans (h.source_eq.symm.subset)

-- theorem IsWeakMap.subset_target (h : IsWeakMap e M N) (X : Set β) (hX : X ⊆ N.E := by aesop_mat) :
--     X ⊆ e.target :=
--   hX.trans (h.target_eq.symm.subset)

-- theorem IsWeakMap.dep_of_dep (h : IsWeakMap e M N) {D : Set α} (hD : M.Dep D) : N.Dep (e '' D) := by
--   rw [dep_iff, ← h.target_eq]
--   refine ⟨fun hi ↦ hD.not_indep ?_, e.image_subset_target (h.subset_source D)⟩
--   replace hi := h.symm_image_indep hi
--   rwa [e.symm_image_image_of_subset_source (h.subset_source D)] at hi

-- theorem isWeakMap_iff_dep_of_dep_forall (hM : e.source = M.E) (hN : e.target = N.E) :
--     IsWeakMap e M N ↔ ∀ {D}, M.Dep D → N.Dep (e '' D) := by
--   refine ⟨IsWeakMap.dep_of_dep, fun h ↦ IsWeakMap.mk hM⟩

-- structure WeakMap (M : Matroid α) (N : Matroid β) where
--   (toPartialEquiv : PartialEquiv α β)
--   (weakMap : IsWeakMap toPartialEquiv M N)

-- theorem IsWeakMap.trans {e : PartialEquiv α β} {e' : PartialEquiv β γ} (he : IsWeakMap e M N)
--     (he' : IsWeakMap e' N R) : IsWeakMap (e.trans e') M R where
--   source_eq := by
--     rw [e.trans_source, ← he.source_eq, he'.source_eq, ← he.target_eq, inter_eq_left]
--     exact e.source_subset_preimage_target
--   target_eq := by
--     rw [e.trans_target, ← he'.target_eq, inter_eq_left, he.target_eq, ← he'.source_eq]
--     exact e'.target_subset_preimage_source
--   symm_image_indep := by
--     intro I hI
--     replace hI := he.symm_image_indep <| he'.symm_image_indep hI
--     rw [image_image] at hI
--     rwa [PartialEquiv.trans_symm_eq_symm_trans_symm]

-- def WeakMap.trans (e : WeakMap M N) (f : WeakMap N R) : WeakMap M R where
--   toPartialEquiv := e.toPartialEquiv.trans f.toPartialEquiv
--   weakMap := e.weakMap.trans f.weakMap

-- def WeakLE (M N : Matroid α) := IsWeakMap (PartialEquiv.refl _) M N

-- infixl:50 " ≤w " => Matroid.WeakLE

-- -- theorem WeakLE.trans



end WeakMap
