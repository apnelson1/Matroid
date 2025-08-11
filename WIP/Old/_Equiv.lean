import Mathlib.Data.Matroid.Constructions
import Matroid.ForMathlib.PartialEquiv
import Matroid.ForMathlib.Function


-- TODO : refactor (maybe using `FunLike` so `toPartialEquiv` is invisible in the infoview)
namespace Matroid

open Set PartialEquiv

variable {α β γ α₁ α₂ α₃ : Type*} {M : Matroid α} {N : Matroid β} {B I D X Y : Set α}

/-- An isomorphism between two matroids. Sadly this doesn't exist if one has empty ground
  type and the other is an empty matroid on a nonempty type; this is a shortcoming of the
  implementation via `PartialEquiv`, which otherwise has many advantages.  -/
structure Iso (M : Matroid α) (N : Matroid β) where
  (toPartialEquiv : PartialEquiv α β)
  (source_eq' : toPartialEquiv.source = M.E)
  (target_eq' : toPartialEquiv.target = N.E)
  (setOf_isBase_eq' : setOf N.IsBase = (image toPartialEquiv) '' (setOf M.IsBase))

instance {M : Matroid α} {N : Matroid β} : CoeFun (Iso M N) (fun _ ↦ (α → β)) where
  coe e := (e.toPartialEquiv : α → β)

theorem Iso.setOf_isBase_eq (e : Iso M N) : setOf N.IsBase = (image e) '' (setOf M.IsBase) :=
  e.setOf_isBase_eq'

@[simp] theorem Iso.source_eq (e : Iso M N) : e.toPartialEquiv.source = M.E :=
  e.source_eq'

@[simp] theorem Iso.target_eq (e : Iso M N) : e.toPartialEquiv.target = N.E :=
  e.target_eq'

@[simp] theorem Iso.subset_source (e : Iso M N) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    X ⊆ e.toPartialEquiv.source :=
  hX.trans_eq e.source_eq.symm

@[simp] theorem Iso.subset_target (e : Iso M N) (X : Set β) (hX : X ⊆ N.E := by aesop_mat) :
    X ⊆ e.toPartialEquiv.target :=
  hX.trans_eq e.target_eq.symm

@[simp] theorem Iso.image_subset_target (e : Iso M N) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    e '' X ⊆ e.toPartialEquiv.target := by
  rw [← image_source_eq_target]; exact image_mono (e.subset_source X)

@[simp] theorem Iso.image_ground (e : Iso M N) : e '' M.E = N.E := by
  rw [← e.source_eq, ← e.target_eq, image_source_eq_target]

@[simp] theorem Iso.map_mem (e : Iso M N) {x : α} (hx : x ∈ M.E) : e x ∈ N.E :=
  e.image_ground.subset ⟨x,hx, rfl⟩

theorem Iso.ground_subset_preimage_ground (e : Iso M N) : M.E ⊆ e ⁻¹' N.E := by
  rw [← e.source_eq, ← e.target_eq]; exact source_subset_preimage_target e.toPartialEquiv

-- @[aesop unsafe 10% (rule_sets [Matroid])]
theorem Iso.image_subset_ground (e : Iso M N) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    e '' X ⊆ N.E := by
  convert image_mono hX
  rw [← e.source_eq, image_source_eq_target, e.target_eq]

theorem Iso.injOn_ground (e : Iso M N) : InjOn e M.E := by
  rw [← e.source_eq]; exact e.toPartialEquiv.injOn

theorem Iso.on_isBase_iff (e : Iso M N) (hB : B ⊆ M.E := by aesop_mat) :
    M.IsBase B ↔ N.IsBase (e '' B) := by
  change (_ ↔ _ ∈ setOf N.IsBase)
  simp_rw [e.setOf_isBase_eq', mem_image, mem_setOf_eq]
  refine' ⟨fun h ↦ ⟨B, h, rfl⟩, fun ⟨B', h, h'⟩ ↦ _⟩
  rw [e.injOn_ground.image_eq_image_iff_of_subset h.subset_ground hB] at h'
  rwa [← h']

def Iso.refl (M : Matroid α) : Iso M M where
  toPartialEquiv := ofSet M.E
  source_eq' := rfl
  target_eq' := rfl
  setOf_isBase_eq' := by simp

@[simp] theorem Iso.refl_toPartialEquiv (M : Matroid α) :
    (Iso.refl M).toPartialEquiv = ofSet M.E := rfl

def Iso.symm (e : Iso M N) : Iso N M where
  toPartialEquiv := e.toPartialEquiv.symm
  source_eq' := by rw [symm_source, e.target_eq']
  target_eq' := by rw [symm_target, e.source_eq']
  setOf_isBase_eq' := by
    { rw [e.setOf_isBase_eq']
      ext B
      simp only [mem_setOf_eq, mem_image, exists_exists_and_eq_and]
      refine' ⟨fun h ↦ ⟨B, h, _⟩, fun ⟨B', hB', h⟩ ↦ _⟩
      · exact symm_image_image_of_subset_source e.toPartialEquiv (by simp [h.subset_ground])
      rw [← h]; convert hB';
      exact symm_image_image_of_subset_source e.toPartialEquiv (by simp [hB'.subset_ground]) }

@[simp] theorem Iso.symm_toPartialEquiv (e : Iso M N) :
    e.symm.toPartialEquiv = e.toPartialEquiv.symm := rfl

def Iso.trans {M₁ : Matroid α₁} {M₂ : Matroid α₂} {M₃ : Matroid α₃} (e₁₂ : Iso M₁ M₂)
    (e₂₃ : Iso M₂ M₃) : Iso M₁ M₃ where
  toPartialEquiv := e₁₂.toPartialEquiv.trans e₂₃.toPartialEquiv
  source_eq' := by
  { rw [trans_source, e₁₂.source_eq', e₂₃.source_eq', ← e₁₂.target_eq', inter_eq_left,
    ← e₁₂.source_eq']
    exact source_subset_preimage_target _ }
  target_eq' := by
  { rw [trans_target, e₁₂.target_eq', e₂₃.target_eq', inter_eq_left, ← e₂₃.source_eq',
    ← e₂₃.target_eq']
    exact target_subset_preimage_source _ }
  setOf_isBase_eq' := by rw [e₂₃.setOf_isBase_eq', e₁₂.setOf_isBase_eq']; ext B; simp [image_image]

@[simp] theorem Iso.trans_toPartialEquiv {M₁ : Matroid α₁} {M₂ : Matroid α₂} {M₃ : Matroid α₃}
    (e₁₂ : Iso M₁ M₂) (e₂₃ : Iso M₂ M₃) :
  (e₁₂.trans e₂₃).toPartialEquiv = e₁₂.toPartialEquiv.trans e₂₃.toPartialEquiv := rfl

-- @[aesop unsafe 10% (rule_sets [Matroid])]
theorem Iso.image_symm_subset_ground (e : Iso M N) (X : Set β) (hX : X ⊆ N.E := by aesop_mat) :
    e.symm '' X ⊆ M.E :=
  e.symm.image_subset_ground X hX

@[simp] theorem Iso.symm_apply (e : Iso M N) : e.symm.toPartialEquiv = e.toPartialEquiv.symm := rfl

@[simp] theorem Iso.symm_symm (e : Iso M N) : e.symm.symm = e := by
  cases e; rfl

theorem Iso.apply_symm_apply_mem (e : Iso M N) {x : α} (hx : x ∈ M.E) : e.symm (e x) = x :=
  e.toPartialEquiv.leftInvOn (show x ∈ _ by rwa [e.source_eq])

theorem Iso.symm_apply_apply_mem (e : Iso M N) {x : β} (hx : x ∈ N.E) : e (e.symm x) = x :=
  e.symm.apply_symm_apply_mem hx

/-- Equal matroids are isomorphic -/
def Iso.ofEq {M N : Matroid α} (h : M = N) : Iso M N where
  toPartialEquiv := ofSet M.E
  source_eq' := rfl
  target_eq' := by simp [h]
  setOf_isBase_eq' := by simp [h]

@[simp] theorem Iso.ofEq_toPartialEquiv {M N : Matroid α} (h : M = N) :
    (Iso.ofEq h).toPartialEquiv = ofSet M.E := rfl

-- /-- A `PartialEquiv` behaving well on independent sets also gives an isomorphism -/
-- def Iso.of_forall_indep {M : Matroid α} {N : Matroid β} (f : PartialEquiv α β)
--     (h_source : f.source = M.E) (h_target : f.target = N.E)
--     (h_ind : ∀ I, I ⊆ M.E → (M.Indep I ↔ N.Indep (f '' I))) : Iso M N where
--   toPartialEquiv := f
--   source_eq' := h_source
--   target_eq' := h_target
--   setOf_isBase_eq' :=
--   ( by
--     ext B
--     have lN : ∀ {J}, J ⊆ N.E → f.symm '' J ⊆ M.E := fun hJ ↦
--       (image_subset f.symm hJ).trans (by rw [← h_target, ← h_source, f.symm_image_target_eq_source])
--     have hM' : ∀ {I}, I ⊆ M.E → f.symm '' (f '' I) = I :=
--       fun hI ↦ symm_image_image_of_subset_source _ (by rwa [h_source])
--     have hN' : ∀ {J}, J ⊆ N.E → f '' (f.symm '' J) = J :=
--       fun hJ ↦ image_symm_image_of_subset_target _ (by rwa [h_target])

--     have h_ind' : ∀ I ⊆ N.E, M.Indep (f.symm '' I) ↔ N.Indep I :=
--       fun I hI ↦ by rw [h_ind _ (lN hI), hN' hI]
--     simp only [mem_setOf_eq, mem_image, base_iff_maximal_indep]

--     refine ⟨fun ⟨hB, hB'⟩ ↦ ⟨f.symm '' B, ⟨?_, fun I hI hBI ↦ ?_⟩, hN' hB.subset_ground⟩, ?_⟩
--     · rwa [h_ind' _ hB.subset_ground]
--     · rw [hB' _ <| (h_ind _ hI.subset_ground).1 hI, hM' hI.subset_ground]
--       replace hBI := image_mono hBI
--       rwa [hN' hB.subset_ground] at hBI
--     rintro ⟨I, ⟨hI, hImax⟩, rfl⟩
--     rw [← h_ind _ hI.subset_ground, and_iff_right hI]
--     refine fun J hJ hIJ ↦ ?_
--     rw [hImax (f.symm '' J) ?_ ?_, hN' hJ.subset_ground]
--     · rwa [h_ind' _ hJ.subset_ground]
--     replace hIJ := image_subset f.symm hIJ
--     rwa [hM' hI.subset_ground] at hIJ )

-- @[simp] theorem Iso.of_forall_indep_apply {M : Matroid α} {N : Matroid β} (f : PartialEquiv α β)
--     (h_source : f.source = M.E) (h_target : f.target = N.E)
--     (h_ind : ∀ I, I ⊆ M.E → (M.Indep I ↔ N.Indep (f '' I))) :
--     (Iso.of_forall_indep f h_source h_target h_ind : α → β) = f := rfl



section transfer

-- Some generic theorems to carry a matroid `Set` property across an isomorphism

variable {PM : Set α → Prop} {PN : Set β → Prop}

/-- A matroid proposition transfers across an isomorphism-/
theorem Iso.setOf_prop_eq (e : Iso M N)
    (hN : ∀ {Y}, PN Y → Y ⊆ N.E) (hMN : ∀ {X}, PM X → PN (e '' X))
    (hNM : ∀ {Y}, PN Y → PM (e.symm '' Y)) : setOf PN = (image e) '' (setOf PM) := by
  refine' Set.ext (fun Y ↦ ⟨fun h ↦ _, _⟩)
  · refine' ⟨e.symm '' Y, hNM h, _⟩
    rw [symm_apply, image_symm_image_of_subset_target _ ((hN h).trans_eq e.target_eq.symm)]
  intro h; obtain ⟨X, hX, rfl⟩ := h
  exact hMN hX

theorem Iso.on_prop_symm (e : Iso M N) (on_prop : ∀ {Y}, PN Y → PM (e.symm '' Y)) (h : PN (e '' X))
    (hX : X ⊆ M.E := by aesop_mat) : PM X := by
  convert on_prop h; rw [symm_apply, symm_image_image_of_subset_source _ (e.subset_source X)]

theorem Iso.prop_subset_iff_subset (e : Iso M N) (hM : ∀ {X}, PM X → X ⊆ M.E) :
    ∀ ⦃X Y : Set α⦄, PM X → PM Y → (X ⊆ Y ↔ e '' X ⊆ e '' Y) :=
  fun _ _ hX hY ↦ (e.injOn_ground.image_subset_image_iff_of_subset (hM hX) (hM hY)).symm

end transfer

/-- A `PartialEquiv` that respects bases is an isomorphism. -/
def iso_of_forall_isBase (e : PartialEquiv α β) (hM : e.source = M.E) (hN : e.target = N.E)
    (on_isBase : ∀ B, M.IsBase B → N.IsBase (e '' B))
    (on_isBase_symm : ∀ B, N.IsBase B → M.IsBase (e.symm '' B)) : Iso M N where
  toPartialEquiv := e
  source_eq' := hM
  target_eq' := hN
  setOf_isBase_eq' := by
  { refine' Set.ext (fun B ↦ ⟨fun (hB : N.IsBase B) ↦ ⟨_, on_isBase_symm B hB,_⟩,_⟩)
    · rw [e.image_symm_image_of_subset_target (hB.subset_ground.trans_eq hN.symm)]
    rintro ⟨B, hB, rfl⟩
    exact on_isBase B hB }

/-- A `PartialEquiv` that respects independence is an isomorphism. -/
def iso_of_forall_indep (e : PartialEquiv α β) (hM : e.source = M.E) (hN : e.target = N.E)
    (on_indep : ∀ I, M.Indep I → N.Indep (e '' I))
    (on_indep_symm : ∀ I, N.Indep I → M.Indep (e.symm '' I)) : Iso M N where
  toPartialEquiv := e
  source_eq' := hM
  target_eq' := hN
  setOf_isBase_eq' := by
  { have setOfIndep : setOf N.Indep = (Set.image e) '' (setOf M.Indep) := by
      refine' subset_antisymm (fun I (hI : N.Indep I) ↦ ⟨_, on_indep_symm I hI, _⟩) _
      · rintro _ ⟨I, (hI : M.Indep I), rfl⟩; exact on_indep I hI
      · rw [e.image_symm_image_of_subset_target (hI.subset_ground.trans_eq hN.symm)]
    rw [setOf_isBase_eq_maximals_setOf_indep, setOfIndep, ← image_maximals_of_rel_iff_rel
      (r := (· ⊆ ·)), ← setOf_isBase_eq_maximals_setOf_indep]
    rintro I J (hI : M.Indep I) (hJ : M.Indep J)
    rw [e.injOn.image_subset_image_iff_of_subset (hI.subset_ground.trans hM.symm.subset)
      (hJ.subset_ground.trans hM.symm.subset)] }

@[simp] theorem iso_of_forall_indep_apply {M : Matroid α} {N : Matroid β} (e : PartialEquiv α β)
    (hM : e.source = M.E) (hN : e.target = N.E) (on_indep : ∀ I, M.Indep I → N.Indep (e '' I))
    (on_indep_symm : ∀ I, N.Indep I → M.Indep (e.symm '' I)) :
  (iso_of_forall_indep e hM hN on_indep on_indep_symm).toPartialEquiv = e := rfl

/-- Empty matroids (on nonempty types) are isomorphic. -/
noncomputable def Iso.of_emptyOn [Nonempty α] [Nonempty β] : (emptyOn α).Iso (emptyOn β) :=
  let f : (α → β) := Classical.arbitrary _
  iso_of_forall_indep ((injOn_empty f).toPartialEquiv) (by simp) (by simp) (by simp) (by simp)

def iso_of_forall_indep' (e : PartialEquiv α β) (hM : e.source = M.E) (hN : e.target = N.E)
    (on_indep : ∀ I, I ⊆ M.E → (M.Indep I ↔ N.Indep (e '' I))) : Iso M N :=
  iso_of_forall_indep e hM hN (fun I hI ↦ (on_indep I hI.subset_ground).mp hI)
    (by
      intro I hI
      have h' : e.symm '' I ⊆ M.E := by
        rw [← hM, ← symm_image_target_eq_source, hN]; exact image_mono hI.subset_ground
      rwa [on_indep _ h', image_symm_image_of_subset_target _
        (by rw [hN]; exact hI.subset_ground)] )

@[simp] theorem iso_of_forall_indep'_apply {M : Matroid α} {N : Matroid β} (e : PartialEquiv α β)
    (hM : e.source = M.E) (hN : e.target = N.E)
    (on_indep : ∀ I, I ⊆ M.E → (M.Indep I ↔ N.Indep (e '' I))) :
  (iso_of_forall_indep' e hM hN on_indep).toPartialEquiv = e := rfl

theorem Iso.on_isBase (e : Iso M N) (hB : M.IsBase B) : N.IsBase (e '' B) := by
  rwa [← e.on_isBase_iff]

theorem Iso.on_indep (e : Iso M N) (hI : M.Indep I) : N.Indep (e '' I) := by
  change (_ ∈ (setOf N.Indep))
  rw [setOf_indep_eq, e.setOf_isBase_eq]
  simp only [SetLike.mem_coe, mem_lowerClosure, mem_image, mem_setOf_eq, le_eq_subset,
    image_subset_iff, exists_exists_and_eq_and]
  obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
  exact ⟨B, hB, hIB.trans (subset_preimage_image _ _)⟩

theorem Iso.on_indep_symm (e : Iso M N) (h : N.Indep (e '' I)) (hI : I ⊆ M.E := by aesop_mat) :
    M.Indep I :=
  e.on_prop_symm (e.symm.on_indep) h

theorem Iso.on_indep_iff (e : Iso M N) (hI : I ⊆ M.E := by aesop_mat) :
    M.Indep I ↔ N.Indep (e '' I) := by
  refine ⟨e.on_indep, fun h ↦ e.on_indep_symm h hI⟩

theorem Iso.setOf_indep_eq (e : Iso M N) : setOf N.Indep = (image e) '' (setOf M.Indep) :=
  e.setOf_prop_eq Indep.subset_ground e.on_indep e.symm.on_indep

theorem Iso.on_isBase_symm (e : Iso M N) (h : N.IsBase (e '' B)) (hB : B ⊆ M.E := by aesop_mat) :
    M.IsBase B :=
  e.on_prop_symm (e.symm.on_isBase) h

theorem Iso.on_dep (e : Iso M N) (h : M.Dep D) : N.Dep (e '' D) := by
  rw [Dep, and_iff_left (e.image_subset_ground D)]; exact fun hI ↦ h.not_indep (e.on_indep_symm hI)

theorem Iso.on_dep_symm (e : Iso M N) (h : N.Dep (e '' D)) (hD : D ⊆ M.E := by aesop_mat) :
    M.Dep D :=
  e.on_prop_symm (e.symm.on_dep) h

theorem Iso.setOf_dep_eq (e : Iso M N) : setOf N.Dep = (image e) '' setOf M.Dep :=
  e.setOf_prop_eq Dep.subset_ground e.on_dep e.symm.on_dep

theorem Iso.encard_ground_eq (e : Iso M N) : M.E.encard = N.E.encard := by
  rw [← e.image_ground, e.injOn_ground.encard_image]

/-- The duals of isomorphic matroids are isomorphic -/
def Iso.dual (e : Iso M N) : Iso M✶ N✶ :=
  iso_of_forall_isBase e.toPartialEquiv
    (by simp) (by simp)
    (by {
      simp_rw [dual_isBase_iff', image_subset_iff, and_imp]
      refine fun B hB hBE ↦ ⟨?_, hBE.trans e.ground_subset_preimage_ground⟩
      convert e.on_isBase hB
      rw [e.injOn_ground.image_diff hBE, e.image_ground] } )
    (by {
      simp only [image_subset_iff, dual_isBase_iff', and_imp]
      refine fun B hB hBE ↦ ⟨?_, hBE.trans e.symm.ground_subset_preimage_ground⟩
      convert e.symm.on_isBase hB
      rw [e.symm.injOn_ground.image_diff hBE, e.symm.image_ground, symm_apply] } )

@[simp] theorem Iso.dual_apply (e : Iso M N) : e.dual.toPartialEquiv = e.toPartialEquiv := rfl

/-- Restrictions of isomorphic matroids are isomorphic -/
def Iso.restrict (e : Iso M N) (R : Set α) (hR : R ⊆ M.E := by aesop_mat) :
    Iso (M ↾ R) (N ↾ (e '' R)) :=
  iso_of_forall_indep (e.toPartialEquiv.restr R)
  (by simpa [restrict_ground_eq])
  (by rw [restr_target, restrict_ground_eq,
    image_eq_target_inter_inv_preimage _ (by rwa [e.source_eq])] )

  (by {
    simp only [restrict_indep_iff, restr_coe, image_subset_iff, and_imp]
    exact fun I hI hIR ↦ ⟨e.on_indep hI, hIR.trans (subset_preimage_image _ _)⟩ })
  (by {
    simp only [restrict_indep_iff, restr_coe_symm, image_subset_iff, and_imp]
    refine' fun I hI hIR ↦ ⟨e.symm.on_indep hI, hIR.trans _⟩
    rw [image_eq_target_inter_inv_preimage _ (by rwa [e.source_eq])]
    apply inter_subset_right })

@[simp] theorem Iso.restrict_apply (e : Iso M N) {R : Set α} (hR : R ⊆ M.E := by aesop_mat) :
    (e.restrict R hR).toPartialEquiv = e.toPartialEquiv.restr R := by
  simp [restrict]

theorem Iso.on_isBasis (e : Iso M N) (hI : M.IsBasis I X) : N.IsBasis (e '' I) (e '' X) := by
  rw [← base_restrict_iff _, (e.restrict X).symm.on_isBase_iff _, base_restrict_iff]
  · convert hI
    simp only [symm_apply, restrict_apply, restr_coe_symm]
    apply e.toPartialEquiv.symm_image_image_of_subset_source
    rw [e.source_eq]
    exact hI.indep.subset_ground
  · simp only [restrict_ground_eq]
    exact image_mono hI.subset
  exact e.image_subset_ground X hI.subset_ground

section IsIso

variable {M : Matroid α} {N : Matroid β}

/-- We write `M ≂ N` if there is an isomorphism from `M` to `N`. This is defined as
  a disjunction so it behaves mathematically correctly even when `α` or `β` is empty,
  even though `M.Iso N` may be 'incorrectly' empty in such cases. -/
def IsIso : Matroid α → Matroid β → Prop := fun M N ↦
  (M = emptyOn α ∧ N = emptyOn β) ∨ Nonempty (M.Iso N)

infixl:65  " ≂ " => IsIso

@[simp] theorem isIso_emptyOn_iff {M : Matroid α} {β : Type*} : M ≂ emptyOn β ↔ M = emptyOn α := by
  constructor
  · rintro (⟨rfl,-⟩ | ⟨⟨i⟩⟩ ); rfl
    rw [← ground_eq_empty_iff, ← i.symm.image_ground]
    simp
  rintro rfl
  exact Or.inl ⟨rfl, rfl⟩

theorem IsIso.symm {M : Matroid α} {N : Matroid β} (h : M ≂ N) : N ≂ M := by
  obtain (⟨hM,hN⟩ | ⟨⟨e⟩⟩)  := h
  · exact Or.inl ⟨hN, hM⟩
  exact Or.inr ⟨e.symm⟩

theorem IsIso.comm {M : Matroid α} {N : Matroid β} : M ≂ N ↔ N ≂ M :=
  ⟨IsIso.symm, IsIso.symm⟩

theorem IsIso.refl (M : Matroid α) : M ≂ M :=
  Or.inr ⟨Iso.refl M⟩

theorem Iso.isIso (h : M.Iso N) : M ≂ N :=
  Or.inr ⟨h⟩

theorem IsIso.trans {O : Matroid γ}
    (h1 : M ≂ N) (h2 : N ≂ O) : M ≂ O := by
  obtain (⟨rfl,rfl⟩ | ⟨⟨i1⟩⟩) := h1
  · rwa [IsIso.comm, isIso_emptyOn_iff] at h2 ⊢
  obtain (⟨rfl,rfl⟩ | ⟨⟨i2⟩⟩) := h2
  · rw [isIso_emptyOn_iff]
    exact isIso_emptyOn_iff.1 i1.isIso
  exact Or.inr ⟨i1.trans i2⟩

theorem IsIso.empty_or_nonempty_iso (h : M ≂ N) :
    (M = emptyOn α ∧ N = emptyOn β) ∨ (Nonempty α ∧ Nonempty β ∧ Nonempty (M.Iso N)) := by
  obtain (⟨rfl,rfl⟩ | ⟨⟨e⟩⟩) := h
  · exact Or.inl ⟨rfl,rfl⟩
  cases isEmpty_or_nonempty α
  · left
    obtain rfl := eq_emptyOn M
    simp [isIso_emptyOn_iff.1 e.symm.isIso]
  cases isEmpty_or_nonempty β
  · left
    obtain rfl := eq_emptyOn N
    simp [isIso_emptyOn_iff.1 e.isIso]
  right
  exact ⟨by assumption, by assumption, ⟨e⟩⟩

theorem IsIso.nonempty_iso [Nonempty α] [Nonempty β] (h : M ≂ N) :
    Nonempty (M.Iso N) := by
  obtain (⟨rfl, rfl⟩ | ⟨⟨e⟩⟩) := h
  · exact ⟨Iso.of_emptyOn⟩
  exact ⟨e⟩

/-- Noncomputably choose an `Iso M N` from `M ≂ N` whenever both ground types are nonempty -/
noncomputable def IsIso.iso [Nonempty α] [Nonempty β] (h : M ≂ N) :
    Iso M N := h.nonempty_iso.some

theorem IsIso.finite_iff (h : M ≂ N) : M.Finite ↔ N.Finite := by
  obtain (⟨rfl,rfl⟩ | ⟨⟨e⟩⟩) := h
  · exact iff_of_true (finite_emptyOn α) (finite_emptyOn β)
  refine ⟨fun ⟨h⟩ ↦ ⟨?_⟩, fun ⟨h⟩ ↦ ⟨?_⟩⟩
  · rw [← encard_ne_top_iff] at h ⊢
    rwa [e.encard_ground_eq] at h
  rw [← encard_ne_top_iff] at h ⊢
  rwa [e.encard_ground_eq]

theorem IsIso.rankFinite_iff (h : M ≂ N) : M.RankFinite ↔ N.RankFinite := by
  obtain (⟨rfl,rfl⟩ | ⟨⟨e⟩⟩) := h
  · apply iff_of_true <;> infer_instance
  exact ⟨fun ⟨B, hB, hBfin⟩ ↦ ⟨e '' B, e.on_isBase hB, hBfin.image _⟩,
    fun ⟨B, hB, hBfin⟩ ↦ ⟨e.symm '' B, e.symm.on_isBase hB, hBfin.image _⟩⟩

theorem IsIso.dual (h : M ≂ N) : M✶ ≂ N✶ := by
  obtain (⟨rfl, rfl⟩ | ⟨⟨e⟩⟩) := h
  · exact Or.inl ⟨by simp, by simp⟩
  exact Or.inr ⟨e.dual⟩

theorem isIso_dual_iff : M✶ ≂ N✶ ↔ M ≂ N := by
  refine ⟨fun h ↦ ?_, IsIso.dual⟩
  rw [← dual_dual M, ← dual_dual N]
  exact h.dual

theorem isIso_emptyOn_emptyOn (α β : Type*) : emptyOn α ≂ emptyOn β := by
  rw [isIso_emptyOn_iff]

@[simp] theorem emptyOn_isIso_iff {M : Matroid α} (β : Type*) : emptyOn β ≂ M ↔ M = emptyOn α := by
  rw [IsIso.comm, isIso_emptyOn_iff]

theorem isIso_loopyOn_iff {M : Matroid α} {β : Type*} {E : Set β} :
    M ≂ loopyOn E ↔ M = loopyOn M.E ∧ Nonempty (M.E ≃ E) := by
  classical
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain (⟨rfl,hLoopy⟩ | ⟨-, -, ⟨e⟩⟩) := h.empty_or_nonempty_iso
    · simp only [emptyOn_ground, loopyOn_empty, true_and]
      rw [← ground_eq_empty_iff, loopyOn_ground] at hLoopy
      subst hLoopy
      exact Fintype.card_eq.mp rfl
    rw [eq_loopyOn_iff, and_iff_right rfl]
    refine ⟨fun I _ hI ↦ by simpa using e.on_indep hI, ?_⟩
    · convert Nonempty.intro e.toPartialEquiv.toEquiv <;> simp
  rintro ⟨hM, ⟨e⟩⟩
  cases isEmpty_or_nonempty α
  · simp only [eq_emptyOn, emptyOn_isIso_iff, ← ground_eq_empty_iff, loopyOn_ground]
    exact isEmpty_coe_sort.1 e.symm.isEmpty
  cases isEmpty_or_nonempty β
  · simp only [eq_emptyOn, isIso_emptyOn_iff]
    rw [← ground_eq_empty_iff, ← isEmpty_coe_sort]
    rw [E.eq_empty_of_isEmpty] at e
    exact e.isEmpty
  refine (iso_of_forall_indep (PartialEquiv.ofSetEquiv e) (by simp) (by simp) ?_ (by simp)).isIso
  intro I hI
  simp only [ext_iff_indep, loopyOn_ground, loopyOn_indep_iff, true_and] at hM
  simpa using (hM I hI.subset_ground).1 hI


theorem isIso_freeOn_iff {M : Matroid α} {β : Type*} {E : Set β} :
    M ≂ freeOn E ↔ M = freeOn M.E ∧ Nonempty (M.E ≃ E) := by
  rw [← isIso_dual_iff, freeOn_dual_eq, isIso_loopyOn_iff, ← eq_dual_iff_dual_eq, dual_ground,
    loopyOn_dual_eq]

end IsIso

--   refine ⟨fun h ↦ ?_, fun ⟨h, ⟨i⟩⟩ ↦ ?_⟩
--   · obtain (⟨hM, hN⟩ | ⟨⟨i⟩⟩) := h
--     · rw [loopyOn_ground] at hN
--       obtain rfl := ground_eq_empty_iff.1 hM
--       simp only [emptyOn_ground, loopyOn_empty, hN, true_and]
--       exact Fintype.card_eq.mp rfl
--     refine ⟨?_, ⟨by simpa using i.toPartialEquiv.bijOn.equiv⟩⟩
--     apply ext_indep (by simp) fun I hIE ↦ ?_
--     rw [i.on_indep_iff, loopyOn_indep_iff, loopyOn_indep_iff, image_eq_empty]
--     sorry



end Matroid
