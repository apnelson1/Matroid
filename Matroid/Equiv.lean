import Matroid.Constructions.Basic
import Mathlib.Logic.Equiv.LocalEquiv
import Matroid.ForMathlib.Other

namespace Matroid

open Set LocalEquiv

variable {α β α₁ α₂ α₃ : Type*}

/-- An isomorphism between two matroids. Sadly this doesn't exist if one has empty ground
  type and the other is an empty matroid on a nonempty type; this is a shortcoming of the
  implementation via `LocalEquiv`, which otherwise has many advantages.  -/
structure Iso (M : Matroid α) (N : Matroid β) where
  (toLocalEquiv : LocalEquiv α β)
  (source_eq' : toLocalEquiv.source = M.E)
  (target_eq' : toLocalEquiv.target = N.E)
  (setOf_base_eq' : setOf N.Base = (image toLocalEquiv) '' (setOf M.Base))

instance {M : Matroid α} {N : Matroid β} : CoeFun (Iso M N) (fun _ ↦ (α → β)) where
  coe e := (e.toLocalEquiv : α → β)

theorem Iso.setOf_base_eq (e : Iso M N) : setOf N.Base = (image e) '' (setOf M.Base) :=
  e.setOf_base_eq'

@[simp] lemma Iso.source_eq (e : Iso M N) : e.toLocalEquiv.source = M.E :=
  e.source_eq'

@[simp] lemma Iso.target_eq (e : Iso M N) : e.toLocalEquiv.target = N.E :=
  e.target_eq'

@[simp] lemma Iso.subset_source (e : Iso M N) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    X ⊆ e.toLocalEquiv.source :=
  hX.trans_eq e.source_eq.symm

@[simp] lemma Iso.subset_target (e : Iso M N) (X : Set β) (hX : X ⊆ N.E := by aesop_mat) :
    X ⊆ e.toLocalEquiv.target :=
  hX.trans_eq e.target_eq.symm

@[simp] lemma Iso.image_subset_target (e : Iso M N) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    e '' X ⊆ e.toLocalEquiv.target := by
  rw [←image_source_eq_target]; exact image_subset _ (e.subset_source X)

@[simp] lemma Iso.image_ground (e : Iso M N) : e '' M.E = N.E := by
  rw [←e.source_eq, ←e.target_eq, image_source_eq_target]

lemma Iso.ground_subset_preimage_ground (e : Iso M N) : M.E ⊆ e ⁻¹' N.E := by
  rw [←e.source_eq, ←e.target_eq]; exact source_subset_preimage_target e.toLocalEquiv

@[aesop unsafe 10% (rule_sets [Matroid])]
theorem Iso.image_subset_ground (e : Iso M N) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    e '' X ⊆ N.E := by
  convert image_subset _ hX
  rw [←e.source_eq, image_source_eq_target, e.target_eq]

lemma Iso.injOn_ground (e : Iso M N) : InjOn e M.E := by
  rw [←e.source_eq]; exact e.toLocalEquiv.injOn

theorem Iso.on_base_iff (e : Iso M N) (hB : B ⊆ M.E := by aesop_mat) :
    M.Base B ↔ N.Base (e '' B) := by
  change (_ ↔ _ ∈ setOf N.Base)
  simp_rw [e.setOf_base_eq', mem_image, mem_setOf_eq]
  refine' ⟨fun h ↦ ⟨B, h, rfl⟩, fun ⟨B', h, h'⟩ ↦ _⟩
  rw [e.injOn_ground.image_eq_image_iff_of_subset h.subset_ground hB] at h'
  rwa [←h']

def Iso.refl (M : Matroid α) : Iso M M where
  toLocalEquiv := ofSet M.E
  source_eq' := rfl
  target_eq' := rfl
  setOf_base_eq' := by simp

@[simp] theorem Iso.refl_toLocalEquiv (M : Matroid α) :
    (Iso.refl M).toLocalEquiv = ofSet M.E := rfl

def Iso.symm (e : Iso M N) : Iso N M where
  toLocalEquiv := e.toLocalEquiv.symm
  source_eq' := by rw [symm_source, e.target_eq']
  target_eq' := by rw [symm_target, e.source_eq']
  setOf_base_eq' := by
    { rw [e.setOf_base_eq']
      ext B
      simp only [mem_setOf_eq, mem_image, exists_exists_and_eq_and]
      refine' ⟨fun h ↦ ⟨B, h, _⟩, fun ⟨B', hB', h⟩ ↦ _⟩
      · exact symm_image_image_of_subset_source e.toLocalEquiv (by simp [h.subset_ground])
      rw [←h]; convert hB';
      exact symm_image_image_of_subset_source e.toLocalEquiv (by simp [hB'.subset_ground]) }

@[simp] theorem Iso.symm_toLocalEquiv (e : Iso M N) :
    e.symm.toLocalEquiv = e.toLocalEquiv.symm := rfl

def Iso.trans {M₁ : Matroid α₁} {M₂ : Matroid α₂} {M₃ : Matroid α₃} (e₁₂ : Iso M₁ M₂)
    (e₂₃ : Iso M₂ M₃) : Iso M₁ M₃ where
  toLocalEquiv := e₁₂.toLocalEquiv.trans e₂₃.toLocalEquiv
  source_eq' := by
  { rw [trans_source, e₁₂.source_eq', e₂₃.source_eq', ←e₁₂.target_eq', inter_eq_left,
    ←e₁₂.source_eq']
    exact source_subset_preimage_target _ }
  target_eq' := by
  { rw [trans_target, e₁₂.target_eq', e₂₃.target_eq', inter_eq_left, ←e₂₃.source_eq',
    ←e₂₃.target_eq']
    exact target_subset_preimage_source _ }
  setOf_base_eq' := by rw [e₂₃.setOf_base_eq', e₁₂.setOf_base_eq']; ext B; simp [image_image]

@[simp] theorem Iso.trans_toLocalEquiv {M₁ : Matroid α₁} {M₂ : Matroid α₂} {M₃ : Matroid α₃}
    (e₁₂ : Iso M₁ M₂) (e₂₃ : Iso M₂ M₃) :
  (e₁₂.trans e₂₃).toLocalEquiv = e₁₂.toLocalEquiv.trans e₂₃.toLocalEquiv := rfl

@[aesop unsafe 10% (rule_sets [Matroid])]
theorem Iso.image_symm_subset_ground (e : Iso M N) (X : Set β) (hX : X ⊆ N.E := by aesop_mat) :
    e.symm '' X ⊆ M.E :=
  e.symm.image_subset_ground X hX

@[simp] theorem Iso.symm_apply (e : Iso M N) : e.symm.toLocalEquiv = e.toLocalEquiv.symm := rfl

/-- Equal matroids are isomorphic -/
def Iso.ofEq {M N : Matroid α} (h : M = N) : Iso M N where
  toLocalEquiv := ofSet M.E
  source_eq' := rfl
  target_eq' := by simp [h]
  setOf_base_eq' := by simp [h]

@[simp] theorem Iso.ofEq_toLocalEquiv {M N : Matroid α} (h : M = N) :
    (Iso.ofEq h).toLocalEquiv = ofSet M.E := rfl

/-- A `LocalEquiv` behaving well on independent sets also gives an isomorphism -/
def Iso.of_forall_indep {M : Matroid α} {N : Matroid β} (f : LocalEquiv α β)
    (h_source : f.source = M.E) (h_target : f.target = N.E)
    (h_ind : ∀ I, I ⊆ M.E → (M.Indep I ↔ N.Indep (f '' I))) : Iso M N where
  toLocalEquiv := f
  source_eq' := h_source
  target_eq' := h_target
  setOf_base_eq' :=
  ( by
    rw [setOf_base_eq_maximals_setOf_indep, setOf_base_eq_maximals_setOf_indep,
      ←maximals_image_of_rel_iff_rel_on (f := image f) (s := (· ⊆ ·))]
    · convert rfl
      ext I
      simp_rw [mem_image, mem_setOf]
      refine ⟨?_, fun h ↦ ?_⟩
      · rintro ⟨I, hI, rfl⟩
        rwa [h_ind _ hI.subset_ground] at hI
      use f.symm '' I
      rwa [h_ind, f.image_symm_image_of_subset_target (h.subset_ground.trans_eq h_target.symm),
        and_iff_left rfl]
      refine (image_subset _ h.subset_ground).trans ?_
      rw [←h_target, ←h_source, f.symm_image_target_eq_source]
    rintro I J (hI : M.Indep I) (hJ : M.Indep J)
    rw [f.injOn.image_subset_image_iff_of_subset
      (hI.subset_ground.trans_eq h_source.symm) (hJ.subset_ground.trans_eq h_source.symm)] )

@[simp] theorem Iso.of_forall_indep_apply {M : Matroid α} {N : Matroid β} (f : LocalEquiv α β)
    (h_source : f.source = M.E) (h_target : f.target = N.E)
    (h_ind : ∀ I, I ⊆ M.E → (M.Indep I ↔ N.Indep (f '' I))) :
    (Iso.of_forall_indep f h_source h_target h_ind : α → β) = f := rfl

/-- Empty matroids (on nonempty types) are isomorphic. -/
noncomputable def Iso.of_emptyOn [Nonempty α] [Nonempty β] : (emptyOn α).Iso (emptyOn β) :=
  let f : (α → β) := Pi.Nonempty.some
  Iso.of_forall_indep ((injOn_empty f).toLocalEquiv) (by simp) (by simp) (by simp)

section transfer

-- Some generic lemmas to carry a matroid `Set` property across an isomorphism

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

/-- A `LocalEquiv` that respects bases is an isomorphism. -/
def iso_of_forall_base (e : LocalEquiv α β) (hM : e.source = M.E) (hN : e.target = N.E)
    (on_base : ∀ B, M.Base B → N.Base (e '' B))
    (on_base_symm : ∀ B, N.Base B → M.Base (e.symm '' B)) : Iso M N where
  toLocalEquiv := e
  source_eq' := hM
  target_eq' := hN
  setOf_base_eq' := by
  { refine' Set.ext (fun B ↦ ⟨fun (hB : N.Base B) ↦ ⟨_, on_base_symm B hB,_⟩,_⟩)
    · rw [e.image_symm_image_of_subset_target (hB.subset_ground.trans_eq hN.symm)]
    rintro ⟨B, hB, rfl⟩
    exact on_base B hB }

/-- A `LocalEquiv` that respects independence is an isomorphism. -/
def iso_of_forall_indep (e : LocalEquiv α β) (hM : e.source = M.E) (hN : e.target = N.E)
    (on_indep : ∀ I, M.Indep I → N.Indep (e '' I))
    (on_indep_symm : ∀ I, N.Indep I → M.Indep (e.symm '' I)) : Iso M N where
  toLocalEquiv := e
  source_eq' := hM
  target_eq' := hN
  setOf_base_eq' := by
  { have setOfIndep : setOf N.Indep = (Set.image e) '' (setOf M.Indep)
    · refine' subset_antisymm (fun I (hI : N.Indep I) ↦ ⟨_, on_indep_symm I hI, _⟩) _
      · rintro _ ⟨I, (hI : M.Indep I), rfl⟩; exact on_indep I hI
      · rw [e.image_symm_image_of_subset_target (hI.subset_ground.trans_eq hN.symm)]
    rw [setOf_base_eq_maximals_setOf_indep, setOfIndep,
      maximals_image_of_rel_iff_rel_on (r := (· ⊆ ·)), ←setOf_base_eq_maximals_setOf_indep]
    rintro I J (hI : M.Indep I) (hJ : M.Indep J)
    rw [e.injOn.image_subset_image_iff_of_subset (hI.subset_ground.trans hM.symm.subset)
      (hJ.subset_ground.trans hM.symm.subset)] }

@[simp] theorem iso_of_forall_indep_apply {M : Matroid α} {N : Matroid β} (e : LocalEquiv α β)
    (hM : e.source = M.E) (hN : e.target = N.E) (on_indep : ∀ I, M.Indep I → N.Indep (e '' I))
    (on_indep_symm : ∀ I, N.Indep I → M.Indep (e.symm '' I)) :
  (iso_of_forall_indep e hM hN on_indep on_indep_symm).toLocalEquiv = e := rfl

def iso_of_forall_indep' (e : LocalEquiv α β) (hM : e.source = M.E) (hN : e.target = N.E)
    (on_indep : ∀ I, I ⊆ M.E → (M.Indep I ↔ N.Indep (e '' I))) : Iso M N :=
  iso_of_forall_indep e hM hN (fun I hI ↦ (on_indep I hI.subset_ground).mp hI)
    (by {
      intro I hI
      have h' : e.symm '' I ⊆ M.E
      · rw [←hM, ←symm_image_target_eq_source, hN]; exact image_subset _ hI.subset_ground
      rwa [on_indep _ h', image_symm_image_of_subset_target _
        (by rw [hN]; exact hI.subset_ground)] })

@[simp] theorem iso_of_forall_indep'_apply {M : Matroid α} {N : Matroid β} (e : LocalEquiv α β)
    (hM : e.source = M.E) (hN : e.target = N.E)
    (on_indep : ∀ I, I ⊆ M.E → (M.Indep I ↔ N.Indep (e '' I))) :
  (iso_of_forall_indep' e hM hN on_indep).toLocalEquiv = e := rfl

theorem Iso.on_base (e : Iso M N) (hB : M.Base B) : N.Base (e '' B) := by
  rwa [←e.on_base_iff]

lemma Iso.on_indep (e : Iso M N) (hI : M.Indep I) : N.Indep (e '' I) := by
  change (_ ∈ (setOf N.Indep))
  rw [setOf_indep_eq, e.setOf_base_eq]
  simp only [SetLike.mem_coe, mem_lowerClosure, mem_image, mem_setOf_eq, le_eq_subset,
    image_subset_iff, exists_exists_and_eq_and]
  obtain ⟨B, hB, hIB⟩ := hI.exists_base_superset
  exact ⟨B, hB, hIB.trans (subset_preimage_image _ _)⟩

theorem Iso.on_indep_symm (e : Iso M N) (h : N.Indep (e '' I)) (hI : I ⊆ M.E := by aesop_mat) :
    M.Indep I :=
  e.on_prop_symm (e.symm.on_indep) h

theorem Iso.on_indep_iff (e : Iso M N) (hI : I ⊆ M.E := by aesop_mat) :
    M.Indep I ↔ N.Indep (e '' I) := by
  refine ⟨e.on_indep, fun h ↦ e.on_indep_symm h hI⟩

theorem Iso.setOf_indep_eq (e : Iso M N) : setOf N.Indep = (image e) '' (setOf M.Indep) :=
  e.setOf_prop_eq Indep.subset_ground e.on_indep e.symm.on_indep

theorem Iso.on_base_symm (e : Iso M N) (h : N.Base (e '' B)) (hB : B ⊆ M.E := by aesop_mat) :
    M.Base B :=
  e.on_prop_symm (e.symm.on_base) h

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
def Iso.dual (e : Iso M N) : Iso M﹡ N﹡ :=
  iso_of_forall_base e.toLocalEquiv
    (by simp) (by simp)
    (by {
      simp_rw [dual_base_iff', image_subset_iff, and_imp]
      refine fun B hB hBE ↦ ⟨?_, hBE.trans e.ground_subset_preimage_ground⟩
      convert e.on_base hB
      rw [e.injOn_ground.image_diff hBE, e.image_ground] } )
    (by {
      simp only [image_subset_iff, dual_base_iff', and_imp]
      refine fun B hB hBE ↦ ⟨?_, hBE.trans e.symm.ground_subset_preimage_ground⟩
      convert e.symm.on_base hB
      rw [e.symm.injOn_ground.image_diff hBE, e.symm.image_ground, symm_apply] } )

@[simp] lemma Iso.dual_apply (e : Iso M N) : e.dual.toLocalEquiv = e.toLocalEquiv := rfl

/-- Restrictions of isomorphic matroids are isomorphic -/
def Iso.restrict (e : Iso M N) (R : Set α) (hR : R ⊆ M.E := by aesop_mat) :
    Iso (M ↾ R) (N ↾ (e '' R)) :=
  iso_of_forall_indep (e.toLocalEquiv.restr R)
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

@[simp] lemma Iso.restrict_apply (e : Iso M N) {R : Set α} (hR : R ⊆ M.E := by aesop_mat) :
    (e.restrict R hR).toLocalEquiv = e.toLocalEquiv.restr R := by
  simp [restrict]

theorem Iso.on_basis (e : Iso M N) (hI : M.Basis I X) : N.Basis (e '' I) (e '' X) := by
  rw [← base_restrict_iff _, (e.restrict X).symm.on_base_iff _, base_restrict_iff]
  · convert hI
    simp only [symm_apply, restrict_apply, restr_coe_symm]
    apply e.toLocalEquiv.symm_image_image_of_subset_source
    rw [e.source_eq]
    exact hI.indep.subset_ground
  · simp only [restrict_ground_eq]
    exact image_subset _ hI.subset
  exact e.image_subset_ground X hI.subset_ground

section IsIso

variable {M : Matroid α} {N : Matroid β}

/-- We write `M ≅ N` if there is an isomorphism from `M` to `N`. This is defined as
  a disjunction so it behaves mathematically correctly even when `α` or `β` is empty,
  even though `M.Iso N` may be 'incorrectly' empty in such cases. -/
def IsIso : Matroid α → Matroid β → Prop := fun M N ↦
  (M = emptyOn α ∧ N = emptyOn β) ∨ Nonempty (M.Iso N)

infixl:65  " ≅ " => IsIso


@[simp] theorem isIso_emptyOn_iff {M : Matroid α} {β : Type*} : M ≅ emptyOn β ↔ M = emptyOn α := by
  constructor
  · rintro (⟨rfl,-⟩ | ⟨⟨i⟩⟩ ); rfl
    rw [← ground_eq_empty_iff, ← i.symm.image_ground]
    simp
  rintro rfl
  exact Or.inl ⟨rfl, rfl⟩

theorem IsIso.symm {M : Matroid α} {N : Matroid β} (h : M ≅ N) : N ≅ M := by
  obtain (⟨hM,hN⟩ | ⟨⟨e⟩⟩)  := h
  · exact Or.inl ⟨hN, hM⟩
  exact Or.inr ⟨e.symm⟩

theorem IsIso.comm {M : Matroid α} {N : Matroid β} : M ≅ N ↔ N ≅ M :=
  ⟨IsIso.symm, IsIso.symm⟩

theorem IsIso.refl (M : Matroid α) : M ≅ M :=
  Or.inr ⟨Iso.refl M⟩

theorem Iso.isIso (h : M.Iso N) : M ≅ N :=
  Or.inr ⟨h⟩

theorem IsIso.trans {O : Matroid γ}
    (h1 : M ≅ N) (h2 : N ≅ O) : M ≅ O := by
  obtain (⟨rfl,rfl⟩ | ⟨⟨i1⟩⟩) := h1
  · rwa [IsIso.comm, isIso_emptyOn_iff] at h2 ⊢
  obtain (⟨rfl,rfl⟩ | ⟨⟨i2⟩⟩) := h2
  · rw [isIso_emptyOn_iff]
    exact isIso_emptyOn_iff.1 i1.isIso
  exact Or.inr ⟨i1.trans i2⟩

theorem IsIso.empty_or_nonempty_iso (h : M ≅ N) :
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

theorem IsIso.nonempty_iso [Nonempty α] [Nonempty β] (h : M ≅ N) :
    Nonempty (M.Iso N) := by
  obtain (⟨rfl, rfl⟩ | ⟨⟨e⟩⟩) := h
  · exact ⟨Iso.of_emptyOn⟩
  exact ⟨e⟩

/-- Noncomputably produce an `Iso M N` from `M ≅ N` whenever both ground types are nonempty -/
noncomputable def IsIso.iso [Nonempty α] [Nonempty β] (h : M ≅ N) :
    Iso M N := h.nonempty_iso.some

theorem IsIso.finite_iff (h : M ≅ N) : M.Finite ↔ N.Finite := by
  obtain (⟨rfl,rfl⟩ | ⟨⟨e⟩⟩) := h
  · exact iff_of_true (finite_emptyOn α) (finite_emptyOn β)
  refine ⟨fun ⟨h⟩ ↦ ⟨?_⟩, fun ⟨h⟩ ↦ ⟨?_⟩⟩
  · rw [← encard_ne_top_iff] at h ⊢
    rwa [e.encard_ground_eq] at h
  rw [← encard_ne_top_iff] at h ⊢
  rwa [e.encard_ground_eq]

theorem IsIso.finiteRk_iff (h : M ≅ N) : M.FiniteRk ↔ N.FiniteRk := by
  obtain (⟨rfl,rfl⟩ | ⟨⟨e⟩⟩) := h
  · apply iff_of_true <;> infer_instance
  exact ⟨fun ⟨B, hB, hBfin⟩ ↦ ⟨e '' B, e.on_base hB, hBfin.image _⟩,
    fun ⟨B, hB, hBfin⟩ ↦ ⟨e.symm '' B, e.symm.on_base hB, hBfin.image _⟩⟩

theorem IsIso.dual (h : M ≅ N) : M﹡ ≅ N﹡ := by
  obtain (⟨rfl, rfl⟩ | ⟨⟨e⟩⟩) := h
  · exact Or.inl ⟨by simp, by simp⟩
  exact Or.inr ⟨e.dual⟩

theorem isIso_dual_iff : M﹡ ≅ N﹡ ↔ M ≅ N := by
  refine ⟨fun h ↦ ?_, IsIso.dual⟩
  rw [←dual_dual M, ←dual_dual N]
  exact h.dual

theorem isIso_emptyOn_emptyOn (α β : Type*) : emptyOn α ≅ emptyOn β := by
  rw [isIso_emptyOn_iff]

@[simp] theorem emptyOn_isIso_iff {M : Matroid α} (β : Type*) : emptyOn β ≅ M ↔ M = emptyOn α := by
  rw [IsIso.comm, isIso_emptyOn_iff]

theorem isIso_loopyOn_iff {M : Matroid α} {β : Type*} {E : Set β} :
    M ≅ loopyOn E ↔ M = loopyOn M.E ∧ Nonempty (M.E ≃ E) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain (⟨rfl,hLoopy⟩ | ⟨-, -, ⟨e⟩⟩) := h.empty_or_nonempty_iso
    · simp only [emptyOn_ground, loopyOn_empty, true_and]
      rw [← ground_eq_empty_iff, loopyOn_ground] at hLoopy
      subst hLoopy
      exact Fintype.card_eq.mp rfl
    rw [eq_loopyOn_iff, and_iff_right rfl]
    refine ⟨fun I _ hI ↦ by simpa using e.on_indep hI, ?_⟩
    · convert Nonempty.intro e.toLocalEquiv.toEquiv <;> simp
  rintro ⟨hM, ⟨e⟩⟩
  cases isEmpty_or_nonempty α
  · simp only [eq_emptyOn, emptyOn_isIso_iff, ← ground_eq_empty_iff, loopyOn_ground]
    exact isEmpty_coe_sort.1 e.symm.isEmpty
  cases isEmpty_or_nonempty β
  · simp only [eq_emptyOn, isIso_emptyOn_iff]
    rw [← ground_eq_empty_iff, ← isEmpty_coe_sort]
    rw [E.eq_empty_of_isEmpty] at e
    exact e.isEmpty
  refine (Iso.of_forall_indep (LocalEquiv.ofSetEquiv e) (by simp) (by simp) ?_).isIso
  simp only [eq_iff_indep_iff_indep_forall, loopyOn_ground, loopyOn_indep_iff, true_and] at hM
  simpa

theorem isIso_freeOn_iff {M : Matroid α} {β : Type*} {E : Set β} :
    M ≅ freeOn E ↔ M = freeOn M.E ∧ Nonempty (M.E ≃ E) := by
  rw [← isIso_dual_iff, freeOn_dual_eq, isIso_loopyOn_iff, dual_eq_comm, dual_ground,
    loopyOn_dual_eq, eq_comm]

end IsIso

section Invariant

def Invariant {η : Type*} (f : ∀ {α : Type u}, Matroid α → η) : Prop :=
  ∀ {α β : Type u} {M : Matroid α} {N : Matroid β}, M ≅ N → f M = f N

theorem Invariant.pred_iff_pred {P : ∀ {η : Type u}, Matroid η → Prop} (hP : Invariant P)
    {α β : Type u} {M : Matroid α} {N : Matroid β} (hMN : M ≅ N) : P M ↔ P N := by
  simp [hP hMN]

theorem Invariant.and {P Q : ∀ {η : Type u}, Matroid η → Prop} (hP : Invariant P)
    (hQ : Invariant Q) : Invariant (fun M ↦ P M ∧ Q M) := by
  intro α β M N hMN
  simp only [eq_iff_iff]
  rw [hP.pred_iff_pred hMN, hQ.pred_iff_pred hMN]

theorem invariant_finite : Invariant Matroid.Finite := by
  intro α β M N hMN
  simp only [eq_iff_iff]
  exact hMN.finite_iff

theorem invariant_finiteRk : Invariant Matroid.FiniteRk := by
  intro α β M N hMN
  simp only [eq_iff_iff]
  exact hMN.finiteRk_iff

-- def InvariantPred (f : ∀ {α : Type u}, Matroid α → Prop) : Prop :=
--   Invariant f

-- theorem Invariant.onIso {η α β : Type*} {f : ∀ {α : Type u}, Matroid α → η}
--     (hf : Invariant f) {M : Matroid α} {N : Matroid β} (hMN : M ≅ N) :

end Invariant



--   refine ⟨fun h ↦ ?_, fun ⟨h, ⟨i⟩⟩ ↦ ?_⟩
--   · obtain (⟨hM, hN⟩ | ⟨⟨i⟩⟩) := h
--     · rw [loopyOn_ground] at hN
--       obtain rfl := ground_eq_empty_iff.1 hM
--       simp only [emptyOn_ground, loopyOn_empty, hN, true_and]
--       exact Fintype.card_eq.mp rfl
--     refine ⟨?_, ⟨by simpa using i.toLocalEquiv.bijOn.equiv⟩⟩
--     apply eq_of_indep_iff_indep_forall (by simp) fun I hIE ↦ ?_
--     rw [i.on_indep_iff, loopyOn_indep_iff, loopyOn_indep_iff, image_eq_empty]
--     sorry



end Matroid
