import Matroid.DualRestrict
import Mathlib.Logic.Equiv.LocalEquiv
namespace Matroid

open Set LocalEquiv

variable {α β α₁ α₂ α₃ : Type _} 

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

def Iso.trans {M₁ : Matroid α₁} {M₂ : Matroid α₂} {M₃ : Matroid α₃} (e₁₂ : Iso M₁ M₂) 
    (e₂₃ : Iso M₂ M₃) : Iso M₁ M₃ where 
  toLocalEquiv := e₁₂.toLocalEquiv.trans e₂₃.toLocalEquiv
  source_eq' := by 
  { rw [trans_source, e₁₂.source_eq', e₂₃.source_eq', ←e₁₂.target_eq', 
      inter_eq_left_iff_subset, ←e₁₂.source_eq']
    exact source_subset_preimage_target _ }
  target_eq' := by 
  { rw [trans_target, e₁₂.target_eq', e₂₃.target_eq', inter_eq_left_iff_subset, 
      ←e₂₃.source_eq', ←e₂₃.target_eq']
    exact target_subset_preimage_source _ }
  setOf_base_eq' := by rw [e₂₃.setOf_base_eq', e₁₂.setOf_base_eq']; ext B; simp [image_image]

@[aesop unsafe 10% (rule_sets [Matroid])] 
theorem Iso.image_symm_subset_ground (e : Iso M N) (X : Set β) (hX : X ⊆ N.E := by aesop_mat) : 
    e.symm '' X ⊆ M.E :=
  e.symm.image_subset_ground X hX 

@[simp] theorem Iso.symm_apply (e : Iso M N) : e.symm.toLocalEquiv = e.toLocalEquiv.symm := rfl

/-- Equal matroids are isomorphic -/
def Iso.of_eq {M N : Matroid α} (h : M = N) : Iso M N where
  toLocalEquiv := ofSet M.E
  source_eq' := rfl
  target_eq' := by simp [h]
  setOf_base_eq' := by simp [h]
  
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
def Iso_of_forall_base (e : LocalEquiv α β) (hM : e.source = M.E) (hN : e.target = N.E) 
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
def Iso_of_forall_indep (e : LocalEquiv α β) (hM : e.source = M.E) (hN : e.target = N.E) 
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

@[simp] theorem Iso_of_forall_indep_apply {M : Matroid α} {N : Matroid β} (e : LocalEquiv α β) 
    (hM : e.source = M.E) (hN : e.target = N.E) (on_indep : ∀ I, M.Indep I → N.Indep (e '' I)) 
    (on_indep_symm : ∀ I, N.Indep I → M.Indep (e.symm '' I)) : 
  (Iso_of_forall_indep e hM hN on_indep on_indep_symm).toLocalEquiv = e := rfl 

def Iso_of_forall_indep' (e : LocalEquiv α β) (hM : e.source = M.E) (hN : e.target = N.E) 
    (on_indep : ∀ I, I ⊆ M.E → (M.Indep I ↔ N.Indep (e '' I))) : Iso M N := 
  Iso_of_forall_indep e hM hN (fun I hI ↦ (on_indep I hI.subset_ground).mp hI) 
    (by {
      intro I hI
      have h' : e.symm '' I ⊆ M.E
      · rw [←hM, ←symm_image_target_eq_source, hN]; exact image_subset _ hI.subset_ground
      rwa [on_indep _ h', image_symm_image_of_subset_target _ 
        (by rw [hN]; exact hI.subset_ground)] })

@[simp] theorem Iso_of_forall_indep'_apply {M : Matroid α} {N : Matroid β} (e : LocalEquiv α β)
    (hM : e.source = M.E) (hN : e.target = N.E) 
    (on_indep : ∀ I, I ⊆ M.E → (M.Indep I ↔ N.Indep (e '' I))) : 
  (Iso_of_forall_indep' e hM hN on_indep).toLocalEquiv = e := rfl

theorem Iso.on_base (e : Iso M N) (hB : M.Base B) : N.Base (e '' B) := by 
  rwa [←e.on_base_iff]

lemma Iso.on_indep (e : Iso M N) (hI : M.Indep I) : N.Indep (e '' I) := by
  change (_ ∈ (setOf N.Indep))
  rw [setOf_indep_eq, e.setOf_base_eq]
  simp only [SetLike.mem_coe, mem_lowerClosure, mem_image, mem_setOf_eq, le_eq_subset, 
    image_subset_iff, exists_exists_and_eq_and]
  obtain ⟨B, hB, hIB⟩ := hI.exists_base_supset
  exact ⟨B, hB, hIB.trans (subset_preimage_image _ _)⟩ 

theorem Iso.on_indep_symm (e : Iso M N) (h : N.Indep (e '' I)) (hI : I ⊆ M.E := by aesop_mat) : 
    M.Indep I :=
    e.on_prop_symm (e.symm.on_indep) h
  
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


/-- Restrictions of isomorphic matroids are isomorphic -/
def Iso.restrict (e : Iso M N) (R : Set α) (hR : R ⊆ M.E := by aesop_mat) :
    Iso (M ↾ R) (N ↾ (e '' R)) := 
  Iso_of_forall_indep (e.toLocalEquiv.restr R)
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

/-- The duals of isomorphic matroids are isomorphic -/
def Iso.dual (e : Iso M N) : Iso M﹡ N﹡ := 
  Iso_of_forall_base e.toLocalEquiv 
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

/-- We write `M ≃ N` if there is an isomorphism from `M` to `N`. -/
def IsIso : Matroid α → Matroid β → Prop := fun M N ↦ Nonempty (M.Iso N)

infixl:65  " ≃ " => IsIso 

instance : IsEquiv (Matroid α) (fun (M N : Matroid α) ↦ M ≃ N) where
  refl := fun M ↦ ⟨Iso.refl M⟩
  trans := fun _ _ _ ⟨e⟩ ⟨e'⟩ ↦ ⟨e.trans e'⟩ 
  symm := fun _ _ ⟨e⟩ ↦ ⟨e.symm⟩  
  
end Matroid