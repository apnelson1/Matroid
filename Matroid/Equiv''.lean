import Matroid.Basic
import Mathlib.Logic.Equiv.LocalEquiv

namespace Matroid

open Set LocalEquiv

variable {α β α₁ α₂ α₃ : Type _} {M : Matroid α} {N : Matroid β}

theorem LocalEquiv.image_isImage_of_subset_source {e : LocalEquiv α β} (hs : s ⊆ e.source) : 
    e.IsImage s (e '' s) := by
  apply IsImage.of_image_eq
  rw [inter_eq_self_of_subset_right hs, ←image_source_eq_target, inter_eq_self_of_subset_right]
  exact image_subset _ hs

theorem LocalEquiv.isImage_trans_iff {α β γ : Type _} {s : Set α} {t : Set γ} (e : LocalEquiv α β) 
    (f : LocalEquiv β γ) : (IsImage (LocalEquiv.trans e f) s t) ↔ IsImage f (e '' s) t := by
  simp_rw [IsImage.iff_preimage_eq, trans_source, coe_trans]
  refine' ⟨fun h ↦ _, fun h ↦ _⟩
  

structure Iso (M : Matroid α) (N : Matroid β) where
  (toLocalEquiv : LocalEquiv α β)
  (source_eq' : toLocalEquiv.source = M.E)
  (target_eq' : toLocalEquiv.target = N.E)
  (indep_iff' : ∀ ⦃I J⦄, I ⊆ M.E → J ⊆ N.E → toLocalEquiv.IsImage I J → (M.Indep I ↔ N.Indep J))

instance {M : Matroid α} {N : Matroid β} : CoeFun (Iso M N) (fun _ ↦ (α → β)) where
  coe e := (e.toLocalEquiv : α → β)  

@[simp] lemma Iso.source_eq (e : Iso M N) : e.toLocalEquiv.source = M.E :=
  e.source_eq'

@[simp] lemma Iso.target_eq (e : Iso M N) : e.toLocalEquiv.target = N.E :=
  e.target_eq'

@[simp] lemma Iso.subset_source (e : Iso M N) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) : 
    X ⊆ e.toLocalEquiv.source := 
  hX.trans_eq e.source_eq.symm

@[simp] lemma Iso.image_subset_target (e : Iso M N) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) : 
    e '' X ⊆ e.toLocalEquiv.target := by
  rw [←image_source_eq_target]; exact image_subset _ (e.subset_source X)

@[aesop unsafe 10% (rule_sets [Matroid])] 
theorem Iso.image_subset_ground (e : Iso M N) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) : 
    e '' X ⊆ N.E := by
  convert image_subset _ hX
  rw [←e.source_eq, image_source_eq_target, e.target_eq]

lemma Iso.injOn_ground (e : Iso M N) : InjOn e M.E := by
  rw [←e.source_eq]; exact e.toLocalEquiv.injOn

theorem Iso.on_indep (e : Iso M N) (hI : M.Indep I) : N.Indep (e '' I) := by
 rwa [←e.indep_iff' hI.subset_ground (e.image_subset_ground I)
  (LocalEquiv.image_isImage_of_subset_source (e.subset_source I))]
 
 

  -- rwa [←e.indep_iff]

-- theorem Iso.on_base (e : Iso M N) (hB : B ⊆ M.E) : M.Base B ↔ N.Base (e '' B) := by
--   change (_ ↔ _ ∈ setOf N.Base)
--   simp_rw [e.setOf_base_eq, mem_image, mem_setOf_eq]
--   refine' ⟨fun h ↦ ⟨B, h, rfl⟩, fun ⟨B', h, h'⟩ ↦ _⟩
--   rw [e.injOn_ground.image_eq_image_iff_of_subset h.subset_ground hB] at h'
--   rwa [←h']

def Iso.refl (M : Matroid α) : Iso M M where
  toLocalEquiv := ofSet M.E 
  source_eq' := rfl 
  target_eq' := rfl
  indep_iff' := by {
    rintro I J hI hJ hIJ
    rw [IsImage.iff_preimage_eq, ofSet_source, ofSet_coe, preimage_id_eq, id_eq, 
      inter_eq_self_of_subset_right hI, inter_eq_self_of_subset_right hJ] at hIJ
    rw [hIJ] }

def Iso.symm (e : Iso M N) : Iso N M where
  toLocalEquiv := e.toLocalEquiv.symm
  source_eq' := by rw [symm_source, e.target_eq']
  target_eq' := by rw [symm_target, e.source_eq']
  indep_iff' := by { rintro I J hI hJ hIJ; rw [e.indep_iff' hJ hI (IsImage.symm_iff.mpr hIJ)] }

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
  indep_iff' := by 
  { rintro I J hI hJ hIJ
    -- have := hIJ.image_eq
    rw [e₁₂.indep_iff' hI (e₁₂.image_subset_ground I) 
      (LocalEquiv.image_isImage_of_subset_source (e₁₂.subset_source I)), 
      e₂₃.indep_iff' (e₁₂.image_subset_ground I) hJ]
    
      
      }

@[aesop unsafe 10% (rule_sets [Matroid])] 
theorem Iso.image_symm_subset_ground (e : Iso M N) (X : Set β) (hX : X ⊆ N.E := by aesop_mat) : 
    e.symm '' X ⊆ M.E :=
  e.symm.image_subset_ground X hX 

/-- A `LocalEquiv` that respects independence is an isomorphism. -/
def Iso_of_forall_indep (e : LocalEquiv α β) (hM : e.source = M.E) (hN : e.target = N.E) 
    (on_indep : ∀ I, M.Indep I → N.Indep (e '' I)) 
    (on_indep_symm : ∀ I, N.Indep I → M.Indep (e.symm '' I)) : Iso M N where 
  toLocalEquiv := e
  source_eq' := hM
  target_eq' := hN
  setOf_base_eq := by 
  { have setOfIndep : setOf N.Indep = (Set.image e) '' (setOf M.Indep)
    · refine' subset_antisymm (fun I (hI : N.Indep I) ↦ ⟨_, on_indep_symm I hI, _⟩) _
      · rintro _ ⟨I, (hI : M.Indep I), rfl⟩; exact on_indep I hI
      · rw [e.image_symm_image_of_subset_target (hI.subset_ground.trans_eq hN.symm)]
    rw [setOf_base_eq_maximals_setOf_indep, setOfIndep, 
      maximals_image_of_rel_iff_rel_on (r := (· ⊆ ·)), ←setOf_base_eq_maximals_setOf_indep]
    rintro I J (hI : M.Indep I) (hJ : M.Indep J)
    rw [e.injOn.image_subset_image_iff_of_subset (hI.subset_ground.trans hM.symm.subset) 
      (hJ.subset_ground.trans hM.symm.subset)] }

def Iso_of_forall_indep' (e : LocalEquiv α β) (hM : e.source = M.E) (hN : e.target = N.E) 
    (on_indep : ∀ I, I ⊆ M.E → (M.Indep I ↔ N.Indep (e '' I))) : Iso M N := 
  Iso_of_forall_indep e hM hN (fun I hI ↦ (on_indep I hI.subset_ground).mp hI) 
    (by {
      intro I hI
      have h' : e.symm '' I ⊆ M.E
      · rw [←hM, ←symm_image_target_eq_source, hN]; exact image_subset _ hI.subset_ground
      rwa [on_indep _ h', image_symm_image_of_subset_target _ 
        (by rw [hN]; exact hI.subset_ground)] })

lemma Iso.on_indep (e : Iso M N) (hI : M.Indep I) : N.Indep (e '' I) := by
  change (_ ∈ (setOf N.Indep))
  rw [setOf_indep_eq, e.setOf_base_eq]
  simp only [SetLike.mem_coe, mem_lowerClosure, mem_image, mem_setOf_eq, le_eq_subset, 
    image_subset_iff, exists_exists_and_eq_and]
  obtain ⟨B, hB, hIB⟩ := hI.exists_base_supset
  exact ⟨B, hB, hIB.trans (subset_preimage_image _ _)⟩ 
  
def Iso.restrict (e : Iso M N) (hR : R ⊆ M.E) : Iso (M | R) (N | (e '' R)) := 
  Iso_of_forall_indep (e.toLocalEquiv.restr R)
  (by simpa [restrict_ground_eq hR]) 
  (by {
    simp only [restr_target, target_eq, source_eq, image_subset_iff, restrict_ground_eq'] 
    rw [image_eq_target_inter_inv_preimage _ (by rwa [e.source_eq]),  target_eq, inter_comm N.E, 
      inter_assoc, inter_self] }) 
  (by { 
    simp only [restrict_indep_iff, restr_coe, image_subset_iff, and_imp] 
    exact fun I hI hIR ↦ ⟨e.on_indep hI, hIR.trans (subset_preimage_image _ _)⟩ }) 
  (by {
    simp only [restrict_indep_iff, restr_coe_symm, image_subset_iff, and_imp]
    refine' fun I hI hIR ↦ ⟨e.symm.on_indep hI, hIR.trans _⟩   
    rw [image_eq_target_inter_inv_preimage _ (by rwa [e.source_eq])]
    apply inter_subset_right })


/-- We write `M ≃i N` if there is an isomorphism from `M` to `N`. -/
def IsIso (M : Matroid α) (N : Matroid β) : Prop := Nonempty (M.Iso N)

infixl:65  " ≃i " => IsIso 

/-- Restrict an isomorphism to a set not necessarily contained in the ground set.  -/
def Iso.restrict' (e : Iso M N) (R : Set α) : Iso (M | (R ∩ M.E)) (N | (e '' (R ∩ M.E))) := 
  Iso_of_forall_indep (e.toLocalEquiv.restr (R ∩ M.E)) 
    (by simp)
    (by { 
      rw [restrict_ground_eq', restr_target, preimage_inter, ←e.source_eq, ←inter_assoc, inter_comm, 
        ←inter_assoc, inter_eq_self_of_subset_right e.toLocalEquiv.target_subset_preimage_source, 
        ←image_source_inter_eq', inter_comm R, eq_comm, inter_eq_left_iff_subset, ←e.target_eq, 
        ←image_source_eq_target] 
      exact image_subset _ (inter_subset_left _ _) } ) 
    (by { 
      simp only [restrict_indep_iff, subset_inter_iff, restr_coe, image_subset_iff, and_imp] 
      exact fun I hI hIR hIE ↦ 
        ⟨e.on_indep hI, (subset_inter hIR hIE).trans (subset_preimage_image _ _)⟩ })
    (by {
      simp only [restrict_indep_iff, restr_coe_symm, image_subset_iff, and_imp]
      refine' fun I hI hIss ↦ ⟨e.symm.on_indep hI,hIss.trans _⟩
      rw [← e.source_eq, image_eq_target_inter_inv_preimage _ (inter_subset_right _ _)]
      apply inter_subset_right })

-- theorem Iso.on_circuit (e : Iso M N) (h : M.Circuit C) : N.Circuit (e '' C) := by
--   rw [Circuit, setOf_dep_eq, setOf_indep_eq, e.setOf_base_eq]
--   rw [Circuit, setOf_dep_eq, setOf_indep_eq] at h
  
  
 



-- def LocalEquiv.LocalEquivSet (i : LocalEquiv α β) : LocalEquiv (Set α) (Set β) where
--   toFun := image i.toFun
--   invFun := image i.invFun
--   source := Iic i.source
--   target := Iic i.target
--   map_source' := by 
--   { simp only [mem_Iic, le_eq_subset, image_subset_iff]
--     exact fun s hs a has ↦ i.map_source' (hs has) }
--   map_target' := by
--   { simp only [mem_Iic, le_eq_subset, image_subset_iff]
--     exact fun s hs a has ↦ i.map_target' (hs has) }
--   left_inv' := by
--   { simp only [mem_Iic, le_eq_subset, invFun_as_coe]
--     exact fun _ h ↦ symm_image_image_of_subset_source i h }
--   right_inv' := by
--   { simp only [mem_Iic, le_eq_subset, invFun_as_coe]
--     exact fun _ h ↦ image_symm_image_of_subset_target i h }








end Matroid