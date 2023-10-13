import Mathlib.LinearAlgebra.Dual

open Submodule Set 

variable {W W' R : Type _} [AddCommMonoid W] [CommSemiring R] [Module R W] [AddCommMonoid W']
  [Module R W']

def Submodule.dual_compMap (f : α → W) (R : Type _) [CommSemiring R] [Module R W] : 
    Module.Dual R W →ₗ[R] (α → R) where 
  toFun φ := φ ∘ f  
  map_add' := fun _ _ ↦ rfl
  map_smul' := fun _ _ ↦ rfl 
  
@[simp] theorem Submodule.dual_compMap_apply (f : α → W) (R : Type _) [CommSemiring R] [Module R W]
  (φ : Module.Dual R W) : 
    Submodule.dual_compMap f R φ = φ ∘ f := rfl 

/-- The 'row space' of a representation -/
def Submodule.subspaceRep (R : Type _) [CommSemiring R] [Module R W] (f : α → W) : 
    Submodule R (α → R) :=
  LinearMap.range (Submodule.dual_compMap f R)

variable {R W W' : Type _} [Field R] [AddCommGroup W] [AddCommGroup W'] [Module R W] [Module R W']

theorem Submodule.subspaceRep_map (f : α → W) (e : W →ₗ[R] W') 
  (h_inj : Disjoint (span R (Set.range f)) (LinearMap.ker e)) : 
    subspaceRep R (e ∘ f) = subspaceRep R f := by 
  ext w
  simp only [Submodule.subspaceRep, Submodule.dual_compMap_apply, LinearMap.mem_range, 
    LinearMap.coe_mk, AddHom.coe_mk]
  constructor
  · rintro ⟨φ, _, rfl⟩
    exact ⟨φ.comp e, rfl⟩ 
  rintro ⟨φ, _, rfl⟩  
  have hker : LinearMap.ker (LinearMap.domRestrict e (span R (Set.range f))) = ⊥
  · rwa [LinearMap.ker_eq_bot, LinearMap.injective_domRestrict_iff, ←disjoint_iff] 
    
  obtain ⟨einv, hinv⟩ := (e.domRestrict (span R (Set.range f))).exists_leftInverse_of_injective hker

  use φ.comp ((Submodule.subtype _).comp einv)
  ext x
  simp only [LinearMap.coe_comp, coeSubtype, Function.comp_apply]
  have hinv' := LinearMap.congr_fun hinv ⟨f x , subset_span (by simp)⟩ 
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.domRestrict_apply, 
    LinearMap.id_coe, id_eq] at hinv'
  rw [hinv']
    
theorem Submodule.subspaceRep_map' (f : α → W) (e : W →ₗ[R] W') (h_inj : LinearMap.ker e = ⊥) : 
    subspaceRep R (e ∘ f) = subspaceRep R f :=
  subspaceRep_map _ _ (by simp [h_inj])
  
@[simp] theorem Submodule.subspaceRep_map_equiv (f : α → W) (e : W ≃ₗ[R] W') : 
    subspaceRep R (e ∘ f) = subspaceRep R f :=
  subspaceRep_map' _ _ e.ker 

theorem mem_subspaceRep_iff : 
    x ∈ subspaceRep R f ↔ ∃ φ : Module.Dual R W, x = φ ∘ f := by 
  rw [subspaceRep, dual_compMap]; aesop
   
theorem subspaceRep_eq_top_iff (f : α → W) :
    subspaceRep R f = ⊤ ↔ LinearIndependent R f := by 
  refine' ⟨fun h ↦ linearIndependent_iff.2 fun c hc ↦ ?_, fun h ↦ _⟩
  · have hcmem : (c : α→R)  ∈ subspaceRep R f := sorry 
    obtain ⟨φ, hcφ⟩ := mem_subspaceRep_iff.1 hcmem
    ext i
    -- have t := Finsupp.total α W R f
    have := congr_fun hcφ i 
    rw [Finsupp.total_apply] at hc
    


    
  

  -- simp [subspaceRep, dual_compMap]

-- def Submodule.subspaceRep_subtype (R : Type _) [Field R] [Module R W] (f : α → W) 
--   (s : Set α) : Submodule R (s → R) := 
--     (subspaceRep R f).map (LinearMap.funLeft R R Subtype.val)

-- theorem foo (f : α → W) (X : Set α) :
--     LinearIndependent R (X.restrict f) ↔ subspaceRep_subtype R f X = ⊤ := by 


  


