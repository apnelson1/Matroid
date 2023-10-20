import Matroid.Representation.Basic 

variable {α β W W' 𝔽 R : Type _} {e f x : α} {I B X Y : Set α} {M : Matroid α} [Field 𝔽] 
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']

open Function Set Submodule FiniteDimensional BigOperators

namespace Matroid

-- /-- The 'row space' corresponding to the representation `v` -/
-- def Rep.subspaceRep (v : M.Rep 𝔽 W) : Submodule 𝔽 (α → 𝔽) := Submodule.ofFun 𝔽 v

/-- the subspace of `X → 𝔽` corresponding to a set `X` -/
def Rep.projSet (v : M.Rep 𝔽 W) (X : Set α) : Submodule 𝔽 (X → 𝔽) := ofFun 𝔽 (v ∘ Subtype.val)
  
theorem Rep.projSet_eq_map (v : M.Rep 𝔽 W) (X : Set α) : 
    v.projSet X = (Submodule.ofFun 𝔽 v).map (LinearMap.fun_subtype 𝔽 X) := by 
  ext x; simp only [projSet, mem_ofFun_iff, mem_map, exists_exists_eq_and]; aesop
  
theorem Rep.indep_iff_projSet_eq_top (v : M.Rep 𝔽 W) : M.Indep I ↔ v.projSet I = ⊤ := by 
  rw [v.indep_iff, Rep.projSet, ofFun_eq_top_iff]; rfl  

/-- A finite submodule of `α → 𝔽` determines a matroid on `α` -/
def matroid_on_univ_of_subspace (U : Submodule 𝔽 (α → 𝔽)) [FiniteDimensional 𝔽 U] : Matroid α := 
  matroid_of_indep_of_exists_matroid 
    univ 
    (fun I ↦ (U.map (LinearMap.fun_subtype 𝔽 I) = ⊤)) 
  ( by 
    obtain ⟨s, ⟨b⟩⟩ := Basis.exists_basis 𝔽 U
    set v := rep_of_fun_univ 𝔽 <| fun a i ↦ (b i).1 a 
    refine ⟨matroid_on_univ_of_fun 𝔽 <| fun a i ↦ (b i).1 a, rfl, fun I ↦ ?_⟩ 
    rw [v.indep_iff_projSet_eq_top, v.projSet_eq_map]
    have hUf : (ofFun 𝔽 <| fun a i ↦ (b i).1 a) = U := b.eq_ofFun
    simp_rw [←hUf]
    rfl )

def matroid_of_subspace (E : Set α) (U : Submodule 𝔽 (α → 𝔽)) [FiniteDimensional 𝔽 U] : 
    Matroid α := (matroid_on_univ_of_subspace U) ↾ E 

/-- A representation of `M` by a subspace where independence corresponds to projections having 
  full dimension -/
structure SubspaceRep (M : Matroid α) (𝔽 : Type _) [Field 𝔽] where
  ( space : Submodule 𝔽 (α → 𝔽) )
  ( valid : ∀ I, M.Indep I ↔ space.map (LinearMap.fun_subtype 𝔽 I) = ⊤ )

instance {M : Matroid α} {𝔽 : Type _} [Field 𝔽] : 
    CoeOut (SubspaceRep M 𝔽) (Submodule 𝔽 (α → 𝔽)) where
  coe := SubspaceRep.space

/-- This doesn't seem to work - coercion is just displayed as `U.carrier` in the pp. -/
@[simp] theorem SubspaceRep.carrier_eq_coe {M : Matroid α} {𝔽 : Type _} [Field 𝔽] 
  (U : SubspaceRep M 𝔽) : U.space = (↑U : Submodule 𝔽 (α → 𝔽)) := rfl 

@[simp] theorem SubspaceRep.indep_iff {M : Matroid α} {𝔽 : Type _} [Field 𝔽] (U : SubspaceRep M 𝔽) 
    {I : Set α} : M.Indep I ↔ (U : Submodule 𝔽 (α → 𝔽)).map (LinearMap.fun_subtype 𝔽 I) = ⊤ := 
  U.valid I

/-- A representation `v` canonically gives a subspace representation (its 'row space')-/
def Rep.subspaceRep (v : M.Rep 𝔽 W) : M.SubspaceRep 𝔽 where
  space := ofFun 𝔽 v
  valid := fun I ↦ by rw [←v.projSet_eq_map, v.indep_iff_projSet_eq_top]
   
theorem SubspaceRep.representable (U : M.SubspaceRep 𝔽) [FiniteDimensional 𝔽 U] : 
    M.Representable 𝔽 := by 
  obtain ⟨s, ⟨b⟩⟩ := Basis.exists_basis 𝔽 U
  have hM : M = matroid_of_fun 𝔽 (fun a i ↦ (b i).1 a : α → (s → 𝔽)) M.E 
  · rw [eq_iff_indep_iff_indep_forall]
    refine ⟨rfl, fun I hIE ↦ ?_⟩ 
    rw [matroid_of_fun_indep_iff', and_iff_left hIE, U.indep_iff]
    simp_rw [←b.eq_ofFun, ←ofFun_comp_coe, ofFun_eq_top_iff]
    rfl 
  rw [hM]
  apply matroid_of_fun_representable 
  
end Matroid 

@[pp_dot] noncomputable def Submodule.orthspace [Fintype α] (U : Submodule 𝔽 (α → 𝔽)) : 
    Submodule 𝔽 (α → 𝔽) :=
  U.dualAnnihilator.map (Module.piEquiv α 𝔽 𝔽).symm 

theorem foo [Fintype α] {U : Submodule 𝔽 (α → 𝔽)} {x : α → 𝔽}: 
    x ∈ U.orthspace ↔ ∀ y ∈ U, ∑ i, x i * y i = 0 := by  
  simp only [orthspace, mem_map, mem_dualAnnihilator]
  constructor
  · rintro ⟨y, hy, rfl⟩ x hxU 
    convert hy x hxU using 1
    -- rw [Module.piEquiv_apply_symm]

@[simp] theorem Module.piEquiv_apply_symm [Fintype α] (y : Module.Dual 𝔽 (α → 𝔽)) (i : α) : 
    (Module.piEquiv α 𝔽 𝔽).symm y i = 0 := by 
  

theorem foo [Fintype α] (U : Submodule 𝔽 (α → 𝔽)) : U.orthspace.orthspace = U := by 
  simp [Submodule.orthspace]

-- theorem [Fintype α] (U U' : Submodule 𝔽 (α → 𝔽)) : 






-- theorem foo [Fintype α] (U : Submodule 𝔽 (α → 𝔽)) (B : Set α) (hB : )

-- theorem dual_foo [Fintype α] {M M' : Matroid α} (hM : M.E = univ) (hM' : M'.E = univ) 
--   (v : M.Rep 𝔽 W) (v' : M.Rep 𝔽 W') 

-- theorem dual_foo (E : Set α) (U W : )


-- noncomputable def matroid_of_subspace_substype 


-- theorem rep_of_subspace_rep (E : Set α) (U : Submodule 𝔽 (α → 𝔽)) [FiniteDimensional 𝔽 U] : 
--     (matroid_of_subspace E U).Representable 𝔽 := by 
--   rw [matroid_of_subspace]
--   -- apply Rep.representable
  

    





