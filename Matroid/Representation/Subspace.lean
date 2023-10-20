import Matroid.Representation.Basic 

variable {α β W W' 𝔽 R : Type _} {e f x : α} {I B X Y : Set α} {M : Matroid α} [Field 𝔽] 
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']

open Function Set Submodule FiniteDimensional

namespace Matroid

/-- The 'row space' corresponding to the representation `v` -/
def Rep.subspaceRep (v : M.Rep 𝔽 W) : Submodule 𝔽 (α → 𝔽) := Submodule.ofFun 𝔽 v

/-- the subspace of `X → 𝔽` corresponding to a set `X` -/
def Rep.projSet (v : M.Rep 𝔽 W) (X : Set α) : Submodule 𝔽 (X → 𝔽) := ofFun 𝔽 (v ∘ Subtype.val)
  
theorem Rep.projSet_eq_map (v : M.Rep 𝔽 W) (X : Set α) : 
    v.projSet X = v.subspaceRep.map (LinearMap.fun_subtype 𝔽 X) := by 
  ext x; simp only [projSet, mem_ofFun_iff, subspaceRep, mem_map, exists_exists_eq_and]; aesop
  
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
    rw [v.indep_iff_projSet_eq_top, v.projSet_eq_map, Rep.subspaceRep]
    have hUf : (ofFun 𝔽 <| fun a i ↦ (b i).1 a) = U := b.eq_ofFun
    simp_rw [←hUf]
    rfl )

-- theorem foo (U : Submodule 𝔽 (α → 𝔽)) [FiniteDimensional 𝔽 U] (b : Basis ι 𝔽 U)

def matroid_of_subspace (E : Set α) (U : Submodule 𝔽 (α → 𝔽)) [FiniteDimensional 𝔽 U] : 
    Matroid α := (matroid_on_univ_of_subspace U) ↾ E 

-- theorem dual_foo (E : Set α) (U W : )


-- noncomputable def matroid_of_subspace_substype 


-- theorem rep_of_subspace_rep (E : Set α) (U : Submodule 𝔽 (α → 𝔽)) [FiniteDimensional 𝔽 U] : 
--     (matroid_of_subspace E U).Representable 𝔽 := by 
--   rw [matroid_of_subspace]
--   -- apply Rep.representable
  

    





