import Matroid.Flat
import Mathlib.LinearAlgebra.LinearIndependent

variable {α β W W' 𝔽 : Type _} {e f x : α} {M : Matroid α} [Field 𝔽] [AddCommGroup W] [Module 𝔽 W]
  [AddCommGroup W'] [Module 𝔽 W']

open Function Set

namespace Matroid

structure Rep (M : Matroid α) (𝔽 W : Type _) [Field 𝔽] [AddCommMonoid W] [Module 𝔽 W] where
  -- A representation assigns co-ordinates to each element of `α`
  (to_fun : α → W)
  -- A set is independent in `M` if and only if its image is linearly independent over `𝔽` in `W`
  (valid' : ∀ I, M.Indep I ↔ LinearIndependent 𝔽 (to_fun ∘ ((↑) : I → α))) 
 
instance : FunLike (M.Rep 𝔽 W) α (fun _ ↦ W) where
  coe φ := φ.to_fun
  coe_injective' := by rintro ⟨f,h⟩ ⟨f', h'⟩; simp 
  
instance coeFun : CoeFun (M.Rep 𝔽 W) fun _ ↦ (α → W) :=
  ⟨FunLike.coe⟩

@[simp] theorem Rep.to_fun_eq_coe (φ : M.Rep 𝔽 W) : φ.to_fun = (φ : α → W) := rfl

theorem Rep.eq_zero_iff_not_indep {φ : M.Rep 𝔽 W} : φ e = 0 ↔ ¬ M.Indep {e} := by
  simp [φ.valid',linearIndependent_unique_iff, -indep_singleton]
  
theorem Rep.eq_zero_of_not_mem_ground (φ : M.Rep 𝔽 W) (he : e ∉ M.E) : φ e = 0 := by 
  rw [φ.eq_zero_iff_not_indep, indep_singleton]
  exact fun hl ↦ he hl.mem_ground
  
/-- A function with support contained in `M.E` that gives the correct independent sets 
  within the ground set gives a representation -/
def rep_of_ground (f : α → W) (h_support : support f ⊆ M.E) 
    (hf : ∀ {I}, I ⊆ M.E → (M.Indep I ↔ LinearIndependent 𝔽 (f ∘ ((↑) : I → α)))) : M.Rep 𝔽 W where
  to_fun := f
  valid' := ( by 
    intro I
    obtain (hI | hI) := em (I ⊆ M.E)
    · rw [hf hI]
    rw [←not_iff_not, iff_true_left (fun hi ↦ hI hi.subset_ground)]
    intro h_ind
    obtain ⟨e, heI, heE⟩ := not_subset.1 hI
    have h0 := h_ind.ne_zero ⟨e, heI⟩ 
    simp only [comp_apply, ne_eq] at h0  
    apply not_mem_subset h_support heE
    exact h0 )

@[simp] theorem rep_of_ground_coe_eq (f : α → W) (h_support : support f ⊆ M.E) 
  (hf : ∀ {I}, I ⊆ M.E → (M.Indep I ↔ LinearIndependent 𝔽 (f ∘ ((↑) : I → α)))) : 
  (rep_of_ground f h_support hf : α → W) = f := rfl 

/-- Compose a representation with a linear injection. -/
def Rep.map (φ : M.Rep 𝔽 W) (ψ : W →ₗ[𝔽] W') (hψ : LinearMap.ker ψ = ⊥) : M.Rep 𝔽 W' where
  to_fun := ψ ∘ φ  
  valid' := fun _ ↦ by rw [comp.assoc, ψ.linearIndependent_iff hψ, φ.valid', φ.to_fun_eq_coe]

@[simp] theorem Rep.map_apply (φ : M.Rep 𝔽 W) (ψ : W →ₗ[𝔽] W') (hψ : LinearMap.ker ψ = ⊥) (e : α) : 
    (φ.map ψ hψ) e = ψ (φ e) := rfl 

/-- Each function from a type to a vector space defines a matroid on each finite superset of its 
  support -/
def MatroidOfFun (f : α → W) (E : Set α) (hf : f.support ⊆ E) (hfin : E.Finite) : Matroid α := 
  matroid_of_indep_of_finite 
  hfin 
  ( fun I ↦ LinearIndependent 𝔽 (f ∘ ((↑) : I → α)) ) 
  ( linearIndependent_empty_type )
  ( fun I J hI hJI ↦ by convert hI.comp _ (inclusion_injective hJI) )
 
  ( by 
    intro I J hI hJ hIJ
    have h : ¬ (f '' J ⊆ Submodule.span 𝔽 (f '' I))
    · sorry
    obtain ⟨_, ⟨e, he, rfl⟩, heI⟩ := not_subset.1 h
    refine' ⟨e, he, 
      fun heI' ↦ heI (subset_trans Subset.rfl Submodule.subset_span (mem_image_of_mem _ heI')), _⟩
    simp

  ) 
  ( by 
    refine fun I hI ↦ subset_trans (fun e heI ↦ ?_) hf
    exact hI.ne_zero ⟨_, heI⟩ )
