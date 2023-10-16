import Mathlib.LinearAlgebra.pi

variable {α 𝔽 : Type _} [Field 𝔽] 

-- forget all entries outside s 
def drop_entries (s : Set α) : (α → 𝔽) →ₗ[𝔽] (s → 𝔽) where
  toFun v x := v x
  map_add' := fun _ _ ↦ by ext; simp 
  map_smul' := fun _ _ ↦ by ext; simp  

-- forget all entries outside s 
def drop_entries' (s t : Set α) (hst : s ⊆ t) : (t → 𝔽) →ₗ[𝔽] (s → 𝔽) where
  toFun v x := v ⟨x, hst x.prop⟩ 
  map_add' := fun _ _ ↦ by ext; simp 
  map_smul' := fun _ _ ↦ by ext; simp  



noncomputable def append_zeroes (s : Set α) : 
    (s → 𝔽) →ₗ[𝔽] (α → 𝔽) := Function.ExtendByZero.linearMap 𝔽 Subtype.val


