import Mathlib

example {α ι 𝔽 : Type*} [Field 𝔽] (f : ι ↪ α) : (ι → 𝔽) →ₗ[𝔽] (α → 𝔽) := by
  apply?
