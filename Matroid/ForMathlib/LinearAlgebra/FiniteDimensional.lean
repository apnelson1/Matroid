import Mathlib.LinearAlgebra.FiniteDimensional

/-- Unlike the unprimed version, `f` isn't coerced here, so the simplifier can find it. -/
@[simp] theorem LinearEquiv.finrank_map_eq' {R M M₂ : Type _} [Ring R] [AddCommGroup M]
    [AddCommGroup M₂] [Module R M] [Module R M₂] (f : M ≃ₗ[R] M₂) (p : Submodule R M) :
    FiniteDimensional.finrank R (p.map f) = FiniteDimensional.finrank R p :=
  finrank_map_eq f p
