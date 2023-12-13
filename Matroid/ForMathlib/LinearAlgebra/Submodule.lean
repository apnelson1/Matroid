import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.LinearAlgebra.Finrank

theorem LinearEquiv.map_coe {R M₁ M₂ : Type*} [CommSemiring R]
    [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂] (e : M₁ ≃ₗ[R] M₂)
    (U : Submodule R M₁):
  U.map (e : M₁ →ₗ[R] M₂) = U.map e := rfl

@[simp] theorem LinearEquiv.map_trans {R M₁ M₂ M₃ : Type*} [CommSemiring R]
    [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃] [Module R M₁]
    [Module R M₂] [Module R M₃] (e₁₂ : M₁ ≃ₗ[R] M₂) (e₂₃ : M₂ ≃ₗ[R] M₃)
    (U : Submodule R M₁) :
    U.map (e₁₂.trans e₂₃) = (U.map e₁₂).map e₂₃ := by
  rw [← LinearEquiv.map_coe,  LinearEquiv.coe_trans, Submodule.map_comp]; rfl

@[simp] theorem LinearMap.range_domRestrict {R R₂ M M₂ : Type*} [Semiring R] [Semiring R₂]
    [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R₂ M₂] {σ₁₂ : R →+* R₂}
    [RingHomSurjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) :
    LinearMap.range (LinearMap.domRestrict f p) = p.map f := by
  ext; simp

@[simp] theorem LinearMap.domRestrict_injective {R R₂ M M₂ : Type*} [Semiring R] [Semiring R₂]
    [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R₂ M₂] {σ₁₂ : R →+* R₂}
    {f : M →ₛₗ[σ₁₂] M₂} (hf : Function.Injective f) (p : Submodule R M) :
    Function.Injective (f.domRestrict p) := by
  intro x y h
  apply_fun (↑) using Subtype.coe_injective
  apply_fun f using hf
  simpa using h

theorem LinearMap.finrank_map_of_inj {K V : Type*} [Ring K] [AddCommGroup V]
    [Module K V] {V₂ : Type v'} [AddCommGroup V₂] [Module K V₂] {f : V →ₗ[K] V₂}
    (hf : Function.Injective ↑f) (U : Submodule K V) :
    FiniteDimensional.finrank K (U.map f) = FiniteDimensional.finrank K U := by
  rw [← LinearMap.finrank_range_of_inj (LinearMap.domRestrict_injective hf _),
    LinearMap.range_domRestrict]
