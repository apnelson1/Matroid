import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.LinearAlgebra.Span.Defs

theorem LinearEquiv.map_coe {R M₁ M₂ : Type*} [CommSemiring R]
    [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂] (e : M₁ ≃ₗ[R] M₂)
    (U : Submodule R M₁):
  U.map (e : M₁ →ₗ[R] M₂) = U.map e.toLinearMap := rfl

@[simp] theorem LinearEquiv.map_trans {R M₁ M₂ M₃ : Type*} [CommSemiring R]
    [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃] [Module R M₁]
    [Module R M₂] [Module R M₃] (e₁₂ : M₁ ≃ₗ[R] M₂) (e₂₃ : M₂ ≃ₗ[R] M₃)
    (U : Submodule R M₁) :
    U.map (e₁₂.trans e₂₃).toLinearMap = (U.map e₁₂.toLinearMap).map e₂₃.toLinearMap := by
  rw [← LinearEquiv.map_coe,  LinearEquiv.coe_trans, Submodule.map_comp]

lemma Submodule.mem_span_singleton₀ {R M : Type*} [DivisionRing R] [AddCommMonoid M] [Module R M]
    {x y : M} (hx : x ≠ 0) : x ∈ Submodule.span R {y} ↔ ∃ (a : Rˣ), a • y = x := by
  rw [mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨Units.mk0 a (by rintro rfl; simp at hx), by simp⟩
  rintro ⟨a, rfl⟩
  exact ⟨a, rfl⟩

-- @[simp] theorem LinearMap.range_domRestrict {R R₂ M M₂ : Type*} [Semiring R] [Semiring R₂]
--     [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R₂ M₂] {σ₁₂ : R →+* R₂}
--     [RingHomSurjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) :
--     LinearMap.range (LinearMap.domRestrict f p) = p.map f := by
--   ext; simp

-- @[simp] theorem LinearMap.domRestrict_injective {R R₂ M M₂ : Type*} [Semiring R] [Semiring R₂]
--     [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R₂ M₂] {σ₁₂ : R →+* R₂}
--     {f : M →ₛₗ[σ₁₂] M₂} (hf : Function.Injective f) (p : Submodule R M) :
--     Function.Injective (f.domRestrict p) := by
--   intro x y h
--   apply_fun (↑) using Subtype.coe_injective
--   apply_fun f using hf
--   simpa using h

-- theorem LinearMap.finrank_map_of_inj {K V V₂ : Type*} [Ring K] [AddCommGroup V]
--     [Module K V] [AddCommGroup V₂] [Module K V₂] {f : V →ₗ[K] V₂}
--     (hf : Function.Injective ↑f) (U : Submodule K V) :
--     FiniteDimensional.finrank K (U.map f) = FiniteDimensional.finrank K U := by
--   rw [← LinearMap.finrank_range_of_inj (LinearMap.domRestrict_injective hf _),
--     LinearMap.range_domRestrict]
