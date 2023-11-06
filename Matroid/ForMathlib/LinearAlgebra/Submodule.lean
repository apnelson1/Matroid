import Mathlib.Algebra.Module.Submodule.Map

theorem LinearEquiv.map_coe {R M₁ M₂ : Type*} [CommSemiring R]
    [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂] (e : M₁ ≃ₗ[R] M₂)
    (U : Submodule R M₁):
  U.map (e : M₁ →ₗ[R] M₂) = U.map e := rfl

@[simp] theorem LinearEquiv.map_trans {R M₁ M₂ M₃ : Type*} [CommSemiring R]
    [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃] [Module R M₁]
    [Module R M₂] [Module R M₃] (e₁₂ : M₁ ≃ₗ[R] M₂) (e₂₃ : M₂ ≃ₗ[R] M₃)
    (U : Submodule R M₁) :
    U.map (e₁₂.trans e₂₃) = (U.map e₁₂).map e₂₃ := by
  rw [←LinearEquiv.map_coe,  LinearEquiv.coe_trans, Submodule.map_comp]; rfl
