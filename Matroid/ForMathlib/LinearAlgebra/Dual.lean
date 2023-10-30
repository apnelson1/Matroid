import Mathlib.LinearAlgebra.Dual

open Submodule

@[simp]
theorem LinearEquiv.dualMap_apply_symm {R : Type u} [CommSemiring R] {M₁ : Type v} {M₂ : Type v'}
    [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂] (f : M₁ ≃ₗ[R] M₂)
    (g : Module.Dual R M₁) : f.symm.dualMap g = g.comp (f.symm : M₂ →ₗ[R] M₁) := rfl

@[simp] theorem LinearEquiv.dualAnnihilator_map_eq {R : Type u} {M : Type v} [CommSemiring R]
    [AddCommMonoid M] [AddCommMonoid M'] [Module R M] [Module R M'] (e : M ≃ₗ[R] M')
    (U : Submodule R M) :
    dualAnnihilator (U.map e) = (dualAnnihilator U).map e.symm.dualMap :=  by
  ext x
  simp only [mem_dualAnnihilator, mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    dualMap_apply_symm]
  refine ⟨fun h ↦ ⟨e.dualMap x, h, by ext; simp⟩, ?_⟩
  rintro ⟨y, hy, rfl⟩ x hxu
  simpa using hy x hxu
