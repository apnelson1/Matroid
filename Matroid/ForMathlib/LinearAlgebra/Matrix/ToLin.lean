import Mathlib.LinearAlgebra.Matrix.ToLin

open Matrix Submodule Set LinearMap BigOperators

variable {R m n : Type*}

section Semiring

variable [Semiring R]

theorem vecMul_eq_sum [Fintype m] (M : Matrix m n R) (x : m → R) :
    x ᵥ* M = ∑ i, x i • M i := by
  ext j; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]; rfl

theorem Matrix.vecMulLinear_injective_iff {R : Type*} [CommRing R] [Fintype m] {M : Matrix m n R} :
    Function.Injective M.vecMulLinear ↔ LinearIndependent R (fun i ↦ M i) := by
  rw [← vecMul_injective_iff]; rfl

end Semiring

section CommRing

variable [CommRing R] {M : Matrix m n R}

theorem mulVec_eq_sum [Fintype n] (M : Matrix m n R) (x : n → R) :
    M *ᵥ x = ∑ i, (x i) • (M · i) := by
  ext j; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]; rfl

theorem Matrix.mulVecLin_injective_iff [Fintype n] :
    Function.Injective M.mulVecLin ↔ LinearIndependent R (fun i ↦ Mᵀ i) := by
  rw [← vecMulLinear_transpose, vecMulLinear_injective_iff]

end CommRing
