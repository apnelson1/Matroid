import Mathlib.LinearAlgebra.Matrix.ToLin

open Matrix Submodule Set LinearMap BigOperators

variable {R m n : Type*}

section Semiring

variable [Semiring R]

@[simp] theorem Matrix.vecMulLinear_apply' [Fintype m] (M : Matrix m n R) (x : m → R) :
    M.vecMulLinear x = M.vecMul x := rfl

theorem Matrix.coe_vecMulLinear [Fintype m] (M : Matrix m n R) :
    (M.vecMulLinear : _ → _) = M.vecMul := rfl

theorem vecMul_eq_sum [Fintype m] (M : Matrix m n R) (x : m → R) :
    M.vecMul x = ∑ i, x i • M i := by
  ext j; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]; rfl

theorem mulVec_eq_sum {R : Type*} [CommRing R] [Fintype n] (M : Matrix m n R) (x : n → R) :
    M.mulVec x = ∑ i, (x i) • (M · i) := by
  ext J
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  rfl

end Semiring

section CommRing

variable [CommRing R] {M : Matrix m n R}

theorem Matrix.range_vecMulLinear {R : Type*} [CommSemiring R] [Fintype m] (M : Matrix m n R) :
    LinearMap.range M.vecMulLinear = span R (range M) := by
  letI := Classical.decEq m
  simp_rw [range_eq_map, ← iSup_range_stdBasis, Submodule.map_iSup, range_eq_map, ←
    Ideal.span_singleton_one, Ideal.span, Submodule.map_span, image_image, image_singleton,
    Matrix.vecMulLinear_apply', iSup_span, range_eq_iUnion, iUnion_singleton_eq_range]
  simp only [LinearMap.stdBasis, coe_single, single_vecMul, one_mul]

theorem Matrix.coe_mulVecLin [Fintype n] (M : Matrix m n R) :
    (M.mulVecLin : _ → _) = M.mulVec := rfl

@[simp] theorem Matrix.mulVecLin_transpose [Fintype m] (M : Matrix m n R) :
    Mᵀ.mulVecLin = M.vecMulLinear := by
  ext; simp [mulVec_transpose]

@[simp] theorem Matrix.vecMulLinear_transpose [Fintype n] (M : Matrix m n R) :
    Mᵀ.vecMulLinear = M.mulVecLin := by
  ext; simp [vecMul_transpose]

theorem Matrix.vecMulLinear_injective_iff {R : Type*} [CommRing R] [Fintype m] {M : Matrix m n R} :
    Function.Injective M.vecMulLinear ↔ LinearIndependent R (fun i ↦ M i) := by
  simp only [←LinearMap.ker_eq_bot, Fintype.linearIndependent_iff, Submodule.eq_bot_iff,
     LinearMap.mem_ker, vecMulLinear_apply', vecMul_eq_sum]
  aesop

theorem Matrix.ker_mulVecLin_eq_bot_iff' [Fintype n] :
    (LinearMap.ker M.mulVecLin) = ⊥ ↔ ∀ v, M.mulVec v = 0 → v = 0 := by
  simp only [Submodule.eq_bot_iff, LinearMap.mem_ker, Matrix.mulVecLin_apply]

theorem Matrix.mulVecLin_injective_iff [Fintype n] :
    Function.Injective M.mulVecLin ↔ LinearIndependent R (fun i ↦ Mᵀ i) := by
  rw [←vecMulLinear_transpose, vecMulLinear_injective_iff]

end CommRing
