import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Matroid.ForMathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional

open Matrix

section vecMul

variable {α : Type*} [Field α] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  {K : Type*} [Field K]

theorem mulVec_surjective_iff_exists_rightInverse {A : Matrix m n α} :
    Function.Surjective A.mulVec ↔ ∃ B : Matrix n m α, A * B = 1 := by
  refine ⟨fun h ↦ ?_, fun ⟨B, hBA⟩ y ↦ ⟨B.mulVec y, by simp [hBA]⟩⟩
  have hch : ∀ i : m, ∃ x, A.mulVec x = Pi.single i 1 := fun _ ↦ h _
  choose cols hcols using hch
  use (Matrix.of cols).transpose
  apply_fun Matrix.transpose using transpose_injective
  apply funext fun j ↦ ?_
  convert hcols j
  ext i
  rw [Pi.single_apply]
  rfl

theorem vecMul_surjective_iff_exists_leftInverse {A : Matrix m n α} :
    Function.Surjective A.vecMul ↔ ∃ B : Matrix n m α, B * A = 1 := by
  simp_rw [←mulVec_transpose, mulVec_surjective_iff_exists_rightInverse]
  refine ⟨fun ⟨B, hB⟩ ↦ ⟨Bᵀ, ?_⟩, fun ⟨B, hB⟩ ↦ ⟨Bᵀ, by rw [←transpose_mul, hB, transpose_one]⟩⟩
  apply_fun Matrix.transpose using transpose_injective
  rw [transpose_mul, transpose_transpose, hB, transpose_one]

theorem vecMul_surjective_iff_isUnit {A : Matrix m m α} :
    Function.Surjective A.vecMul ↔ IsUnit A := by
  rw [vecMul_surjective_iff_exists_leftInverse]
  exact ⟨fun ⟨B, hBA⟩ ↦ isUnit_of_left_inverse hBA,
    fun h ↦ ⟨A⁻¹, @inv_mul_of_invertible _ _ _ _ _ A h.invertible ⟩⟩

theorem mulVec_surjective_iff_isUnit {A : Matrix m m α} :
    Function.Surjective A.mulVec ↔ IsUnit A := by
  rw [←isUnit_transpose, ←vecMul_surjective_iff_isUnit]; convert Iff.rfl; rw [vecMul_transpose]

theorem mulVec_injective_iff_isUnit {A : Matrix m m K} :
    Function.Injective A.mulVec ↔ IsUnit A := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [←isUnit_transpose, ←vecMul_surjective_iff_isUnit]
    simp_rw [vecMul_transpose]
    exact LinearMap.surjective_of_injective (f := A.mulVecLin) h
  change Function.Injective A.mulVecLin
  rw [←LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  replace h := h.invertible
  simpa using congr_arg A⁻¹.mulVecLin hc

theorem vecMul_injective_iff_isUnit {A : Matrix m m K} :
    Function.Injective A.vecMul ↔ IsUnit A := by
  simp_rw [←mulVec_transpose, mulVec_injective_iff_isUnit, isUnit_transpose]

theorem linearIndependent_rows_iff_isUnit {A : Matrix m m K} :
    LinearIndependent K (fun i ↦ A i) ↔ IsUnit A := by
  rw [←transpose_transpose A, ←mulVecLin_injective_iff, mulVecLin_transpose,
    transpose_transpose, ←vecMul_injective_iff_isUnit, coe_vecMulLinear]

theorem linearIndependent_cols_iff_isUnit {A : Matrix m m K} :
    LinearIndependent K (fun i ↦ Aᵀ i) ↔ IsUnit A := by
  rw [←transpose_transpose A, isUnit_transpose, linearIndependent_rows_iff_isUnit,
    transpose_transpose]

theorem vecMul_surjective_of_invertible (A : Matrix m m α) [Invertible A] :
    Function.Surjective A.vecMul :=
  fun y ↦ ⟨A⁻¹.vecMul y, by simp⟩

theorem mulVec_surjective_of_invertible (A : Matrix m m α) [Invertible A] :
    Function.Surjective A.mulVec :=
  fun y ↦ ⟨A⁻¹.mulVec y, by simp⟩

theorem vecMul_injective_of_invertible (A : Matrix m m K) [Invertible A] :
    Function.Injective A.vecMul :=
  vecMul_injective_iff_isUnit.2 <| isUnit_of_invertible A

theorem mulVec_injective_of_invertible (A : Matrix m m K) [Invertible A] :
    Function.Injective A.mulVec :=
  mulVec_injective_iff_isUnit.2 <| isUnit_of_invertible A

theorem linearIndependent_rows_of_invertible (A : Matrix m m K) [Invertible A] :
    LinearIndependent K (fun i ↦ A i) :=
  linearIndependent_rows_iff_isUnit.2 <| isUnit_of_invertible A

theorem linearIndependent_cols_of_invertible (A : Matrix m m K) [Invertible A] :
    LinearIndependent K (fun i ↦ Aᵀ i) :=
  linearIndependent_cols_iff_isUnit.2 <| isUnit_of_invertible A

end vecMul
