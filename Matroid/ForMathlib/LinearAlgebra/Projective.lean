import Mathlib.LinearAlgebra.Projectivization.Independence
import Matroid.ForMathlib.LinearAlgebra.LinearIndependent

variable {ι K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    {f : ι → Projectivization K V}

open Set Function Projectivization

lemma Projectivization.linearIndependent_iff (f : ι → V) (hf0 : ∀ i, f i ≠ 0) :
    LinearIndependent K f ↔ Independent (fun i ↦ mk K (f i) (hf0 i)) := by
  rw [independent_iff]
  choose c hc using fun i ↦ exists_smul_eq_mk_rep K (f i) (hf0 i)
  convert LinearIndependent.units_smul_iff (w := fun i ↦ (c i)⁻¹)
  ext i
  simp [← hc]
