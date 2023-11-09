import Matroid.Representation.Basic
import Matroid.ForMathlib.LinearAlgebra.Matrix.Rowspace

variable {α β ι W W' 𝔽 R : Type*} {e f x : α} {I B X Y : Set α} {M : Matroid α} [Field 𝔽]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']


open Submodule Set Matroid Matrix


def Matrix.matroidOf (A : Matrix m α 𝔽) (E : Set α) := matroidOfFun 𝔽 A.colFun E

def Matrix.subtypeMatroidOf {E : Set α} (A : Matrix m E 𝔽) := matroidOfSubtypeFun 𝔽 A.colFun

namespace Matroid

abbrev Rep.toMatrix (v : M.Rep 𝔽 (ι → 𝔽)) : Matrix ι α 𝔽 := (Matrix.of v)ᵀ

theorem Rep.column_basis_eq_base (v : M.Rep 𝔽 (ι → 𝔽)) : v.toMatrix.ColBasis = M.Base := by
  ext B
  change _ ↔ B ∈ {B | M.Base B}
  simp_rw [setOf_base_eq_maximals_setOf_indep, colBasis_iff_maximal_linearIndependent, v.indep_iff]
  rfl

theorem foo {M N : Matroid α} {E : Set α} [Fintype E] (hME : M.E = E) (hNE : N.E = E)
    (vM : M.Rep 𝔽 (α → 𝔽)) (vN : N.Rep 𝔽 (β → 𝔽))
    (h : (vM.toMatrix.colSubmatrix E).rowSpace = (vN.toMatrix.colSubmatrix E).nullSpace) : N = M﹡ := by
  sorry





-- theorem rep_iff_exists_matrix : M.Representable 𝔽 ↔ ∃ A : Matrix α α 𝔽, M = A.matroidOf M.E := by
--   refine ⟨fun ⟨A, hM⟩ ↦ ?_, fun h ↦ ?_⟩
--   ·



-- structure MatrixRep (M : Matroid α) (𝔽 R : Type*) [Field 𝔽] where
--   ( A : Matrix R α 𝔽 )
--   ( v : M.Rep 𝔽 (R → 𝔽) )
--   ( compatible : ∀ i e, A i e = v e i )

-- def MatrixRep.Emat (P : M.MatrixRep 𝔽 R) : Matrix R M.E 𝔽 :=
--   Matrix.of fun (i : R) (e : M.E) ↦ P.A i e
