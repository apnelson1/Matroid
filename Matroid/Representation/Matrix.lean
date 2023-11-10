import Matroid.Representation.Basic
import Matroid.ForMathlib.LinearAlgebra.Matrix.Rowspace

variable {α β ι W W' 𝔽 R : Type*} {e f x : α} {I B X Y : Set α} {M : Matroid α} [Field 𝔽]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']


open Submodule Set Matroid Matrix


def Matrix.matroidOf (A : Matrix m α 𝔽) (E : Set α) := matroidOfFun 𝔽 A.colFun E

def Matrix.subtypeMatroidOf {E : Set α} (A : Matrix m E 𝔽) := matroidOfSubtypeFun 𝔽 A.colFun

namespace Matroid

abbrev Rep.toMatrix (v : M.Rep 𝔽 (ι → 𝔽)) : Matrix ι α 𝔽 := (Matrix.of v)ᵀ

theorem Rep.colBasis_eq_base (v : M.Rep 𝔽 (ι → 𝔽)) : v.toMatrix.ColBasis = M.Base := by
  ext B
  change _ ↔ B ∈ {B | M.Base B}
  simp_rw [setOf_base_eq_maximals_setOf_indep, colBasis_iff_maximal_linearIndependent, v.indep_iff]
  rfl

theorem dual_aux [Fintype α] {M N : Matroid α} (hM : M.E = univ) (hN : N.E = univ)
    (vM : M.Rep 𝔽 (ι → 𝔽)) (vN : N.Rep 𝔽 (η → 𝔽))
    (h : vM.toMatrix.rowSpace = vN.toMatrix.nullSpace) : N = M﹡ := by
  apply eq_of_base_iff_base_forall (by rw [hN, dual_ground, hM]) (fun B _ ↦ ?_)
  rw [← vN.colBasis_eq_base, dual_base_iff, ← vM.colBasis_eq_base, hM, ← compl_eq_univ_diff,
    colBasis_iff_colBasis_compl_of_orth h, compl_compl]

theorem dual_aux2 {M N : Matroid α} {E : Set α} (hE : E.Finite) (hME : M.E = E) (hNE : N.E = E)
    (vM : M.Rep 𝔽 (ι → 𝔽)) (vN : N.Rep 𝔽 (η → 𝔽))
    (h : (vM.toMatrix.colSubmatrix E).rowSpace = (vN.toMatrix.colSubmatrix E).nullSpace) :
    N = M﹡ := by
  apply eq_of_onGround_eq hNE (by rwa [dual_ground])
  rw [← onGround_dual]
  have _ := hE.fintype
  have _ := (hNE.symm ▸ hE).fintype
  have _ := (hME.symm ▸ hE).fintype
  apply dual_aux (onGround_ground hME.symm.subset) (onGround_ground hNE.symm.subset)
    (vM.onGround' E) (vN.onGround' E)
  convert h
  exact hME

theorem Representable.dual [M.Finite] (h : M.Representable 𝔽) : M﹡.Representable 𝔽 := by
  obtain ⟨v⟩ := h
  set ns := (v.toMatrix.colSubmatrix M.E).nullSpace
  obtain b := Basis.ofVectorSpace 𝔽 ns
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
