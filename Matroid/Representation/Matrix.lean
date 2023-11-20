import Matroid.Representation.Basic
import Matroid.ForMathlib.LinearAlgebra.Matrix.Rowspace

variable {α β ι W W' 𝔽 R : Type*} {e f x : α} {I B X Y : Set α} {M : Matroid α} [Field 𝔽]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']

open Submodule Set Matroid Matrix

namespace Matroid

abbrev Rep.toMatrix (v : M.Rep 𝔽 (ι → 𝔽)) : Matrix ι α 𝔽 := (Matrix.of v)ᵀ

theorem Rep.colBasis_eq_base (v : M.Rep 𝔽 (ι → 𝔽)) : v.toMatrix.ColBasis = M.Base := by
  ext B
  change _ ↔ B ∈ {B | M.Base B}
  simp_rw [setOf_base_eq_maximals_setOf_indep, colBasis_iff_maximal_linearIndependent, v.indep_iff]
  rfl

section Dual

theorem eq_dual_of_rowSpace_eq_nullSpace_on_univ [Fintype α] {M N : Matroid α}
    (hM : M.E = univ) (hN : N.E = univ) (vM : M.Rep 𝔽 (ι → 𝔽)) (vN : N.Rep 𝔽 (η → 𝔽))
    (h : vM.toMatrix.rowSpace = vN.toMatrix.nullSpace) : N = M﹡ := by
  apply eq_of_base_iff_base_forall (by rw [hN, dual_ground, hM]) (fun B _ ↦ ?_)
  rw [← vN.colBasis_eq_base, dual_base_iff, ← vM.colBasis_eq_base, hM, ← compl_eq_univ_diff,
    colBasis_iff_colBasis_compl_of_orth h, compl_compl]

theorem eq_dual_of_rowSpace_eq_nullSpace {M N : Matroid α} {E : Set α} (hE : E.Finite)
    (hME : M.E = E) (hNE : N.E = E) (vM : M.Rep 𝔽 (ι → 𝔽)) (vN : N.Rep 𝔽 (η → 𝔽))
    (h : (vM.toMatrix.colSubmatrix E).rowSpace = (vN.toMatrix.colSubmatrix E).nullSpace) :
    N = M﹡ := by
  apply eq_of_onGround_eq hNE (by rwa [dual_ground])
  rw [← onGround_dual]
  have _ := hE.fintype
  have _ := (hNE.symm ▸ hE).fintype
  have _ := (hME.symm ▸ hE).fintype
  apply eq_dual_of_rowSpace_eq_nullSpace_on_univ (onGround_ground hME.symm.subset)
    (onGround_ground hNE.symm.subset) (vM.onGround' E) (vN.onGround' E)
  convert h
  exact hME

/-- The dual of a representable matroid is representable -/
theorem Representable.dual [M.Finite] (h : M.Representable 𝔽) : M﹡.Representable 𝔽 := by
  obtain ⟨v⟩ := h
  set ns : Submodule 𝔽 (M﹡.E → 𝔽):= (v.toMatrix.colSubmatrix M.E).nullSpace
  obtain b := Basis.ofVectorSpace 𝔽 ns
  have : Fintype M﹡.E
  · exact M.ground_finite.fintype
  set Mdrep := (matroidOfSubtypeFun_rep 𝔽 b.toRowMatrix.colFun)
  have Mdrep' := Mdrep.representable
  rwa [← eq_dual_of_rowSpace_eq_nullSpace (ground_finite M) rfl (by simp) v Mdrep]
  have hbs := b.toRowMatrix_rowSpace
  change _ = nullSpace _ at hbs
  rw [← orthSpace_nullSpace_eq_rowSpace, eq_comm, eq_orthSpace_comm,
    orthSpace_nullSpace_eq_rowSpace] at hbs
  rw [← hbs]
  apply congr_arg
  ext
  simp

@[simp] theorem dual_representable_iff [M.Finite] : M﹡.Representable 𝔽 ↔ M.Representable 𝔽 :=
  ⟨fun h ↦ dual_dual M ▸ h.dual, Representable.dual⟩


-- TODO  : if [I|A] represents M, then [Aᵀ|I] represents M﹡

end Dual
