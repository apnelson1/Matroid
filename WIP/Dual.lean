import Matroid.Representation.Basic

open Set Matrix

variable {α β η 𝔽 : Type*} [Field 𝔽]

namespace Matroid


section Dual

variable {ι η 𝔽 : Type*} [Field 𝔽]

abbrev Rep.toMatrix {M : Matroid α} {η 𝔽 : Type*} [Field 𝔽] (v : M.Rep 𝔽 (η → 𝔽)) : Matrix η α 𝔽 :=
  (Matrix.of v)ᵀ

lemma Rep.colBasis_eq_isBase (v : M.Rep 𝔽 (η → 𝔽)) : v.toMatrix.ColBasis = M.IsBase := by
  ext B
  change _ ↔ B ∈ {B | M.IsBase B}
  simp_rw [setOf_isBase_eq_maximals_setOf_indep, colBasis_iff_maximal_linearIndependent, v.indep_iff]
  rfl

lemma eq_dual_of_rowSpace_eq_nullSpace_on_univ [Fintype α] {M N : Matroid α}
    (hM : M.E = univ) (hN : N.E = univ) (vM : M.Rep 𝔽 (ι → 𝔽)) (vN : N.Rep 𝔽 (η → 𝔽))
    (h : vM.toMatrix.rowSpace = vN.toMatrix.nullSpace) : N = M✶ := by
  apply ext_isBase (by rw [hN, dual_ground, hM]) (fun B _ ↦ ?_)
  rw [← vN.colBasis_eq_isBase, dual_isBase_iff, ← vM.colBasis_eq_isBase, hM, ← compl_eq_univ_diff,
    colBasis_iff_colBasis_compl_of_orth h, compl_compl]

lemma eq_dual_of_rowSpace_eq_nullSpace {M N : Matroid α} {E : Set α} (hE : E.Finite)
    (hME : M.E = E) (hNE : N.E = E) (vM : M.Rep 𝔽 (ι → 𝔽)) (vN : N.Rep 𝔽 (η → 𝔽))
    (h : (vM.toMatrix.colSubmatrix E).rowSpace = (vN.toMatrix.colSubmatrix E).nullSpace) :
    N = M✶ := by
  apply eq_of_restrictSubtype_eq hNE (by rwa [dual_ground])
  rw [← restrictSubtype_dual']
  have _ := hE.fintype
  have _ := (hNE.symm ▸ hE).fintype
  have _ := (hME.symm ▸ hE).fintype
  refine eq_dual_of_rowSpace_eq_nullSpace_on_univ (by simp) (by simp)
    (vM.restrictSubtype E) (vN.restrictSubtype E) ?_
  convert h
  · ext
    simp [Rep.restrictSubtype, Rep.comap, Rep.ofGround]
  · ext
    simp [Rep.restrictSubtype, Rep.comap, Rep.ofGround]
  exact hME

/-- The dual of a representable matroid is representable -/
lemma Representable.dual [M.Finite] (h : M.Representable 𝔽) : M✶.Representable 𝔽 := by
  obtain ⟨v⟩ := h
  set ns : Submodule 𝔽 (M✶.E → 𝔽) := (v.toMatrix.colSubmatrix M.E).nullSpace
  obtain b := IsBasis.ofVectorSpace 𝔽 ns
  have : Fintype M✶.E := M.ground_finite.fintype
  set Mdrep := (Matroid.ofSubtypeFun_rep 𝔽 b.toRowMatrix.colFun)
  have Mdrep' := Mdrep.representable
  rwa [← eq_dual_of_rowSpace_eq_nullSpace (ground_finite M) rfl (by simp) v Mdrep]
  have hbs := b.toRowMatrix_rowSpace
  change _ = nullSpace _ at hbs
  rw [← orthSpace_nullSpace_eq_rowSpace, eq_comm, eq_orthSpace_comm,
    orthSpace_nullSpace_eq_rowSpace] at hbs
  rw [← hbs]
  apply congr_arg

  ext i j
  simp [Mdrep]

  rw [extend_apply']




@[simp] lemma dual_representable_iff [M.Finite] : M✶.Representable 𝔽 ↔ M.Representable 𝔽 :=
  ⟨fun h ↦ dual_dual M ▸ h.dual, Representable.dual⟩


-- TODO  : if [I|A] represents M, then [Aᵀ|I] represents M✶

end Dual
