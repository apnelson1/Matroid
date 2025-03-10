import Matroid.Representation.StandardRep
import Matroid.ForMathlib.LinearAlgebra.Matrix

variable {α β ι W W' 𝔽 R : Type*} {e f x : α} {I B X Y : Set α} {M : Matroid α} [Field 𝔽]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']

open Submodule Set Matroid Matrix Set.Notation


abbrev Matrix.submatrixOn {α β R : Type*} (A : Matrix α β R) (s : Set α) (t : Set β) :=
    A.submatrix ((↑) : s → α) ((↑) : t → β)

abbrev Matrix.rowSubmatrixOn {α β R : Type*} (A : Matrix α β R) (s : Set α) :=
    A.submatrix ((↑) : s → α) id


notation:max A"["s", " t"]" => Matrix.submatrixOn A s t

notation:max A"["s",*]" => Matrix.rowSubmatrixOn A s

lemma foo (A : Matrix α β 𝔽) (s : Set α) (t : Set β) (hst : A[s,t] = 0) :
    LinearIndependent 𝔽 A ↔ LinearIndependent 𝔽 A[s,tᶜ] ∧ LinearIndependent 𝔽 A[sᶜ,*] := by
  refine ⟨fun h ↦ ⟨?_, h.comp _ Subtype.val_injective⟩, fun h ↦ ?_⟩
  · have hli := h.comp ((↑) : s → α) Subtype.val_injective
    refine hli.map_injOn (f := LinearMap.funLeft 𝔽 𝔽 (Subtype.val : ↥tᶜ → β)) ?_
    simp only [InjOn, SetLike.mem_coe, Finsupp.mem_span_range_iff_exists_finsupp, Finsupp.sum,
      Function.comp_apply, funext_iff, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      LinearMap.funLeft, LinearMap.coe_mk, AddHom.coe_mk, Subtype.forall, mem_compl_iff,
      forall_exists_index]

    -- simp [DFunLike.ext_iff]
    intro x x' hx y y' hy hxy i
    rw [← hx, ← hy]


    ext i
    intro x hx y hy hxy
    simp at hx
    simp [Finsupp.mem_span_range_iff_exists_finsupp] at hx
    ext i

    simp [LinearMap.funLeft_apply]
  sorry
    -- rw [linearIndependent_iff'] at h ⊢
    -- simp only [Subtype.forall]



namespace Matroid

set_option linter.style.longLine false

-- lemma foo (𝔽 )

structure MatrixRep (M : Matroid α) (𝔽 : Type*) [Field 𝔽] (B : Set α) where
  toMatrix : Matrix B ↥(M.E \ B) 𝔽
  forall_indep_iff' : ∀ (X : Set B) (Y : Set ↥(M.E \ B)),
    M.Indep (X ∪ Y) ↔ LinearIndependent 𝔽 (toMatrix.submatrix ((↑) : X → B) ((↑) : Y → ↥(M.E \ B)))ᵀ
  -- forall_indep_iff : ∀ {I : Set α} (hI : I ⊆ M.E), M.Indep I ↔ LinearIndependent 𝔽
  --   (toMatrix.submatrix (fun x : ↥(B \ I) ↦ ⟨x, x.2.1⟩) (fun y : ↥(I \ B) ↦ ⟨y, hI y.2.1, y.2.2⟩))ᵀ

noncomputable def Rep.IsStandard.toMatrixRep (v : M.Rep 𝔽 (B →₀ 𝔽)) (hv : v.IsStandard) :
    M.MatrixRep 𝔽 B where
  toMatrix := .of fun e f ↦ v f.1 e
  forall_indep_iff' := by
    intro X Y
    sorry



noncomputable def Rep.toMatrixRep (v : M.Rep 𝔽 W) (hB : M.IsBase B) : M.MatrixRep 𝔽 B where
  toMatrix := .of fun e f ↦ v.standardRep hB f.1 e
  forall_indep_iff' := by
    intro X Y
    rw [v.indep_iff, linearIndepOn_union_iff_quotient, ← v.indep_iff,
      and_iff_right (hB.indep.subset (by simp))]
    simp only [v.indep_iff, linearIndepOn_iff, transpose_submatrix, linearIndependent_iff]
    refine ⟨fun h c hc0 ↦ ?_, fun h ↦ ?_⟩
    · simp [Finsupp.linearCombination, Finsupp.sum, Matrix.of] at hc0
      sorry
    sorry
    sorry
    -- rw [v.indep_iff, linearIndepOn_union_iff_quotient, ← v.indep_iff,
    --   and_iff_right (hB.indep.subset (by simp))]
    -- swap
    -- · refine (disjoint_sdiff_inter (s := M.E) (t := B)).symm.mono ?_ ?_
    --   · convert image_subset_range Subtype.val X
    --     simp [hB.subset_ground]
    --   · convert image_subset_range Subtype.val Y
    --     simp [Set.ext_iff]
    -- simp only [linearIndepOn_iff, transpose_submatrix, linearIndependent_iff]
    -- refine ⟨fun h c hc0 ↦ ?_, fun h ↦ ?_⟩
    -- · simp [Finsupp.linearCombination, Finsupp.sum] at hc0




    -- nth_rewrite 1 [← diff_union_inter I B]
    -- rw [union_comm, v.indep_iff, linearIndepOn_union_iff_quotient disjoint_sdiff_inter.symm,
    --   ← v.indep_iff, and_iff_right (hB.indep.inter_left _), LinearIndepOn]
