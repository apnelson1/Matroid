import Matroid.Representation.StandardRep
import Matroid.ForMathlib.LinearAlgebra.Matrix

variable {α β ι W W' 𝔽 R : Type*} {e f x : α} {I B X Y : Set α} {M : Matroid α} [Field 𝔽]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']

open Submodule Set Matroid Matrix Set.Notation


abbrev Matrix.submatrixOn {α β R : Type*} (A : Matrix α β R) (s : Set α) (t : Set β) :=
    A.submatrix ((↑) : s → α) ((↑) : t → β)

abbrev Matrix.rowSubmatrixOn {α β R : Type*} (A : Matrix α β R) (s : Set α) :=
    A.submatrix ((↑) : s → α) id


-- notation:max A"["s", " t"]" => Matrix.submatrixOn A s t

-- notation:max A"["s",*]" => Matrix.rowSubmatrixOn A s

-- lemma foo (A : Matrix α β 𝔽) (s : Set α) (t : Set β) (hst : A[s,t] = 0) :
--     LinearIndependent 𝔽 A ↔ LinearIndependent 𝔽 A[s,tᶜ] ∧ LinearIndependent 𝔽 A[sᶜ,*] := by
--   refine ⟨fun h ↦ ⟨?_, h.comp _ Subtype.val_injective⟩, fun h ↦ ?_⟩
--   · have hli := h.comp ((↑) : s → α) Subtype.val_injective
--     refine hli.map_injOn (f := LinearMap.funLeft 𝔽 𝔽 (Subtype.val : ↥tᶜ → β)) ?_
--     simp only [InjOn, SetLike.mem_coe, Finsupp.mem_span_range_iff_exists_finsupp, Finsupp.sum,
--       Function.comp_apply, funext_iff, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
--       LinearMap.funLeft, LinearMap.coe_mk, AddHom.coe_mk, Subtype.forall, mem_compl_iff,
--       forall_exists_index]

--     -- simp [DFunLike.ext_iff]
--     intro x x' hx y y' hy hxy i
--     rw [← hx, ← hy]


--     ext i
--     intro x hx y hy hxy
--     simp at hx
--     simp [Finsupp.mem_span_range_iff_exists_finsupp] at hx
--     ext i

--     simp [LinearMap.funLeft_apply]
--   sorry
--     -- rw [linearIndependent_iff'] at h ⊢
--     -- simp only [Subtype.forall]



namespace Matroid

set_option linter.style.longLine false

-- lemma foo (𝔽 )

structure ReducedRep (M : Matroid α) (𝔽 : Type*) [Field 𝔽] (B : Set α) where
  toMatrix : Matrix B ↥(M.E \ B) 𝔽
  forall_indep_iff' : ∀ (X : Set B) (Y : Set ↥(M.E \ B)),
    M.Indep (X ∪ Y) ↔
    LinearIndependent 𝔽 (toMatrix.submatrix (fun x : ↥Xᶜ ↦ x.1) (fun y : Y ↦ y.1))ᵀ
  -- forall_indep_iff : ∀ {I : Set α} (hI : I ⊆ M.E), M.Indep I ↔ LinearIndependent 𝔽
  -- (toMatrix.submatrix (fun x : ↥(B \ I) ↦ ⟨x, x.2.1⟩) (fun y : ↥(I \ B) ↦ ⟨y, hI y.2.1, y.2.2⟩))ᵀ

theorem linearIndepOn_image_injOn_iff {ι ι' R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {e : ι → ι'} {f : ι' → M} {s : Set ι} (he : InjOn e s) :
    LinearIndepOn R (f ∘ e) s ↔ LinearIndepOn R f (e '' s) := by
  rw [← linearIndependent_set_coe_iff, ← linearIndependent_set_coe_iff]
  exact linearIndependent_equiv' (Equiv.Set.imageOfInjOn _ _ he) <|
    by simp [funext_iff, Equiv.Set.imageOfInjOn]

lemma aux {B : Set α} [Fintype B] [DecidableEq B] (P : Matrix B α 𝔽) (X : Set B)
    (hB : ∀ i : B, Pᵀ i = Pi.single i 1) (Y : Set α) (hYB : Disjoint Y B) :
    LinearIndepOn 𝔽 Pᵀ (((↑) '' X) ∪ Y) ↔
    LinearIndependent 𝔽 (P.submatrix (fun i : ↥Xᶜ ↦ i.1) (fun i : Y ↦ i.1))ᵀ := by
  sorry

lemma aux' {B : Set α} [Fintype B] [DecidableEq B] (P : Matrix B α 𝔽) (X : Set α) (hX : X ⊆ B)
    (hB : ∀ i : B, Pᵀ i = Pi.single i 1) (Y : Set α) (hYB : Disjoint Y B) :
    LinearIndepOn 𝔽 Pᵀ (X ∪ Y) ↔
    LinearIndependent 𝔽
      (P.submatrix (Set.inclusion (show B \ X ⊆ B from diff_subset)) (fun i : Y ↦ i.1))ᵀ := by
  sorry

noncomputable def Rep.IsStandard.toReducedRep [Fintype B] (v : M.Rep 𝔽 (B → 𝔽))
    (hv : v.IsStandard') : M.ReducedRep 𝔽 B where
  toMatrix := .of fun e f ↦ v f.1 e
  forall_indep_iff' := by
    classical
    intro X Y
    set P := (Matrix.of v)ᵀ
    simp_rw [v.indep_iff, show v = fun i j ↦ Pᵀ i j from rfl]
    rw [aux _ _ hv.apply_eq_single]
    · apply linearIndependent_equiv' (Equiv.Set.image _ Y Subtype.val_injective).symm
      ext i j
      obtain ⟨_, ⟨i, hi, rfl⟩⟩ := i
      simp
    refine disjoint_left.2 ?_
    rintro _ ⟨⟨a,ha'⟩, ha, rfl⟩ haB
    exact ha'.2 haB

noncomputable def ReducedRep.toRep [DecidablePred (· ∈ M.E)] [DecidablePred (· ∈ B)]
    [DecidableEq B] (P : M.ReducedRep 𝔽 B) := _
    -- M.Rep 𝔽 (B → 𝔽) := Rep.ofSubtypeFun
    -- (fun x ↦ if hx : x.1 ∈ B then (Pi.single ⟨x, hx⟩ 1) else (P.1 · ⟨x, x.2, hx⟩))
    -- (by
    --   intro I

    -- )

      -- change LinearIndependent 𝔽 (fun (j : Subtype.val '' Y) ↦ (P.submatrix _ _)ᵀ j) ↔ _
      -- rw [linearIndependent_set_coe_iff]
  --   rw [v.indep_iff]
  --   have hli : LinearIndependent 𝔽 <| of (fun (i : X) (j : X) ↦ v (j : α) i) := by
  --     convert (Pi.basisFun (η := ↥X) 𝔽).linearIndependent with ⟨a, ha⟩
  --     ext ⟨k, hk⟩ ⟨j, hj⟩
  --     simp [hv.apply_eq_single, Pi.single_comm, Pi.single_apply]
  --   have hli' : LinearIndependent 𝔽 <| (of (fun (i : X) (j : X) ↦ v (j : α) i))ᵀ := by
  --     convert (Pi.basisFun (η := ↥X) 𝔽).linearIndependent with ⟨a, ha⟩
  --     ext ⟨k, hk⟩ ⟨j, hj⟩
  --     simp [hv.apply_eq_single, Pi.single_apply]

  --   convert Matrix.fromBlocks_zero₁₁_cols_linearIndependent_iff_of_rows
  --     (m₁ := ↥Xᶜ) (m₂ := X) (n₁ := X) (n₂ := Y) (K := 𝔽) (B := .of fun i j ↦ v j i)
  --     (D := .of fun i j ↦ v j i) (C := .of fun i j ↦ v j i) hli
  --   swap
  --   · rw [and_iff_left hli']
  --     rfl

  --   -- have aux (Q : Set α) (P : Set Q) : LinearIndependent 𝔽
  --   -- ((fun i : P ↦ (fromBlocks 0 (of fun i j ↦ v ↑↑j ↑i) (of fun i j ↦ v ↑↑j ↑i) (of fun i j ↦ v ↑↑j ↑i))ᵀ i) ∘ Sum.inl) ↔
  -- -- LinearIndepOn 𝔽 (⇑v) (Subtype.val '' X)
  --   let ψ : (B → 𝔽) ≃ₗ[𝔽] (↥Xᶜ ⊕ X → 𝔽) :=
  --     LinearEquiv.funCongrLeft _ _ <| ((Equiv.Set.sumCompl X).symm.trans (Equiv.sumComm _ _)).symm


  --   rw [linearIndepOn_union_iff sorry, linearIndependent_sum, ← ψ.symm.linearIndependent_iff]
  --   convert Iff.rfl
  --   · rw [← linearIndepOn_image_injOn_iff Subtype.val_injective.injOn,
  --       ← linearIndependent_set_coe_iff]
  --     convert Iff.rfl with i
  --     ext j


  --     simp [ψ, LinearMap.funLeft, Sum.swap, fromBlocks, Equiv.Set.sumCompl]
  --     rw [IsStandard'.apply_eq_single hv ↑i]
  --     simp



    --  Equiv.sumCongr
    --     (Equiv.Set.imageOfInjOn _ _ Subtype.val_injective.injOn)
    --     (Equiv.Set.imageOfInjOn _ _ Subtype.val_injective.injOn) |>.trans
    --     (Equiv.Set.union sorry).symm


    -- rw [← linearIndependent_set_coe_iff, ← ψ.linearIndependent_iff]
    -- refine linearIndependent_equiv' (R := 𝔽) e.symm ?_
    -- ext ⟨i, hi⟩ ⟨j, hj⟩
    -- by_cases hjX : ⟨j, hj⟩ ∈ X
    -- obtain ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ := hi
    -- · simp [ψ, fromBlocks, Equiv.Set.union, Equiv.Set.union', e, hi, hjX]
    --   split_ifs
    --   simp [Equiv.Set.imageOfInjOn]
    -- simp [e, ψ]











    -- convert Matrix.fromBlocks_zero₂₂_cols_linearIndependent_iff
    --   (m₁ := ↥Xᶜ) (m₂ := X) (n₁ := X) (n₂ := Y) (R := 𝔽) (B := .of fun i j ↦ v j i)
    --   (D := .of fun i j ↦ v j i) (C := .of fun i j ↦ v j i) ?_
    -- sorry



noncomputable def Rep.toReducedRep (v : M.Rep 𝔽 W) (hB : M.IsBase B) : M.ReducedRep 𝔽 B where
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
