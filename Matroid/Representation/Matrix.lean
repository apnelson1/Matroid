import Matroid.Representation.StandardRep
import Mathlib.LinearAlgebra.Matrix.Rank

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
  subset_ground : B ⊆ M.E
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

theorem linearIndepOn_image_injOn_iff' {ι ι' R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {e : ι → ι'} {f : ι' → M} {g : ι → M} {s : Set ι} (he : InjOn e s)
    (hg : ∀ ⦃x⦄, x ∈ s → g x = f (e x)) :
    LinearIndepOn R g s ↔ LinearIndepOn R f (e '' s) := by
  rw [ ← linearIndepOn_image_injOn_iff he, linearIndepOn_congr hg]
  rfl

-- lemma Equiv.Set.image_subtype_symm_apply (t : Set α) (s : Set t) (x : α) (hx : x ∈ Subtype.val '' s):
--     (Equiv.Set.image _ s Subtype.val_injective).symm ⟨x, sorry⟩ = ⟨⟨x, sorry⟩, sorry⟩ := by
--   rfl

@[simps?] def foo {s t : Set α} (hst : s ⊆ t) : s ≃ t ↓∩ s where
  toFun x := ⟨⟨x, hst (by simp)⟩, by simp⟩
  invFun x := ⟨x.1.1, by aesop⟩
  left_inv x := rfl
  right_inv x := rfl

lemma aux' {B : Set α} [Fintype B] [DecidableEq B] (P : Matrix B α 𝔽) (X : Set B)
    (hB : ∀ i : B, P.col i = Pi.single i 1) (Y : Set α) (hdj : Disjoint ((↑) '' X) Y) :
    LinearIndepOn 𝔽 P.col (((↑) '' X) ∪ Y) ↔
    LinearIndependent 𝔽 (P.submatrix (fun i : ↥Xᶜ ↦ i.1) (fun i : Y ↦ i.1)).col := by
  classical
  let c := (↑) '' X ∪ Y
  -- have := foo (t := c) subset_union_left
  let Q := P.submatrix id (fun j : c ↦ j.1)
  change LinearIndependent 𝔽 Q.col ↔ LinearIndependent 𝔽
    (Q.submatrix (fun i : ↥Xᶜ ↦ i.1) (fun j : Y ↦ ⟨j, .inr j.2⟩)).col


  let Q := P.submatrix id (fun j : ↥(((↑) '' X) ∪ Y) ↦ j.1)
  have hQB : ∀ i j {h'}, ⟨j.1, h'⟩ ∈ X → Q i j = if i.1 = j.1 then 1 else 0 := by
    rintro i ⟨j, (hj | hj)⟩ h' hjX
    · simp only [submatrix_apply, id_eq, Q]
      rw [← P.col_apply, hB ⟨j, h'⟩, Pi.single_apply]
      simp_rw [← Subtype.val_inj]
    exact hdj.notMem_of_mem_left (a := j) (by simpa [h'] using hjX) hj |>.elim




  change LinearIndependent 𝔽 Q.colFun ↔ LinearIndependent 𝔽
    (Q.submatrix (fun i : ↥Xᶜ ↦ i.1) (fun j : Y ↦ ⟨j, .inr j.2⟩)).colFun
  have h0 : Q.block Xᶜ ( _ ↓∩ ((↑) '' X)) = 0 := by aesop
  -- have := foo (t := c) subset_union_left
  set e : (c ↓∩ (↑) '' X) ≃ X := (foo (t := c) subset_union_left).symm
      -- (Equiv.Set.image  _ _ Subtype.val_injective).trans
      -- <| (Equiv.Set.ofEq (by aesop)).trans (Equiv.Set.image _ _ Subtype.val_injective).symm with he

  set C := (Q.block Xᶜᶜ (((↑) '' X ∪ Y) ↓∩ ↑X)) with hC

  have h1 : C.submatrix (Equiv.Set.ofEq (compl_compl X).symm) e.symm = 1 := by
    -- simp [← Matrix.ext_iff, e]
    ext i j

    simp [C, e]

    rw [hQB]
    · sorry
    simp [e]

    rw [hej]
    simp only [Equiv.coe_trans, submatrix_apply, Equiv.Set.ofEq_apply, Function.comp_apply,
      Equiv.Set.image_apply, block_apply, one_apply, Subtype.mk.injEq, C]

    -- rw [hQB]
    -- -- rw [hQB _ _ (by aesop)]
    -- -- simp +contextual [eq_ite_iff]

    -- -- rw [hQB _ _ sorry]
    -- aesop
    -- convert rfl

    -- simp [e, ← Subtype.val_inj]



  have htop : span 𝔽 (range (1 : Matrix X X 𝔽).colFun) = ⊤ := sorry
  rw [span_col_eq_top_iff_linearIndependent_rows, ← h1,
    linearIndependent_rows_submatrix_iff_of_surjective _ _ hsurj,
    ← span_col_eq_top_iff_linearIndependent_rows] at htop


  nth_rw 1 [Q.eq_fromBlocks_block_reindex Xᶜ ( _ ↓∩ ((↑) '' X)), reindex_apply,
    linearIndependent_cols_iff_submatrix, h0, ← hC,
    fromBlocks_zero₁₁_linearIndependent_cols_iff_of_span htop,
    ← linearIndependent_cols_submatrix_iff_of_surjective _ _ hsurj]


  -- rw [P.eq_fromBlocks_block_reindex Xᶜ Y]
  -- simp only [reindex_apply, submatrix_submatrix]
  -- rw [fromBlocks_]


lemma aux {B : Set α} [Fintype B] [DecidableEq B] (P : Matrix B α 𝔽) (X : Set B)
    (hB : ∀ i : B, Pᵀ i = Pi.single i 1) (Y : Set α) (hdj : Disjoint ((↑) '' X) Y) :
    LinearIndepOn 𝔽 Pᵀ (((↑) '' X) ∪ Y) ↔
    LinearIndependent 𝔽 (P.submatrix (fun i : ↥Xᶜ ↦ i.1) (fun i : Y ↦ i.1))ᵀ := by
  classical
  rw [LinearIndepOn]
  -- have hPX : P.submatrix (fun i : X ↦ i.1) (fun i : X ↦ i.1) = 1 := sorry
  convert fromBlocks_zero₁₁_cols_linearIndependent_iff_of_span (R := 𝔽) (m₁ := ↥Xᶜ) (m₂ := X)
    (n₁ := X) (n₂ := Y) (B := P.submatrix (↑) (↑)) (C := P.submatrix (↑) (↑))
      (D := P.submatrix (↑) (↑)) sorry
  have ha1 (a : ↥Xᶜ) (i : α) (hiB : i ∈ B) : 0 = P a.1 i ↔ (a.1.1 ≠ i) := sorry
  -- have ha2 (a : ↥X) (i : α) (hiB : i ∈ B) : 0 = P a.1 i ↔ (a.1.1 ≠ i) := sorry
  · let e : ↥((↑X) ∪ Y) ≃ X ⊕ Y :=

      (Equiv.Set.union hdj).trans <|
        Equiv.sumCongr ((Equiv.Set.image _ X Subtype.val_injective).symm) (Equiv.refl _)


    set ψ : (B → 𝔽) →ₗ[𝔽] ((↥Xᶜ ⊕ X) → 𝔽) := LinearMap.funLeft _ _ (Sum.elim (↑) (↑))
    have hinj : InjOn ⇑ψ ↑(span 𝔽 (range fun (x : ↥(↑X ∪ Y)) ↦ Pᵀ ↑x)) := by
      refine fun x _ y _ hxy ↦ funext fun ⟨i, hi⟩ ↦ ?_
      simp only [funext_iff, LinearMap.funLeft_apply, Sum.forall, Sum.elim_inl, Subtype.forall,
        mem_compl_iff, Sum.elim_inr, ← forall_and, ← or_imp, em', forall_const, ψ] at hxy
      exact hxy i hi

    rw [← linearIndependent_equiv e, ← ψ.linearIndependent_iff_of_injOn hinj]
    convert Iff.rfl

    rw [funext_iff]
    rintro ⟨i, (⟨⟨i, hiB⟩, hi, rfl⟩ | hi)⟩
    . simp only [Equiv.coe_trans, Function.comp_apply, Equiv.sumCongr_apply, Equiv.coe_refl,
      funext_iff, transpose_apply, LinearMap.funLeft_apply, Sum.forall, Sum.elim_inl,
      Sum.elim_inr, e, ψ]
      rw [Equiv.Set.union_apply_left]
      · simp only [Sum.map_inl, fromBlocks_apply₁₁, zero_apply, fromBlocks_apply₂₁,
          submatrix_apply, ψ, e]
        refine ⟨fun ⟨a, ha⟩ ↦ ?_, fun j ↦ ?_⟩
        · rw [ha1 _ _ hiB]
          rintro rfl
          contradiction
        have hwin := Equiv.Set.image_symm_apply (α := B) (f := Subtype.val) (s := X)
          Subtype.val_injective ⟨i, hiB⟩ (by simpa [hiB])
        rw [← Subtype.val_inj, ← Subtype.val_inj] at hwin
        rw [hwin]
    simp only [Equiv.coe_trans, Function.comp_apply, Equiv.sumCongr_apply, Equiv.coe_refl,
      funext_iff, transpose_apply, LinearMap.funLeft_apply, Sum.forall, Sum.elim_inl,
      Sum.elim_inr, e, ψ]
    refine ⟨fun a ↦ ?_, fun a ↦ ?_⟩ <;>
    · rw [Equiv.Set.union_apply_right]
      · simp
      simpa

noncomputable def Rep.IsStandard.toReducedRep [Fintype B] (v : M.Rep 𝔽 (B → 𝔽)) (hB : B ⊆ M.E)
    (hv : v.IsStandard') : M.ReducedRep 𝔽 B where
  toMatrix := .of fun e f ↦ v f.1 e
  subset_ground := hB
  forall_indep_iff' := by
    classical
    intro X Y
    set P := (Matrix.of v)ᵀ
    simp_rw [v.indep_iff, show v = fun i j ↦ Pᵀ i j from rfl]
    rw [aux _ _ hv.apply_eq_single _ (by simp +contextual [disjoint_left])]
    · apply linearIndependent_equiv' (Equiv.Set.image _ Y Subtype.val_injective).symm
      ext i j
      obtain ⟨_, ⟨i, hi, rfl⟩⟩ := i
      simp


noncomputable def ReducedRep.toRep [DecidablePred (· ∈ M.E)] [DecidablePred (· ∈ B)] [Fintype B]
    [DecidableEq B] (P : M.ReducedRep 𝔽 B) : M.Rep 𝔽 (B → 𝔽) :=  Rep.ofSubtypeFun
  (fun x ↦ if hx : x.1 ∈ B then (Pi.single ⟨x, hx⟩ 1) else (P.1 · ⟨x, x.2, hx⟩))
  (by
    set fn := (fun x : M.E ↦ if hx : x.1 ∈ B then (Pi.single ⟨x, hx⟩ 1) else (P.1 · ⟨x, x.2, hx⟩))
    intro I
    set X := (Set.inclusion P.subset_ground) ⁻¹' I with hX
    set Y := (Set.inclusion (show M.E \ B ⊆ M.E from diff_subset)) ⁻¹' I with hY
    have hIXY : Subtype.val '' I = Subtype.val '' X ∪ Subtype.val '' Y := by
      simp +contextual [hX, hY, Set.ext_iff, em, or_imp, iff_def,
        show ∀ x ∈ B, x ∈ M.E from fun x hx ↦ P.subset_ground hx]
    set fn' := fun x ↦ if hx : x ∈ M.E then fn ⟨x, hx⟩ else 0
    rw [hIXY, P.forall_indep_iff', linearIndepOn_image_injOn_iff' Subtype.val_injective.injOn
      (f := fn') (by simp [fn']), hIXY, iff_comm]
    have hsing : ∀ (i : ↑B), fn' ↑i = Pi.single i 1 :=
      fun ⟨i, hi⟩ ↦ by simp [funext_iff, fn', dite_apply, P.subset_ground hi, fn, hi]
    convert aux (.of fn')ᵀ X hsing (Subtype.val '' Y) (by simp +contextual [disjoint_left]) using 1
    rw [linearIndependent_equiv' (Equiv.Set.image _ _ Subtype.val_injective)]
    ext ⟨⟨i,hi'⟩, hi⟩ j
    simp [fn', fn, dite_apply, hi'.2, hi'.1] )


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



-- noncomputable def Rep.toReducedRep (v : M.Rep 𝔽 W) (hB : M.IsBase B) : M.ReducedRep 𝔽 B where
--   toMatrix := .of fun e f ↦ v.standardRep hB f.1 e
--   forall_indep_iff' := by
--     intro X Y
--     rw [v.indep_iff, linearIndepOn_union_iff_quotient, ← v.indep_iff,
--       and_iff_right (hB.indep.subset (by simp))]
--     simp only [v.indep_iff, linearIndepOn_iff, transpose_submatrix, linearIndependent_iff]
--     refine ⟨fun h c hc0 ↦ ?_, fun h ↦ ?_⟩
--     · simp [Finsupp.linearCombination, Finsupp.sum, Matrix.of] at hc0
--       sorry
--     sorry
--     sorry
--     -- rw [v.indep_iff, linearIndepOn_union_iff_quotient, ← v.indep_iff,
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
