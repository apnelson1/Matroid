import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.Dual
import Mathlib.LinearAlgebra.FiniteDimensional
import Matroid.ForMathlib.Representation
import Matroid.ForMathlib.LinearAlgebra.LinearIndependent
import Matroid.ForMathlib.LinearAlgebra.StdBasis

open Set Function Submodule BigOperators

/- Given `A : Matrix m n R` and `s : Set m`, We write `s.restrict A` for the function
  function assigning each `i : s` to its row in `n → R`.

  And similarly, given `t : Set n`, write `t.restrict Aᵀ` for the function assigning
  each `j : t` to its column.

  These are spellings of `A.submatrix ((↑) : s → m) id` and `A.submatrix id ((↑) : t → n)`
  respectively, but are preferable since they are shorter, and show the sets `s,t`
  explicitly in the infoview.
  -/
namespace Matrix


variable {l m n o α : Type _} {A B : Matrix m n R} {s : Set m} {t : Set n}

theorem restrict_eq_submatrix (A : Matrix m n α) (s : Set m) :
  s.restrict A = A.submatrix ((↑) : s → m) id := rfl

theorem transpose_restrict_eq_submatrix {m n R : Type _} (A : Matrix m n R) (t : Set m) :
  (t.restrict A)ᵀ = (Aᵀ.submatrix id ((↑) : t → m)) := rfl

theorem image_eq_range_submatrix (A : Matrix m n α) (s : Set m) :
    A '' s = range (A.submatrix ((↑) : s → m) id) := by
  aesop

theorem range_col_submatrix (A : Matrix m n α) (c_reindex : l → n) :
    range (A.submatrix id c_reindex) = (· ∘ c_reindex) '' range A := by
  aesop

@[simp] theorem range_row_submatrix {l m n α : Type _} (A : Matrix m n α) (r_reindex : l → m) :
    range (A.submatrix r_reindex id) = A '' range (r_reindex) := by
  aesop

@[simp] theorem range_restrict {m n R : Type _} (A : Matrix m n R) (s : Set m) :
    range (s.restrict A) = A '' s := by
  simp [restrict_eq_submatrix]

@[simp] theorem range_submatrix {l m n o R : Type _} [CommRing R] (A : Matrix m n R)
    (r_reindex : l → m) (c_reindex : o → n) :
    range (A.submatrix r_reindex c_reindex) =
      (LinearMap.funLeft R _ c_reindex) '' (A '' range (r_reindex)) := by
  aesop

section Fintype

@[simp] theorem vecMulLinear_apply' {R m n : Type _} [Semiring R] [Fintype m]
    (M : Matrix m n R) (x : m → R) : M.vecMulLinear x = M.vecMul x := rfl

theorem range_vecMulLinear {R m n : Type _} [CommSemiring R] [Fintype m] (M : Matrix m n R) :
    LinearMap.range M.vecMulLinear = span R (range M) := by
  convert range_mulVecLin Mᵀ; ext x; simp [← vecMul_transpose]

end Fintype

section ColBasis

variable {m n R : Type _} {s : Set m} {t : Set n} {A B : Matrix m n R}

section Ring

variable [Ring R]

/-- `A.RowBasis s` means that the rows `A_i : i ∈ s` are a basis for the row space of `A` -/
def RowBasis (A : Matrix m n R) (s : Set m) : Prop :=
    LinearIndependent R (restrict s A) ∧ span R (A '' s) = span R (range A)

/-- A `RowBasis` as a `Basis` for the row space -/
noncomputable def RowBasis.basis (h : A.RowBasis s) : Basis s R (span R (range A)) :=
   (Basis.span h.1).map <| LinearEquiv.ofEq _ _ (by simp [h.2])

@[simp] theorem RowBasis.basis_apply (h : A.RowBasis s) (i : s) : h.basis i = A i := by
  ext; simp [Matrix.RowBasis.basis, Basis.span_apply]

theorem RowBasis.linearIndependent (h : A.RowBasis s) : LinearIndependent R (s.restrict A) :=
  h.1

theorem RowBasis.span_eq (h : A.RowBasis s) :
  span R (A '' s) = span R (range A) := h.2

/-- `A.ColBasis t` means that the columns `A_i : i ∈ t` are a basis for the column space of `A` -/
def ColBasis (A : Matrix m n R) (t : Set n) := Aᵀ.RowBasis t

/-- A `ColBasis` as a `Basis` for the column space -/
noncomputable def ColBasis.basis (h : A.ColBasis t) : Basis t R (span R (range Aᵀ)) :=
  RowBasis.basis h

@[simp] theorem ColBasis.basis_apply (h : A.ColBasis t) (j : t) : h.basis j = Aᵀ j := by
  ext; simp [ColBasis.basis]

theorem ColBasis.linearIndependent (h : A.ColBasis t) : LinearIndependent R (t.restrict Aᵀ) :=
  h.1

theorem ColBasis.span_eq (h : A.ColBasis t) : span R (Aᵀ '' t) = span R (range Aᵀ) :=
  h.2

@[simp] theorem rowBasis_transpose : Aᵀ.RowBasis t ↔ A.ColBasis t := Iff.rfl
@[simp] theorem colBasis_transpose : Aᵀ.ColBasis s ↔ A.RowBasis s := Iff.rfl


theorem rows_linearIndependent_iff [Fintype m] :
    LinearIndependent R A ↔ LinearMap.ker A.vecMulLinear = ⊥ := by
  simp only [Fintype.linearIndependent_iff, Submodule.eq_bot_iff, LinearMap.mem_ker,
    vecMulLinear_apply', vecMul, dotProduct]
  refine ⟨fun h x h0 ↦ funext fun i ↦ h _ (by rw [←h0]; ext; simp) _, fun h x h0 i ↦ ?_⟩
  rw [h x]; rfl
  rw [←h0]; ext; simp

theorem cols_linearIndependent_iff {R : Type _} [CommRing R] {A : Matrix m n R} [Fintype n] :
    LinearIndependent R Aᵀ ↔ LinearMap.ker A.mulVecLin = ⊥ := by
  rw [rows_linearIndependent_iff]
  convert Iff.rfl; ext; simp [← mulVec_transpose]

end Ring

section DivisionRing

variable [DivisionRing R]

theorem RowBasis.finite [Fintype n] (hs : A.RowBasis s) : s.Finite := by
  have := hs.linearIndependent.finite_index; exact toFinite s

theorem ColBasis.finite [Fintype m] (h : A.ColBasis t) : t.Finite :=
  RowBasis.finite h

theorem exists_rowBasis_superset (A : Matrix m n R) {s₀ : Set m}
    (hs₀ : LinearIndependent R (s₀.restrict A)) : ∃ s, A.RowBasis s ∧ s₀ ⊆ s := by
  obtain ⟨s, hss, -, h1,h2⟩ := exists_linearIndependent_extension' hs₀ (subset_univ _)
  refine ⟨s, ⟨h2, le_antisymm (span_mono (image_subset_range _ _)) ?_⟩, hss⟩
  rw [image_univ] at h1
  exact span_le.mpr h1

theorem exists_rowBasis (A : Matrix m n R) : ∃ s, A.RowBasis s :=
  let ⟨s, hs, _⟩ := exists_rowBasis_superset A (s₀ := ∅) linearIndependent_empty_type
  ⟨s,hs⟩

theorem rowBasis_iff_maximal_linearIndependent : A.RowBasis s ↔
    s ∈ maximals (· ⊆ ·) {b : Set m | LinearIndependent R (b.restrict A)} := by
  rw [mem_maximals_setOf_iff, RowBasis, and_congr_right_iff]
  refine fun hli ↦ ⟨fun h y hy hsy ↦ hsy.antisymm fun e he ↦ by_contra fun hes ↦ ?_,
      fun h ↦ le_antisymm (span_mono ?_) ?_⟩
  · have hse : LinearIndependent R (A.submatrix ((↑) : ↑(insert e s) → m) id)
    · apply hy.comp (inclusion (insert_subset he hsy)) <| inclusion_injective _
    apply ((linearIndependent_insert' hes).1 hse).2
    have hsp := h.symm.le.subset <| (subset_span <| mem_range_self _   : A e ∈ _)
    rwa [SetLike.mem_coe] at hsp
  · rintro _ ⟨x, -, rfl⟩; exact ⟨x, rfl⟩
  rintro x hx
  obtain ⟨k, c, f, g, rfl⟩ := mem_span_set'.1 hx
  apply sum_smul_mem
  rintro i -
  obtain ⟨_,⟨j,hj,rfl⟩⟩ := f i
  simp only
  obtain (hjs | hjs) := em (j ∈ s)
  · apply subset_span; exact ⟨j,hjs,rfl⟩
  by_contra hsp
  have heq := (h <| (linearIndependent_insert' hjs).2 ⟨hli, fun hsp' ↦ hsp ?_⟩) (subset_insert _ _)
  · exact hjs (heq.symm.subset (mem_insert _ _))
  contradiction

theorem colBasis_iff_maximal_linearIndependent : A.ColBasis t ↔
    t ∈ maximals (· ⊆ ·) {b : Set n | LinearIndependent R (b.restrict Aᵀ)}  := by
  rw [ColBasis, rowBasis_iff_maximal_linearIndependent]

theorem exists_colBasis_superset (A : Matrix m n R) {t₀ : Set n}
    (ht₀ : LinearIndependent R (t₀.restrict Aᵀ)) : ∃ t, A.ColBasis t ∧ t₀ ⊆ t :=
  Aᵀ.exists_rowBasis_superset ht₀

theorem exists_colBasis (A : Matrix m n R) : ∃ t, A.ColBasis t :=
  Aᵀ.exists_rowBasis

end DivisionRing

section Field

variable [Field R]

theorem subset_rows_notLinearIndependent_iff [Fintype m] [Field R] :
    ¬ LinearIndependent R (s.restrict A) ↔ ∃ c, A.vecMul c = 0 ∧ c ≠ 0 ∧ support c ⊆ s := by
  simp only [Fintype.subtype_notLinearIndependent_iff, ne_eq, vecMul, dotProduct,
    support_subset_iff, not_imp_comm]
  refine ⟨fun ⟨c,h,⟨i, _, hci⟩,h'⟩ ↦
    ⟨c, by convert h; simp, by rintro rfl; exact hci rfl, h'⟩,
    fun ⟨c,h,hi,h'⟩ ↦ ⟨c, by convert h; simp, ?_, h'⟩⟩
  by_contra hc; push_neg at hc
  exact hi (funext fun i ↦ (em (i ∈ s)).elim (hc i) (h' i))

theorem subset_cols_notLinearIndependent_iff [Fintype n] :
    ¬ LinearIndependent R (t.restrict Aᵀ) ↔ ∃ c, A.mulVec c = 0 ∧ c ≠ 0 ∧ support c ⊆ t := by
  simp_rw [subset_rows_notLinearIndependent_iff, vecMul_transpose]

theorem toLin'_transpose [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] :
    toLin' Aᵀ = (Module.piEquiv n R R).symm.comp
      (A.toLin'.dualMap.comp (Module.piEquiv m R R).toLinearMap) := by
  ext i j; simp [Module.piEquiv_apply_apply, ←Pi.single_mul_right_apply (A · j)]

theorem toLin'_dualMap [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] :
    A.toLin'.dualMap =
      ((Module.piEquiv n R R).comp (toLin' Aᵀ)).comp (Module.piEquiv m R R).symm.toLinearMap := by
  rw [toLin'_transpose]; aesop

/-- TODO : remove the assumption that `m` is finite -/
theorem span_rows_eq_top_iff_linearIndependent_cols [Fintype m] [Fintype n] :
    span R (range A) = ⊤ ↔ LinearIndependent R Aᵀ := by
  classical
  convert (LinearMap.dualMap_surjective_iff (f := toLin' A))
  · rw [←range_vecMulLinear, LinearMap.range_eq_top, toLin'_dualMap]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_bijective,
      EquivLike.surjective_comp, EquivLike.comp_surjective]
    convert Iff.rfl; ext i j; simp
  rw [rows_linearIndependent_iff, LinearMap.ker_eq_bot]; convert Iff.rfl; ext; simp

/-- TODO : remove the assumption that `n` is finite -/
theorem span_cols_eq_top_iff_linearIndependent_rows [Fintype m] [Fintype n] :
    span R (range Aᵀ) = ⊤ ↔ LinearIndependent R A := by
  rw [span_rows_eq_top_iff_linearIndependent_cols, transpose_transpose]

theorem ColBasis.rows_linearIndependent [Fintype m] [Fintype n] (ht : A.ColBasis t)
    (hA : LinearIndependent R A) : LinearIndependent R (t.restrict Aᵀ)ᵀ  := by
  have _ := t.toFinite.fintype
  rw [←span_cols_eq_top_iff_linearIndependent_rows, Submodule.eq_top_iff']
  rw [←span_cols_eq_top_iff_linearIndependent_rows] at hA
  exact fun x ↦ by simp [hA ▸ ht.span_eq]

theorem RowBasis.cols_linearIndependent [Fintype m] [Fintype n] (hs : A.RowBasis s)
    (hA : LinearIndependent R Aᵀ) : LinearIndependent R (s.restrict A)ᵀ :=
  (colBasis_transpose.2 hs).rows_linearIndependent hA

/-- Matrices with the same column space have the same row bases -/
theorem rowBases_eq_of_colSpaces_eq [Fintype m] [Fintype n]
    (h : span R (range Aᵀ) = span R (range Bᵀ)) :  A.RowBasis = B.RowBasis := by
  ext s
  simp_rw [rowBasis_iff_maximal_linearIndependent]
  convert Iff.rfl using 4
  ext s'
  have _ := s'.toFinite.fintype
  simp [←span_cols_eq_top_iff_linearIndependent_rows, transpose_restrict_eq_submatrix,
    range_submatrix, h]

/-- Matrices with the same row space have the same column bases -/
theorem colBases_eq_of_rowSpaces_eq [Fintype m] [Fintype n]
    (h : span R (range A) = span R (range B)) : A.ColBasis = B.ColBasis := by
  ext
  rw [←rowBasis_transpose, ←rowBasis_transpose, rowBases_eq_of_colSpaces_eq]
  rwa [transpose_transpose, transpose_transpose]

/-- If an `m × n` matrix `A` with entries in `R` has linearly independent rows,
    a column basis for `A` gives a basis for `m → R`. -/
noncomputable def ColBasis.basis' [Fintype m] [Fintype n] (ht : A.ColBasis t)
  (hA : LinearIndependent R A) : Basis t R (m → R) :=
  have _ := t.toFinite.fintype
  ( Basis.span ht.linearIndependent ).map <| LinearEquiv.ofTop _ <| eq_top_iff'.2 fun x ↦
    ( by simp [ht.span_eq, span_cols_eq_top_iff_linearIndependent_rows.2 hA] )

@[simp] theorem ColBasis.basis'_apply [Fintype m] [Fintype n] (ht : A.ColBasis t)
    (hA : LinearIndependent R A) (j : t) : ht.basis' hA j = (A · j) := by
  ext; simp [basis', Basis.span_apply]

noncomputable def RowBasis.basis' [Fintype m] [Fintype n] (hs : A.RowBasis s)
    (hA : LinearIndependent R Aᵀ) : Basis s R (n → R) :=
  (colBasis_transpose.2 hs).basis' hA

@[simp] theorem RowBasis.basis'_apply [Fintype m] [Fintype n] (hs : A.RowBasis s)
    (hA : LinearIndependent R Aᵀ) (i : s) : hs.basis' hA i = A i := by
  ext; simp [basis']

end Field

end ColBasis

end Matrix





-- theorem foo [Fintype m] [Fintype n] (hA : LinearIndependent R A)
--     (hAB : LinearMap.ker B.mulVecLin ≤ span R (range A)) (ht : A.ColBasis tᶜ) :
--     LinearIndependent R (Bᵀ.submatrix ((↑) : t → n) id) := by
--   have _ := (tᶜ).toFinite.fintype
--   by_contra hdep
--   simp_rw [subset_cols_notLinearIndependent_iff] at hdep
--   obtain ⟨c, hc0, hcn, hcs⟩ := hdep
--   have hcsp : c ∈ span R (range A) := hAB hc0
--   rw [←range_vecMulLinear, LinearMap.mem_range] at hcsp
--   obtain ⟨d, rfl⟩ := hcsp
--   have hker : d ∈ LinearMap.ker (vecMulLinear (A.submatrix id ((↑) : ↑tᶜ → n)))
--   · ext j
--     simp only [vecMulLinear_apply, Pi.zero_apply]
--     convert congr_fun (submatrix_vecMul_equiv A d (Equiv.refl _) _) j
--     have hj' : j.val ∉ support (A.vecMulLinear d) := not_mem_subset hcs j.prop
--     simp only [vecMulLinear_apply', mem_support, ne_eq, not_not] at hj'
--     simp [hj']
--   rw [rows_linearIndependent_iff.1 <| ht.rows_linearIndependent hA, mem_bot] at hker
--   subst hker
--   exact hcn (by simp)

-- theorem foo' [Fintype m] [Fintype n] (hA : LinearIndependent R A) (hB : LinearIndependent R B)
--     (hAB : LinearMap.ker B.mulVecLin = span R (range A)) : A.ColBasis t ↔ B.ColBasis tᶜ := by
--   sorry
