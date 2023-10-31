import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.Dual
import Mathlib.LinearAlgebra.FiniteDimensional
import Matroid.ForMathlib.Representation
import Matroid.ForMathlib.LinearAlgebra.LinearIndependent
import Matroid.ForMathlib.LinearAlgebra.StdBasis

open Set Function Submodule BigOperators FiniteDimensional

namespace Matrix

variable {l m n o α : Type _} {A B : Matrix m n R} {s : Set m} {t : Set n}

section Fintype

@[simp] theorem vecMulLinear_apply' {R m n : Type _} [Semiring R] [Fintype m]
    (M : Matrix m n R) (x : m → R) : M.vecMulLinear x = M.vecMul x := rfl

theorem range_vecMulLinear {R m n : Type _} [CommSemiring R] [Fintype m] (M : Matrix m n R) :
    LinearMap.range M.vecMulLinear = span R (range M) := by
  convert range_mulVecLin Mᵀ; ext x; simp [← vecMul_transpose]

@[simp] theorem vecMulLinear_transpose {R m n : Type _} [CommSemiring R] [Fintype n]
    (M : Matrix m n R) : Mᵀ.vecMulLinear = M.mulVecLin := by
  ext x; simp [vecMul_transpose]

@[simp] theorem mulVecLin_transpose {R m n : Type _} [CommSemiring R] [Fintype m]
    (M : Matrix m n R) : Mᵀ.mulVecLin = M.vecMulLinear := by
  rw [←vecMulLinear_transpose, transpose_transpose]

end Fintype

section spaces

@[pp_dot] def rowFun (A : Matrix m n R) : m → (n → R) := A

@[pp_dot] def colFun (A : Matrix m n R) : n → (m → R) := Aᵀ

@[simp] theorem rowFun_transpose (A : Matrix m n R) : Aᵀ.rowFun = A.colFun := rfl

@[simp] theorem colFun_transpose (A : Matrix m n R) : Aᵀ.colFun = A.rowFun := rfl

@[simp] theorem rowFun_apply (A : Matrix m n r) (i : m) : A.rowFun i = A i := rfl

@[simp] theorem colFun_apply (A : Matrix m n r) (j : n) : A.colFun j = Aᵀ j := rfl

section semiring

variable [Semiring R]

@[pp_dot] def rowSpace (A : Matrix m n R) : Submodule R (n → R) := span R (range A.rowFun)

@[pp_dot] def colSpace (A : Matrix m n R) : Submodule R (m → R) := Aᵀ.rowSpace

@[simp] theorem rowSpace_transpose (A : Matrix m n R) : Aᵀ.rowSpace = A.colSpace := rfl

@[simp] theorem colSpace_transpose (A : Matrix m n R) : Aᵀ.colSpace = A.rowSpace := rfl

@[simp] theorem rowSpace_eq_span (A : Matrix m n R) : span R (range A.rowFun) = A.rowSpace := rfl

@[simp] theorem colSpace_eq_span (A : Matrix m n R) : span R (range A.colFun) = A.colSpace := rfl

end semiring

section commring

variable [CommRing R]

theorem rowSpace_eq_lin_range [Fintype m] (A : Matrix m n R) :
    A.rowSpace = LinearMap.range A.vecMulLinear :=
  A.range_vecMulLinear.symm

theorem colSpace_eq_lin_range [Fintype n] (A : Matrix m n R) :
    A.colSpace = LinearMap.range A.mulVecLin :=
  A.range_mulVecLin.symm

theorem mem_rowSpace_iff [Fintype m] : x ∈ A.rowSpace ↔ ∃ y, x = A.vecMul y := by
  simp [rowSpace_eq_lin_range, eq_comm]

theorem mem_colSpace_iff [Fintype n] : x ∈ A.colSpace ↔ ∃ y, x = A.mulVec y := by
  rw [←rowSpace_transpose, mem_rowSpace_iff]; simp [vecMul_transpose]

theorem vecMul_mem_rowSpace [Fintype m] (A : Matrix m n R) (c : m → R) :
    A.vecMul c ∈ A.rowSpace := by
  rw [mem_rowSpace_iff]; exact ⟨_, rfl⟩

theorem mulVec_mem_colSpace [Fintype n] (A : Matrix m n R) (c : n → R) :
    A.mulVec c ∈ A.colSpace := by
  rw [mem_colSpace_iff]; exact ⟨_, rfl⟩

end commring

end spaces

@[pp_dot] def rowSubmatrix (A : Matrix m n α) (s : Set m) : Matrix s n α :=
  A.submatrix ((↑) : s → m) id

@[pp_dot] def colSubmatrix (A : Matrix m n α) (t : Set n) : Matrix m t α :=
  A.submatrix id ((↑) : t → n)

@[simp] theorem rowSubmatrix_apply (i : s) : (A.rowSubmatrix s) i = A i := rfl

@[simp] theorem colSubmatrix_apply (i : m) (j : t) : (A.colSubmatrix t) i j = A i j := rfl

@[simp] theorem rowSubmatrix_transpose (A : Matrix m n α) (s : Set m) :
    (A.rowSubmatrix s)ᵀ = Aᵀ.colSubmatrix s := rfl

@[simp] theorem colSubmatrix_transpose (A : Matrix m n α) (t : Set n) :
    (A.colSubmatrix t)ᵀ = Aᵀ.rowSubmatrix t := rfl

theorem rowFun_rowSubmatrix_eq (A : Matrix m n α) (s : Set m) :
  rowFun (rowSubmatrix A s) = s.restrict A.rowFun := rfl

theorem colFun_colSubmatrix_eq (A : Matrix m n α) (t : Set n) :
  colFun (colSubmatrix A t) = t.restrict A.colFun := rfl

theorem restrict_eq_submatrix (A : Matrix m n α) (s : Set m) :
  s.restrict A = (A.rowSubmatrix s).rowFun := rfl

theorem transpose_restrict_eq_submatrix (A : Matrix m n R) (t : Set m) :
  (t.restrict A)ᵀ = Aᵀ.colSubmatrix t := rfl

-- theorem transpose_transpose_restrict_eq_submatrix (A : Matrix m n R) (t : Set n) :
--   (t.restrict Aᵀ)ᵀ = (A.submatrix id ((↑) : t → n)) := rfl

theorem image_eq_range_submatrix (A : Matrix m n α) (s : Set m) :
    A '' s = range (A.rowSubmatrix s).rowFun := by
  aesop

-- theorem range_col_submatrix (A : Matrix m n α) (c_reindex : l → n) :
--     range (A.submatrix id c_reindex) = (· ∘ c_reindex) '' range A := by
--   aesop

-- @[simp] theorem range_row_submatrix {l m n α : Type _} (A : Matrix m n α) (r_reindex : l → m) :
--     range (A.submatrix r_reindex id) = A '' range (r_reindex) := by
--   aesop

-- @[simp] theorem range_restrict {m n R : Type _} (A : Matrix m n R) (s : Set m) :
--     range (s.restrict A) = A '' s := by
--   simp [restrict_eq_submatrix]

-- @[simp] theorem range_submatrix {l m n o R : Type _} [CommRing R] (A : Matrix m n R)
--     (r_reindex : l → m) (c_reindex : o → n) :
--     range (A.submatrix r_reindex c_reindex) =
--       (LinearMap.funLeft R _ c_reindex) '' (A '' range (r_reindex)) := by
--   aesop


@[simp] theorem rowFun_colSubmatrix_eq [CommRing R] (A : Matrix m n R) (t : Set n) :
    rowFun (colSubmatrix A t) = LinearMap.funLeft R R (↑) ∘ A.rowFun := by
  ext; simp

@[simp] theorem colFun_rowSubmatrix_eq [CommRing R] (A : Matrix m n R) (s : Set m) :
    colFun (rowSubmatrix A s) = LinearMap.funLeft R R (↑) ∘ A.colFun := by
  ext; simp

theorem dotProduct_eq_zero_of_mem_span [Fintype m] [CommSemiring R] {x y : m → R} {s : Set (m → R)}
    (hy : y ∈ span R s) (h : ∀ z ∈ s, x ⬝ᵥ z = 0) : x ⬝ᵥ y = 0 := by
  obtain ⟨c, y,z, rfl⟩ := mem_span_set'.1 hy
  simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_eq_zero]
  rintro w -
  obtain ⟨i, hi⟩ := z w
  simp_rw [mul_comm (y w), ←mul_assoc, ←Finset.sum_mul]
  convert zero_mul _
  rw [←h i hi, dotProduct]

variable {m n R : Type _} {s : Set m} {t : Set n} {A B : Matrix m n R}

section Ring

/-- `A.RowBasis s` means that the rows `A_i : i ∈ s` are a basis for the row space of `A` -/
def RowBasis {R : Type _} [Semiring R] (A : Matrix m n R) (s : Set m) : Prop :=
    LinearIndependent R (A.rowSubmatrix s).rowFun ∧ (A.rowSubmatrix s).rowSpace = A.rowSpace

/-- `A.ColBasis t` means that the columns `A_i : i ∈ t` are a basis for the column space of `A` -/
def ColBasis {R : Type _} [Semiring R] (A : Matrix m n R) (t : Set n) := Aᵀ.RowBasis t

variable [Ring R]

/-- A `RowBasis` as a `Basis` for the row space -/
noncomputable def RowBasis.basis (h : A.RowBasis s) : Basis s R A.rowSpace :=
   (Basis.span h.1).map <| LinearEquiv.ofEq _ _ h.2

@[simp] theorem RowBasis.basis_apply (h : A.RowBasis s) (i : s) : h.basis i = A i := by
  ext; simp only [basis, Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.span_apply]; rfl

theorem RowBasis.linearIndependent (h : A.RowBasis s) :
    LinearIndependent R (A.rowSubmatrix s).rowFun :=
  h.1

theorem RowBasis.rowSpace_eq (h : A.RowBasis s) :
    (A.rowSubmatrix s).rowSpace = A.rowSpace :=
  h.2

-- theorem RowBasis.span_submatrix_eq (h : A.RowBasis s) :
--     span R (range (A.submatrix ((↑) : s → m) id)) = span R (range A) := by
--   simp [h.span_eq]


/-- A `ColBasis` as a `Basis` for the column space -/
noncomputable def ColBasis.basis (h : A.ColBasis t) : Basis t R A.colSpace :=
  RowBasis.basis h

@[simp] theorem ColBasis.basis_apply (h : A.ColBasis t) (j : t) : h.basis j = Aᵀ j :=
  funext <| congrFun (RowBasis.basis_apply h j)

theorem ColBasis.linearIndependent (h : A.ColBasis t) :
    LinearIndependent R (A.colSubmatrix t).colFun :=
  h.1

theorem ColBasis.colSpace_eq (h : A.ColBasis t) : (A.colSubmatrix t).colSpace = A.colSpace :=
  h.2

@[simp] theorem rowBasis_transpose : Aᵀ.RowBasis t ↔ A.ColBasis t := Iff.rfl
@[simp] theorem colBasis_transpose : Aᵀ.ColBasis s ↔ A.RowBasis s := Iff.rfl

theorem RowBasis.colBasis_transpose (h : A.RowBasis s) : Aᵀ.ColBasis s := rowBasis_transpose.1 h

theorem ColBasis.rowBasis_transpose (h : A.ColBasis t) : Aᵀ.RowBasis t := colBasis_transpose.1 h

theorem rows_linearIndependent_iff [Fintype m] :
    LinearIndependent R A.rowFun ↔ LinearMap.ker A.vecMulLinear = ⊥ := by
  simp only [Fintype.linearIndependent_iff, Submodule.eq_bot_iff, LinearMap.mem_ker,
    vecMulLinear_apply', vecMul, dotProduct]
  refine ⟨fun h x h0 ↦ funext fun i ↦ h _ (by rw [←h0]; ext; simp) _, fun h x h0 i ↦ ?_⟩
  rw [h x]; rfl
  rw [←h0]; ext; simp

theorem cols_linearIndependent_iff {R : Type _} [CommRing R] {A : Matrix m n R} [Fintype n] :
    LinearIndependent R A.colFun ↔ LinearMap.ker A.mulVecLin = ⊥ := by
  rw [←rowFun_transpose, rows_linearIndependent_iff]
  convert Iff.rfl; ext; simp [← mulVec_transpose]

end Ring

section DivisionRing

variable [DivisionRing R]

theorem RowBasis.finite [Fintype n] (hs : A.RowBasis s) : s.Finite := by
  have := hs.linearIndependent.finite_index; exact toFinite s

theorem ColBasis.finite [Fintype m] (h : A.ColBasis t) : t.Finite :=
  RowBasis.finite h

theorem exists_rowBasis_superset {A : Matrix m n R} {s₀ : Set m}
    (hs₀ : LinearIndependent R (A.rowSubmatrix s₀).rowFun) : ∃ s, A.RowBasis s ∧ s₀ ⊆ s := by
  obtain ⟨s, hss, -, h1,h2⟩ := exists_linearIndependent_extension' hs₀ (subset_univ _)
  refine ⟨s, ⟨h2, le_antisymm (span_mono ?_) ?_⟩, hss⟩
  · rw [rowFun_rowSubmatrix_eq, range_restrict]
    apply image_subset_range
  rw [image_univ, image_eq_range_submatrix] at h1
  rwa [rowSpace, rowSpace, Submodule.span_le, rowFun]

theorem exists_rowBasis (A : Matrix m n R) : ∃ s, A.RowBasis s :=
  let ⟨s, hs, _⟩ := exists_rowBasis_superset (s₀ := ∅) linearIndependent_empty_type
  ⟨s,hs⟩

theorem rowBasis_iff_maximal_linearIndependent : A.RowBasis s ↔
    s ∈ maximals (· ⊆ ·) {b : Set m | LinearIndependent R (A.rowSubmatrix b).rowFun} := by
  rw [mem_maximals_setOf_iff, RowBasis, and_congr_right_iff]
  refine fun hli ↦ ⟨fun h y hy hsy ↦ hsy.antisymm fun e he ↦ by_contra fun hes ↦ ?_,
      fun h ↦ le_antisymm (span_mono ?_) ?_⟩
  · have hse : LinearIndependent R (A.rowSubmatrix (insert e s))
    · apply hy.comp (inclusion (insert_subset he hsy)) <| inclusion_injective _
    apply ((linearIndependent_insert' hes).1 hse).2
    have hsp := h.symm.le.subset <| (subset_span <| mem_range_self _   : A e ∈ _)
    rwa [image_eq_range_submatrix, rowSpace_eq_span]
  · rintro _ ⟨x, -, rfl⟩; exact ⟨x, rfl⟩
  rintro x hx
  obtain ⟨k, c, f, g, rfl⟩ := mem_span_set'.1 hx
  apply sum_smul_mem
  rintro i -
  obtain ⟨_,⟨j,hj,rfl⟩⟩ := f i
  simp only
  obtain (hjs | hjs) := em (j ∈ s)
  · apply subset_span;
    simp only [rowFun_apply, rowFun_rowSubmatrix_eq, range_restrict, mem_image]
    exact ⟨j,hjs,rfl⟩
  by_contra hsp
  have heq := (h <| (linearIndependent_insert' hjs).2 ⟨hli, fun hsp' ↦ hsp ?_⟩) (subset_insert _ _)
  · exact hjs (heq.symm.subset (mem_insert _ _))
  rwa [image_eq_range_submatrix, rowSpace_eq_span ] at hsp'

theorem colBasis_iff_maximal_linearIndependent : A.ColBasis t ↔
    t ∈ maximals (· ⊆ ·) {b : Set n | LinearIndependent R (A.colSubmatrix b).colFun}  := by
  simp [ColBasis, rowBasis_iff_maximal_linearIndependent, rowFun_rowSubmatrix_eq,
    colFun_colSubmatrix_eq]

theorem exists_colBasis_superset {A : Matrix m n R} {t₀ : Set n}
    (ht₀ : LinearIndependent R (t₀.restrict Aᵀ)) : ∃ t, A.ColBasis t ∧ t₀ ⊆ t :=
  Aᵀ.exists_rowBasis_superset ht₀

theorem exists_colBasis (A : Matrix m n R) : ∃ t, A.ColBasis t :=
  Aᵀ.exists_rowBasis

end DivisionRing
section Field

variable [Field R]

theorem subset_rows_notLinearIndependent_iff [Fintype m] [Field R] :
    ¬ LinearIndependent R (A.rowSubmatrix s).rowFun ↔
      ∃ c, A.vecMul c = 0 ∧ c ≠ 0 ∧ support c ⊆ s := by
  simp only [rowFun_rowSubmatrix_eq, Fintype.subtype_notLinearIndependent_iff, ne_eq,
    vecMul, dotProduct, support_subset_iff, not_imp_comm]
  refine ⟨fun ⟨c,h,⟨i, _, hci⟩,h'⟩ ↦
    ⟨c, by convert h; simp, by rintro rfl; exact hci rfl, h'⟩,
    fun ⟨c,h,hi,h'⟩ ↦ ⟨c, by convert h; simp, ?_, h'⟩⟩
  by_contra hc; push_neg at hc
  exact hi (funext fun i ↦ (em (i ∈ s)).elim (hc i) (h' i))

theorem subset_cols_notLinearIndependent_iff [Fintype n] :
    ¬ LinearIndependent R (A.colSubmatrix t).colFun ↔
      ∃ c, A.mulVec c = 0 ∧ c ≠ 0 ∧ support c ⊆ t := by
  simp_rw [←rowFun_transpose, colSubmatrix_transpose,
    subset_rows_notLinearIndependent_iff, vecMul_transpose]

theorem toLin'_transpose [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] :
    toLin' Aᵀ = (Module.piEquiv n R R).symm.comp
      (A.toLin'.dualMap.comp (Module.piEquiv m R R).toLinearMap) := by
  ext i j; simp [Module.piEquiv_apply_apply, ←Pi.single_mul_right_apply (A · j)]

theorem toLin'_dualMap [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] :
    A.toLin'.dualMap =
      ((Module.piEquiv n R R).comp (toLin' Aᵀ)).comp (Module.piEquiv m R R).symm.toLinearMap := by
  rw [toLin'_transpose]; aesop

theorem colSpace_eq_top_iff_linearIndependent_rows [Fintype m] :
    A.colSpace = ⊤ ↔ LinearIndependent R A.rowFun := by
  rw [←not_iff_not, ←Ne.def, ←lt_top_iff_ne_top, ←orthSpace_lt_iff_lt, orthSpace_top,
    bot_lt_iff_ne_bot, Submodule.ne_bot_iff, Fintype.not_linearIndependent_iff]
  simp only [mem_orthSpace_iff', ne_eq, ← smul_eq_mul]
  refine ⟨fun ⟨x,hx,h0⟩ ↦ ⟨x, ?_, ne_iff.mp h0⟩, fun ⟨x,hx,h0⟩ ↦ ⟨x, fun y hy ↦ ?_, ne_iff.mpr h0⟩⟩
  · ext a; convert hx (A · a) <| subset_span ⟨a, rfl⟩; simp
  apply dotProduct_eq_zero_of_mem_span hy
  rintro _ ⟨i,hi,rfl⟩
  convert congr_fun hx i
  simp [dotProduct]

theorem rowSpace_eq_top_iff_linearIndependent_cols [Fintype n] :
    A.rowSpace = ⊤ ↔ LinearIndependent R A.colFun := by
  rw [←colSpace_transpose, colSpace_eq_top_iff_linearIndependent_rows, rowFun_transpose]

theorem ColBasis.rows_linearIndependent [Fintype m] (ht : A.ColBasis t)
    (hA : LinearIndependent R A.rowFun) : LinearIndependent R (A.colSubmatrix t).rowFun := by
  rw [←colSpace_eq_top_iff_linearIndependent_rows, Submodule.eq_top_iff']
  rw [←colSpace_eq_top_iff_linearIndependent_rows] at hA
  exact fun x ↦ by simp [hA ▸ ht.colSpace_eq]

theorem RowBasis.cols_linearIndependent [Fintype n] (hs : A.RowBasis s)
    (hA : LinearIndependent R Aᵀ) : LinearIndependent R (s.restrict A)ᵀ :=
  hs.colBasis_transpose.rows_linearIndependent hA

theorem cols_linearIndependent_of_rowSpace_le_rowSpace {A₁ : Matrix m₁ n R} {A₂ : Matrix m₂ n R}
    (h : A₁.rowSpace ≤ A₂.rowSpace) {t : Set n}
    (ht : LinearIndependent R (A₁.colSubmatrix t).colFun) :
    LinearIndependent R (A₂.colSubmatrix t).colFun := by
  rw [linearIndependent_iff'] at ht ⊢
  by_contra h'; push_neg at h'; obtain ⟨t₀, c, hne, i₀, hit₀, hnz⟩ := h'
  refine hnz <| ht t₀ c ?_ _ hit₀
  ext i
  simp only [colFun_apply, colSubmatrix_transpose, rowSubmatrix_apply, Finset.sum_apply,
    Pi.smul_apply, transpose_apply, smul_eq_mul, Pi.zero_apply]
  simp only [colFun_apply, colSubmatrix_transpose, rowSubmatrix_apply] at hne

  have hrs := h (subset_span <| mem_range_self i : A₁ i ∈ A₁.rowSpace)
  rw [rowSpace, mem_span_set'] at hrs
  obtain ⟨k, d, g, h_eq⟩ := hrs
  simp only [←h_eq, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun ind _ ↦ ?_)
  simp_rw [mul_comm (d _), ← mul_assoc, ← Finset.sum_mul]
  obtain ⟨_, i', hi', rfl⟩:=  g ind
  simp only [rowFun_apply, mul_eq_zero]
  left
  convert congr_fun hne i'
  simp

/-- Matrices with the same row space have the same column bases -/
theorem colBases_eq_of_rowSpaces_eq {A₁ : Matrix m₁ n R} {A₂ : Matrix m₂ n R}
    (h : A₁.rowSpace = A₂.rowSpace) : A₁.ColBasis = A₂.ColBasis := by
  ext
  simp_rw [colBasis_iff_maximal_linearIndependent]
  convert Iff.rfl with t
  exact ⟨fun h' ↦ cols_linearIndependent_of_rowSpace_le_rowSpace h.symm.le h',
    fun h' ↦ cols_linearIndependent_of_rowSpace_le_rowSpace h.le h'⟩

/-- Matrices with the same column space have the same row bases -/
theorem rowBases_eq_of_colSpaces_eq {A₁ : Matrix m n₁ R} {A₂ : Matrix m n₂ R}
    (h : A₁.colSpace = A₂.colSpace) : A₁.RowBasis = A₂.RowBasis := by
  ext s
  rw [←rowSpace_transpose, ←rowSpace_transpose] at h
  simpa using congr_fun (colBases_eq_of_rowSpaces_eq h) s

theorem RowBasis.submatrix_colBasis (hs : A.RowBasis s) (ht : A.ColBasis t) :
    (A.rowSubmatrix s).ColBasis t := by
  rwa [colBases_eq_of_rowSpaces_eq hs.rowSpace_eq]

theorem ColBasis.submatrix_rowBasis (ht : A.ColBasis t) (hs : A.RowBasis s) :
    (A.colSubmatrix t).RowBasis s := by
  rwa [rowBases_eq_of_colSpaces_eq ht.colSpace_eq]

/-- If an `m × n` matrix `A` with entries in `R` has linearly independent rows,
    a column basis for `A` gives a basis for `m → R`. -/
noncomputable def ColBasis.basisFun [Fintype m] (ht : A.ColBasis t)
  (hA : LinearIndependent R A.rowFun) : Basis t R (m → R) :=
    (Basis.span ht.linearIndependent).map <| LinearEquiv.ofTop _ <| eq_top_iff'.2 fun x ↦
    ( by simp [ht.colSpace_eq, colSpace_eq_top_iff_linearIndependent_rows.2 hA] )

@[simp] theorem ColBasis.basisFun_apply [Fintype m] (ht : A.ColBasis t)
    (hA : LinearIndependent R A.rowFun) (j : t) : ht.basisFun hA j = (A · j) := by
  ext x; exact congr_fun (Basis.span_apply ht.linearIndependent j) x

noncomputable def RowBasis.basisFun [Fintype n] (hs : A.RowBasis s)
    (hA : LinearIndependent R A.colFun) : Basis s R (n → R) :=
  hs.colBasis_transpose.basisFun hA

@[simp] theorem RowBasis.basisFun_apply [Fintype n] (hs : A.RowBasis s)
    (hA : LinearIndependent R Aᵀ) (i : s) : hs.basisFun hA i = A i := by
  ext; simp [basisFun]

end Field
section NullSpace

variable [Field R] [Fintype n] {m₁ m₂ : Type _} [Fintype m₁] [Fintype m₂] {A₁ : Matrix m₁ n R}
  {A₂ : Matrix m₂ n R} {t : Set n}

@[pp_dot] noncomputable def nullSpace {R : Type _} [CommRing R] (A : Matrix m n R) :
    Submodule R (n → R) :=
  A.rowSpace.orthSpace





@[simp] theorem mem_nullSpace_iff : x ∈ A.nullSpace ↔ A.mulVec x = 0 := by
  simp only [nullSpace, mem_orthSpace_iff', mulVec, dotProduct, mul_comm (x _)]
  refine ⟨fun h ↦ funext fun i ↦ h _ (subset_span <| mem_range_self i), fun h y hy ↦ ?_⟩
  rw [rowSpace] at hy
  rw [←dotProduct_eq_zero_of_mem_span hy (x := x)]
  · simp [dotProduct, mul_comm]
  rintro _ ⟨a ,ha, rfl⟩
  convert congr_fun h a using 1
  simp [dotProduct, mul_comm]

@[simp] theorem orthSpace_rowSpace_eq_nullSpace : A.rowSpace.orthSpace = A.nullSpace := rfl

@[simp] theorem orthSpace_nullSpace_eq_rowSpace : A.nullSpace.orthSpace = A.rowSpace := by
  rw [←orthSpace_rowSpace_eq_nullSpace, orthSpace_orthSpace]

theorem nullSpace_eq_ker_mulVecLin : A.nullSpace = LinearMap.ker A.mulVecLin := by
  ext x; rw [mem_nullSpace_iff, LinearMap.mem_ker, mulVecLin_apply]

theorem colBasis_iff_aux (h : A₁.rowSpace = A₂.nullSpace) (h₁ : LinearIndependent R A₁.rowFun)
    (h₂ : LinearIndependent R A₂.rowFun) (ht : A₁.ColBasis t) :  A₂.ColBasis tᶜ := by
  classical
  refine ⟨by_contra fun hld ↦?_ , ?_⟩
  · rw [rowFun_rowSubmatrix_eq, Fintype.subtype_notLinearIndependent_iff] at hld
    obtain ⟨c, hc0, hcex, hct⟩ := hld
    have hnull : c ∈ A₂.nullSpace
    · rw [mem_nullSpace_iff]
      ext i
      convert congr_fun hc0 i
      simp [mulVec, dotProduct, mul_comm (A₂ _ _), Finset.sum_fn]
    rw [←h, rowSpace_eq_lin_range, LinearMap.mem_range] at hnull
    obtain ⟨d, rfl⟩ := hnull
    have hker : d ∈ LinearMap.ker (vecMulLinear (A₁.colSubmatrix t))
    · ext j
      convert congr_fun (submatrix_vecMul_equiv A₁ d (Equiv.refl _) _) j
      simp only [Equiv.refl_symm, Equiv.coe_refl, comp.right_id]
      ext ⟨i,hi⟩
      exact (hct i (by simpa)).symm
    rw [← transpose_transpose A₁, ←rowSubmatrix_transpose, rows_linearIndependent_iff.1, mem_bot]
      at hker
    · simp [hker] at hcex
    rwa [rowSubmatrix_transpose, transpose_transpose, ←colSpace_eq_top_iff_linearIndependent_rows,
      ht.colSpace_eq, colSpace_eq_top_iff_linearIndependent_rows]
  rw [rowSpace_transpose, ←colSubmatrix_transpose, rowSpace_transpose,
    colSpace_eq_top_iff_linearIndependent_rows.2 h₂, colSpace_eq_top_iff_linearIndependent_rows,
    Fintype.linearIndependent_iff]
  intro c hc0
  have h₂₁ : LinearMap.range A₂.vecMulLinear = A₁.nullSpace
  · rw [← rowSpace_eq_lin_range, ← orthSpace_rowSpace_eq_nullSpace, h,
      orthSpace_nullSpace_eq_rowSpace]
  have h0 := mem_nullSpace_iff.1 <| h₂₁.le (LinearMap.mem_range_self A₂.vecMulLinear c)
  simp [mulVec, dotProduct, vecMul, Finset.sum_fn] at h0
  --   rw [← transpose_transpose A₁, ← transpose_restrict_eq_submatrix,
  -- --     rows_linearIndependent_iff.1 <| ht.rows_linearIndependent h₁, mem_bot] at hker
  -- have _ := t.toFinite.fintype; have _ := tᶜ.toFinite.fintype
  -- refine ⟨by_contra fun hld ↦ ?_, ?_⟩
  -- · rw [rowFun_rowSubmatrix_eq, Fintype.subtype_notLinearIndependent_iff] at hld
  --   obtain ⟨c, hc0, hcex, hct⟩ := Fintype.subtype_notLinearIndependent_iff.1 hld
  --   have hnull : c ∈ A₂.nullSpace
  --   · rw [mem_nullSpace_iff]
  --     ext i
  --     convert congr_fun hc0 i
  --     simp [mulVec, dotProduct, mul_comm (A₂ _ _), Finset.sum_fn]
  --   rw [←h, ←range_vecMulLinear, LinearMap.mem_range] at hnull
  --   obtain ⟨d, rfl⟩ := hnull
  --   have hker : d ∈ LinearMap.ker (vecMulLinear (A₁.submatrix id ((↑) : t → n)))
  --   · ext j
  --     convert congr_fun (submatrix_vecMul_equiv A₁ d (Equiv.refl _) _) j
  --     simp only [Equiv.refl_symm, Equiv.coe_refl, comp.right_id]
  --     ext ⟨i,hi⟩
  --     exact (hct i (by simpa)).symm
  --   rw [← transpose_transpose A₁, ← transpose_restrict_eq_submatrix,
  --     rows_linearIndependent_iff.1 <| ht.rows_linearIndependent h₁, mem_bot] at hker
  --   subst hker
  --   simp at hcex
  -- rw [span_cols_eq_top_iff_linearIndependent_rows.2 h₂, image_eq_range_submatrix,
  --   span_rows_eq_top_iff_linearIndependent_cols, transpose_submatrix, transpose_transpose,
  --   Fintype.linearIndependent_iff]
  -- intro c hc0
  -- have h₂₁ : LinearMap.range A₂.vecMulLinear = A₁.nullSpace
  -- · rw [range_vecMulLinear, nullSpace_eq_orthSpace_rowSpace, h, nullSpace_eq_orthSpace_rowSpace,
  --     orthSpace_orthSpace]
  -- have hA₁0 := mem_nullSpace_iff.1 <| h₂₁.le (LinearMap.mem_range_self A₂.vecMulLinear c)
  -- simp only [mulVec, dotProduct._eq_1, vecMulLinear_apply, ←Finset.sum_fn] at hA₁0

  have h01 := Fintype.linearIndependent_iff.1 ht.linearIndependent (fun x ↦ vecMul c A₂ x) ?_
  · refine Fintype.linearIndependent_iff.1 h₂ c <| funext fun j ↦ ?_
    obtain (hjt | hjt) := em (j ∈ t)
    · convert h01 ⟨j,hjt⟩ using 1; simp [vecMul, dotProduct]
    convert congr_fun hc0 ⟨j,hjt⟩; simp

  rw [←hA₁0]
  simp only [restrict_apply]
  rw [← Finset.sum_subset (s₁ := t.toFinset) (by simp)]
  · convert (Finset.sum_toFinset_eq_subtype (· ∈ t) _).symm; ext; simp [mul_comm]

  simp only [Finset.mem_univ, mem_toFinset, vecMul, dotProduct._eq_1, funext_iff, Pi.zero_apply,
    mul_eq_zero, forall_true_left]
  refine fun x hxt _ ↦ Or.inr ?_
  convert congr_fun hc0 ⟨x,hxt⟩
  simp

theorem colBasis_iff_colBasis_compl_of_Orth (h : span R (range A₁) = A₂.nullSpace) :
    A₁.ColBasis t ↔ A₂.ColBasis tᶜ := by
  obtain ⟨b₁, hb₁⟩ := A₁.exists_rowBasis
  obtain ⟨b₂, hb₂⟩ := A₂.exists_rowBasis
  have _ := hb₁.finite.fintype
  have _ := hb₂.finite.fintype
  rw [←colBases_eq_of_rowSpaces_eq hb₁.span_submatrix_eq,
    ←colBases_eq_of_rowSpaces_eq hb₂.span_submatrix_eq]
  refine ⟨colBasis_iff_aux ?_ hb₁.linearIndependent hb₂.linearIndependent,
    fun h' ↦ (compl_compl t) ▸ colBasis_iff_aux ?_ hb₂.linearIndependent hb₁.linearIndependent h'⟩
  · rw [range_row_submatrix, Subtype.range_val, hb₁.span_eq, h, nullSpace_eq_orthSpace_rowSpace,
      nullSpace_eq_orthSpace_rowSpace, range_row_submatrix, Subtype.range_val, hb₂.span_eq]
  rw [range_restrict, nullSpace_eq_orthSpace_rowSpace, range_row_submatrix, Subtype.range_val,
    hb₁.span_eq, h, nullSpace_eq_orthSpace_rowSpace, orthSpace_orthSpace, hb₂.span_eq]

end NullSpace

section Rank



noncomputable def rank' {R : Type _} [DivisionRing R] (A : Matrix m n R) : ℕ :=
  finrank R <| span R (range A)

theorem ncard_rowBasis {R : Type _} [DivisionRing R] [StrongRankCondition R]
  {A : Matrix m n R} (hs : A.RowBasis s) :
    s.ncard = A.rank' := by
  obtain (hfin | hinf) := s.finite_or_infinite
  · have _ := hfin.fintype
    rw [rank', finrank, rank_eq_card_basis hs.basis, Cardinal.toNat_cast, ←Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq]
  rw [hinf.ncard, rank', @finrank_of_infinite_dimensional _ _ _ _ _ fun hfin ↦ hinf <| ?_]
  have _ := hs.basis.linearIndependent.finite_index
  exact toFinite s





theorem foo1 [DivisionRing R] (hs : A.RowBasis s) (ht : A.ColBasis t) : s.ncard = t.ncard := by
  obtain (hfin | hinf) := em s.Finite
  ·





end Rank










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
