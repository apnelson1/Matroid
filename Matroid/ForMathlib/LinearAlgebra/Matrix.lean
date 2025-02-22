import Mathlib.Data.Matrix.Rank
import Matroid.ForMathlib.LinearAlgebra.LinearIndepOn

namespace Matrix

section Cardinal



open Set Submodule Cardinal

@[simp]
lemma Set.toENat_cardinalMk {α : Type*} (s : Set α) : (#s).toENat = s.encard := rfl

@[simp]
lemma Set.cast_fintype_card {α : Type*} (s : Set α) [Fintype s] :
    (Fintype.card s : ℕ∞) = s.encard := by
  simp [encard_eq_coe_toFinset_card]

universe u

variable {m n R : Type*} {A A₁ A₂ : Matrix m n R} {s : Set m} {t : Set n}

/-- The rank of a matrix, defined as the dimension of its column space.  -/
noncomputable def cRank [Semiring R] (A : Matrix m n R) : Cardinal :=
  Module.rank R (Submodule.span R (Set.range Aᵀ))

/-- The rank of a matrix, defined as the dimension of its column space, as a term in `ℕ∞`. -/
noncomputable def eRank [Semiring R] (A : Matrix m n R) : ℕ∞ := A.cRank.toENat

-- This means we could redefine mathlib's `Matrix.rank` as `A.eRank.toNat` to not need finiteness.
lemma eRank_toNat [CommRing R] [Fintype n] (A : Matrix m n R) : A.eRank.toNat = A.rank := by
  rw [eRank, cRank, rank, range_mulVecLin, toNat_toENat, Module.finrank]

/-- For `A : Matrix m n R` and `s : Set m`,
`A.IsRowBasis R s` means that `s` indexes an `R`-basis for the row space of `A`. -/
def IsRowBasis (R : Type*) [Semiring R] (A : Matrix m n R) (s : Set m) : Prop :=
  Maximal (LinearIndepOn R A ·) s

/-- For `A : Matrix m n R` and `t : Set n`,
`A.IsColBasis R t` means that `t` indexes an `R`-basis for the column space of `A`. -/
def IsColBasis (R : Type*) [Semiring R] (A : Matrix m n R) (t : Set n) : Prop :=
  Aᵀ.IsRowBasis R t

lemma exists_isRowBasis (R : Type*) [DivisionRing R] (A : Matrix m n R) :
    ∃ s, A.IsRowBasis R s := by
  obtain ⟨s, -, hs⟩ := (linearIndepOn_empty R A).exists_maximal (subset_univ _)
  exact ⟨s, by simpa using hs⟩

lemma IsRowBasis.isColBasis_transpose [Semiring R] (h : A.IsRowBasis R s) : Aᵀ.IsColBasis R s :=
  h

lemma exists_isColBasis (R : Type*) [DivisionRing R] (A : Matrix m n R) : ∃ s, A.IsColBasis R s :=
  Aᵀ.exists_isRowBasis R

lemma IsColBasis.isRowBasis_transpose [Semiring R] (h : A.IsColBasis R t) : Aᵀ.IsRowBasis R t :=
  h

lemma IsRowBasis.span_eq [DivisionRing R] (hs : A.IsRowBasis R s) :
    span R (A '' s) = span R (range A) := by
  refine span_eq_span (span_le.1 <| span_mono <| image_subset_range ..) ?_
  rintro _ ⟨i, rfl⟩
  by_contra h
  rw [SetLike.mem_coe, hs.prop.not_mem_span_iff] at h
  exact h.1 <| hs.mem_of_prop_insert h.2

@[simp]
lemma range_submatrix_left {α l : Type*} (A : Matrix m n α) (r_reindex : l → m) :
    range (A.submatrix r_reindex id) = A '' range r_reindex := by
  ext x
  simp only [mem_range, mem_image, exists_exists_eq_and]
  rfl

lemma range_submatrix_right {α l : Type*} (A : Matrix m n α) (c_reindex : l → n) :
    range (A.submatrix id c_reindex) = (· ∘ c_reindex) '' range A := by
  ext x
  simp_all only [mem_range, mem_image, exists_exists_eq_and]
  rfl

lemma IsRowBasis.span_submatrix_eq [DivisionRing R] (hs : A.IsRowBasis R s) :
    span R (range (A.submatrix (fun x : s ↦ x) id)) = span R (range A) := by
  simp [← hs.span_eq]

lemma IsColBasis.span_submatrix_eq [DivisionRing R] (hs : A.IsColBasis R t) :
    span R (range (A.submatrix id (fun x : t ↦ x))ᵀ) = span R (range Aᵀ) := by
  simp [← hs.span_eq]

/-- If `A.IsRowBasis R s`, then `s` naturally indexes an `R`-`Basis` for the row space of `A`. -/
noncomputable def IsRowBasis.basis [DivisionRing R] (hs : A.IsRowBasis R s) :
    Basis s R <| span R (range A) :=
  (Basis.span hs.prop.linearIndependent).map <|
    LinearEquiv.ofEq _ _ <| by rw [← image_eq_range, hs.span_eq]

/-- If `A.IsColBasis R t`, then `t` naturally indexes an `R`-`Basis` for the column space of `A`. -/
noncomputable def IsColBasis.basis [DivisionRing R] (ht : A.IsColBasis R t) :
    Basis t R <| span R (range Aᵀ) :=
  ht.isRowBasis_transpose.basis

-- lemma IsColBasis.ncard_eq [Field R] (h : A.IsColBasis R t) : t.ncard = A.rank' := by
--   simpa using congr_arg Cardinal.toNat h.basis.mk_eq_rank

lemma IsColBasis.encard_eq [DivisionRing R] (h : A.IsColBasis R t) : t.encard = A.eRank := by
  simpa using congr_arg Cardinal.toENat h.basis.mk_eq_rank

theorem linearIndepOn_col_le_of_span_row_le {m₁ m₂ : Type*} [CommRing R] {A₁ : Matrix m₁ n R}
    {A₂ : Matrix m₂ n R} (h : span R (range A₁) ≤ span R (range A₂)) :
    LinearIndepOn R A₁ᵀ ≤ LinearIndepOn R A₂ᵀ := by
  -- Perhaps this proof can be simplified by not fully unfolding `LinearCombination` and `sum`.
  refine fun t ht ↦ linearIndepOn_iff.2 fun l hl hl0 ↦ linearIndepOn_iff.1 ht l hl ?_
  ext i
  have hi : A₁ i ∈ span R (range A₂) := h <| subset_span <| mem_range_self ..
  simp_rw [Finsupp.mem_span_range_iff_exists_finsupp, Finsupp.sum] at hi
  obtain ⟨c, hc⟩ := hi
  have hrw (i' : m₂) : ∑ x ∈ l.support, l x * A₂ i' x = 0 := by
    simpa [Finsupp.linearCombination, Finsupp.sum] using congr_fun hl0 i'
  suffices ∑ x ∈ l.support, l x * ∑ x_1 ∈ c.support, c x_1 * A₂ x_1 x = 0 by
    simpa [Finsupp.linearCombination, Finsupp.sum, ← hc]
  simp_rw [Finset.mul_sum, Finset.sum_comm (s := l.support), mul_left_comm (a := l _),
    ← Finset.mul_sum]
  simp [hrw]

theorem linearIndepOn_row_le_of_span_col_le {n₁ n₂ : Type*} [CommRing R] {A₁ : Matrix m n₁ R}
    {A₂ : Matrix m n₂ R} (h : span R (range A₁ᵀ) ≤ span R (range A₂ᵀ)) :
    LinearIndepOn R A₁ ≤ LinearIndepOn R A₂ := by
  simpa using linearIndepOn_col_le_of_span_row_le h

lemma linearIndepOn_col_eq_of_span_row_eq {m₁ m₂ : Type*} [CommRing R] {A₁ : Matrix m₁ n R}
    {A₂ : Matrix m₂ n R} (h : span R (range A₁) = span R (range A₂)) :
    LinearIndepOn R A₁ᵀ = LinearIndepOn R A₂ᵀ :=
  (linearIndepOn_col_le_of_span_row_le h.le).antisymm
    (linearIndepOn_col_le_of_span_row_le h.symm.le)

lemma linearIndepOn_row_eq_of_span_col_eq {n₁ n₂ : Type*} [CommRing R] {A₁ : Matrix m n₁ R}
    {A₂ : Matrix m n₂ R} (h : span R (range A₁ᵀ) = span R (range A₂ᵀ)) :
    LinearIndepOn R A₁ = LinearIndepOn R A₂ := by
  simpa using linearIndepOn_col_eq_of_span_row_eq h

lemma isColBasis_iff_of_span_row_eq {m₁ m₂ : Type*} [CommRing R] {A₁ : Matrix m₁ n R}
    {A₂ : Matrix m₂ n R} (h : span R (range A₁) = span R (range A₂)) (t : Set n) :
    A₁.IsColBasis R t ↔ A₂.IsColBasis R t := by
  rw [IsColBasis, IsRowBasis, linearIndepOn_col_eq_of_span_row_eq h, IsColBasis, IsRowBasis]

lemma IsColBasis.submatrix_isColBasis [Field R] (ht : A.IsColBasis R t) (hs : A.IsRowBasis R s) :
    (A.submatrix (fun x : s ↦ x) id).IsColBasis R t :=
  (isColBasis_iff_of_span_row_eq hs.span_submatrix_eq _).2 ht

lemma IsRowBasis.submatrix_isRowBasis [Field R] (hs : A.IsRowBasis R s) (ht : A.IsColBasis R t) :
    (A.submatrix id (fun x : t ↦ x)).IsRowBasis R s :=
  IsColBasis.submatrix_isColBasis (A := Aᵀ) hs ht

/-- An auxiliary lemma used to prove `IsRowBasis.encard_eq`.
It is difficult to make this as a claim within the proof itself,
due to universe issues when swapping row/column types.  -/
private lemma basis_encard_le_aux [Field R] (hs : A.IsRowBasis R s)
    (ht : A.IsColBasis R t) : s.encard ≤ t.encard := by
  wlog hfin : t.Finite
  · simp [Infinite.encard_eq hfin]
  have := hfin.fintype
  convert OrderHomClass.mono toENat <|
    (hs.submatrix_isRowBasis ht).prop.linearIndependent.cardinal_lift_le_rank <;>
  simp

/-- The `encard` of a row basis is equal to the rank of the column space.
Unlike the column basis case, this requires a `Field` assumption.
(One can also prove `s.encard = Aᵀ.eRank` with `h.IsColBasis.encard_eq`,
and this just needs `DivisionRing`. ) -/
lemma IsRowBasis.encard_eq [Field R] (h : A.IsRowBasis R s) : s.encard = A.eRank := by
  obtain ⟨t, ht⟩ := A.exists_isColBasis
  rw [← ht.encard_eq]
  exact (basis_encard_le_aux h ht).antisymm (basis_encard_le_aux ht.isRowBasis_transpose h)

/-- The `eRank` of a (possibly infinite) matrix over a field is the `eRank` of its transpose.
This is not true for `cRank`, because of (say) the matrix `id : Matrix (ℕ → ℚ) ℕ ℚ`,
which has countable-dimensional column space and uncountable-dimensional row space. -/
lemma eRank_transpose [Field R] (A : Matrix m n R) : Aᵀ.eRank = A.eRank := by
  obtain ⟨t, ht⟩ := A.exists_isColBasis
  rw [← ht.isRowBasis_transpose.encard_eq, ht.encard_eq]

/-- A matrix with finite linearly independent row set has full column space. -/
lemma span_col_eq_top_of_linearIndependent_row [Fintype m] [Field R] (h : LinearIndependent R A) :
    span R (range Aᵀ) = ⊤ := by
  apply eq_top_of_finrank_eq
  rw [Module.finrank, ← Matrix.cRank, ← Cardinal.toNat_toENat, ← Matrix.eRank, ← eRank_transpose,
    Matrix.eRank, Matrix.cRank, transpose_transpose, toNat_toENat,
    show Module.rank R ↥(span R (range A)) = ↑(Fintype.card m) by
    simpa using (Basis.span h).mk_eq_rank.symm]
  simp

/-- A matrix with finite linearly independent column set has full row space. -/
lemma span_row_eq_top_of_linearIndependent_col [Fintype n] [Field R] (h : LinearIndependent R Aᵀ) :
    span R (range A) = ⊤ := by
  rw [← Aᵀ.span_col_eq_top_of_linearIndependent_row h, transpose_transpose]

end Cardinal

end Matrix
