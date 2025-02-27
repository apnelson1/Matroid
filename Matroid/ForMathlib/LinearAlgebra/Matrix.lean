import Mathlib.Data.Matrix.Rank
import Matroid.ForMathlib.LinearAlgebra.LinearIndepOn

namespace Matrix


open Set Submodule Cardinal


universe u v w u₁ u₂

variable {m n R : Type*} {A A₁ A₂ : Matrix m n R} {s : Set m} {t : Set n}

@[simp]
lemma range_submatrix_left {α l : Type*} (A : Matrix m n α) (r_reindex : l → m) :
    range (A.submatrix r_reindex id) = A '' range r_reindex := by
  ext x
  simp only [mem_range, mem_image, exists_exists_eq_and]
  rfl

lemma range_submatrix_right {α l : Type*} (A : Matrix m n α) (c_reindex : l → n) :
    range (A.submatrix id c_reindex) = (· ∘ c_reindex) '' range A := by
  ext x
  simp only [mem_range, mem_image, exists_exists_eq_and]
  rfl

/-- The rank of a matrix, defined as the dimension of its column space.  -/
noncomputable def cRank [Semiring R] (A : Matrix m n R) : Cardinal :=
  Module.rank R (span R (Set.range Aᵀ))

lemma cRank_mono_col {n₀ : Type*} [Semiring R] (A : Matrix m n R) (c : n₀ → n) :
    (A.submatrix id c).cRank ≤ A.cRank := by
  apply Submodule.rank_mono <| span_mono ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨c x, rfl⟩

lemma cRank_lift_mono_row {m : Type u₁} {m₀ : Type u₂} {R : Type u} [Semiring R] (A : Matrix m n R)
    (r : m₀ → m) : lift.{u₁, max u₂ u} (A.submatrix r id).cRank ≤ lift.{u₂, max u₁ u} A.cRank := by
  let f : (m → R) →ₗ[R] (m₀ → R) := (LinearMap.funLeft R R r)
  have h_eq : Submodule.map f (span R (range Aᵀ)) = span R (range (A.submatrix r id)ᵀ) := by
    rw [LinearMap.map_span, ← image_univ, image_image, transpose_submatrix, range_submatrix_right]
    convert rfl
    aesop
  rw [cRank, ← h_eq]
  have hwin := lift_rank_map_le f (span R (range Aᵀ))
  simp_rw [← lift_umax] at hwin ⊢
  exact hwin

lemma cRank_mono_row {m m₀ : Type u} [Semiring R] (A : Matrix m n R) (r : m₀ → m) :
    (A.submatrix r id).cRank ≤ A.cRank  := by
  simpa using A.cRank_lift_mono_row r

lemma cRank_le_card_row [Semiring R] [StrongRankCondition R] [Fintype m] (A : Matrix m n R) :
    A.cRank ≤ Fintype.card m :=
  (Submodule.rank_le (span R (range Aᵀ))).trans <| by rw [rank_fun']

lemma cRank_le_card_col [Semiring R] [StrongRankCondition R] [Fintype n] (A : Matrix m n R) :
    A.cRank ≤ Fintype.card n :=
  (rank_span_le ..).trans <| by simpa using Cardinal.mk_range_le_lift (f := Aᵀ)

/-- The rank of a matrix, defined as the dimension of its column space, as a term in `ℕ∞`. -/
noncomputable def eRank [Semiring R] (A : Matrix m n R) : ℕ∞ := A.cRank.toENat

-- This means we could redefine mathlib's `Matrix.rank` as `A.eRank.toNat` to not need finiteness.
lemma eRank_toNat [CommRing R] [Fintype n] (A : Matrix m n R) : A.eRank.toNat = A.rank := by
  rw [eRank, cRank, rank, range_mulVecLin, toNat_toENat, Module.finrank]

lemma eRank_toNat_eq_finrank [Semiring R] (A : Matrix m n R) :
    A.eRank.toNat = Module.finrank R (span R (range Aᵀ)) := by
  simp [eRank, cRank, Module.finrank]

lemma eRank_mono_col {n₀ : Type*} [Semiring R] (A : Matrix m n R) (c : n₀ → n) :
    (A.submatrix id c).eRank ≤ A.eRank :=
  OrderHomClass.mono _ <| A.cRank_mono_col c

lemma eRank_mono_row {m₀ : Type*} [Semiring R] (A : Matrix m n R) (r : m₀ → m) :
    (A.submatrix r id).eRank ≤ A.eRank := by
  obtain hlt | hle := lt_or_le A.cRank Cardinal.aleph0
  · simpa using (toENat_le_iff_of_lt_aleph0 (by simpa)).2 <| A.cRank_lift_mono_row r
  simp [eRank, toENat_eq_top.2 hle]

lemma eRank_mono {m₀ n₀ : Type*} [Semiring R] (A : Matrix m n R) (r : m₀ → m) (c : n₀ → n) :
    (A.submatrix r c).eRank ≤ A.eRank :=
  ((A.submatrix r id).eRank_mono_col c).trans (A.eRank_mono_row r)

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
    span R (A '' s) = span R (range A) :=
  LinearIndepOn.span_eq_top_of_maximal hs

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
This is not true for division rings (as easily seen with the quaternion matrix [[1,i],[j,k]]),
and is also untrue if `cRank` is cardinal_valued; for example, the matrix `id : Matrix (ℕ → ℚ) ℕ ℚ`
has a countable-dimensional column space and an uncountable-dimensional row space. -/
@[simp]
lemma eRank_transpose [Field R] (A : Matrix m n R) : Aᵀ.eRank = A.eRank := by
  obtain ⟨t, ht⟩ := A.exists_isColBasis
  rw [← ht.isRowBasis_transpose.encard_eq, ht.encard_eq]

/-- A matrix with finite linearly independent row set has full column space. -/
lemma span_col_eq_top_of_linearIndependent_row [Fintype m] [Field R] (h : LinearIndependent R A) :
    span R (range Aᵀ) = ⊤ :=
  eq_top_of_finrank_eq <| by
    rw [← eRank_toNat_eq_finrank, ← eRank_transpose, eRank_toNat_eq_finrank, transpose_transpose,
    Module.finrank_eq_card_basis (Basis.span h), Module.finrank_fintype_fun_eq_card]

/-- A matrix with finite linearly independent column set has full row space. -/
lemma span_row_eq_top_of_linearIndependent_col [Fintype n] [Field R] (h : LinearIndependent R Aᵀ) :
    span R (range A) = ⊤ := by
  rw [← Aᵀ.span_col_eq_top_of_linearIndependent_row h, transpose_transpose]



section Submatrix

variable [Ring R]

/-- If a column-submatrix of `A` has linearly independent rows, then so does `A`. -/
theorem rows_linearIndependent_of_submatrix {m₀ n₀ : Type*} (e : m₀ ≃ m) (f : n₀ → n)
    (h : LinearIndependent R (A.submatrix e f)) : LinearIndependent R A := by
    classical
  rw [linearIndependent_iff'] at h ⊢
  intro s c hc i his
  rw [← h (s.image e.symm) (c ∘ e) _ (e.symm i) (by simpa)]
  · simp
  ext j
  convert congr_fun hc (f j)
  simp

/-- If a row-submatrix of `A` has linearly independent columns, then so does `A`. -/
theorem cols_linearIndependent_of_submatrix {m₀ n₀ : Type*} (e : m₀ → m) (f : n₀ ≃ n)
    (h : LinearIndependent R (A.submatrix e f)ᵀ) : LinearIndependent R Aᵀ :=
  rows_linearIndependent_of_submatrix f e h

end Submatrix

end Matrix
