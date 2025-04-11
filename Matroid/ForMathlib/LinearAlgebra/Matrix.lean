import Mathlib.Data.Matrix.Rank
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Finset.Preimage
import Matroid.ForMathlib.LinearAlgebra.LinearIndepOn
import Matroid.ForMathlib.Minimal

namespace Matrix


open Set Submodule Cardinal


universe u v w u₁ u₂

variable {m n R : Type*} {A A₁ A₂ : Matrix m n R} {s : Set m} {t : Set n}

def rowFun (A : Matrix m n R) (i : m) : n → R := A i

def colFun (A : Matrix m n R) (i : n) : m → R := Aᵀ i

lemma rowFun_def (A : Matrix m n R) : A.rowFun = A := rfl

lemma colFun_def (A : Matrix m n R) : A.colFun = Aᵀ := rfl

@[simp]
lemma rowFun_apply (A : Matrix m n R) (i : m) (j : n) : A.rowFun i j = A i j := rfl

@[simp]
lemma colFun_apply (A : Matrix m n R) (i : m) (j : n) : A.colFun j i = A i j := rfl

@[simp]
lemma transpose_rowFun (A : Matrix m n R) : Aᵀ.rowFun = A.colFun := rfl

@[simp]
lemma transpose_colFun (A : Matrix m n R) : Aᵀ.colFun = A.rowFun := rfl

lemma submatrix_rowFun {m₀ n₀ : Type*} (A : Matrix m n R) (r : m₀ → m) (c : n₀ → n) (i : m₀) :
    (A.submatrix r c).rowFun i = (A.submatrix id c).rowFun (r i) := rfl

lemma submatrix_row_eq_comp {m₀ n₀ : Type*} (A : Matrix m n R) (r : m₀ → m) (c : n₀ → n) (i : m₀) :
    (A.submatrix r c).rowFun i = A.rowFun (r i) ∘ c := rfl

lemma submatrix_colFun {m₀ n₀ : Type*} (A : Matrix m n R) (r : m₀ → m) (c : n₀ → n) (j : n₀) :
    (A.submatrix r c).colFun j = (A.submatrix r id).colFun (c j) := rfl


@[simp]
lemma submatrix_colFun_id {n₀ : Type*} (A : Matrix m n R) (c : n₀ → n) (j : n₀) :
    (A.submatrix id c).colFun j = A.colFun (c j) := rfl

lemma submatrix_col_eq_comp {m₀ n₀ : Type*} (A : Matrix m n R) (r : m₀ → m) (c : n₀ → n) (j : n₀) :
    (A.submatrix r c).colFun j = A.colFun (c j) ∘ r := rfl

def EqOn (A B : Matrix m n R) (s : Set m) (t : Set n) : Prop :=
  ∀ ⦃i j⦄, i ∈ s → j ∈ t → A i j = B i j

variable {α : Type*}

def block (A : Matrix m n α) (s : Set m) (t : Set n) :
    Matrix s t α := A.toBlock (· ∈ s) (· ∈ t)


@[simp] lemma block_apply (A : Matrix m n α) (s : Set m) (t : Set n) (i : s) (j : t) :
    A.block s t i j = A i.1 j.1 := rfl

lemma eq_fromBlocks_block_reindex (A : Matrix m n α) (s : Set m) (t : Set n)
    [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] :
    A = (Matrix.fromBlocks (A.block s t) (A.block s tᶜ) (A.block sᶜ t) (A.block sᶜ tᶜ)).reindex
      (Equiv.Set.sumCompl s) (Equiv.Set.sumCompl t) := by
  ext i j
  simp only [reindex_apply, submatrix_apply]
  by_cases hi : i ∈ s
  · by_cases hj : j ∈ t
    · simp [Equiv.Set.sumCompl_symm_apply_of_mem hj, Equiv.Set.sumCompl_symm_apply_of_mem hi]
    simp [Equiv.Set.sumCompl_symm_apply_of_not_mem hj, Equiv.Set.sumCompl_symm_apply_of_mem hi]
  by_cases hj : j ∈ t
  · simp [Equiv.Set.sumCompl_symm_apply_of_not_mem hi, Equiv.Set.sumCompl_symm_apply_of_mem hj]
  simp [Equiv.Set.sumCompl_symm_apply_of_not_mem hi, Equiv.Set.sumCompl_symm_apply_of_not_mem hj]

@[simp]
lemma range_submatrix_left {α l : Type*} (A : Matrix m n α) (r_reindex : l → m) :
    range (A.submatrix r_reindex id).rowFun = A.rowFun '' range r_reindex := by
  ext x
  simp only [mem_range, mem_image, exists_exists_eq_and]
  rfl

lemma range_submatrix_right {α l : Type*} (A : Matrix m n α) (c_reindex : l → n) :
    range (A.submatrix id c_reindex).rowFun = (· ∘ c_reindex) '' range A.rowFun := by
  ext x
  simp only [mem_range, mem_image, exists_exists_eq_and]
  rfl

/-- The rank of a matrix, defined as the dimension of its column space.  -/
noncomputable def cRank [Semiring R] (A : Matrix m n R) : Cardinal :=
  Module.rank R (span R (Set.range A.colFun))

lemma cRank_mono_col {n₀ : Type*} [Semiring R] (A : Matrix m n R) (c : n₀ → n) :
    (A.submatrix id c).cRank ≤ A.cRank := by
  apply Submodule.rank_mono <| span_mono ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨c x, rfl⟩

lemma cRank_lift_mono_row {m : Type u₁} {m₀ : Type u₂} {R : Type u} [Semiring R] (A : Matrix m n R)
    (r : m₀ → m) : lift.{u₁, max u₂ u} (A.submatrix r id).cRank ≤ lift.{u₂, max u₁ u} A.cRank := by
  let f : (m → R) →ₗ[R] (m₀ → R) := LinearMap.funLeft R R r
  have h_eq : Submodule.map f (span R (range A.colFun))
    = span R (range (A.submatrix r id).colFun) := by
    rw [LinearMap.map_span, ← image_univ, image_image, ← transpose_rowFun,
      ← transpose_rowFun, transpose_submatrix, range_submatrix_right]
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
  rw [eRank, cRank, rank, range_mulVecLin, ← colFun_def, toNat_toENat, Module.finrank]

lemma eRank_toNat_eq_finrank [Semiring R] (A : Matrix m n R) :
    A.eRank.toNat = Module.finrank R (span R (range A.colFun)) := by
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
  Maximal (LinearIndepOn R A.rowFun ·) s

/-- For `A : Matrix m n R` and `t : Set n`,
`A.IsColBasis R t` means that `t` indexes an `R`-basis for the column space of `A`. -/
def IsColBasis (R : Type*) [Semiring R] (A : Matrix m n R) (t : Set n) : Prop :=
  Aᵀ.IsRowBasis R t

lemma isRowBasis_univ (R : Type*) [Semiring R] (A : Matrix m n R) :
    A.IsRowBasis R univ ↔ LinearIndependent R A.rowFun := by
  simp [IsRowBasis]

lemma isColBasis_univ (R : Type*) [Semiring R] (A : Matrix m n R) :
    A.IsColBasis R univ ↔ LinearIndependent R A.colFun := by
  simp [IsColBasis, isRowBasis_univ]

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
    span R (A.rowFun '' s) = span R (range A.rowFun) :=
  LinearIndepOn.span_eq_top_of_maximal hs

lemma IsRowBasis.span_submatrix_eq [DivisionRing R] (hs : A.IsRowBasis R s) :
    span R (range (A.submatrix (fun x : s ↦ x) id).rowFun) = span R (range A.rowFun) := by
  simp [← hs.span_eq]

lemma IsColBasis.span_submatrix_eq [DivisionRing R] (hs : A.IsColBasis R t) :
    span R (range (A.submatrix id (fun x : t ↦ x)).colFun) = span R (range A.colFun) :=
  hs.isRowBasis_transpose.span_submatrix_eq

/-- If `A.IsRowBasis R s`, then `s` naturally indexes an `R`-`Basis` for the row space of `A`. -/
noncomputable def IsRowBasis.basis [DivisionRing R] (hs : A.IsRowBasis R s) :
    Basis s R <| span R (range A.rowFun) :=
  (Basis.span hs.prop.linearIndependent).map <|
    LinearEquiv.ofEq _ _ <| by rw [← image_eq_range, hs.span_eq]

/-- If `A.IsColBasis R t`, then `t` naturally indexes an `R`-`Basis` for the column space of `A`. -/
noncomputable def IsColBasis.basis [DivisionRing R] (ht : A.IsColBasis R t) :
    Basis t R <| span R (range A.colFun) :=
  ht.isRowBasis_transpose.basis

lemma IsColBasis.encard_eq [DivisionRing R] (h : A.IsColBasis R t) : t.encard = A.eRank := by
  simpa using congr_arg Cardinal.toENat h.basis.mk_eq_rank

/-- If the row space of `A₁` is a subspace of the row space of `A₂`, then independence of
a set of columns of `A₁` implies independence in `A₂`. -/
theorem linearIndepOn_col_le_of_span_row_le {m₁ m₂ : Type*} [CommRing R] {A₁ : Matrix m₁ n R}
    {A₂ : Matrix m₂ n R} (h : span R (range A₁.rowFun) ≤ span R (range A₂.rowFun)) :
    LinearIndepOn R A₁.colFun ≤ LinearIndepOn R A₂.colFun := by
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
    {A₂ : Matrix m n₂ R} (h : span R (range A₁.colFun) ≤ span R (range A₂.colFun)) :
    LinearIndepOn R A₁.rowFun ≤ LinearIndepOn R A₂.rowFun := by
  simpa using linearIndepOn_col_le_of_span_row_le h

/-- Two matrices with the same row space have the same linearly independent sets of columns. -/
lemma linearIndepOn_col_eq_of_span_row_eq {m₁ m₂ : Type*} [CommRing R] {A₁ : Matrix m₁ n R}
    {A₂ : Matrix m₂ n R} (h : span R (range A₁.rowFun) = span R (range A₂.rowFun)) :
    LinearIndepOn R A₁.colFun = LinearIndepOn R A₂.colFun :=
  (linearIndepOn_col_le_of_span_row_le h.le).antisymm
    (linearIndepOn_col_le_of_span_row_le h.symm.le)

/-- Two matrices with the same column space have the same linearly independent sets of rows. -/
lemma linearIndepOn_row_eq_of_span_col_eq {n₁ n₂ : Type*} [CommRing R] {A₁ : Matrix m n₁ R}
    {A₂ : Matrix m n₂ R} (h : span R (range A₁.colFun) = span R (range A₂.colFun)) :
    LinearIndepOn R A₁.rowFun = LinearIndepOn R A₂.rowFun := by
  simpa using linearIndepOn_col_eq_of_span_row_eq h

lemma isColBasis_iff_of_span_row_eq {m₁ m₂ : Type*} [CommRing R] {A₁ : Matrix m₁ n R}
    {A₂ : Matrix m₂ n R} (h : span R (range A₁.rowFun) = span R (range A₂.rowFun)) (t : Set n) :
    A₁.IsColBasis R t ↔ A₂.IsColBasis R t := by
  rw [IsColBasis, IsRowBasis, transpose_rowFun, linearIndepOn_col_eq_of_span_row_eq h,
     IsColBasis, IsRowBasis, transpose_rowFun]

lemma isRowBasis_iff_of_span_col_eq {n₁ n₂ : Type*} [CommRing R] {A₁ : Matrix m n₁ R}
    {A₂ : Matrix m n₂ R} (h : span R (range A₁ᵀ) = span R (range A₂ᵀ)) (s : Set m) :
    A₁.IsRowBasis R s ↔ A₂.IsRowBasis R s :=
  isColBasis_iff_of_span_row_eq h s

lemma IsColBasis.submatrix_isColBasis [Field R] (ht : A.IsColBasis R t) (hs : A.IsRowBasis R s) :
    (A.submatrix (fun x : s ↦ x) id).IsColBasis R t :=
  (isColBasis_iff_of_span_row_eq hs.span_submatrix_eq _).2 ht

lemma IsRowBasis.submatrix_isRowBasis [Field R] (hs : A.IsRowBasis R s) (ht : A.IsColBasis R t) :
    (A.submatrix id (fun x : t ↦ x)).IsRowBasis R s :=
  IsColBasis.submatrix_isColBasis (A := Aᵀ) hs ht

/-- An auxiliary lemma used to prove `IsRowBasis.encard_eq`.
It is difficult to make this as a claim within the proof itself,
due to universe issues when swapping row/column types.  -/
private lemma basis_encard_le_aux [Field R] (hs : A.IsRowBasis R s) (ht : A.IsColBasis R t) :
    s.encard ≤ t.encard := by
  wlog hfin : t.Finite
  · simp [Infinite.encard_eq hfin]
  have := hfin.fintype
  convert OrderHomClass.mono toENat <|
    (hs.submatrix_isRowBasis ht).prop.linearIndependent.cardinal_lift_le_rank <;>
  simp

/-- The `encard` of a row basis is equal to the rank of the column space.
Unlike the column basis case (where this is essentially just the definition), this needs a `Field`.
One can also prove with `DivisionRing` that `s.encard = Aᵀ.eRank` using `h.IsColBasis.encard_eq` -/
lemma IsRowBasis.encard_eq [Field R] (h : A.IsRowBasis R s) : s.encard = A.eRank := by
  obtain ⟨t, ht⟩ := A.exists_isColBasis
  rw [← ht.encard_eq]
  exact (basis_encard_le_aux h ht).antisymm (basis_encard_le_aux ht.isRowBasis_transpose h)

/-- The `eRank` of a (possibly infinite) matrix over a field is the `eRank` of its transpose.
This is not true for division rings (as easily seen with the quaternion matrix [[1,i],[j,k]]),
and is also untrue if rank is cardinal_valued; for example, the matrix `id : Matrix (ℕ → ℚ) ℕ ℚ`
has a countable-dimensional column space and an uncountable-dimensional row space. -/
@[simp]
lemma eRank_transpose [Field R] (A : Matrix m n R) : Aᵀ.eRank = A.eRank := by
  obtain ⟨t, ht⟩ := A.exists_isColBasis
  rw [← ht.isRowBasis_transpose.encard_eq, ht.encard_eq]

/-- A matrix with finite linearly independent row set has full column space. -/
lemma span_col_eq_top_of_linearIndependent_rows [Fintype m] [Field R]
    (h : LinearIndependent R A.rowFun) : span R (range A.colFun) = ⊤ :=
  eq_top_of_finrank_eq <| by
    rw [← eRank_toNat_eq_finrank, ← eRank_transpose, eRank_toNat_eq_finrank, transpose_colFun,
    Module.finrank_eq_card_basis (Basis.span h), Module.finrank_fintype_fun_eq_card]

lemma span_col_eq_top_iff_linearIndependent_rows {K : Type*} [Fintype m] [Field K]
    {A : Matrix m n K} : span K (range A.colFun) = ⊤ ↔ LinearIndependent K A.rowFun := by
  refine ⟨fun h ↦ ?_, span_col_eq_top_of_linearIndependent_rows⟩
  obtain ⟨s, hs⟩ := A.exists_isRowBasis
  obtain ⟨s, rfl⟩ := s.toFinite.exists_finset_coe
  have hr := hs.encard_eq
  rw [eRank, cRank, h] at hr
  obtain rfl : s = Finset.univ := by simpa [Finset.card_eq_iff_eq_univ] using hr
  rw [← linearIndepOn_univ, ← Finset.coe_univ]
  exact hs.prop

/-- A matrix with finite linearly independent column set has full row space. -/
lemma span_row_eq_top_of_linearIndependent_cols [Fintype n] [Field R]
    (h : LinearIndependent R A.colFun) : span R (range A.rowFun) = ⊤ := by
  rw [← Aᵀ.span_col_eq_top_of_linearIndependent_rows h, transpose_colFun]

lemma span_row_eq_top_iff_linearIndependent_col {K : Type*} [Fintype n] [Field K]
    {A : Matrix m n K} : span K (range A.rowFun) = ⊤ ↔ LinearIndependent K A.colFun :=
  span_col_eq_top_iff_linearIndependent_rows

section Submatrix

variable [Semiring R]

/-- If a column-submatrix of `A` has linearly independent rows, then so does `A`. -/
theorem linearIndependent_rows_of_submatrix {m₀ n₀ : Type*} (e : m₀ ≃ m) (f : n₀ → n)
    (h : LinearIndependent R (A.submatrix e f).rowFun) : LinearIndependent R A.rowFun := by
    classical
  rw [linearIndependent_iff'ₛ] at h ⊢
  intro s c c' hc i his
  simpa using h (s.image e.symm) (c ∘ e) (c' ∘ e)
    (funext fun j ↦ by simpa using congr_fun hc (f j)) (e.symm i) (by simpa)

/-- If a row-submatrix of `A` has linearly independent columns, then so does `A`. -/
theorem linearIndependent_cols_of_submatrix {m₀ n₀ : Type*} (e : m₀ → m) (f : n₀ ≃ n)
    (h : LinearIndependent R (fun i ↦ (A.submatrix e f)ᵀ i)) : LinearIndependent R (fun i ↦ Aᵀ i) :=
  linearIndependent_rows_of_submatrix f e h

variable (R) in
theorem linearIndependent_rows_submatrix_iff_of_surjective {m₀ n₀ : Type*} (e : m₀ ≃ m)
    {f : n₀ → n} (hf : Function.Surjective f) :
    LinearIndependent R (A.submatrix e f).rowFun ↔ LinearIndependent R A.rowFun :=
  ⟨fun h ↦ linearIndependent_rows_of_submatrix _ _ h,
    fun h ↦ linearIndependent_rows_of_submatrix e.symm (Function.surjInv hf) <| by
    simpa [(Function.rightInverse_surjInv hf).comp_eq_id]⟩

variable (R) in
theorem linearIndependent_cols_submatrix_iff_of_surjective {m₀ n₀ : Type*} {e : m₀ → m}
    (f : n₀ ≃ n) (he : Function.Surjective e) :
    LinearIndependent R (A.submatrix e f).colFun ↔ LinearIndependent R A.colFun :=
  linearIndependent_rows_submatrix_iff_of_surjective (A := Aᵀ) R f he

variable (R) in
@[simp]
theorem linearIndependent_rows_submatrix_iff {m₀ n₀ : Type*} (e : m₀ ≃ m) (f : n₀ ≃ n) :
    LinearIndependent R (A.submatrix e f).rowFun ↔ LinearIndependent R A.rowFun :=
  linearIndependent_rows_submatrix_iff_of_surjective R e f.surjective

variable (R) in
@[simp]
theorem linearIndependent_cols_iff_submatrix {m₀ n₀ : Type*} (e : m₀ ≃ m) (f : n₀ ≃ n) :
    LinearIndependent R (A.submatrix e f).colFun ↔ LinearIndependent R A.colFun :=
  ⟨fun h ↦ linearIndependent_cols_of_submatrix _ _ h,
    fun h ↦ linearIndependent_cols_of_submatrix e.symm f.symm (by simpa)⟩

end Submatrix

section Block

variable {m m₁ m₂ n n₁ n₂ : Type*}

section Ring
variable [Ring R] {A : Matrix m₁ n₁ R} {B : Matrix m₁ n₂ R}
  {C : Matrix m₂ n₁ R} {D : Matrix m₂ n₂ R}

@[simp]
lemma fromCols_zero_right_linearIndependent_rows_iff (A : Matrix m n₁ R) :
    LinearIndependent R (fromCols A (0 : Matrix m n₂ R)).rowFun
    ↔ LinearIndependent R A.rowFun := by
  refine ⟨fun h ↦ h.map_injOn (LinearMap.funLeft R R .inl) ?_, fun h ↦ ?_⟩
  · simp only [InjOn, SetLike.mem_coe, Finsupp.mem_span_range_iff_exists_finsupp, Finsupp.sum,
      LinearMap.funLeft, LinearMap.coe_mk, AddHom.coe_mk, forall_exists_index,
      forall_apply_eq_imp_iff]
    intro c c' h
    suffices ∀ (a : n₁), ∑ x ∈ c.support, c x * A x a = ∑ x ∈ c'.support, c' x * A x a by
      simpa [funext_iff]
    exact fun a ↦ by simpa using congr_fun h a
  /- `Function.ExtendByZero.linearMap` isn't type-heterogeneous, so we need to roll our own. -/
  let f : (n₁ → R) →ₗ[R] (n₁ ⊕ n₂ → R) := {
    toFun := fun x ↦ Sum.elim x 0
    map_add' := fun _ _ ↦ funext <| Sum.rec (by simp) (by simp)
    map_smul' := fun _ _ ↦ funext <| Sum.rec (by simp) (by simp) }
  exact h.map_injOn f <| by simp +contextual [f, InjOn, funext_iff]

@[simp]
lemma fromCols_zero_left_linearIndependent_cols_iff (A : Matrix m n₂ R) :
    (LinearIndependent R (Matrix.fromCols (0 : Matrix m n₁ R) A).rowFun)
    ↔ LinearIndependent R A.rowFun := by
  rw [← fromCols_zero_right_linearIndependent_rows_iff A (n₂ := n₁),
    ← linearIndependent_rows_submatrix_iff R (Equiv.refl m) (Equiv.sumComm n₁ n₂)]
  convert Iff.rfl
  ext i (j | j)
  <;> simp [fromCols]

variable (D) in
lemma fromBlocks_zero₁₁_linearIndependent_rows_iff (hC : LinearIndependent R C.rowFun) :
    LinearIndependent R (Matrix.fromBlocks 0 B C D).rowFun ↔ LinearIndependent R B.rowFun := by
  refine ⟨fun h ↦ ?_, fun hB ↦ ?_⟩
  · rw [← fromCols_zero_left_linearIndependent_cols_iff (n₁ := n₁)]
    exact h.comp Sum.inl Sum.inl_injective
  rw [linearIndependent_iff'] at hC hB ⊢
  intro s c hc i his
  rw [← s.toLeft_disjSum_toRight, Finset.sum_disj_sum] at hc
  simp only [funext_iff, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    Sum.forall, fromBlocks_apply₁₁, zero_apply, mul_zero, Finset.sum_const_zero, fromBlocks_apply₂₁,
    zero_add, fromBlocks_apply₁₂, fromBlocks_apply₂₂] at hc
  have hin {j : m₂} (hj : j ∈ s.toRight) : c (.inr j) = 0 :=
    hC _ (c ∘ .inr) (by simpa [funext_iff] using hc.1) _ hj
  cases i with
  | inr i => exact hin (by simpa)
  | inl i =>
  refine hB s.toLeft (c ∘ .inl) (funext fun j ↦ ?_) _ (by simpa)
  convert hc.2 j
  simp only [Function.comp_apply, Finset.sum_apply, Pi.smul_apply, rowFun_apply, smul_eq_mul,
    fromBlocks_apply₁₂, fromBlocks_apply₂₂, self_eq_add_right]
  rw [Finset.sum_eq_zero]
  exact fun i hi ↦ by simp [hin hi]


variable (B) in
/-- If `A` has linearly independent rows, then `[[A,B],[0,D]]` has linearly independent rows
if and only if `D` does. -/
lemma fromBlocks_zero₁₂_linearIndependent_rows_iff (hA : LinearIndependent R A.rowFun) :
    LinearIndependent R (Matrix.fromBlocks A B 0 D).rowFun ↔
    LinearIndependent R D.rowFun := by
  refine ⟨fun h ↦ ?_, fun hD ↦ ?_⟩
  · rw [← fromCols_zero_left_linearIndependent_cols_iff (n₁ := n₁)]
    exact h.comp Sum.inr Sum.inr_injective
  rw [linearIndependent_iff'] at hA hD ⊢
  intro s c hc i his
  rw [← s.toLeft_disjSum_toRight, Finset.sum_disj_sum] at hc
  simp only [funext_iff, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    Sum.forall, fromBlocks_apply₁₁, fromBlocks_apply₂₁, zero_apply, mul_zero, Finset.sum_const_zero,
    add_zero, fromBlocks_apply₁₂, fromBlocks_apply₂₂] at hc
  have hin {j : m₁} (hj : j ∈ s.toLeft) : c (.inl j) = 0 :=
    hA s.toLeft (c ∘ .inl) (by simpa [funext_iff] using hc.1) _ hj
  cases i with
  | inl i => exact hin (by simpa)
  | inr i =>
  refine hD s.toRight (c ∘ .inr) (funext fun j ↦ ?_) _ (by simpa)
  convert hc.2 j
  simp only [Function.comp_apply, Finset.sum_apply, Pi.smul_apply, rowFun_apply, smul_eq_mul,
    fromBlocks_apply₁₂, fromBlocks_apply₂₂, self_eq_add_left]
  rw [Finset.sum_eq_zero (fun i hi ↦ by simp [hin hi])]

lemma fromBlocks_zero₁₁_linearIndependent_cols_iff (hB : LinearIndependent R B.colFun) :
    LinearIndependent R (Matrix.fromBlocks 0 B C D).colFun ↔ LinearIndependent R C.colFun := by
  rwa [← transpose_rowFun, fromBlocks_transpose, transpose_zero,
    fromBlocks_zero₁₁_linearIndependent_rows_iff, transpose_rowFun]

lemma fromBlocks_zero₂₂_linearIndependent_rows_iff (hB : LinearIndependent R B.rowFun) :
    LinearIndependent R (Matrix.fromBlocks A B C 0).rowFun ↔ LinearIndependent R C.rowFun := by
  rw [← fromBlocks_zero₁₁_linearIndependent_rows_iff A hB]
  convert linearIndependent_rows_submatrix_iff R (Equiv.sumComm m₁ m₂) (Equiv.sumComm n₁ n₂)
  ext (i | i) (j | j) <;>
  rfl

lemma fromBlocks_zero₂₂_linearIndependent_cols_iff (hB : LinearIndependent R C.colFun) :
    LinearIndependent R (Matrix.fromBlocks A B C 0).colFun ↔ LinearIndependent R B.colFun := by
  rwa [← transpose_rowFun, fromBlocks_transpose, transpose_zero,
    fromBlocks_zero₂₂_linearIndependent_rows_iff, transpose_rowFun]

variable (C) in
/-- If `D` has linearly independent rows, then the block matrix `[[A,0],[C,D]]`
has linearly independent rows if and only if `A` does. -/
lemma fromBlocks_zero₂₁_linearIndependent_rows_iff (hD : LinearIndependent R D.rowFun) :
    LinearIndependent R (Matrix.fromBlocks A 0 C D).rowFun ↔ LinearIndependent R A.rowFun := by
  rw [← fromBlocks_zero₁₂_linearIndependent_rows_iff C hD (D := A)]
  convert linearIndependent_rows_submatrix_iff R (Equiv.sumComm m₁ m₂) (Equiv.sumComm n₁ n₂)
  ext (i | i) (j | j) <;> rfl

variable (B) in
/-- If `D` has linearly independent columns, then the block matrix `[[A,B],[0,D]]`
has linearly independent columns if and only if `A` does. -/
lemma fromBlocks_zero₁₂_linearIndependent_cols_iff (hD : LinearIndependent R D.colFun) :
    LinearIndependent R (Matrix.fromBlocks A B 0 D).colFun ↔ LinearIndependent R A.colFun := by
  rwa [← transpose_rowFun, fromBlocks_transpose, Matrix.transpose_zero,
    fromBlocks_zero₂₁_linearIndependent_rows_iff, transpose_rowFun]

variable (C) in
/-- If `A` has linearly independent columns, then the block matrix `[[A,0],[C,D]]`
has linearly independent columns if and only if `D` does. -/
lemma fromBlocks_zero₂₁_linearIndependent_cols_iff (hA : LinearIndependent R A.colFun) :
    LinearIndependent R (Matrix.fromBlocks A 0 C D).colFun ↔ LinearIndependent R D.colFun := by
  rwa [← transpose_rowFun, fromBlocks_transpose, Matrix.transpose_zero,
    fromBlocks_zero₁₂_linearIndependent_rows_iff, transpose_rowFun]

/-- The block matrix `[[A,0],[0,D]]` has linearly independent rows iff `A` and `D` do. -/
@[simp]
lemma fromBlocks_zero₁₁_zero₂₂_linearIndependent_rows_iff :
    LinearIndependent R (Matrix.fromBlocks A 0 0 D).rowFun ↔
    LinearIndependent R A.rowFun ∧ LinearIndependent R D.rowFun := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨h1, h2⟩ ↦ (fromBlocks_zero₁₂_linearIndependent_rows_iff _ h1).2 h2⟩
  · rw [← fromCols_zero_right_linearIndependent_rows_iff (n₁ := n₁)]
    exact h.comp Sum.inl Sum.inl_injective
  rw [← fromCols_zero_left_linearIndependent_cols_iff (n₂ := n₂)]
  exact h.comp Sum.inr Sum.inr_injective

/-- If `B` has full row space, then the block matrix `[[0,B],[C,D]]` has
linearly independent rows if and only if both `B` and `C` do. -/
lemma fromBlocks_zero₁₁_linearIndependent_rows_iff_of_span (hB : span R (range B.rowFun) = ⊤) :
    LinearIndependent R (Matrix.fromBlocks 0 B C D).rowFun
    ↔ LinearIndependent R B.rowFun ∧ LinearIndependent R C.rowFun := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨_, h⟩ ↦ by rwa [fromBlocks_zero₁₁_linearIndependent_rows_iff _ h]⟩
  · rw [← fromCols_zero_left_linearIndependent_cols_iff (n₁ := n₁)]
    refine h.comp Sum.inl Sum.inl_injective
  rw [linearIndependent_iff] at h ⊢
  intro c hc0
  have hsp : Finsupp.linearCombination R D.rowFun c ∈ span R (range B.rowFun) := by simp [hB]
  obtain ⟨d, hd⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hsp
  specialize h (c.embDomain Function.Embedding.inr - d.embDomain Function.Embedding.inl) ?_
  · ext (j | j)
    simp only [map_sub, Finsupp.linearCombination_embDomain]
    · simpa [Finsupp.sum, Finsupp.linearCombination] using congr_fun hc0 j
    convert sub_eq_zero_of_eq <| congr_fun hd.symm j
    rw [Finsupp.linearCombination_apply, Finsupp.sum_sub_index (by simp [funext_iff, sub_smul]),
      Finsupp.sum_embDomain, Finsupp.sum_embDomain]
    simp [Finsupp.linearCombination_apply, Finsupp.sum]
  ext i
  convert DFunLike.congr_fun h <| Function.Embedding.inr i
  rw [Finsupp.sub_apply, Finsupp.embDomain_apply, Finsupp.embDomain_notin_range _ _ _ (by simp),
    sub_zero]

/-- If `C` has full column space, then the block matrix `[[0,B],[C,D]]` has
linearly independent rows if and only if both `B` and `C` do. -/
lemma fromBlocks_zero₁₁_linearIndependent_cols_iff_of_span (hC : span R (range C.colFun) = ⊤) :
    LinearIndependent R (Matrix.fromBlocks 0 B C D).colFun
    ↔ LinearIndependent R B.colFun ∧ LinearIndependent R C.colFun := by
  rw [← transpose_rowFun, fromBlocks_transpose, transpose_zero, and_comm,
    fromBlocks_zero₁₁_linearIndependent_rows_iff_of_span hC, transpose_rowFun, transpose_rowFun]

/- If `C` has linearly independent rows and has finite row type, then `[[0,B],[C,D]]` has
linearly independent columns if and only if both `B` and `C` do. -/
-- lemma foo [Fintype m₂] (hC : LinearIndependent R (fun i ↦ C i)) :
--     LinearIndependent R (fun i ↦ (Matrix.fromBlocks 0 B C D)ᵀ i)
--     ↔ LinearIndependent R (fun i ↦ Cᵀ i) ∧ LinearIndependent R (fun i ↦ Bᵀ i) := by
--   refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
--   ·

end Ring







-- lemma fromBlocks_linearIndependent_iff_of_zero₁₂ {R : Type*} [Ring R] {A : Matrix n l R}
--     {B : Matrix n m R} {D : Matrix o m R} (hA : LinearIndependent R (fun i ↦ Aᵀ i)) :
--     LinearIndependent R (Matrix.fromBlocks A B 0 D) ↔
--     LinearIndependent R (Matrix.fromCols A B) ∧ LinearIndependent R D := by
--   _



-- lemma fromBlocks_zero_linearIndependent_of_diag' {R : Type*} [Ring R] {A : Matrix n l R}
--     {D : Matrix o m R} (hA : LinearIndependent R (fun i ↦ A i))
--     (hD : LinearIndependent R (fun i ↦ D i)) (B : Matrix n m R) :
--     LinearIndependent R (fun i ↦ (Matrix.fromBlocks A 0 B D) i) := by
--   sorry
  -- simp_rw [linearIndependent_iff, Finsupp.linearCombination_apply] at *
  -- intro l hl
  -- specialize hA (l.comapDomain Sum.inl Sum.inl_injective.injOn)
  -- specialize hD (l.comapDomain Sum.inr Sum.inr_injective.injOn)
  -- simp only [Finsupp.sum, Finsupp.comapDomain_support, Finsupp.comapDomain_apply] at hA hD hl
  -- specialize hA ?_
  -- · ext j
  --   convert congr_fun hl (Sum.inl j)
  --   simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  --   convert Finset.sum_preimage Sum.inl l.support Sum.inl_injective.injOn
  --     (fun i ↦ l i * ((Matrix.fromBlocks A B 0 D) i (Sum.inl j)))
  --   simp
  -- ext (i | i)
  -- · exact DFunLike.congr_fun hA i
  -- refine DFunLike.congr_fun (hD ?_) i
  -- ext j
  -- convert congr_fun hl (Sum.inr j)
  -- simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]


-- lemma fromBlocks_zero_linearIndependent_iff {R : Type*} [Ring R]
--     {A : Matrix n l R} {B : Matrix n m R} {D : Matrix o m R} :
--     LinearIndependent R (fun i ↦ (Matrix.fromBlocks A B 0 D) i) ↔
--     LinearIndependent R (fun i ↦ Matrix.fromCols A B i) ∧ LinearIndependent R (fun i ↦ D i) := by
--   refine ⟨fun h ↦ ⟨h.comp Sum.inl Sum.inl_injective, ?_⟩, fun ⟨h1, h2⟩ ↦ ?_⟩
--   · rw [← fromCols_zero_left_linearIndependent_iff]
--     exact h.comp Sum.inr Sum.inr_injective
--   rw [linearIndependent_iff'] at h1 h2 ⊢
--   intro s c hc i his
--   rw [← s.toLeft_disjSum_toRight, Finset.sum_disj_sum] at hc
--   simp [funext_iff] at hc

--   have hin (j : n) (hj : j ∈ s.toLeft) : c (.inl j) = 0 := by

--     refine h1 s.toLeft (c ∘ .inl) ?_ (by simpa) hj
--     ext (k | k)
--     · simpa using congr_fun hc (.inl k)

--     -- simp
--     -- replace hc := congr_fun hc (.inr k)
--     -- simp
--     -- simp at hc

--   -- simp only [hin, zero_smul, Finset.sum_const_zero, zero_add] at hc
--   cases i with
--   | inl i => apply hin _ (by simpa)
--   | inr i =>
--   refine h2 s.toRight (c ∘ .inr) (funext fun j ↦ ?_) i (by simpa)
--   convert congr_fun hc (.inr j)
--   suffices ∑ x ∈ s.toLeft, c (Sum.inl x) * B x j = 0 by simpa
--   exact Finset.sum_eq_zero fun x hx ↦ by simp [hin x hx]
  -- by simpa using congr_fun hc (.inr j)



  -- have := h1 s.toLeft (c ∘ .inl) sorry (.inr i)
  -- refine h1 s.toLeft (c ∘ .inl) ?_ ?_ ?_his
  --   sorry
  -- cases i with
  -- | inl i => exact hin i
  -- | inr i =>

  -- -- refine i.rec hin fun i ↦ ?_
  -- refine h2 s.toRight (c₁ ∘ .inr) (c₂ ∘ .inr) ?_ i (by simpa)
  -- ext j
  -- replace hc := congr_fun hc (.inr j)
  -- simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, fromBlocks_apply₁₂, smul_eq_mul,
  --   fromBlocks_apply₂₂, hin] at hc
  -- convert add_left_cancel hc <;> simp

  -- cases i with
  -- |

  --   inl i =>
  --   refine h1 s.toLeft (c₁ ∘ .inl) (c₂ ∘ .inl) ?_ i (by simpa)
  --   ext (j | j)
  --   · simpa using congr_fun hc (.inl j)


  --   sorry
  --   -- rw [← s.toLeft_disjSum_toRight, Finset.sum_disj_sum, Finset.sum_eq_zero (s := s.toRight),
  --   --   add_zero] at hc
  --   -- · sorry
  --   -- sorry


  -- | inr i =>



  -- rw [← s.toLeft_disjSum_toRight]







end Block

end Matrix
