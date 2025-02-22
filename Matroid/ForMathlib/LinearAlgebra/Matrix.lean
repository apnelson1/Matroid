import Mathlib.Data.Matrix.Rank
import Matroid.ForMathlib.LinearAlgebra.LinearIndepOn

namespace Matrix

section Cardinal

open Set Submodule Cardinal

universe u

variable {m m₁ m₂ n n₁ n₂ R : Type*} {A A₁ A₂ : Matrix m n R} {s : Set m} {t : Set n}

noncomputable def cRank [Semiring R] (A : Matrix m n R) : Cardinal :=
  Module.rank R (Submodule.span R (Set.range Aᵀ))

noncomputable def rank' [Semiring R] (A : Matrix m n R) : ℕ := A.cRank.toNat

lemma rank'_eq_rank [CommRing R] [Fintype n] (A : Matrix m n R) : A.rank' = A.rank := by
  rw [rank', cRank, rank, ← Module.finrank, @range_mulVecLin]

def IsRowBasis (R : Type*) [Semiring R] (A : Matrix m n R) (s : Set m) :=
    Maximal (LinearIndepOn R A ·) s

lemma exists_isRowBasis (R : Type*) [DivisionRing R] (A : Matrix m n R) :
    ∃ s, A.IsRowBasis R s := by
  obtain ⟨s, -, hs⟩ := (linearIndepOn_empty R A).exists_maximal (subset_univ _)
  exact ⟨s, by simpa using hs⟩

def IsColBasis (R : Type*) [Semiring R] (A : Matrix m n R) := Aᵀ.IsRowBasis R

lemma IsRowBasis.isColBasis_transpose [Semiring R] (h : A.IsRowBasis R s) : Aᵀ.IsColBasis R s :=
  h

lemma exists_isColBasis (R : Type*) [DivisionRing R] (A : Matrix m n R) : ∃ s, A.IsColBasis R s :=
  Aᵀ.exists_isRowBasis R

lemma IsColBasis.isRowBasis_transpose [Semiring R] (h : A.IsColBasis R t) : Aᵀ.IsRowBasis R t :=
  h

lemma IsRowBasis.isRowBasis_univ_submatrix [Semiring R] (h : A.IsRowBasis R s) :
    (A.submatrix (fun x : s ↦ x) id).IsRowBasis R univ := by
  sorry

lemma IsColBasis.isColBasis_univ_submatrix [Semiring R] (h : A.IsColBasis R t) :
    (A.submatrix id (fun x : t ↦ x)).IsColBasis R univ := by
  sorry

lemma IsRowBasis.span_eq [Field R] (hs : A.IsRowBasis R s) :
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

lemma IsRowBasis.span_submatrix_eq [Field R] (hs : A.IsRowBasis R s) :
    span R (range (A.submatrix (fun x : s ↦ x) id)) = span R (range A) := by
  simp [← hs.span_eq]

lemma IsColBasis.span_submatrix_eq [Field R] (hs : A.IsColBasis R t) :
    span R (range (A.submatrix id (fun x : t ↦ x))ᵀ) = span R (range Aᵀ) := by
  simp [← hs.span_eq]

noncomputable def IsRowBasis.basis [Field R] (hs : A.IsRowBasis R s) :
    Basis s R <| span R (range A) :=
  (Basis.span hs.prop.linearIndependent).map <| LinearEquiv.ofEq _ _ <|
    by rw [← image_eq_range, hs.span_eq]

lemma IsRowBasis.ncard_eq [Field R] (h : A.IsRowBasis R s) : s.ncard = Aᵀ.rank' := by
  simpa using congr_arg Cardinal.toNat h.basis.mk_eq_rank

lemma IsColBasis.ncard_eq [Field R] (h : A.IsColBasis R t) : t.ncard = A.rank' := by
  simpa using congr_arg Cardinal.toNat h.basis.mk_eq_rank

theorem linearIndepOn_col_le_of_span_row_le {m₁ m₂ : Type*} [CommRing R] {A₁ : Matrix m₁ n R}
    {A₂ : Matrix m₂ n R} (h : span R (range A₁) ≤ span R (range A₂)) :
    LinearIndepOn R A₁ᵀ ≤ LinearIndepOn R A₂ᵀ := by
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

lemma linearIndepOn_col_eq_of_span_row_eq [CommRing R] {A₁ : Matrix m₁ n R} {A₂ : Matrix m₂ n R}
    (h : span R (range A₁) = span R (range A₂)) : LinearIndepOn R A₁ᵀ = LinearIndepOn R A₂ᵀ :=
  (linearIndepOn_col_le_of_span_row_le h.le).antisymm
    (linearIndepOn_col_le_of_span_row_le h.symm.le)

theorem linearIndepOn_row_eq_of_span_col_eq {n₁ n₂ : Type*} [CommRing R] {A₁ : Matrix m n₁ R}
    {A₂ : Matrix m n₂ R} (h : span R (range A₁ᵀ) = span R (range A₂ᵀ)) :
    LinearIndepOn R A₁ = LinearIndepOn R A₂ := by
  simpa using linearIndepOn_col_eq_of_span_row_eq h

lemma isColBasis_iff_of_span_row_eq [CommRing R] {A₁ : Matrix m₁ n R} {A₂ : Matrix m₂ n R}
    (h : span R (range A₁) = span R (range A₂)) (t : Set n) :
    A₁.IsColBasis R t ↔ A₂.IsColBasis R t := by
  rw [IsColBasis, IsRowBasis, linearIndepOn_col_eq_of_span_row_eq h, IsColBasis, IsRowBasis]

lemma IsColBasis.submatrix_isColBasis [Field R] (ht : A.IsColBasis R t) (hs : A.IsRowBasis R s) :
    (A.submatrix (fun x : s ↦ x) id).IsColBasis R t :=
  (isColBasis_iff_of_span_row_eq hs.span_submatrix_eq _).2 ht

lemma IsRowBasis.submatrix_isRowBasis [Field R] (hs : A.IsRowBasis R s) (ht : A.IsColBasis R t) :
    (A.submatrix id (fun x : t ↦ x)).IsRowBasis R s :=
  IsColBasis.submatrix_isColBasis (A := Aᵀ) hs ht

-- lemma IsRowBasis.submatrix_row_linearIndependent [Field R] (hs : A.IsRowBasis R s) :
--     LinearIndependent R (A.submatrix (fun x : s ↦ x) id) :=
--   hs.prop.linearIndependent

lemma span_col_eq_top_of_linearIndependent_row [Fintype m] [Field R] (h : LinearIndependent R A) :
    span R (range Aᵀ) = ⊤ := by
  classical
  obtain ⟨t, ht⟩ := A.exists_isColBasis
  have htfin := Finite.fintype ht.prop.linearIndependent.finite
  have hs : A.IsRowBasis R univ := by simpa +contextual [IsRowBasis, maximal_subset_iff]
  suffices h' : Module.finrank R (span R (range (A.submatrix id (fun x : t ↦ x))ᵀ))
    = Module.finrank R (m → R) by
    rw [← top_le_iff, ← eq_top_of_finrank_eq h']
    exact span_mono <| by simp
  rw [← rank_eq_finrank_span_cols, rank_eq_finrank_span_row,
    finrank_span_eq_card (by simpa using (hs.submatrix_isRowBasis ht).prop),
    Module.finrank_fintype_fun_eq_card]

lemma span_row_eq_top_of_linearIndependent_col [Fintype n] [Field R] (h : LinearIndependent R Aᵀ) :
    span R (range A) = ⊤ := by
  rw [← Aᵀ.span_col_eq_top_of_linearIndependent_row h, transpose_transpose]


lemma rank'_transpose [Field R] (A : Matrix m n R) : Aᵀ.rank' = A.rank' := by
  classical
  obtain ⟨s, hs⟩ := A.exists_isRowBasis
  obtain ⟨t, ht⟩ := A.exists_isColBasis
  set A' := A.submatrix (fun x : s ↦ x) (fun x : t ↦ x)
  have hcol : A'.IsColBasis R univ :=
    ht.isColBasis_univ_submatrix.submatrix_isColBasis (hs.submatrix_isRowBasis ht)
  have hrow : A'.IsRowBasis R univ :=
    hs.isRowBasis_univ_submatrix.submatrix_isRowBasis (ht.submatrix_isColBasis hs)

  rw [← hs.ncard_eq, ← ht.ncard_eq, show t.ncard = A'.rank' by simpa using hcol.ncard_eq,
    show s.ncard = A'ᵀ.rank' by simpa using hrow.ncard_eq]
  have := hcol.ncard_eq
  simp at this


end Cardinal

end Matrix
