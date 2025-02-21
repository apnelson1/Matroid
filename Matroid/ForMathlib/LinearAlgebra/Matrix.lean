import Mathlib.Data.Matrix.Rank
import Matroid.ForMathlib.LinearAlgebra.LinearIndepOn

namespace Matrix

section Cardinal

open Set Submodule Cardinal

universe u

variable {m m₁ m₂ n n₁ n₂ R : Type*} {A A₁ A₂ : Matrix m n R} {s : Set m} {t : Set n}

noncomputable def cRank [Semiring R] (A : Matrix m n R) : Cardinal :=
  Module.rank R (Submodule.span R (Set.range Aᵀ))

lemma cRank_toNat [CommRing R] [Fintype n] (A : Matrix m n R) : (cRank A).toNat = A.rank := by
  rw [cRank, rank, ← Module.finrank, @range_mulVecLin]


def IsRowBasis (R : Type*) [Semiring R] (A : Matrix m n R) (s : Set m) :=
    Maximal (LinearIndepOn R A ·) s

lemma exists_isRowBasis (R : Type*) [DivisionRing R] (A : Matrix m n R) :
    ∃ s, A.IsRowBasis R s := by
  obtain ⟨s, -, hs⟩ := (linearIndepOn_empty R A).exists_maximal (subset_univ _)
  exact ⟨s, by simpa using hs⟩

def IsColBasis (R : Type*) [Semiring R] (A : Matrix m n R) := Aᵀ.IsRowBasis R

lemma exists_isColBasis (R : Type*) [DivisionRing R] (A : Matrix m n R) : ∃ s, A.IsColBasis R s :=
  Aᵀ.exists_isRowBasis R

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
    LinearIndepOn R A₁ᵀ = LinearIndepOn R A₂ᵀ := by
  simpa

lemma isColBasis_iff_of_span_row_eq [CommRing R] {A₁ : Matrix m₁ n R} {A₂ : Matrix m₂ n R}
    (h : span R (range A₁) = span R (range A₂)) (t : Set n) :
    A₁.IsColBasis R t ↔ A₂.IsColBasis R t := by
  rw [IsColBasis, IsRowBasis, linearIndepOn_col_eq_of_span_row_eq h, IsColBasis, IsRowBasis]

lemma IsRowBasis.submatrix_isColBasis [Field R] (hs : A.IsRowBasis R s) (ht : A.IsColBasis R t) :
    (A.submatrix (fun x : s ↦ x) id).IsColBasis R t :=
  (isColBasis_iff_of_span_row_eq hs.span_submatrix_eq _).2 ht

lemma IsColBasis.submatrix_isRowBasis [Field R] (ht : A.IsColBasis R t) (hs : A.IsRowBasis R s) :
    (A.submatrix id (fun x : t ↦ x)).IsRowBasis R s :=
  IsRowBasis.submatrix_isColBasis (A := Aᵀ) ht hs

lemma span_col_eq_top_of_linearIndependent_row [Fintype m] [Field R] (h : LinearIndependent R A) :
    span R (range Aᵀ) = ⊤ := by
  classical
  obtain ⟨t, ht⟩ := A.exists_isColBasis
  have hs : A.IsRowBasis R univ := by simpa +contextual [IsRowBasis, maximal_subset_iff]
  set A' := A.submatrix id (fun x : t ↦ x)
  suffices h' : span R (range A'ᵀ) = ⊤ by
    rw [← top_le_iff, ← h']
    exact span_mono <| by simp [A']
  apply eq_top_of_finrank_eq
  have htfin := Finite.fintype ht.prop.linearIndependent.finite
  rw [← A'.rank_eq_finrank_span_cols, A'.rank_eq_finrank_span_row,
    finrank_span_eq_card (by simpa using (ht.submatrix_isRowBasis hs).prop),
    Module.finrank_fintype_fun_eq_card]

lemma span_row_eq_top_of_linearIndependent_col [Fintype n] [Field R] (h : LinearIndependent R Aᵀ) :
    span R (range A) = ⊤ := by
  rw [← Aᵀ.span_col_eq_top_of_linearIndependent_row h, transpose_transpose]





-- lemma foo5 {m n : Type u} {s : Set m} {t : Set n} {A : Matrix m n R} [Field R]
--     (hs : A.IsRowBasis R s) (ht : A.IsColBasis R t) : #s = #t := by
--   have := hs.submatrix_isColBasis ht

end Cardinal

end Matrix
