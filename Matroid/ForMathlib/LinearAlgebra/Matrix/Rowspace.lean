import Mathlib.Data.Matrix.Rank
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Dual
import Mathlib.LinearAlgebra.FiniteDimensional
import Matroid.ForMathlib.LinearAlgebra.LinearIndependent
import Matroid.ForMathlib.LinearAlgebra.StdBasis
import Matroid.ForMathlib.LinearAlgebra.Matrix.NonsingularInverse
import Matroid.ForMathlib.SetSubtype
import Matroid.ForMathlib.Minimal

open Set Function Submodule BigOperators FiniteDimensional

namespace Matrix

variable {l m n o α : Type*} {A B : Matrix m n R} {s : Set m} {t : Set n}

section spaces

abbrev rowFun (A : Matrix m n R) : m → (n → R) := A

abbrev colFun (A : Matrix m n R) : n → (m → R) := Aᵀ

@[simp] theorem rowFun_transpose (A : Matrix m n R) : Aᵀ.rowFun = A.colFun := rfl

@[simp] theorem colFun_transpose (A : Matrix m n R) : Aᵀ.colFun = A.rowFun := rfl

section semiring

variable [Semiring R]

@[pp_dot] def rowSpace (A : Matrix m n R) : Submodule R (n → R) := span R (range A.rowFun)

@[pp_dot] def colSpace (A : Matrix m n R) : Submodule R (m → R) := Aᵀ.rowSpace

@[simp] theorem rowSpace_transpose (A : Matrix m n R) : Aᵀ.rowSpace = A.colSpace := rfl

@[simp] theorem colSpace_transpose (A : Matrix m n R) : Aᵀ.colSpace = A.rowSpace := rfl

@[simp] theorem span_eq_rowSpace (A : Matrix m n R) : span R (range A.rowFun) = A.rowSpace := rfl

@[simp] theorem span_eq_colSpace (A : Matrix m n R) : span R (range A.colFun) = A.colSpace := rfl

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

theorem submatrix_eq_restrict (A : Matrix m n R) (s : Set m) (t : Set n) :
  A.submatrix s.incl t.incl = s.restrict (A.colSubmatrix t) := rfl

theorem image_eq_range_submatrix (A : Matrix m n α) (s : Set m) :
    A '' s = range (A.rowSubmatrix s).rowFun := by
  aesop

theorem rowFun_colSubmatrix_eq [CommRing R] (A : Matrix m n R) (t : Set n) :
    rowFun (colSubmatrix A t) = LinearMap.funLeft R R (↑) ∘ A.rowFun := rfl

theorem colFun_rowSubmatrix_eq [CommRing R] (A : Matrix m n R) (s : Set m) :
    colFun (rowSubmatrix A s) = LinearMap.funLeft R R (↑) ∘ A.colFun := rfl

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

variable {m n R : Type*} {s : Set m} {t : Set n} {A B : Matrix m n R}

section Ring

/-- `A.RowBasis s` means that the rows `A_i : i ∈ s` are a basis for the row space of `A` -/
def RowBasis {R : Type*} [Semiring R] (A : Matrix m n R) (s : Set m) : Prop :=
    LinearIndependent R (A.rowSubmatrix s).rowFun ∧ (A.rowSubmatrix s).rowSpace = A.rowSpace

/-- `A.ColBasis t` means that the columns `A_i : i ∈ t` are a basis for the column space of `A` -/
def ColBasis {R : Type*} [Semiring R] (A : Matrix m n R) (t : Set n) := Aᵀ.RowBasis t

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

theorem cols_linearIndependent_iff {R : Type*} [CommRing R] {A : Matrix m n R} [Fintype n] :
    LinearIndependent R A.colFun ↔ LinearMap.ker A.mulVecLin = ⊥ := by
  rw [←rowFun_transpose, rows_linearIndependent_iff]
  convert Iff.rfl; ext; simp [← mulVec_transpose]

/-- If some column-submatrix of `A` has linearly independent rows, then so does `A`. -/
theorem rows_linearIndependent_of_submatrix {m₀ n₀ : Type*} (e : m₀ ≃ m) (f : n₀ → n)
    (h : LinearIndependent R (A.submatrix e f).rowFun) : LinearIndependent R A.rowFun := by
  classical
  rw [linearIndependent_iff'] at h ⊢
  intro s c hc i his
  rw [←h (s.image e.symm) (c ∘ e) _ (e.symm i) (by simpa)]
  · simp
  ext j
  convert congr_fun hc (f j)
  simp

theorem cols_linearIndependent_of_submatrix {m₀ n₀ : Type*} (e : m₀ → m) (f : n₀ ≃ n)
    (h : LinearIndependent R (A.submatrix e f).colFun) : LinearIndependent R A.colFun :=
  rows_linearIndependent_of_submatrix f e h

theorem rows_linearIndependent_of_reindex (em : m' ≃ m) (en : n' ≃ n)
    (h : LinearIndependent R (A.submatrix em en).rowFun) : LinearIndependent R A.rowFun :=
  rows_linearIndependent_of_submatrix em en h

theorem cols_linearIndependent_of_reindex (em : m' ≃ m) (en : n' ≃ n)
    (h : LinearIndependent R (A.submatrix em en).colFun) : LinearIndependent R A.colFun :=
  cols_linearIndependent_of_submatrix em en h

theorem rows_linearIndependent_reindex (em : m' ≃ m) (en : n' ≃ n)
    (h : LinearIndependent R A.rowFun) : LinearIndependent R (A.submatrix em en).rowFun := by
  rw [show A = (A.submatrix em en).submatrix em.symm en.symm from by simp]  at h
  exact rows_linearIndependent_of_submatrix _ _ h

theorem cols_linearIndependent_reindex (em : m' ≃ m) (en : n' ≃ n)
    (h : LinearIndependent R A.colFun) : LinearIndependent R (A.submatrix em en).colFun := by
  convert rows_linearIndependent_reindex en em h

theorem linearIndependent_rows_of_upper_tri {m₀ m₁ n₀ n₁ : Type*} (A : Matrix m₀ n₀ R)
    (B : Matrix m₀ n₁ R) (C : Matrix m₁ n₁ R) (hA : LinearIndependent R A.rowFun)
    (hC : LinearIndependent R C.rowFun) :
    LinearIndependent R (Matrix.fromBlocks A B 0 C).rowFun := by
  simp_rw [linearIndependent_iff, Finsupp.total_apply] at *
  intro l hl
  specialize hA (l.comapDomain Sum.inl (Sum.inl_injective.injOn _))
  specialize hC (l.comapDomain Sum.inr (Sum.inr_injective.injOn _))
  simp only [Finsupp.sum, Finsupp.comapDomain_support, Finsupp.comapDomain_apply] at hA hC hl
  specialize hA ?_
  · ext j
    convert congr_fun hl (Sum.inl j)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    convert Finset.sum_preimage Sum.inl l.support (Sum.inl_injective.injOn _)
      (fun (i : m₀ ⊕ m₁) ↦ l i * ((Matrix.fromBlocks A B 0 C) i (Sum.inl j)))
    simp
  ext (i | i)
  · exact FunLike.congr_fun hA i
  refine FunLike.congr_fun (hC ?_) i
  ext j
  convert congr_fun hl (Sum.inr j)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]

  convert Finset.sum_preimage Sum.inr l.support (Sum.inr_injective.injOn _)
    (fun (i : m₀ ⊕ m₁) ↦ l i * ((Matrix.fromBlocks A B 0 C) i (Sum.inr j))) ?_
  simp only [Finsupp.mem_support_iff, ne_eq, mem_range, not_exists, Sum.forall, not_false_eq_true,
    implies_true, fromBlocks_apply₁₂, forall_true_left, Sum.inr.injEq, forall_eq,
    fromBlocks_apply₂₂, IsEmpty.forall_iff, and_true]
  exact fun i₀ hi₀ ↦ (hi₀ (FunLike.congr_fun hA i₀)).elim

theorem linearIndependent_rows_of_lower_tri {m₀ m₁ n₀ n₁ : Type*} (A : Matrix m₀ n₀ R)
    (B : Matrix m₁ n₀ R) (C : Matrix m₁ n₁ R) (hA : LinearIndependent R A.rowFun)
    (hC : LinearIndependent R C.rowFun) :
    LinearIndependent R (Matrix.fromBlocks A 0 B C).rowFun := by
  refine rows_linearIndependent_of_reindex (Equiv.sumComm _ _) (Equiv.sumComm _ _) ?_
  convert linearIndependent_rows_of_upper_tri C B A hC hA
  simp only [Equiv.sumComm_apply, fromBlocks_submatrix_sum_swap_right,
    fromBlocks_submatrix_sum_swap_left, submatrix_id_id]

theorem rows_linearIndependent_union_of_upper_zero_block
    (hst : LinearIndependent R (A.submatrix (incl s) (incl t)).rowFun)
    (hstc : LinearIndependent R (A.submatrix (incl sᶜ) (incl tᶜ)).rowFun)
    (h0 : A.submatrix (incl s) (incl tᶜ) = 0) :
    LinearIndependent R A.rowFun := by
  classical
  apply rows_linearIndependent_of_reindex (Equiv.sumCompl (· ∈ s)) (Equiv.sumCompl (· ∈ t))
  convert linearIndependent_rows_of_lower_tri _ (A.submatrix (incl sᶜ) (incl t)) _ hst hstc
  ext (i | i) (j | j); rfl; exact congr_fun (congr_fun h0 i) j; rfl; rfl

theorem rows_linearIndependent_union_of_lower_zero_block
    (hst : LinearIndependent R (A.submatrix (incl s) (incl t)).rowFun)
    (hstc : LinearIndependent R (A.submatrix (incl sᶜ) (incl tᶜ)).rowFun)
    (h0 : A.submatrix (incl sᶜ) (incl t) = 0) :
    LinearIndependent R A.rowFun := by
  rw [←compl_compl s, ←compl_compl t] at hst
  apply rows_linearIndependent_union_of_upper_zero_block hstc hst
  rw [compl_compl]
  exact h0

/-- If a matrix `A` has a 2x2 decomposition into blocks where the top right one is zero,
  and both blocks on the diagonal have linearly independent rows,      [S 0]
  then `A` has linearly independent rows.                              [T R] -/
theorem rows_linearIndependent_skew_union {R : Type*} [CommSemiring R] {s s' : Set m} {t t' : Set n}
    {A : Matrix m n R} (h : LinearIndependent R (A.submatrix (incl s) (incl t)).rowFun)
    (h' : LinearIndependent R (A.submatrix (incl s') (incl t')).rowFun)
    (h0 : A.submatrix (incl s) (incl t') = 0) :
    LinearIndependent R (A.submatrix (incl (s ∪ s')) (incl (t ∪ t'))).rowFun := by
  classical

  rw [submatrix_eq_restrict, linearIndependent_restrict_iff] at *
  intro c (hc : _ = (0 : ↑(t ∪ t') → R)) hss
  simp only [Finsupp.total_apply] at hc h h'

  specialize h' (c.filter (· ∈ s')) ?_ ?_
  · ext ⟨j,hj⟩
    convert congr_fun hc ⟨j,Or.inr hj⟩
    rw [←Finsupp.sum_filter_add_sum_filter_not (p := (· ∈ s')) c, eq_comm]
    simp only [Pi.add_apply, Finsupp.sum_filter_index]
    convert add_zero _
    · simp only [Finset.sum_apply, Finsupp.support_filter,
        Finsupp.mem_support_iff, ne_eq, not_not, Pi.smul_apply, colSubmatrix_apply, smul_eq_mul]
      rw [Finset.sum_eq_zero]
      simp only [Finsupp.mem_support_iff, ne_eq, not_not, Finset.mem_filter, and_imp]
      refine fun i hi0 his' ↦ ?_
      have his : i ∈ s := Or.elim (hss (show i ∈ c.support from by simpa)) id his'.elim
      convert mul_zero _
      exact congr_fun (congr_fun h0 ⟨i, his⟩) ⟨j, hj⟩
    simp
  · rintro x hx
    simp only [Finsupp.support_filter, Finsupp.mem_support_iff, ne_eq, Finset.coe_filter,
      mem_setOf_eq] at hx
    exact hx.2
  refine h c ?_ ?_
  · ext ⟨j,hj⟩
    simp only [Finsupp.total_apply, Pi.zero_apply] at hc ⊢
    replace hc := congr_fun hc ⟨j, Or.inl hj⟩
    convert hc
    simp [colSubmatrix, Finsupp.sum]
  rintro i hi
  refine (hss hi).elim id <| fun his' ↦ False.elim ?_
  rw [Finset.mem_coe, Finsupp.mem_support_iff] at hi
  replace h' := FunLike.congr_fun h' i
  rw [Finsupp.filter_apply_pos (· ∈ s') _ his'] at h'
  exact hi h'

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
    rwa [image_eq_range_submatrix, span_eq_rowSpace]
  · rintro _ ⟨x, -, rfl⟩; exact ⟨x, rfl⟩
  rintro x hx
  obtain ⟨k, c, f, g, rfl⟩ := mem_span_set'.1 hx
  apply sum_smul_mem
  rintro i -
  obtain ⟨_,⟨j,hj,rfl⟩⟩ := f i
  simp only
  obtain (hjs | hjs) := em (j ∈ s)
  · apply subset_span;
    simp only [rowFun_rowSubmatrix_eq, range_restrict, mem_image]
    exact ⟨j,hjs,rfl⟩
  by_contra hsp
  have heq := (h <| (linearIndependent_insert' hjs).2 ⟨hli, fun hsp' ↦ hsp ?_⟩) (subset_insert _ _)
  · exact hjs (heq.symm.subset (mem_insert _ _))
  rwa [image_eq_range_submatrix, span_eq_rowSpace ] at hsp'

theorem colBasis_iff_maximal_linearIndependent : A.ColBasis t ↔
    t ∈ maximals (· ⊆ ·) {b : Set n | LinearIndependent R (A.colSubmatrix b).colFun}  := by
  simp [ColBasis, rowBasis_iff_maximal_linearIndependent, rowFun_rowSubmatrix_eq,
    colFun_colSubmatrix_eq]

theorem exists_colBasis_superset {A : Matrix m n R} {t₀ : Set n}
    (ht₀ : LinearIndependent R (t₀.restrict Aᵀ)) : ∃ t, A.ColBasis t ∧ t₀ ⊆ t :=
  Aᵀ.exists_rowBasis_superset ht₀

theorem exists_colBasis (A : Matrix m n R) : ∃ t, A.ColBasis t :=
  Aᵀ.exists_rowBasis

-- theorem colBasis_submatrix_foo (ht : A.colSpace = (A.colSubmatrix t).colSpace)
--   {t' : Set n} (ht' : t' ⊆ t) :
--     A.ColBasis t' ↔ (A.colSubmatrix t).ColBasis (t.subtypeOrderIso.symm ⟨t',ht'⟩) := by
--   simp_rw [colBasis_iff_maximal_linearIndependent]
--   set t₀ : {x // x ⊆ t} := ⟨t', ht'⟩
--   -- obtain rfl : t' = t₀ := rfl

--   change (t₀ : Set n) ∈ _ ↔ t₀ ∈ (t.subtypeOrderIso.toEquiv.symm) ⁻¹' (maximals (· ≤ · ) _)

--   rw [← mem_preimage]
--   have := t.subtypeOrderEmbedding
--   change _ ∈ t.subtypeOrderEmbedding ⁻¹' _ ↔ _

--   rw [← Equiv.image_eq_preimage, RelIso.coe_toEquiv, ← RelIso.coe_toRelEmbedding,
--     ← RelEmbedding.maximals_image_eq]
--   simp
--   have := (subtypeOrderIso t).toRelEmbedding.maximals_image_eq



-- theorem colBasis_submatrix_foo (hs : A.colSpace = (A.colSubmatrix t).colSpace) (t' : Set t) :
--     (A.colSubmatrix t).ColBasis t' ↔ A.ColBasis (t.subtypeOrderIso t').1 := by
--   have hrw : {b | LinearIndependent R ((A.colSubmatrix t).colSubmatrix b).colFun} =
--     t.subtypeOrderIso ⁻¹' {r | LinearIndependent R (r.1.restrict A.colFun)}
--   · ext r
--     sorry
--   simp_rw [colBasis_iff_maximal_linearIndependent]
--   rw [← mem_preimage]


--   simp_rw [colBasis_iff_maximal_linearIndependent, hrw, RelIso.maximals_preimage_eq,
--     ← mem_preimage]

--   simp
--   convert Iff.rfl




end DivisionRing
section Field

variable {K : Type*} [Field K] {A : Matrix m n K}

theorem subset_rows_notLinearIndependent_iff [Fintype m] :
    ¬ LinearIndependent K (A.rowSubmatrix s).rowFun ↔
      ∃ c, A.vecMul c = 0 ∧ c ≠ 0 ∧ support c ⊆ s := by
  simp only [rowFun_rowSubmatrix_eq, Fintype.linearIndependent_restrict_iff, ne_eq,
    vecMul, dotProduct, support_subset_iff, not_imp_comm]
  refine ⟨fun ⟨c,h,⟨i, _, hci⟩,h'⟩ ↦
    ⟨c, by convert h; simp, by rintro rfl; exact hci rfl, h'⟩,
    fun ⟨c,h,hi,h'⟩ ↦ ⟨c, by convert h; simp, ?_, h'⟩⟩
  by_contra hc; push_neg at hc
  exact hi (funext fun i ↦ (em (i ∈ s)).elim (hc i) (h' i))

theorem subset_cols_notLinearIndependent_iff [Fintype n] :
    ¬ LinearIndependent K (A.colSubmatrix t).colFun ↔
      ∃ c, A.mulVec c = 0 ∧ c ≠ 0 ∧ support c ⊆ t := by
  rw [←rowFun_transpose, colSubmatrix_transpose, subset_rows_notLinearIndependent_iff]
  simp_rw [vecMul_transpose]

theorem toLin'_transpose [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] :
    toLin' Aᵀ = (Module.piEquiv n K K).symm.comp
      (A.toLin'.dualMap.comp (Module.piEquiv m K K).toLinearMap) := by
  ext i j; simp [Module.piEquiv_apply_apply, ←Pi.single_mul_right_apply (A · j)]

theorem toLin'_dualMap [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] :
    A.toLin'.dualMap =
      ((Module.piEquiv n K K).comp (toLin' Aᵀ)).comp (Module.piEquiv m K K).symm.toLinearMap := by
  rw [toLin'_transpose]; aesop

theorem colSpace_eq_top_iff_linearIndependent_rows [Fintype m] :
    A.colSpace = ⊤ ↔ LinearIndependent K A.rowFun := by
  rw [←not_iff_not, ←Ne.def, ←lt_top_iff_ne_top, ←orthSpace_lt_iff_lt, orthSpace_top,
    bot_lt_iff_ne_bot, Submodule.ne_bot_iff, Fintype.not_linearIndependent_iff]
  simp only [mem_orthSpace_iff', ne_eq, ← smul_eq_mul]
  refine ⟨fun ⟨x,hx,h0⟩ ↦ ⟨x, ?_, ne_iff.mp h0⟩, fun ⟨x,hx,h0⟩ ↦ ⟨x, fun y hy ↦ ?_, ne_iff.mpr h0⟩⟩
  · convert funext fun a ↦ hx (A · a) <| subset_span ⟨a, rfl⟩
    simp
  apply dotProduct_eq_zero_of_mem_span hy
  rintro _ ⟨i,hi,rfl⟩
  convert congr_fun hx i
  simp only [dotProduct, rowFun_transpose, transpose_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]

theorem rowSpace_eq_top_iff_linearIndependent_cols [Fintype n] :
    A.rowSpace = ⊤ ↔ LinearIndependent K A.colFun := by
  rw [←colSpace_transpose, colSpace_eq_top_iff_linearIndependent_rows, rowFun_transpose]

theorem ColBasis.rows_linearIndependent [Fintype m] (ht : A.ColBasis t)
    (hA : LinearIndependent K A.rowFun) : LinearIndependent K (A.colSubmatrix t).rowFun := by
  rw [←colSpace_eq_top_iff_linearIndependent_rows, Submodule.eq_top_iff']
  rw [←colSpace_eq_top_iff_linearIndependent_rows] at hA
  exact fun x ↦ by simp [hA ▸ ht.colSpace_eq]

theorem RowBasis.cols_linearIndependent [Fintype n] (hs : A.RowBasis s)
    (hA : LinearIndependent K Aᵀ) : LinearIndependent K (s.restrict A)ᵀ :=
  hs.colBasis_transpose.rows_linearIndependent hA

variable {m₁ m₂ : Type*} {A₁ : Matrix m₁ n K} {A₂ : Matrix m₂ n K}

theorem cols_linearIndependent_of_rowSpace_le_rowSpace  (h : A₁.rowSpace ≤ A₂.rowSpace) {t : Set n}
    (ht : LinearIndependent K (A₁.colSubmatrix t).colFun) :
    LinearIndependent K (A₂.colSubmatrix t).colFun := by
  rw [linearIndependent_iff'] at ht ⊢
  by_contra h'; push_neg at h'; obtain ⟨t₀, c, hne, i₀, hit₀, hnz⟩ := h'
  refine hnz <| ht t₀ c ?_ _ hit₀
  ext i
  simp only [colSubmatrix_transpose, rowSubmatrix_apply, Finset.sum_apply,
    Pi.smul_apply, transpose_apply, smul_eq_mul, Pi.zero_apply]
  simp only [colSubmatrix_transpose, rowSubmatrix_apply] at hne

  have hrs := h (subset_span <| mem_range_self i : A₁ i ∈ A₁.rowSpace)
  rw [rowSpace, mem_span_set'] at hrs
  obtain ⟨k, d, g, h_eq⟩ := hrs
  simp only [←h_eq, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun ind _ ↦ ?_)
  simp_rw [mul_comm (d _), ← mul_assoc, ← Finset.sum_mul]
  obtain ⟨_, i', hi', rfl⟩:=  g ind
  simp only [mul_eq_zero]
  left
  convert congr_fun hne i'
  simp

/-- Matrices with the same row space have the same column dependencies -/
theorem cols_linearIndependent_iff_of_rowSpaces_eq (h : A₁.rowSpace = A₂.rowSpace) {t : Set n} :
    LinearIndependent K (A₁.colSubmatrix t).colFun
      ↔ LinearIndependent K (A₂.colSubmatrix t).colFun := by
  exact ⟨fun h' ↦ cols_linearIndependent_of_rowSpace_le_rowSpace h.le h',
    fun h' ↦ cols_linearIndependent_of_rowSpace_le_rowSpace h.symm.le h'⟩

/-- Matrices with the same row space have the same column bases -/
theorem colBases_eq_of_rowSpaces_eq (h : A₁.rowSpace = A₂.rowSpace) :
    A₁.ColBasis = A₂.ColBasis := by
  ext
  simp_rw [colBasis_iff_maximal_linearIndependent, cols_linearIndependent_iff_of_rowSpaces_eq h]

/-- Matrices with the same column space have the same row dependencies-/
theorem rowsLinearIndependent_iff_of_colSpaces_eq {A₁ : Matrix m n₁ K} {A₂ : Matrix m n₂ K}
    (h : A₁.colSpace = A₂.colSpace) :
    LinearIndependent K (A₁.rowSubmatrix s).rowFun
      ↔ LinearIndependent K (A₂.rowSubmatrix s).rowFun := by
  rw [←rowSpace_transpose, ←rowSpace_transpose] at h
  exact cols_linearIndependent_iff_of_rowSpaces_eq h

/-- Matrices with the same column space have the same row bases -/
theorem rowBases_eq_of_colSpaces_eq {A₁ : Matrix m n₁ K} {A₂ : Matrix m n₂ K}
    (h : A₁.colSpace = A₂.colSpace) : A₁.RowBasis = A₂.RowBasis := by
  ext s
  rw [←rowSpace_transpose, ←rowSpace_transpose] at h
  simpa using congr_fun (colBases_eq_of_rowSpaces_eq h) s

theorem RowBasis.colBases_eq (hs : A.RowBasis s) : (A.rowSubmatrix s).ColBasis = A.ColBasis :=
  colBases_eq_of_rowSpaces_eq hs.rowSpace_eq

theorem ColBasis.rowBases_eq (hs : A.ColBasis t) : (A.colSubmatrix t).RowBasis = A.RowBasis :=
  colBases_eq_of_rowSpaces_eq hs.rowSpace_eq

theorem RowBasis.submatrix_colBasis (hs : A.RowBasis s) (ht : A.ColBasis t) :
    (A.rowSubmatrix s).ColBasis t := by
  rwa [colBases_eq_of_rowSpaces_eq hs.rowSpace_eq]

theorem ColBasis.submatrix_rowBasis (ht : A.ColBasis t) (hs : A.RowBasis s) :
    (A.colSubmatrix t).RowBasis s := by
  rwa [rowBases_eq_of_colSpaces_eq ht.colSpace_eq]

/-- If an `m × n` matrix `A` with entries in `R` has linearly independent rows,
    a column basis for `A` gives a basis for `m → R`. -/
noncomputable def ColBasis.basisFun [Fintype m] (ht : A.ColBasis t)
  (hA : LinearIndependent K A.rowFun) : Basis t K (m → K) :=
    (Basis.span ht.linearIndependent).map <| LinearEquiv.ofTop _ <| eq_top_iff'.2 fun x ↦
    ( by
      rw [span_eq_colSpace, ht.colSpace_eq, colSpace_eq_top_iff_linearIndependent_rows.2 hA]
      trivial )

@[simp] theorem ColBasis.basisFun_apply [Fintype m] (ht : A.ColBasis t)
    (hA : LinearIndependent K A.rowFun) (j : t) : ht.basisFun hA j = (A · j) := by
  ext x; exact congr_fun (Basis.span_apply ht.linearIndependent j) x

noncomputable def RowBasis.basisFun [Fintype n] (hs : A.RowBasis s)
    (hA : LinearIndependent K A.colFun) : Basis s K (n → K) :=
  hs.colBasis_transpose.basisFun hA

@[simp] theorem RowBasis.basisFun_apply [Fintype n] (hs : A.RowBasis s)
    (hA : LinearIndependent K Aᵀ) (i : s) : hs.basisFun hA i = A i := by
  ext; simp [basisFun]

end Field
section NullSpace

variable {K : Type*} [Field K] [Fintype n] {m₁ m₂ : Type*} [Fintype m₁] [Fintype m₂]
  {A : Matrix m n K} {A₁ : Matrix m₁ n K} {A₂ : Matrix m₂ n K} {t : Set n}

@[pp_dot] noncomputable def nullSpace {R : Type*} [CommRing R] (A : Matrix m n R) :
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

theorem colBasis_iff_aux (h : A₁.rowSpace = A₂.nullSpace) (h₁ : LinearIndependent K A₁.rowFun)
    (h₂ : LinearIndependent K A₂.rowFun) (ht : A₁.ColBasis t) :  A₂.ColBasis tᶜ := by
  classical
  refine ⟨by_contra fun hld ↦?_ , ?_⟩
  · rw [rowFun_rowSubmatrix_eq, Fintype.linearIndependent_restrict_iff] at hld
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
  simp_rw [mulVec, dotProduct, vecMulLinear_apply, vecMul, dotProduct] at h0

  have h01 := Fintype.linearIndependent_iff.1 ht.linearIndependent (fun x ↦ vecMul c A₂ x) ?_
  · refine Fintype.linearIndependent_iff.1 h₂ c <| funext fun j ↦ ?_
    obtain (hjt | hjt) := em (j ∈ t)
    · convert h01 ⟨j,hjt⟩ using 1; simp [vecMul, dotProduct]
    convert congr_fun hc0 ⟨j,hjt⟩; simp

  rw [←h0]
  simp only [colSubmatrix_transpose, rowSubmatrix_apply, ←Finset.sum_fn]
  rw [← Finset.sum_subset (s₁ := t.toFinset) (by simp)]
  · convert (Finset.sum_toFinset_eq_subtype (· ∈ t) _).symm; ext;
    simp [mul_comm, vecMul, dotProduct]

  simp only [Finset.mem_univ, mem_toFinset, forall_true_left]
  rintro x hxt
  ext i;
  simp only [Pi.zero_apply, mul_eq_zero]; right
  convert congr_fun hc0 ⟨x, hxt⟩
  simp

theorem colBasis_iff_colBasis_compl_of_orth (h : A₁.rowSpace = A₂.nullSpace) :
    A₁.ColBasis t ↔ A₂.ColBasis tᶜ := by
  obtain ⟨b₁, hb₁⟩ := A₁.exists_rowBasis
  obtain ⟨b₂, hb₂⟩ := A₂.exists_rowBasis
  rw [←orthSpace_rowSpace_eq_nullSpace, ←hb₁.rowSpace_eq, ←hb₂.rowSpace_eq] at h
  rw [←hb₁.colBases_eq, ←hb₂.colBases_eq]
  have _ := hb₁.finite.fintype
  have _ := hb₂.finite.fintype
  refine ⟨colBasis_iff_aux (by simp [h]) hb₁.linearIndependent hb₂.linearIndependent, fun h' ↦ ?_⟩
  rw [←compl_compl t]
  refine colBasis_iff_aux ?_ hb₂.linearIndependent hb₁.linearIndependent h'
  rw [←orthSpace_rowSpace_eq_nullSpace, h, orthSpace_orthSpace]

end NullSpace
section Rank

noncomputable def rank' {R : Type*} [CommRing R] (A : Matrix m n R) : ℕ :=
  finrank R <| colSpace A

theorem rank'_eq_finrank_mulVecLin {R : Type*} [CommRing R] [Fintype n] (A : Matrix m n R) :
    A.rank' = finrank R (LinearMap.range A.mulVecLin) := by
  rw [rank', colSpace_eq_lin_range]

variable {K : Type*} [Field K] {A : Matrix m n K}

theorem ncard_colBasis (ht : A.ColBasis t) : t.ncard = A.rank' := by
  obtain (hfin | hinf) := t.finite_or_infinite
  · have _ := hfin.fintype
    rw [rank', finrank, rank_eq_card_basis ht.basis, Cardinal.toNat_cast, ←Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq]
  rw [hinf.ncard, rank', @finrank_of_infinite_dimensional _ _ _ _ _ fun hfin ↦ hinf <| ?_]
  have _ := ht.basis.linearIndependent.finite_index
  exact toFinite t

theorem ncard_rowBasis_eq_ncard_colBasis (hs : A.RowBasis s) (ht : A.ColBasis t) :
    s.ncard = t.ncard := by
  have ht' := hs.submatrix_colBasis ht
  refine s.finite_or_infinite.elim (fun hfin ↦ ?_) (fun hinf ↦ ?_)
  · have _ := hfin.fintype
    have hb := ht'.basisFun hs.linearIndependent
    have _ := hb.linearIndependent.fintype_index
    rw [←Nat.card_coe_set_eq, ←Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, ← finrank_eq_card_basis hb, finrank_fintype_fun_eq_card]
  rw [hinf.ncard, Infinite.ncard]
  refine fun htfin ↦ hinf ?_
  have _ := htfin.fintype
  have hs' := ht.submatrix_rowBasis hs
  have hb := hs'.basisFun ht.linearIndependent
  have _ := hb.linearIndependent.fintype_index
  exact s.toFinite

theorem ncard_rowBasis (hs : A.RowBasis s) : s.ncard = A.rank' := by
  obtain ⟨t, ht⟩ := A.exists_colBasis
  rw [ncard_rowBasis_eq_ncard_colBasis hs ht, ncard_colBasis ht]

theorem rank'_transpose (A : Matrix m n K) : Aᵀ.rank' = A.rank' := by
  obtain ⟨s, hs⟩ := A.exists_rowBasis
  obtain ⟨t, ht⟩ := A.exists_colBasis
  rw [←ncard_colBasis ht, ←ncard_rowBasis_eq_ncard_colBasis hs ht,
    ←ncard_colBasis hs.colBasis_transpose]

end Rank

end Matrix

section Basis

variable {R m n : Type*} [CommRing R] {U : Submodule R (n → R)}

/-- Given a basis for a submodule `U` of `n → R`, put its vectors as the rows of a matrix,
  whose row space will then be `U` . -/
noncomputable def Basis.toRowMatrix (b : Basis m R U) : Matrix m n R :=
  Matrix.of (fun i j ↦ (b i : (n → R)) j)

@[simp] theorem Basis.toRowMatrix_apply (b : Basis m R U) (i : m) (j : n) :
  b.toRowMatrix i j = (b i : n → R) j := rfl

@[simp] theorem Basis.toRowMatrix_rowSpace (b : Basis m R U) : b.toRowMatrix.rowSpace = U := by
  convert congr_arg (fun (W : Submodule R U) ↦ W.map (Submodule.subtype U)) b.span_eq
  · rw [Matrix.rowSpace, map_span]
    convert rfl
    ext x
    simp only [coeSubtype, mem_image, mem_range, exists_exists_eq_and, toRowMatrix]
    rfl
  simp

end Basis



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
