import Mathlib.Data.Matrix.Rank

variable {ι m n R : Type _} [Field R] {A B : Matrix m n R} {s : Set m} {t : Set n}

open Set Function Submodule BigOperators

namespace Matrix

/-- The rows in `s` index a basis for the row space of `A` -/
def RowBasis (A : Matrix m n R) (s : Set m) :=
    LinearIndependent R (A.submatrix ((↑) : s → m) id)
  ∧ span R (range <| A.submatrix ((↑) : s → m) id) = span R (range A)

noncomputable def RowBasis.basis (h : A.RowBasis s) : Basis s R (span R (range A)) :=
  (Basis.span h.1).map <| LinearEquiv.ofEq _ _ h.2

@[simp] theorem RowBasis.basis_apply (h : A.RowBasis s) (i : s) : h.basis i = A i := by
  ext; simp [Matrix.RowBasis.basis, Basis.span_apply]

theorem RowBasis.linearIndependent (h : A.RowBasis s) :
  LinearIndependent R (A.submatrix ((↑) : s → m) id) := h.1

theorem RowBasis.span_eq (h : A.RowBasis s) :
  span R (range <| A.submatrix ((↑) : s → m) id) = span R (range A) := h.2

/-- The columns in `t` index a basis for the column space of `A` -/
def ColBasis (A : Matrix m n R) (t : Set n) := Aᵀ.RowBasis t

noncomputable def ColBasis.basis (h : A.ColBasis t) : Basis t R (span R (range Aᵀ)) :=
  RowBasis.basis h

@[simp] theorem ColBasis.basis_apply (h : A.ColBasis t) (j : t) : h.basis j = Aᵀ j := by
  ext; simp [ColBasis.basis]

theorem ColBasis.linearIndependent (h : A.ColBasis t) :
    LinearIndependent R (A.submatrix id ((↑) : t → n))ᵀ :=
  h.1

theorem ColBasis.span_eq (h : A.ColBasis t) :
    span R (range <| (A.submatrix id ((↑) : t → n))ᵀ) = span R (range Aᵀ) :=
  h.2

@[simp] theorem RowBasis_transpose : Aᵀ.RowBasis t ↔ A.ColBasis t := Iff.rfl
@[simp] theorem ColBasis_transpose : Aᵀ.ColBasis s ↔ A.RowBasis s := Iff.rfl

-- theorem Finset.sum_coe_sort_eq_subtype {β : Type u} {α : Type v} [Fintype α] (s : Set α) [Fintype s]
--   [AddCommMonoid β] (f : s → β) :
--     (∑ x : s, f x) = ∑ x : α, if hx : x ∈ s then f ⟨x,hx⟩ else 0 := sorry

theorem _root_.Fintype.subtype_notLinearIndependent_iff [Fintype ι] [CommSemiring R]
  [AddCommMonoid M] [Module R M] {s : Set ι} {v : ι → M} :
    ¬ LinearIndependent R (s.restrict v) ↔ ∃ c : ι → R, ∑ i, c i • v i = 0 ∧ (∃ i ∈ s, c i ≠ 0)
      ∧ ∀ i, i ∉ s → c i = 0 := by
  classical
  have _ := s.toFinite.fintype
  rw [Fintype.not_linearIndependent_iff]
  refine ⟨fun ⟨c', hc', i₀, hi₀⟩ ↦ ?_, fun ⟨c, hc0, ⟨i₀, hi₀, hne⟩, hi⟩ ↦ ?_⟩
  · set f := fun i ↦ if hi : i ∈ s then c' ⟨i,hi⟩ • (v i) else 0
    refine ⟨fun i ↦ if hi : i ∈ s then c' ⟨i,hi⟩ else 0, ?_, ⟨i₀, i₀.prop, by simpa⟩,
      fun i hi ↦ by simp [hi]⟩
    rw [←hc']
    convert Finset.sum_congr_set s f (fun i ↦ (c' i) • v i) (fun _ h ↦ by simp [h])
      (fun _ h ↦ by simp [h])
    · simp only; split_ifs; rfl; exact zero_smul _ _
  refine ⟨fun i ↦ c i, ?_, ⟨⟨i₀, hi₀⟩, hne⟩⟩
  rw [←hc0, eq_comm]
  convert Finset.sum_congr_set s (fun i ↦ (c i) • (v i)) (fun i ↦ (c i) • v i)
    (fun x _ ↦ rfl) (fun _ hx ↦ by simp [hi _ hx])

@[simp] theorem vecMulLinear_apply' {R m n : Type _} [Semiring R] [Fintype m]
    (M : Matrix m n R) (x : m → R) : M.vecMulLinear x = M.vecMul x := rfl

theorem rows_linearIndependent_iff [Fintype m] :
    LinearIndependent R A ↔ LinearMap.ker A.vecMulLinear = ⊥ := by
  simp only [Fintype.linearIndependent_iff, Submodule.eq_bot_iff, LinearMap.mem_ker,
    vecMulLinear_apply', vecMul, dotProduct]
  refine ⟨fun h x h0 ↦ funext fun i ↦ h _ (by rw [←h0]; ext; simp) _, fun h x h0 i ↦ ?_⟩
  rw [h x]; rfl
  rw [←h0]; ext; simp

theorem cols_linearIndependent_iff [Fintype n] :
    LinearIndependent R Aᵀ ↔ LinearMap.ker A.mulVecLin = ⊥ := by
  rw [rows_linearIndependent_iff]; convert Iff.rfl; ext; simp [← mulVec_transpose]

theorem subset_rows_notLinearIndependent_iff [Fintype m] :
    ¬ LinearIndependent R (A.submatrix ((↑) : s → m) id) ↔
      ∃ c, A.vecMul c = 0 ∧ c ≠ 0 ∧ support c ⊆ s := by
  change (¬LinearIndependent R (s.restrict A)) ↔ _

  simp only [Fintype.subtype_notLinearIndependent_iff, ne_eq, vecMul, dotProduct,
    support_subset_iff, not_imp_comm]
  refine ⟨fun ⟨c,h,⟨i, _, hci⟩,h'⟩ ↦
    ⟨c, by convert h; simp, by rintro rfl; exact hci rfl, h'⟩,
    fun ⟨c,h,hi,h'⟩ ↦ ⟨c, by convert h; simp, ?_, h'⟩⟩
  by_contra hc; push_neg at hc
  exact hi (funext fun i ↦ (em (i ∈ s)).elim (hc i) (h' i))

theorem subset_cols_notLinearIndependent_iff [Fintype n] :
    ¬ LinearIndependent R (Aᵀ.submatrix ((↑) : t → n) id) ↔
      ∃ c, A.mulVec c = 0 ∧ c ≠ 0 ∧ support c ⊆ t := by
  simp_rw [subset_rows_notLinearIndependent_iff, vecMul_transpose]

theorem range_vecMulLinear [Fintype m] (M : Matrix m n R) :
    LinearMap.range M.vecMulLinear = span R (range M) := by
  rw [←M.transpose_transpose, ← Mᵀ.range_mulVecLin]
  ext x
  simp [mulVec_transpose, vecMulLinear]

theorem foo [Fintype m] [Fintype n] (hA : LinearIndependent R A) (hB : LinearIndependent R B)
    (hAB : LinearMap.ker B.mulVecLin ≤ span R (range A)) (ht : A.ColBasis tᶜ) :
    LinearIndependent R (Bᵀ.submatrix ((↑) : t → n) id) := by
  by_contra hdep
  simp_rw [subset_cols_notLinearIndependent_iff] at hdep
  obtain ⟨c, hc0, hcn, hcs⟩ := hdep
  have hcsp : (c ∈ span R (range A)) := hAB hc0
  rw [←range_vecMulLinear, LinearMap.mem_range] at hcsp
  obtain ⟨d, rfl⟩ := hcsp
  rw [rows_linearIndependent_iff] at hA hB
  apply_fun Matrix.row at hc0
  rw [row_mulVec, vecMulLinear_apply', col_vecMul, transpose_mul, transpose_mul] at hc0
  -- rw [col_mulVec, vecMulLinear_apply', col_vecMul, transpose_mul, ← mul_assoc] at hc0
  -- rw [vecMulLinear_apply', mulVec_vecMul] at hc0



  -- rw [Fintype.subtype_notLinearIndependent_iff] at hdep
  -- -- have _ := t.toFinite.fintype
  -- obtain ⟨t, rfl⟩ := t.toFinite.exists_finset_coe

  -- simp only [Finset.coe_sort_coe, transpose_submatrix, Fintype.linearIndependent_iff,
  --   Finset.univ_eq_attach, Subtype.forall]

  -- rintro g hs j hj
  -- set c : n → R := fun j ↦ if hj : j ∈ t then f ⟨j,hj⟩ else 0
  -- set f := fun (i : t) ↦ g i • (submatrix B id ((↑) : t → n))ᵀ i with hf
  -- set h := fun (j : n) ↦ if hj : j ∈ t then f ⟨j,hj⟩ else 0

  -- have hh :


  --   -- then g ⟨j,hj⟩ • (submatrix B id ((↑) : t → n))ᵀ ⟨j,hj⟩ else 0
  -- have := (Finset.sum_congr_set t h f sorry sorry).symm


  -- -- -- set h : s → R :=
  -- -- -- rw [Finset.sum_coe_sort_eq_attach] at hs
