import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.Dual
import Matroid.ForMathlib.Representation

variable {ι m n R : Type _} [Field R] {A B : Matrix m n R} {s : Set m} {t : Set n}

open Set Function Submodule BigOperators

namespace Matrix

/-- `A.RowBasis s` means that the rows `A_i : i ∈ s` are a basis for the row space of `A` -/
def RowBasis (A : Matrix m n R) (s : Set m) : Prop :=
    LinearIndependent R (A.submatrix ((↑) : s → m) id)
  ∧ span R (range <| A.submatrix ((↑) : s → m) id) = span R (range A)

/-- A `RowBasis` as a `Basis` for the row space -/
noncomputable def RowBasis.basis (h : A.RowBasis s) : Basis s R (span R (range A)) :=
  (Basis.span h.1).map <| LinearEquiv.ofEq _ _ h.2

@[simp] theorem RowBasis.basis_apply (h : A.RowBasis s) (i : s) : h.basis i = A i := by
  ext; simp [Matrix.RowBasis.basis, Basis.span_apply]

theorem RowBasis.linearIndependent (h : A.RowBasis s) :
  LinearIndependent R (A.submatrix ((↑) : s → m) id) := h.1

theorem RowBasis.span_eq (h : A.RowBasis s) :
  span R (range <| A.submatrix ((↑) : s → m) id) = span R (range A) := h.2

/-- `A.ColBasis t` means that the columns `A_i : i ∈ t` are a basis for the column space of `A` -/
def ColBasis (A : Matrix m n R) (t : Set n) := Aᵀ.RowBasis t

/-- A `ColBasis` as a `Basis` for the column space -/
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

@[simp] theorem rowBasis_transpose : Aᵀ.RowBasis t ↔ A.ColBasis t := Iff.rfl
@[simp] theorem colBasis_transpose : Aᵀ.ColBasis s ↔ A.RowBasis s := Iff.rfl

theorem Fintype.subtype_notLinearIndependent_iff [Fintype ι] [CommSemiring R]
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

theorem range_vecMulLinear {R m n : Type _} [CommSemiring R] [Fintype m] (M : Matrix m n R) :
    LinearMap.range M.vecMulLinear = span R (range M) := by
  convert range_mulVecLin Mᵀ; ext x; simp [← vecMul_transpose]

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

@[simp] theorem Fintype.sum_pi_single {α : Type v} {β : α → Type u_2} [DecidableEq α] [Fintype α]
    [(a : α) → AddCommMonoid (β a)] (a : α) (f : (a : α) → β a) :
    ∑ a', Pi.single a' (f a') a = f a := by
  convert Finset.sum_pi_single a f Finset.univ; simp

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
    (hA : LinearIndependent R A) : LinearIndependent R (A.submatrix id ((↑) : t → n)) := by
  have _ := t.toFinite.fintype
  rw [←span_cols_eq_top_iff_linearIndependent_rows, Submodule.eq_top_iff']
  intro x
  rw [←span_cols_eq_top_iff_linearIndependent_rows] at hA
  have hsp := hA ▸ ht.span_eq
  rw [hsp];
  apply mem_top

theorem RowBasis.cols_linearIndependent [Fintype m] [Fintype n] (hs : A.RowBasis s)
    (hA : LinearIndependent R Aᵀ) : LinearIndependent R (Aᵀ.submatrix id ((↑) : s → m)) :=
  (colBasis_transpose.2 hs).rows_linearIndependent hA

/-- If an `m × n` matrix `A` with entries in `R` has linearly independent rows,
    a column basis for `A` gives a basis for `m → R`. -/
noncomputable def ColBasis.basis' [Fintype m] [Fintype n] (ht : A.ColBasis t)
  (hA : LinearIndependent R A) : Basis t R (m → R) :=
  have _ := t.toFinite.fintype
  ( Basis.span ht.linearIndependent ).map <| LinearEquiv.ofTop _ <| eq_top_iff'.2 fun x ↦
    ( by rw [ht.span_eq, span_cols_eq_top_iff_linearIndependent_rows.2 hA]; apply mem_top )

@[simp] theorem ColBasis.basis'_apply [Fintype m] [Fintype n] (ht : A.ColBasis t)
    (hA : LinearIndependent R A) (j : t) : ht.basis' hA j = (A · j) := by
  ext; simp [basis', Basis.span_apply]

noncomputable def RowBasis.basis' [Fintype m] [Fintype n] (ht : A.RowBasis s)
    (hA : LinearIndependent R Aᵀ) : Basis s R (n → R) :=z

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
