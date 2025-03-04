import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.Vandermonde
import Matroid.ForMathlib.Perm
import Matroid.ForMathlib.LinearAlgebra.LinearIndepOn
import Mathlib.Algebra.Algebra.Basic

set_option linter.style.longLine false

open Fin Matrix MvPolynomial


variable {n : ℕ} {R K : Type*} [CommRing R] [Field K]

lemma Fin.add_rev_cast (j : Fin (n+1)) : j.1 + j.rev.1 = n := by
  rw [val_rev]
  simp only [Nat.reduceSubDiff]
  omega

lemma Fin.rev_add_cast (j : Fin (n+1)) : j.rev.1 + j.1 = n := by
  rw [add_comm, j.add_rev_cast]

-- @[simp]
-- lemma Fin.castAdd_lt_natAdd {m n : ℕ} (i : Fin m) (j : Fin n) : castAdd n i < natAdd m j := by
--   obtain ⟨i, hi⟩ := i
--   obtain ⟨j, hj⟩ := j
--   simp only [castAdd_mk, natAdd_mk, mk_lt_mk]
--   omega

/-- A matrix with rows all having the form `[b^(n-1), a * b^(n-2), ..., a ^ (n-1)]` -/
def rectVandermonde {α : Type*} (v w : α → R) (n : ℕ) : Matrix α (Fin n) R :=
  .of fun i j ↦ (v i) ^ j.1 * (w i) ^ j.rev.1

def projVandermonde (v w : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  rectVandermonde v w n

/-- We don't mark this as `@[simp]` because the RHS is not simp-nf,
and simplifying it RHS gives a bothersome `Nat` subtraction.  -/
theorem projVandermonde_apply {v w : Fin n → R} {i j : Fin n} :
    projVandermonde v w i j = (v i) ^ j.1 * (w i) ^ j.rev.1 := rfl

theorem rectVandermonde_apply {α : Type*} {v w : α → R} {i : α} {j : Fin n} :
    rectVandermonde v w n i j = (v i) ^ j.1 * (w i) ^ j.rev.1 := rfl

theorem rectVandermonde_apply_zero_right {α : Type*} {v w : α → R} {i : α} (hw : w i = 0) :
    rectVandermonde v w (n+1) i = Pi.single (Fin.last n) ((v i) ^ n) := by
  ext j
  obtain rfl | hlt := j.le_last.eq_or_lt
  · simp [rectVandermonde_apply]
  rw [rectVandermonde_apply, Pi.single_eq_of_ne hlt.ne, hw, zero_pow, mul_zero]
  simpa [Nat.sub_eq_zero_iff_le] using hlt

theorem projVandermonde_apply_of_ne_zero {v w : Fin (n+1) → K} {i j : Fin (n+1)} (hw : w i ≠ 0) :
    projVandermonde v w i j = (v i) ^ j.1 * (w i) ^ n / (w i) ^ j.1 := by
  rw [projVandermonde_apply, eq_div_iff (by simp [hw]), mul_assoc, ← pow_add, rev_add_cast]

theorem projVandermonde_apply_zero_right {v w : Fin (n+1) → R} {i : Fin (n+1)} (hw : w i = 0) :
    projVandermonde v w i = Pi.single (Fin.last n) ((v i) ^ n)  := by
  ext j
  obtain rfl | hlt := j.le_last.eq_or_lt
  · simp [projVandermonde_apply]
  rw [projVandermonde_apply, Pi.single_eq_of_ne hlt.ne, hw, zero_pow, mul_zero]
  simpa [Nat.sub_eq_zero_iff_le] using hlt

theorem projVandermonde_comp {v w : Fin n → R} (f : Fin n → Fin n) :
    projVandermonde (v ∘ f) (w ∘ f) = (projVandermonde v w).submatrix f id := rfl

private theorem projVandermonde_det_of_field (v w : Fin n → K) :
    (projVandermonde v w).det = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ((v j * w i) - (v i * w j)) := by
  induction n with
  | zero => simp
  | succ n ih =>
  /- We can assume not all `w i` are zero, and therefore that `w 0 ≠ 0`,
  since otherwise we can swap row `0` with another nonzero row. -/
  wlog h0 : w 0 ≠ 0 generalizing v w with aux
  · obtain h0' | ⟨i₀, hi₀ : w i₀ ≠ 0⟩ := forall_or_exists_not (w · = 0)
    · obtain rfl | hne := eq_or_ne n 0
      · simp [projVandermonde_apply]
      rw [det_eq_zero_of_column_eq_zero 0 (fun i ↦ by simpa [projVandermonde_apply, h0']),
        Finset.prod_sigma', Finset.prod_eq_zero (i := ⟨0, Fin.last n⟩) (by simpa) (by simp [h0'])]
    rw [← mul_right_inj' (a := ((Equiv.swap 0 i₀).sign : K))
      (by simp [show 0 ≠ i₀ by rintro rfl; contradiction]), ← det_permute, ← projVandermonde_comp,
      aux _ _ (by simpa), ← prod_Ioi_comp_eq_sign_mul_prod (by simp)]
    rfl
  /- Let `W` be obtained from the matrix by subtracting `r = (v 0) / (w 0)` times each column
  from the next column, starting from the penultimate column. This doesn't change the determinant.-/
  set r := v 0 / w 0 with hr
  set W : Matrix (Fin (n+1)) (Fin (n+1)) K := .of fun i ↦ (cons (projVandermonde v w i 0)
    (fun j ↦ projVandermonde v w i j.succ - r * projVandermonde v w i j.castSucc))
  -- deleting the first row and column of `W` gives a row-scaling of a Vandermonde matrix.
  have hW_eq : (W.submatrix succ succ) = .of
    fun i j ↦ (v (succ i) - r * w (succ i)) *
      projVandermonde (v ∘ succ) (w ∘ succ) i j := by
    ext i j
    simp only [projVandermonde_apply, val_zero, rev_zero, val_last, val_succ,
      coe_castSucc, submatrix_apply, cons_succ, Function.comp_apply, rev_succ,
      Pi.smul_apply, smul_eq_mul, W, r, rev_castSucc]
    field_simp
    ring
  /- The first row of `W` is `[(w 0)^n, 0, ..., 0]` - take a cofactor expansion along this row,
  and apply induction. -/
  rw [det_eq_of_forall_col_eq_smul_add_pred (B := W) (c := fun _ ↦ r) (by simp [W])
    (fun i j ↦ by simp [W, r, projVandermonde_apply]), det_succ_row_zero,
    Finset.sum_eq_single 0 _ (by simp)]
  · rw [succAbove_zero, hW_eq, det_mul_column, ih]
    simp only [Nat.succ_eq_add_one, val_zero, pow_zero, projVandermonde_apply, val_rev,
      Nat.reduceSubDiff, tsub_zero, one_mul, val_succ, coe_castSucc, cons_zero,
      Function.comp_apply, W, r, of_apply]
    rw [prod_univ_succ, ← mul_assoc (a := _ ^ n), show (w 0) ^ n = ∏ x : Fin n, w 0 by simp,
      ← Finset.prod_mul_distrib]
    simp_rw [mul_sub, ← mul_assoc (a := w 0), mul_div_cancel₀ _ h0, mul_comm (w 0)]
    simp
  intro j _ hj0
  obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero hj0
  rw [mul_eq_zero, mul_eq_zero]
  refine .inl (.inr ?_)
  simp only [of_apply, projVandermonde_apply_of_ne_zero h0, val_succ, coe_castSucc, cons_succ, W, r]
  ring


theorem projVandermonde_map {R' : Type*} [CommRing R'] (φ : R →+* R') (v w : Fin n → R) :
    projVandermonde (fun i ↦ φ (v i)) (fun i ↦ φ (w i)) = φ.mapMatrix (projVandermonde v w) := by
  ext i j
  simp [projVandermonde_apply]

theorem projVandermonde_det (v w : Fin n → R) : (projVandermonde v w).det =
    ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (v j * w i - v i * w j) := by
  let R' := MvPolynomial (Fin n × Bool) ℤ
  let u : Fin n × Bool → FractionRing R' := fun i ↦ (algebraMap R' _) (MvPolynomial.X ⟨i.1, i.2⟩)
  have hdet := projVandermonde_det_of_field (u ⟨· , true⟩) (u ⟨·, false⟩)
  simp only [u, RingHom.mapMatrix_apply] at hdet
  norm_cast at hdet
  rw [projVandermonde_map, ← RingHom.map_det, IsFractionRing.coe_inj] at hdet
  apply_fun MvPolynomial.eval₂Hom (Int.castRingHom R) (fun x ↦ (if x.2 then v else w) x.1) at hdet
  rw [RingHom.map_det] at hdet
  convert hdet <;>
  simp [← Matrix.ext_iff, projVandermonde_apply, u, R']

lemma projVandermonde_det_eq_zero_of_mul_eq_mul {v w : Fin n → R} {i i' : Fin n} (hne : i ≠ i')
    (hvw : v i * w i' = v i' * w i) : (projVandermonde v w).det = 0 := by
  wlog hlt : i < i' generalizing i i' with aux
  · exact aux hne.symm hvw.symm <| (not_lt.1 hlt).lt_of_ne' hne
  rw [projVandermonde_det, Finset.prod_sigma', Finset.prod_eq_zero (i := ⟨i,i'⟩) (by simpa)]
  simp [hvw]

lemma projVandermonde_det_eq_zero_of_zero {v w : Fin (n+2) → R} {i : Fin (n+2)} (hv : v i = 0)
    (hw : w i = 0) : (projVandermonde v w).det = 0 :=
  det_eq_zero_of_row_eq_zero (i := i) fun j ↦ by simp [projVandermonde_apply_zero_right hw, hv]

section Rect

variable {α K R : Type*} [CommRing R] [Field K] {n : ℕ} {v w : α → K} {s : Set α}

theorem Matrix.linearIndependent_rows_of_det_ne_zero {m R : Type*} [Fintype m] [DecidableEq m]
    [CommRing R] [IsDomain R] {A : Matrix m m R} (hA : A.det ≠ 0) :
    LinearIndependent R (fun i ↦ A i) := by
  contrapose! hA
  obtain ⟨c, hc0, i, hci⟩ := Fintype.not_linearIndependent_iff.1 hA
  have h0 := A.det_updateRow_sum i c
  rwa [det_eq_zero_of_row_eq_zero (i := i) (fun j ↦ by simp [hc0]), smul_eq_mul, eq_comm,
    mul_eq_zero_iff_left hci] at h0

theorem Matrix.linearIndependent_cols_of_det_ne_zero {m R : Type*} [Fintype m] [DecidableEq m]
    [CommRing R] [IsDomain R] {A : Matrix m m R} (hA : A.det ≠ 0) :
    LinearIndependent R (fun i ↦ Aᵀ i) :=
  Matrix.linearIndependent_rows_of_det_ne_zero (by simpa)

lemma rectVandermonde_rows_linearIndependent' [IsDomain R] [Fintype α] (hcard : Fintype.card α ≤ n)
    {v w : α → R} (hvw : ∀ ⦃i i'⦄, v i * w i' = v i' * w i → i = i') (h0 : ∀ ⦃i⦄, w i = 0 → v i ≠ 0) :
    LinearIndependent R (rectVandermonde v w n) := by
  set e := (Fintype.equivFin α).symm
  set m₀ := Fintype.card α
  replace hvw ⦃i i'⦄ : v i * w i' = v i' * w i ↔ i = i' := ⟨fun h ↦ hvw h, fun h ↦ by rw [h]⟩
  -- extend to a square Vandermonde matrix by appending new rows with entries coming from distinct
  -- new elements in `Polynomial R`
  -- This larger matrix has nonzero determininant, so has linearly independent rows;
  -- therefore, so does the original matrix.
  let v' (i : Fin n) :=
    if hi : i < m₀ then Polynomial.C (v (e ⟨i, hi⟩)) else Polynomial.X ^ (i.1 + 1)
  let w' (i : Fin n) := Polynomial.C (if hi : i < m₀ then w (e ⟨i, hi⟩) else 1)
  have hdet : (projVandermonde v' w').det ≠ 0 := by
    simp only [Ne, projVandermonde_det, dite_mul, Polynomial.X_pow_mul_C, Finset.prod_eq_zero_iff,
      Finset.mem_univ, Finset.mem_Ioi, sub_eq_zero, true_and, not_exists, not_and, forall_iff,
      mk_lt_mk, v', w']
    refine fun i hi j hj hij h_eq ↦ hij.ne.symm ?_
    by_cases hj : j < m₀
    · simpa [hj, hij.trans hj, ← Polynomial.C_mul, hvw, -_root_.map_mul] using h_eq
    split_ifs at h_eq with hi
    · obtain ⟨hw0, hv0⟩ :=
        by simpa [hij.ne.symm] using congr_arg (fun p ↦ (⟨p.coeff (j+1), p.coeff 0⟩ : R × R)) h_eq
      exact False.elim <| h0 hw0 hv0.symm
    simpa [Polynomial.X_pow_eq_monomial, Polynomial.monomial_eq_monomial_iff] using h_eq
  refine LinearIndependent.of_comp (M' := Fin n → Polynomial R)
    (LinearMap.compLeft (Algebra.linearMap _ _) _) ?_
  convert ((Matrix.linearIndependent_rows_of_det_ne_zero hdet).restrict_scalars' R).comp _
    ((castLE_injective hcard).comp e.symm.injective)
  ext a i x
  simp [v', w', projVandermonde, rectVandermonde]

/-- A set `s` of rows of `rectVandermonde v w n` is linearly independent if and only if its
cardinality doesn't exceed the number of columns, there is no co-ordinate in `s` on which
both `v i` and `w i` are zero, and `v i * w j ≠ v j * w i` for distinct `i,j ∈ s`. -/
lemma rectVandermonde_linearIndepOn_iff {v w : α → K} (hn : n ≠ 1) :
    LinearIndepOn K (rectVandermonde v w n) s ↔ s.encard ≤ n ∧ (∀ i ∈ s, w i = 0 → v i ≠ 0) ∧
      (∀ ⦃i j⦄, i ∈ s → j ∈ s → v j * w i = v i * w j → i = j) := by
  obtain hlt | hle := lt_or_le (n : ℕ∞) s.encard
  · refine iff_of_false (fun hli ↦ hlt.not_le ?_) (by simp [hlt])
    simpa using hli.encard_le_toENat_rank
  have hsfin := (s.finite_of_encard_le_coe hle).fintype
  refine ⟨fun h ↦ ⟨hle, ?_⟩, fun h ↦ ?_⟩
  · obtain rfl | n := n
    · simp [show s = ∅ by simpa using hle]
    have aux {i} : i ∈ s → w i = 0 → v i ≠ 0 := by
      refine fun hi hw hv ↦ ?_
      apply h.ne_zero hi
      rw [rectVandermonde_apply_zero_right hw, hv, zero_pow (by rintro rfl; contradiction),
        Pi.single_zero]
    refine ⟨@aux, fun i j his hjs hij ↦ by_contra fun hne ↦ ?_⟩
    replace h := ((linearIndepOn_pair_iff _ hne (h.ne_zero his)).1 <|
      h.mono (Set.pair_subset_iff.2 ⟨his, hjs⟩))
    by_cases hi0 : w i = 0
    · refine h ((v j) ^ n / (v i) ^ n) ?_
      rw [rectVandermonde_apply_zero_right hi0, rectVandermonde_apply_zero_right
        (by simpa [hi0, aux his hi0] using hij), ← Pi.single_smul, smul_eq_mul,
        div_mul_cancel₀ _ (by simp [aux his hi0])]
    refine h ((w j) ^ n / (w i) ^ n) ?_
    ext k
    rw [rectVandermonde_apply, Pi.smul_apply, rectVandermonde_apply, smul_eq_mul]
    simp_rw [show n = k.1 + k.rev.1 by rw [k.add_rev_cast]]
    field_simp
    rw [pow_add, mul_right_comm, ← mul_assoc, ← mul_pow, mul_comm (w j), ← hij]
    ring
  rw [← linearIndependent_set_coe_iff]
  refine rectVandermonde_rows_linearIndependent' ?_ (by aesop) (by aesop)
  rwa [Set.encard_eq_coe_toFinset_card, Set.toFinset_card, Nat.cast_le] at hle

lemma rectVandermonde_linearIndepOn_iff' {v w : α → K} (hvw : ∀ i ∈ s, w i = 0 → v i ≠ 0) :
    LinearIndepOn K (rectVandermonde v w n) s ↔ s.encard ≤ n ∧
    (∀ ⦃i j⦄, i ∈ s → j ∈ s → v j * w i = v i * w j → i = j) := by
  obtain rfl | hne := eq_or_ne n 1
  · refine ⟨fun h ↦ ?_, fun ⟨hcard, h⟩ ↦ ?_⟩
    · have hscard := by simpa using h.encard_le_toENat_rank
      refine ⟨hscard, ?_⟩
      rw [Set.encard_le_one_iff] at hscard
      aesop
    obtain rfl | ⟨x, rfl⟩ := Set.encard_le_one_iff_eq.1 hcard <;>
    simp [rectVandermonde, funext_iff]
  rw [rectVandermonde_linearIndepOn_iff hne, and_iff_right hvw]

lemma rectVandermonde_one_linearIndepOn_iff {v : α → K} {s : Set α} :
    LinearIndepOn K (rectVandermonde v 1 n) s ↔ s.encard ≤ n ∧ Set.InjOn v s := by
  obtain rfl | rfl | n := n
  · simp +contextual [rectVandermonde, LinearIndepOn]
  · refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · have hcard : s.encard ≤ 1 := by simpa using h.encard_le_toENat_rank
      exact ⟨hcard, (Set.encard_le_one_iff_subsingleton.1 hcard).injOn _⟩
    simp only [zero_add, Nat.cast_one, Set.encard_le_one_iff_subsingleton] at h
    obtain rfl | ⟨x, rfl⟩ := h.1.eq_empty_or_singleton <;>
    simp [rectVandermonde, funext_iff]
  rw [rectVandermonde_linearIndepOn_iff (by simp)]
  simp only [Pi.one_apply, one_ne_zero, ne_eq, IsEmpty.forall_iff, implies_true, mul_one, true_and,
    Set.InjOn, and_congr_right_iff]
  aesop








-- lemma rectVandermonde_rows_linearIndependent [Fintype α] (hcard : Fintype.card α ≤ n)
--     (hvw : ∀ ⦃i i'⦄, v i * w i' = v i' * w i → i = i') (h0 : ∀ ⦃i⦄, v i = 0 → w i ≠ 0) :
--     LinearIndependent K (rectVandermonde v w n) := by
--   obtain ⟨m, rfl⟩ := exists_add_of_le hcard
--   set e := (Fintype.equivFin α).symm
--   set m₀ := Fintype.card α
--   let v' : Fin (m₀ + m) → FractionRing (MvPolynomial (Fin m) K) :=
--     (algebraMap _ _) ∘ Fin.append (MvPolynomial.C ∘ v ∘ e) MvPolynomial.X
--   let w' : Fin (m₀ + m) → FractionRing (MvPolynomial (Fin m) K) :=
--     (algebraMap ((MvPolynomial (Fin m) K)) _) ∘ Fin.append (MvPolynomial.C ∘ w ∘ e) 1
--   have hli : LinearIndependent (FractionRing (MvPolynomial (Fin m) K)) (projVandermonde v' w') := by
--     rw [linearIndependent_rows_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
--     simp only [projVandermonde_det, Function.comp_apply, ne_eq, Finset.prod_eq_zero_iff,
--       Finset.mem_univ, Finset.mem_Ioi, sub_eq_zero, true_and, not_exists, not_and, v', w']
--     norm_cast
--     refine fun i j ↦ i.addCases (fun i' ↦ ?_) fun i' ↦ j.addCases (fun j' ↦ ?_) fun j' ↦ ?_
--     · refine j.addCases (fun j' hlt heq ↦ hlt.ne ?_) fun j' hlt ↦ ?_
--       · simp only [append_left, Function.comp_apply] at heq
--         rw [← C_mul, ← C_mul, C_inj] at heq
--         rw [show j' = i' by simpa using hvw heq]
--       simp only [append_right, append_left, Function.comp_apply, Pi.one_apply, mul_one,
--         mul_comm (X j'), MvPolynomial.C_mul_X_eq_monomial]
--       rw [C_apply, monomial_eq_monomial_iff]
--       simp [imp_not_comm]
--       apply h0
--     · simp [(Fin.castAdd_lt_natAdd ..).not_lt]
--     simp +contextual [imp_not_comm]
--   have hli' := (hli.restrict_scalars' K).comp _ ((castAdd_injective ..).comp e.symm.injective)
--   refine LinearIndependent.of_comp (LinearMap.compLeft
--     (Algebra.linearMap K (FractionRing (MvPolynomial (Fin m) K))) (Fin (m₀ + m))) ?_
--   convert hli'
--   ext a i
--   simp only [rectVandermonde, val_rev, Function.comp_apply, LinearMap.compLeft_apply, of_apply,
--     Algebra.linearMap_apply, _root_.map_mul, map_pow, projVandermonde, append_left,
--     Equiv.apply_symm_apply, v', w']
--   norm_cast
--   rw [← C_pow, ← C_pow, ← C_mul]
--   rfl

end Rect
