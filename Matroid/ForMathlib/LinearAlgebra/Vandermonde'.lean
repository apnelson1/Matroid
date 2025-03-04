import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.Vandermonde
import Matroid.ForMathlib.Perm
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

@[simp]
lemma Fin.castAdd_lt_natAdd {m n : ℕ} (i : Fin m) (j : Fin n) : castAdd n i < natAdd m j := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  simp only [castAdd_mk, natAdd_mk, mk_lt_mk]
  omega

/-- A matrix with rows all having the form `[b^(n-1), a * b^(n-2), ..., a ^ (n-1)]` -/
def rectVandermonde {α : Type*} (v w : α → R) (n : ℕ) : Matrix α (Fin n) R :=
  .of fun i j ↦ (v i) ^ j.1 * (w i) ^ j.rev.1

def projVandermonde (v w : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  rectVandermonde v w n

/-- We don't mark this as `@[simp]` because the RHS is not simp-nf,
and simplifying it RHS gives a bothersome `Nat` subtraction.  -/
theorem projVandermonde_apply {v w : Fin n → R} {i j : Fin n} :
    projVandermonde v w i j = (v i) ^ j.1 * (w i) ^ j.rev.1 := rfl

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

private theorem projVandermonde_det_of_field (v w : Fin n → K) :
    (projVandermonde v w).det = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ((v j * w i) - (v i * w j)) := by
  induction n with
  | zero => simp
  | succ n ih =>
  -- We may assume that one of the `w i` is nonzero, as otherwise both sides are obviously zero.
  obtain h0 | ⟨i₀, hi₀ : w i₀ ≠ 0⟩ := forall_or_exists_not (w · = 0)
  · obtain rfl | hne := eq_or_ne n 0
    · simp [projVandermonde_apply]
    rw [det_eq_zero_of_column_eq_zero 0]
    · simp [Fin.prod_univ_succ, h0, hne]
    exact fun i ↦ by simp [projVandermonde_apply, h0, hne]
  -- We can assume by permuting rows that `w 0 ≠ 0`. (This makes reindexing with induction easier.)
  wlog hi₀0 : i₀ = 0 generalizing v w i₀ with aux
  · rw [← mul_right_inj' (a := -1) (by simp)]
    convert aux (v ∘ Equiv.swap 0 i₀) (w ∘ Equiv.swap 0 i₀) (i₀ := 0) (by simp [hi₀]) rfl
    · convert (det_permute (M := projVandermonde v w) (σ := Equiv.swap 0 i₀)).symm using 2
      simp [Equiv.Perm.sign_swap (Ne.symm hi₀0)]
    rw [← eq_comm]
    convert prod_Ioi_comp_eq_sign_mul_prod (f := fun i j ↦ v j * w i - v i * w j) (by simp)
      (Equiv.swap 0 i₀) using 2
    simp [Equiv.Perm.sign_swap (Ne.symm hi₀0)]
  obtain rfl := hi₀0
  /- Let `W` be obtained from the matrix by subtracting `r = (v 0) / (w 0)` times each column
  from the next column, starting from the penultimate column. This doesn't change the determinant.-/
  set r := v 0 / w 0 with hr
  set W : Matrix (Fin (n+1)) (Fin (n+1)) K := .of fun i ↦
    (cons (projVandermonde v w i 0)
      (fun j ↦ projVandermonde v w i j.succ - r * projVandermonde v w i j.castSucc))
  -- deleting the first row and column of `W` gives a row-scaling of a Vandermonde matrix.
  have hW_eq : (W.submatrix succ succ) = .of
    fun i j ↦ (v (succ i) - r * w (succ i)) *
      projVandermonde (v ∘ succ) (w ∘ succ) i j := by
    ext i j
    simp only [projVandermonde_apply,  val_zero, rev_zero, val_last, val_succ,
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
    simp_rw [mul_sub, ← mul_assoc (a := w 0), mul_div_cancel₀ _ hi₀, mul_comm (w 0)]
    simp
  intro j _ hj0
  obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero hj0
  suffices h : W 0 j.succ = 0 by simp [h]
  simp [W, r]
  rw [projVandermonde_apply_of_ne_zero hi₀, projVandermonde_apply_of_ne_zero hi₀, sub_eq_zero,
    div_eq_iff (pow_ne_zero _ hi₀)]
  field_simp
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

variable {α K : Type*} [Field K] {n : ℕ} {v w : α → K}

lemma rectVandermonde_rows_linearIndependent [Fintype α] (hcard : Fintype.card α ≤ n)
    (hvw : ∀ ⦃i i'⦄, v i * w i' = v i' * w i → i = i') (h0 : ∀ ⦃i⦄, v i = 0 → w i ≠ 0) :
    LinearIndependent K (rectVandermonde v w n) := by
  obtain ⟨m, rfl⟩ := exists_add_of_le hcard
  set e := (Fintype.equivFin α).symm
  set m₀ := Fintype.card α
  let v' : Fin (m₀ + m) → FractionRing (MvPolynomial (Fin m) K) :=
    (algebraMap _ _) ∘ Fin.append (MvPolynomial.C ∘ v ∘ e) MvPolynomial.X
  let w' : Fin (m₀ + m) → FractionRing (MvPolynomial (Fin m) K) :=
    (algebraMap ((MvPolynomial (Fin m) K)) _) ∘ Fin.append (MvPolynomial.C ∘ w ∘ e) 1
  have hli : LinearIndependent (FractionRing (MvPolynomial (Fin m) K)) (projVandermonde v' w') := by
    rw [linearIndependent_rows_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    simp only [projVandermonde_det, Function.comp_apply, ne_eq, Finset.prod_eq_zero_iff,
      Finset.mem_univ, Finset.mem_Ioi, sub_eq_zero, true_and, not_exists, not_and, v', w']
    norm_cast
    refine fun i j ↦ i.addCases (fun i' ↦ ?_) fun i' ↦ j.addCases (fun j' ↦ ?_) fun j' ↦ ?_
    · refine j.addCases (fun j' hlt heq ↦ hlt.ne ?_) fun j' hlt ↦ ?_
      · simp only [append_left, Function.comp_apply] at heq
        rw [← C_mul, ← C_mul, C_inj] at heq
        rw [show j' = i' by simpa using hvw heq]
      simp only [append_right, append_left, Function.comp_apply, Pi.one_apply, mul_one,
        mul_comm (X j'), MvPolynomial.C_mul_X_eq_monomial]
      rw [C_apply, monomial_eq_monomial_iff]
      simp [imp_not_comm]
      apply h0
    · simp [(Fin.castAdd_lt_natAdd ..).not_lt]
    simp +contextual [imp_not_comm]
  have hli' := (hli.restrict_scalars' K).comp _ ((castAdd_injective ..).comp e.symm.injective)
  refine LinearIndependent.of_comp (LinearMap.compLeft
    (Algebra.linearMap K (FractionRing (MvPolynomial (Fin m) K))) (Fin (m₀ + m))) ?_
  convert hli'
  ext a i
  simp only [rectVandermonde, val_rev, Function.comp_apply, LinearMap.compLeft_apply, of_apply,
    Algebra.linearMap_apply, _root_.map_mul, map_pow, projVandermonde, append_left,
    Equiv.apply_symm_apply, v', w']
  norm_cast
  rw [← C_pow, ← C_pow, ← C_mul]
  rfl

end Rect
