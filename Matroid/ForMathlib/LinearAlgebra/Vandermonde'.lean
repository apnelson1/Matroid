import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.Vandermonde
import Matroid.ForMathlib.Perm

set_option linter.style.longLine false

open Fin Matrix MvPolynomial


variable {n : ℕ} {R K : Type*} [CommRing R] [Field K]

lemma Fin.add_rev_cast (j : Fin (n+1)) : j.1 + j.rev.1 = n := by
  rw [val_rev]
  simp only [Nat.reduceSubDiff]
  omega

lemma Fin.rev_add_cast (j : Fin (n+1)) : j.rev.1 + j.1 = n := by
  rw [add_comm, j.add_rev_cast]

def projVandermonde (v w : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  .of fun i j ↦ (v i)^(j : ℕ) * (w i)^(Fin.rev j : ℕ)

theorem projVandermonde_apply {v w : Fin (n+1) → K} {i j : Fin (n+1)} :
    projVandermonde v w i j = (v i) ^ j.1 * (w i) ^ j.rev.1 := rfl

theorem projVandermonde_apply_of_ne_zero {v w : Fin (n+1) → K} {i j : Fin (n+1)} (hw : w i ≠ 0) :
    projVandermonde v w i j = (v i) ^ j.1 * (w i) ^ n / (w i) ^ j.1 := by
  rw [projVandermonde, eq_div_iff (by simp [hw]), of_apply, mul_assoc, ← pow_add, rev_add_cast]

theorem projVandermonde_apply_zero_right {v w : Fin (n+1) → R} {i : Fin (n+1)} (hw : w i = 0) :
    projVandermonde v w i = Pi.single (Fin.last n) ((v i) ^ n)  := by
  ext j
  obtain rfl | hlt := j.le_last.eq_or_lt
  · simp [projVandermonde]
  rw [projVandermonde, Pi.single_eq_of_ne hlt.ne, of_apply, hw, zero_pow, mul_zero]
  simpa [Nat.sub_eq_zero_iff_le] using hlt

private theorem projVandermonde_det_of_field (v w : Fin n → K) :
    (projVandermonde v w).det = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ((v j * w i) - (v i * w j)) := by
  induction n with
  | zero => simp
  | succ n ih =>
  -- We may assume that one of the `w i` is nonzero, as otherwise both sides are obviously zero.
  obtain h0 | ⟨i₀, hi₀ : w i₀ ≠ 0⟩ := forall_or_exists_not (w · = 0)
  · obtain rfl | hne := eq_or_ne n 0
    · simp [projVandermonde]
    rw [det_eq_zero_of_column_eq_zero 0]
    · simp [Fin.prod_univ_succ, h0, hne]
    exact fun i ↦ by simp [projVandermonde_apply, h0, hne]
  -- We can assume by permuting rows that `w 0 ≠ 0`.
  wlog hi₀0 : i₀ = 0 generalizing v w i₀ with aux
  · rw [← mul_right_inj' (a := -1) (by simp)]
    convert aux (v ∘ Equiv.swap 0 i₀) (w ∘ Equiv.swap 0 i₀) (i₀ := 0) (by simp [hi₀]) rfl
    · convert (det_permute (M := projVandermonde v w) (σ := Equiv.swap 0 i₀)).symm using 2
      simp [Equiv.Perm.sign_swap (Ne.symm hi₀0)]
    rw [← eq_comm]
    convert prod_comp_eq_of_swap_eq_neg' (fun i j ↦ v j * w i - v i * w j) (by simp)
      (Equiv.swap 0 i₀) using 2
    simp [Equiv.Perm.sign_swap (Ne.symm hi₀0)]
  obtain rfl := hi₀0
  /- Let `W` be obtained from the matrix by subtracting `r = (v 0) / (w 0)` times each column
  from the next column, starting from the penultimate column. -/
  set r := v 0 / w 0 with hr
  set W : Matrix (Fin (n+1)) (Fin (n+1)) K := .of fun i ↦
    (cons (projVandermonde v w i 0)
      (fun j ↦ projVandermonde v w i j.succ - r * projVandermonde v w i j.castSucc))
  -- deleting the first row and column of `W` gives a row-scaling of a Vandermonde matrix.
  have hW_eq : (W.submatrix succ succ) = .of
    fun i j ↦ (v (succ i) - r * w (succ i)) *
      projVandermonde (v ∘ succ) (w ∘ succ) i j := by
    ext i j
    simp only [projVandermonde, of_apply, val_zero, rev_zero, val_last, val_succ,
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
    simp only [Nat.succ_eq_add_one, val_zero, add_zero, projVandermonde, val_rev, Nat.reduceSubDiff,
      of_apply, pow_zero, tsub_zero, one_mul, val_succ, coe_castSucc, cons_zero,
      Function.comp_apply, W, r]
    rw [prod_univ_succ, ← mul_assoc (a := _ ^ n),
      show (w 0) ^ n = ∏ x : Fin n, w 0 by simp, ← Finset.prod_mul_distrib]
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
  simp [projVandermonde]

theorem projVandermonde_det (v w : Fin n → R) : (projVandermonde v w).det =
    ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ((v j * w i) - (v i * w j)) := by
  let R' := MvPolynomial (Fin n × Bool) ℤ
  let K := FractionRing R'
  set coordFun : Fin n × Bool → R := fun x ↦ (if x.2 then v else w) x.1 with hcoord
  set φ : R' →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) coordFun with hφ
  have hφv (i : Fin n) : φ (MvPolynomial.X ⟨i, true⟩) = v i := MvPolynomial.eval₂Hom_X' ..
  have hφw (i : Fin n) : φ (MvPolynomial.X ⟨i, false⟩) = w i := MvPolynomial.eval₂Hom_X' ..
  set v' : Fin n → K := fun i ↦ (algebraMap R' K) (MvPolynomial.X ⟨i, true⟩) with hv'
  set w' : Fin n → K := fun i ↦ (algebraMap R' K) (MvPolynomial.X ⟨i, false⟩) with hw'
  have hdet := projVandermonde_det_of_field v' w'
  simp only [hv', hw', RingHom.mapMatrix_apply] at hdet
  norm_cast at hdet
  rw [projVandermonde_map, ← RingHom.map_det,
    (algebraMap_injective_of_field_isFractionRing R' K K K).eq_iff] at hdet
  replace hdet := congr_arg φ <| hdet
  simp only [RingHom.map_det, RingHom.mapMatrix_apply, map_prod, map_sub, _root_.map_mul,
    hφv, hφw] at hdet
  convert hdet
  ext i j
  simp [projVandermonde, hφv, hφw]
