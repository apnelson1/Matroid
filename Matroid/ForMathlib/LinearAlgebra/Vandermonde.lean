import Mathlib.LinearAlgebra.Vandermonde
import Matroid.ForMathlib.LinearAlgebra.Matrix.Rowspace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Set Function

namespace Matrix

variable {R α K : Type*} [CommRing R] [Field K] {n : ℕ} {f : α → R}

theorem vandermonde_isUnit_iff {v : Fin n → K} :
    IsUnit (vandermonde v) ↔ Injective v := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, det_vandermonde_ne_zero_iff]

/-- A rectangular Vandermonde matrix; its columns are indexed by `Fin n`,
    and its rows are geometric progressions `(1, a, a², ..., a^(n-1))`. -/
def rectVandermonde (v : α → R) (n : ℕ) :
    Matrix α (Fin n) R := Matrix.of (fun a (i : Fin n) => (v a) ^ (i : ℕ))

@[simp] theorem rectVandermonde_apply (v : α → R) (n : ℕ) (a : α) (i : Fin n) :
    rectVandermonde v n a i = (v a) ^ (i : ℕ) := rfl

theorem rectVandermonde_linearIndependent_rows [Fintype α] {v : α → K} (hv : Injective v)
    (hn : Fintype.card α ≤ n) : LinearIndependent K (rectVandermonde v n).rowFun := by
  apply rows_linearIndependent_of_submatrix (Fintype.equivFin α).symm (Fin.castLE hn)
  rw [linearIndependent_rows_iff_isUnit]
  exact vandermonde_isUnit_iff.2 (hv.comp (Fintype.equivFin α).symm.injective)

theorem rectVandermonde_linearIndependent_cols [Fintype α] {v : α → K} (hv : Injective v)
    (hn : n ≤ Fintype.card α) : LinearIndependent K (rectVandermonde v n).colFun := by
  rw [←Fintype.card_fin n] at hn
  obtain ⟨g⟩ := Embedding.nonempty_of_card_le hn
  apply cols_linearIndependent_of_submatrix g (Equiv.refl _)
  rw [linearIndependent_cols_iff_isUnit]
  exact vandermonde_isUnit_iff.2 (hv.comp g.injective)

/-- A rectangular Vandermonde matrix with a possible 'infinity' row equal to `(0,0, ..., 1)` -/
def rectProjVandermonde (v : α → Option R) (n : ℕ) : Matrix α (Fin n) R :=
  Matrix.of (fun a ↦ (v a).casesOn
    (n.casesOn finZeroElim (fun _ ↦ Pi.single ⊤ 1)) (fun x i ↦ x^(i : ℕ)))

theorem rectProjVandermonde_apply_some (f : α → Option R) (n : ℕ) {a : α} {x : R}
    (hx : f a = some x) (i : Fin n) : rectProjVandermonde f n a i = x^(i : ℕ) := by
   simp [rectProjVandermonde, hx]

theorem rectProjVandermonde_apply_none_zero (v : α → Option R) (n : ℕ) {a : α} (ha : v a = none)
    (i : Fin n) (hi : i + 1 < n) : rectProjVandermonde v n a i = 0 := by
  simp [rectProjVandermonde, ha, hi]
  cases n
  · apply finZeroElim i
  simp only [ne_eq]
  rw [Pi.single_apply, if_neg]
  rintro rfl
  simp [Fin.top_eq_last] at hi

theorem rectProjVandermonde_apply_none_one (v : α → Option R) (n : ℕ) {a : α} (ha : v a = none)
    (i : Fin n) (hi : i + 1 = n) : rectProjVandermonde v n a i = 1 := by
  simp [rectProjVandermonde, ha, hi]
  obtain (rfl | n) := n
  · apply finZeroElim i
  obtain ⟨i, hi'⟩ := i
  simp only [Nat.succ.injEq] at hi
  subst hi
  simp only [ne_eq]
  rw [Pi.single_apply, if_pos]
  rfl

theorem rectProjVandermonde_linearIndependent_rows [Fintype α] {v : α → Option K}
    (hv : Injective v) (hn : Fintype.card α ≤ n) :
    LinearIndependent K (rectProjVandermonde v n).rowFun := by
  obtain (rfl | n) := n
  · have : IsEmpty α
    · rwa [Nat.le_zero, Fintype.card_eq_zero_iff] at hn
    apply linearIndependent_empty_type
  set V0 : Matrix {a // v a ≠ none} (Fin (n+1)) K :=
    Matrix.of fun a (i : Fin (n+1)) ↦ ((v a.1).get sorry)^(i : ℕ)
  have hV0 : LinearIndependent K V0.rowFun
  · sorry
  obtain (hs | hn) := em' (none ∈ range v)
  · set eα : {a // v a ≠ none} ≃ α :=
      Equiv.subtypeUnivEquiv <| fun x hx ↦ hs (hx ▸ mem_range_self x)
    apply rows_linearIndependent_of_submatrix eα id
    convert hV0
    ext m ⟨a,ha⟩
    simp_rw [ne_eq, submatrix_apply, id_eq, of_apply]
    rw [rectProjVandermonde_apply_some]
    simp
  obtain ⟨a0, ha0⟩ := hn
  have _ : Fintype { a // v a ≠ none } := Fintype.ofFinite _
  rw [Fintype.linearIndependent_iff] at hV0 ⊢
  intro c hc
  specialize hV0 (Set.restrict _ c) ?_
  · ext j
    convert congr_fun hc j
    simp
  simp only [ne_eq, restrict_apply, Subtype.forall] at hV0
  refine fun i ↦ (eq_or_ne i a0).elim ?_ ?_
  · rintro rfl
    replace hc := congr_fun hc ⊤
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hc
    rwa [Fintype.sum_eq_single i, Matrix.rowFun, rectProjVandermonde_apply_none_one v (n.succ) ha0 ⊤
      (by simp [Fin.top_eq_last]), mul_one] at hc
    rintro b hbi
    rw [hV0, zero_mul]
    exact (Injective.ne_iff' hv ha0).mpr hbi
  rintro hne
  rw [hV0]
  exact (Injective.ne_iff' hv ha0).mpr hne
