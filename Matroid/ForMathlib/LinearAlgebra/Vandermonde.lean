import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.Vandermonde
import Matroid.ForMathlib.LinearAlgebra.LinearIndepOn
import Mathlib.Algebra.Algebra.Basic

set_option linter.style.longLine false

open Fin Matrix MvPolynomial


variable {n : ℕ} {R K : Type*} [CommRing R] [Field K]

section Rect

variable {α K R : Type*} [CommRing R] [Field K] {n : ℕ} {v w : α → K} {s : Set α}

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
    simp only [Ne, det_projVandermonde, dite_mul, Polynomial.X_pow_mul_C, Finset.prod_eq_zero_iff,
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
