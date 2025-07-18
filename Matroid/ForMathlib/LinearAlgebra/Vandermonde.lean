import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.Vandermonde
import Matroid.ForMathlib.LinearAlgebra.LinearIndepOn
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.Algebra.Algebra.Basic

set_option linter.style.longLine false

open Fin Matrix MvPolynomial


theorem LinearIndepOn.encard_le_toENat_rank' {ι R M : Type*} [Semiring R] [Nontrivial R]
    [AddCommMonoid M] [Module R M] {s : Set ι} {v : ι → M} (hs : LinearIndepOn R v s) :
    s.encard ≤ Cardinal.toENat (Module.rank R M) := by
  simpa using OrderHom.mono (β := ℕ∞) Cardinal.toENat <| hs.linearIndependent.cardinal_lift_le_rank

variable {n : ℕ} {R K : Type*} [CommRing R] [Field K]

section Rect
variable {α R : Type*} [CommRing R] [IsDomain R]

/-- If `v i` and `w i` are never both zero, and  `v i * w i' ≠ v i' * w i` for all `i ≠ i'`,
and the rectangular Vandermonde matrix coming from `v` and `w` has at least as many columns as rows,
then its rows are linearly independent. -/
lemma rectVandermonde_rows_linearIndependent [Fintype α] (hcard : Fintype.card α ≤ n) {v w : α → R}
    (hvw : ∀ ⦃i i'⦄, v i * w i' = v i' * w i → i = i') (h0 : ∀ ⦃i⦄, w i = 0 → v i ≠ 0) :
    LinearIndependent R (rectVandermonde v w n) := by
  set e := (Fintype.equivFin α).symm
  set m₀ := Fintype.card α
  replace hvw ⦃i i'⦄ : v i * w i' = v i' * w i ↔ i = i' := ⟨fun h ↦ hvw h, fun h ↦ by rw [h]⟩
  /- Extend to a square projective Vandermonde matrix with entries in `Polynomial R`
  by viewing the existing entries as constants, and appending new rows with entries coming from
  distinct new elements.
  This larger matrix has nonzero determininant by construction, so has linearly independent rows;
  therefore, so does the original matrix. -/
  let v' (i : Fin n) :=
    if hi : i < m₀ then Polynomial.C (v (e ⟨i, hi⟩)) else Polynomial.X ^ (i.1 + 1)
  let w' (i : Fin n) := Polynomial.C (if hi : i < m₀ then w (e ⟨i, hi⟩) else 1)
  have hdet : (projVandermonde v' w').det ≠ 0 := by
    simp only [Ne, det_projVandermonde, dite_mul, Polynomial.X_pow_mul_C, Finset.prod_eq_zero_iff,
      Finset.mem_univ, Finset.mem_Ioi, sub_eq_zero, true_and, not_exists, not_and, forall_iff,
      mk_lt_mk, v', w']
    refine fun i hi j hj hij h_eq ↦ hij.ne.symm ((em (j < m₀)).elim (fun hj ↦ ?_) (fun hj ↦ ?_))
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
both `v i` and `w i` are zero, and `v i * w j ≠ v j * w i` for distinct `i,j ∈ s`.
(We require `n = 1`, since otherwise `v i = w i = 0` and `s.encard = 1` gives a counterexample.) -/
lemma rectVandermonde_linearIndepOn_iff {v w : α → R} {s : Set α} (hn : n ≠ 1) :
      LinearIndepOn R (rectVandermonde v w n) s ↔ s.encard ≤ n ∧
      (∀ i ∈ s, v i = 0 → w i ≠ 0) ∧ (∀ ⦃i j⦄, i ∈ s → j ∈ s → v j * w i = v i * w j → i = j) := by
  classical
  obtain hlt | hle := lt_or_ge (n : ℕ∞) s.encard
  · refine iff_of_false (fun hli ↦ hlt.not_ge ?_) (by simp [hlt])
    simpa using hli.encard_le_toENat_rank'
  refine ⟨fun h ↦ ⟨hle, ?_⟩, fun h ↦ ?_⟩
  · obtain rfl | n := n
    · simp [show s = ∅ by simpa using hle]
    have aux (i) : i ∈ s → v i = 0 → w i ≠ 0 := fun hi hv hw ↦ h.ne_zero hi <| by
      rw [rectVandermonde_apply_zero_right hw, hv, zero_pow (by simpa using hn), Pi.single_zero]
    refine ⟨aux, fun i j his hjs hij ↦ by_contra fun hne ↦ ?_⟩
    replace h := (linearIndepOn_pair_iff' _ hne).1 <| h.mono (Set.pair_subset_iff.2 ⟨his, hjs⟩)
    obtain ⟨⟨hvj0,-⟩, ⟨hvi0, -⟩⟩ : (v j = 0 ∧ n ≠ 0) ∧ v i = 0 ∧ n ≠ 0 := by
      simp_rw [← pow_eq_zero_iff']
      apply h _ _ (funext fun k ↦ ?_)
      simp only [Pi.smul_apply, rectVandermonde_apply, smul_eq_mul, ← k.rev_add_cast, pow_add,
        ← mul_assoc, mul_comm _ ((w _) ^ _), ← mul_pow, mul_comm (w i), hij]
      ring
    refine aux i his hvi0 <| by_contra fun hne ↦ ?_
    specialize h ((w j) ^ n) ((w i) ^ n) (funext fun k ↦ ?_)
    · cases k using Fin.cases with
      | zero => simp [rectVandermonde_apply, mul_comm]
      | succ k => simp [rectVandermonde_apply, hvi0, hvj0]
    simp [hne] at h
  have hsfin := (s.finite_of_encard_le_coe hle).fintype
  rw [← linearIndependent_set_coe_iff]
  refine rectVandermonde_rows_linearIndependent ?_ (by aesop) (by aesop)
  rwa [Set.encard_eq_coe_toFinset_card, Set.toFinset_card, Nat.cast_le] at hle

lemma rectVandermonde_linearIndepOn_iff₀ {v w : α → R} {s : Set α}
    (hvw : ∀ i ∈ s, v i = 0 → w i ≠ 0) : LinearIndepOn R (rectVandermonde v w n) s ↔ s.encard ≤ n ∧
    (∀ ⦃i j⦄, i ∈ s → j ∈ s → v j * w i = v i * w j → i = j) := by
  obtain rfl | hne := eq_or_ne n 1
  · refine ⟨fun h ↦ ?_, fun ⟨hcard, h⟩ ↦ ?_⟩
    · have hscard := by simpa using h.encard_le_toENat_rank'
      refine ⟨hscard, ?_⟩
      rw [Set.encard_le_one_iff] at hscard
      aesop
    obtain rfl | ⟨x, rfl⟩ := Set.encard_le_one_iff_eq.1 hcard <;>
    simp [rectVandermonde, funext_iff]
  rw [rectVandermonde_linearIndepOn_iff hne, and_iff_right hvw]

/-- A version of `rectVandermonde_linearIndepOn_iff` for the 'non-projective' Vandermonde matrix
with rows of the form `[1,x,...,x^(n-1)]`. In this case, linear independence is just injectivity. -/
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
  simp only [Pi.one_apply, one_ne_zero, ne_eq, mul_one, Set.InjOn, and_congr_right_iff]
  aesop

end Rect
