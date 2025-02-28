import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Matroid.ForMathlib.LinearAlgebra.LinearIndepOn
import Matroid.ForMathlib.LinearAlgebra.Matrix

open Set Function Fin

namespace Matrix

variable {R α K : Type*} [CommRing R] [Field K] {n : ℕ} {a : α} {f v : α → R}

section WithTop

variable {n : ℕ} {i j : Fin n} {v : Fin n → WithTop R}

/-- The `n × n` matrix whose `i`th row is `[1, a, a^2, ...]` if `v i = ↑a`,
and `[0, 0, ..., 1]` if `v i = ⊤`.
The exceptional type of row can be thought of as a normalization of the regular type of row,
with `a = ⊤`.-/
def vandermondeTop (v : Fin n → WithTop R) : Matrix (Fin n) (Fin n) R :=
  .of fun i j => (v i).recTopCoe (if j.1 + 1 = n then 1 else 0) (· ^ (j : ℕ))

lemma vandermondeTop_apply_ne_top (hi : v i ≠ ⊤) :
    vandermondeTop v i j = ((v i).untop hi) ^ (j : ℕ) := by
  lift v i to R using hi with a ha
  simp [vandermondeTop, of_apply, WithTop.untop_coe, ← ha]

lemma vandermondeTop_apply_top_zero (hi : v i = ⊤) (hj : j.1 + 1 < n) :
    vandermondeTop v i j = 0 := by
  simp [vandermondeTop, hi, hj.ne]

lemma vandermondeTop_apply_top_one (hi : v i = ⊤) (hj : j.1 + 1 = n) :
    vandermondeTop v i j = 1 := by
  simp [vandermondeTop, hi, hj]

lemma vandermondeTop_apply_top_eq_ite {n : ℕ} {i j : Fin (n+1)} {v : Fin (n+1) → WithTop R}
    (hi : v i = ⊤) : vandermondeTop v i j = if j = Fin.last n then 1 else 0 := by
  obtain rfl | hlt := j.le_last.eq_or_lt
  · simp [vandermondeTop_apply_top_one hi]
  rw [vandermondeTop_apply_top_zero hi (by omega), if_neg hlt.ne]

lemma vandermondeTop_eq_vandermonde (hv : ∀ i, (v i ≠ ⊤)) :
    vandermondeTop v = vandermonde fun i ↦ (v i).untop (hv i) := by
  obtain rfl | n := n
  · exact ext_of_single_vecMul (congrFun rfl)
  ext i j
  exact vandermondeTop_apply_ne_top (hv i)

/-- If a `vandermondeTop` matrix has exactly one 'infinity' row,
then its determinant is (up to sign) equal to that of the `vandermonde` matrix obtained by removing
this infinity row and the last column. -/
lemma det_vandermondeTop_of_unique {v : Fin (n+1) → WithTop R} {i₀ : Fin (n+1)}
    (hv : ∀ i, v i = ⊤ ↔ i = i₀) :
    (vandermondeTop v).det = (-1) ^ (i₀.1 + n) *
      (vandermonde (fun i ↦ (v (i₀.succAbove i)).untop
      (fun h ↦ i₀.succAbove_ne i <| (hv _).1 h))).det := by
  have hi₀ : v i₀ = ⊤ := (hv i₀).2 rfl
  have aux (i) : v (i₀.succAbove i) ≠ ⊤ := fun h ↦ i₀.succAbove_ne i <| (hv _).1 h
  rw [det_succ_row (i := i₀), Fintype.sum_eq_single (Fin.last n)]
  · convert rfl
    · simp [vandermondeTop_apply_top_eq_ite hi₀]
    rw [← vandermondeTop_eq_vandermonde]
    ext i j
    rw [vandermondeTop_apply_ne_top (by apply aux), submatrix_apply,
      vandermondeTop_apply_ne_top (aux _)]
    simp
  exact fun i hi ↦ by simp [vandermondeTop_apply_top_eq_ite hi₀, if_neg hi]

lemma det_vandermondeTop_ne_zero_iff [IsDomain R] {v : Fin n → WithTop R} :
    det (vandermondeTop v) ≠ 0 ↔ Function.Injective v := by
  obtain rfl | n := n
  · simp [Function.injective_of_subsingleton v]
  refine ⟨fun h i j hij ↦ by_contra fun hne ↦ h (det_zero_of_row_eq hne ?_), fun h ↦ ?_⟩
  · ext k
    simp [vandermondeTop, hij]
  obtain ⟨i₀, hi₀⟩ | htop := em <| ⊤ ∈ Set.range v
  · have aux (i) : v i = ⊤ ↔ i = i₀ := ⟨fun hi ↦ by rw [← h.eq_iff, hi, hi₀], fun h ↦ h ▸ hi₀⟩
    simp only [det_vandermondeTop_of_unique aux, ne_eq, mul_eq_zero, pow_eq_zero_iff', neg_eq_zero,
      one_ne_zero, AddLeftCancelMonoid.add_eq_zero, not_and, false_and, false_or,
      det_vandermonde_ne_zero_iff]
    intro i j (hij : (v (i₀.succAbove i)).untop _ = (v (i₀.succAbove j)).untop _)
    rwa [WithTop.eq_untop_iff, WithTop.coe_untop, h.eq_iff, Fin.succAbove_right_inj] at hij
  rw [vandermondeTop_eq_vandermonde (by simpa using htop), det_vandermonde_ne_zero_iff]
  intro i j (hij : (v i).untop _ = (v j).untop _)
  rwa [WithTop.eq_untop_iff, WithTop.coe_untop, h.eq_iff] at hij

end WithTop

theorem vandermonde_isUnit_iff {v : Fin n → K} : IsUnit (vandermonde v) ↔ Injective v := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, det_vandermonde_ne_zero_iff]

theorem vandermondeTop_isUnit_iff {v : Fin n → WithTop K} :
    IsUnit (vandermondeTop v) ↔ Injective v := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, det_vandermondeTop_ne_zero_iff]

/-- A rectangular Vandermonde matrix; its columns are indexed by `Fin n`,
    and its rows are geometric progressions `(1, a, a², ..., a^(n-1))`. -/
def rectVandermonde (v : α → R) (n : ℕ) : Matrix α (Fin n) R := .of (fun a i ↦ (v a) ^ (i : ℕ))

@[simp] theorem rectVandermonde_apply (v : α → R) (n : ℕ) (a : α) (i : Fin n) :
    rectVandermonde v n a i = (v a) ^ (i : ℕ) := rfl

/-- A rectangular Vandermonde matrix; its columns are indexed by `Fin n`,
    and its rows are geometric progressions `(1, a, a², ..., a^(n-1))`. -/
def rectVandermondeTop (v : α → WithTop R) (n : ℕ) : Matrix α (Fin n) R :=
  .of fun i j => (v i).recTopCoe (if j.1 + 1 = n then 1 else 0) (· ^ (j : ℕ))

theorem rectVandermonde_linearIndependent_rows [Fintype α] {v : α → K} (hv : Injective v)
    (hn : Fintype.card α ≤ n) : LinearIndependent K (rectVandermonde v n) := by
  apply rows_linearIndependent_of_submatrix (Fintype.equivFin α).symm (Fin.castLE hn)
  rw [linearIndependent_rows_iff_isUnit]
  exact vandermonde_isUnit_iff.2 (hv.comp (Fintype.equivFin α).symm.injective)

set_option linter.style.longLine false

lemma Fin.add_rev_cast (j : Fin (n+1)) : j.1 + j.rev.1 = n := by
  simp only [val_rev, Nat.reduceSubDiff]
  omega

lemma Fin.pow_rev (j : Fin (n+1)) {a : K} (ha : a ≠ 0) : a ^ j.rev.1 = a ^ n / a ^ j.1 := by
  rw [eq_div_iff (by simp [ha]), ← pow_add, add_comm, Fin.add_rev_cast]

def biVandermonde (v w : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  .of fun i j ↦ (v i)^(j : ℕ) * (w i)^(rev j : ℕ)

theorem biVandermonde_apply (v w : Fin n → R) (i j : Fin n) :
    biVandermonde v w i j = (v i)^(j : ℕ) * (w i)^(rev j : ℕ) := rfl

theorem biVandermonde_row_zero_left {v : Fin (n+1) → R} {i} (hv : v i = 0)
    (w : Fin (n+1) → R) : biVandermonde v w i = Pi.single 0 ((w i) ^ n) := by
  ext j
  rw [biVandermonde_apply, hv, Pi.single_apply]
  split_ifs with hj
  · simp [hj]
  rw [zero_pow (mt (by simp [Fin.ext_iff]) hj), zero_mul]

theorem biVandermonde_row_zero_right (v : Fin (n+1) → R) {w : Fin (n+1) → R} {i}  (hw : w i = 0) :
    biVandermonde v w i = Pi.single (Fin.last n) ((v i) ^ n) := by
  ext j
  rw [biVandermonde_apply, hw, Pi.single_apply]
  split_ifs with hj
  · simp [hj]
  rw [zero_pow (mt _ hj), mul_zero]
  rw [← rev_inj, rev_last]
  simp [Fin.ext_iff]

theorem biVandermonde_apply_of_ne (v : Fin (n+1) → K) {w : Fin (n+1) → K} {i j} (hw : w i ≠ 0) :
    biVandermonde v w i j = (v i) ^ j.1 * (w i) ^ n / (w i) ^ j.1 := by
  rw [biVandermonde_apply, Fin.pow_rev _ hw, mul_div_assoc]

theorem eq_biVandermonde_apply_iff {v w : Fin (n+1) → K} {i j} {a : K} (hw : w i ≠ 0) :
    biVandermonde v w i j = a ↔ (w i) ^ j.1 * a = (v i) ^ j.1 * (w i) ^ n := by
  rw [biVandermonde_apply_of_ne _ hw, div_eq_iff (by simp [hw]), eq_comm, mul_comm]

lemma biVandermonde_row_eq_zero_of_zero {v w : Fin (n+2) → K} {i} (hv : v i = 0) (hw : w i = 0) :
    biVandermonde v w i = 0 := by
  simp [biVandermonde_row_zero_left hv, hw]

lemma biVandermonde_row_eq_mul_vandermonde_row (v : Fin (n+1) → K) {i : Fin (n+1)}
    {w : Fin (n+1) → K} (hi : w i ≠ 0) :
    biVandermonde v w i = (w i)^n • (vandermonde (fun i ↦ (v i) / (w i))) i := by
  ext j
  simp only [biVandermonde, Nat.reduceSubDiff, of_apply, vandermonde, div_pow, mul_div]
  rw [Fin.pow_rev _ hi, Pi.smul_apply, smul_eq_mul, of_apply, mul_div_left_comm]

lemma biVandermonde_eq_mul_vandermonde (v w : Fin (n+1) → K) (hw : ∀ i, w i ≠ 0) :
    biVandermonde v w = .of fun i j ↦ (w i)^n • (vandermonde (fun i ↦ (v i) / (w i))) i j := by
  ext i j
  simp_rw [biVandermonde_row_eq_mul_vandermonde_row _ (hw i), of_apply, Pi.smul_apply]

lemma biVandermonde_det_eq_zero_of_zero {v w : Fin (n+2) → K} {i} (hvi : v i = 0)
    (hwi : w i = 0) : (biVandermonde v w).det = 0 :=
  det_eq_zero_of_row_eq_zero i <| by simp [← funext_iff, biVandermonde_row_eq_zero_of_zero hvi hwi]

lemma biVandermonde_det_eq_zero_of_mul_eq_mul {v w : Fin n → K} {i i' : Fin n} (hne : i ≠ i')
    (hvw : v i * w i' = v i' * w i) : (biVandermonde v w).det = 0 := by
  obtain rfl | rfl | n := n
  · apply finZeroElim i
  · exact (hne (by omega)).elim
  suffices h : ¬ LinearIndepOn K (biVandermonde v w) {i,i'} by
    rw [← not_ne_iff, ← isUnit_iff_ne_zero, ← isUnit_iff_isUnit_det,
      ← linearIndependent_rows_iff_isUnit]
    exact fun h' ↦ h <| h'.linearIndepOn.mono <| subset_univ _
  rw [linearDepOn_pair_iff _ hne]
  by_cases hwi : w i = 0
  · by_cases hvi : v i = 0
    · exact ⟨1, 0, by simp [biVandermonde_row_eq_zero_of_zero hvi hwi]⟩
    have hwi' : w i' = 0 := by simpa [hwi, hvi] using hvw
    by_cases hvi' : v i' = 0
    · refine ⟨0, 1, by simp [biVandermonde_row_eq_zero_of_zero hvi' hwi']⟩
    refine ⟨(v i') ^ (n+1), (v i) ^ (n+1), funext fun j ↦ ?_, (by simp [hvi, hvi'])⟩
    simp [biVandermonde_row_zero_right _ hwi, biVandermonde_row_zero_right _ hwi', Pi.single_apply,
      mul_comm]
  by_cases hwi' : w i' = 0
  · obtain hvi' : v i' = 0 := by simpa [hwi', hwi] using hvw
    exact ⟨0, 1, by simp [biVandermonde_row_eq_zero_of_zero hvi' hwi']⟩
  have hv : vandermonde (fun i ↦ v i / w i) i = vandermonde (fun i ↦ v i / w i) i' := by
    ext j
    rw [vandermonde_apply, (div_eq_div_iff hwi hwi').2 hvw]
    rfl
  refine ⟨(w i') ^ (n+1), (w i) ^ (n+1), ?_⟩
  simp [biVandermonde_row_eq_mul_vandermonde_row _ hwi, hv,
    biVandermonde_row_eq_mul_vandermonde_row _ hwi', hwi, hwi', smul_comm (m := (w i) ^ (n+1))]


theorem foo (v w : Fin n → K) : (biVandermonde v w).det =
    ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ((v j * w i) - (v i * w j)) := by
  obtain rfl | n := n
  · simp
  obtain ⟨i₀, i₀', hlt, hi₀, hi₀'⟩ | hnot := em (∃ i₀ i₀', i₀ < i₀' ∧ w i₀ = 0 ∧ w i₀' = 0)
  ·
    rw [det_zero_of_column_eq hlt.ne, eq_comm, Finset.prod_eq_zero (i := i₀) (by simp)]
    · rw [Finset.prod_eq_zero (i := i₀') (by simpa)]
      simp [hi₀, hi₀']



  obtain hw | ⟨i₀, hi₀⟩ := em' (0 ∈ range w)
  · replace hw : ∀ i, w i ≠ 0 := by simpa [mem_range] using hw
    simp_rw [biVandermonde_eq_mul_vandermonde _ _ hw, det_mul_column,
      det_vandermonde, div_sub_div _ _ (hw _) (hw _), Finset.prod_div_distrib, ← mul_div_assoc,
      mul_comm (a := w _) (b := v _)]
    rw [div_eq_iff (by simp [Ne, Finset.prod_eq_zero_iff, hw]), mul_comm]
    convert rfl using 2
    have hrw (x : Fin (n+1)) : (w x) ^ (Finset.Ioi x).card = (w x) ^ n / (w x) ^ x.1 := by
      rw [eq_div_iff (by simp [hw])]
      simp [← pow_add, Nat.sub_add_cancel x.is_le]
    simp_rw [Finset.prod_mul_distrib, Finset.prod_const, hrw, Finset.prod_div_distrib,
      Finset.prod_pow]
    rw [← mul_div_assoc, div_eq_iff (by simp [hw, Finset.prod_eq_zero_iff]), mul_comm,
      Finset.prod_comm' (s' := Finset.Iio) (t' := Finset.univ) (by simp)]
    simp
  obtain ⟨i₀', hne, hi₀'⟩ | hi₀ := em (∃ j ≠ i₀, w j = 0)
  ·
    · rw [Finset.prod_eq_zero (i := max i₀ i₀') (by simp)]
      rw [Finset.prod_eq_zero (i := i₀')]







    -- , Finset.prod_const, card_Ioi, add_tsub_cancel_right










-- theorem rectVandermondeTop_linearIndependent_rows [Fintype α] {v : α → WithTop K} (hv : Injective v)
--     (hn : Fintype.card α ≤ n) : LinearIndependent K (rectVandermondeTop v n) := by
--   classical
--   have hli1 : LinearIndepOn K (rectVandermondeTop v n) {x | v x ≠ ⊤} := by
--     rw [← linearIndependent_comp_subtype_iff]
--     convert rectVandermonde_linearIndependent_rows (α := {x | v x ≠ ⊤})
--       (v := fun x ↦ (v x.1).untop x.2) (n := n) (fun ⟨i,hi⟩ ⟨j,hj⟩ hij ↦ by
--         simpa [WithTop.untop_eq_iff, ne_eq, mem_setOf_eq, WithTop.coe_untop, hv.eq_iff] using hij)
--       (le_trans (by simp) hn)
--     ext ⟨i,hi : v i ≠ ⊤⟩ j
--     lift v i to K using hi with a ha
--     simp [rectVandermondeTop, ← ha]
--   obtain ⟨i₀, hi₀⟩ | h := em (∃ i, v i = ⊤)
--   · have hins : insert i₀ {x | v x ≠ ⊤} = univ := by simp [← hi₀, hv.eq_iff, eq_univ_iff_forall, em]
--     simp only [← linearIndepOn_univ, ← hins, ne_eq, linearIndepOn_insert_iff, hli1,
--       Finsupp.mem_span_image_iff_linearCombination, mem_setOf_eq, hi₀, not_true_eq_false, imp_false,
--       not_exists, not_and, true_and]
--     refine fun c hc hli ↦ ?_
--     have :

--     sorry
--   sorry






    -- rw [WithTop.untop_eq_iff] at hij



  -- obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hn
  -- obtain hnot | ⟨i₀, hi₀⟩ := em' (⊤ ∈ range v)
  -- ·
  -- apply rows_linearIndependent_of_submatrix (Fintype.equivFin α).symm (Fin.castAdd n)
  -- have :=
  -- rw [linearIndependent_rows_iff_isUnit]
  -- convert vandermondeTop_isUnit_iff.2 (hv.comp (Fintype.equivFin α).symm.injective)
  -- ext i j
  -- simp [rectVandermondeTop, vandermondeTop]

-- theorem rectVandermondeTop_linearIndependent_iff {R : Type*} [Field R] {v : α → WithTop R} :
--     LinearIndependent R (rectVandermondeTop v n) ↔ Injective v ∧ ENat.card α ≤ n := by
--   classical
--   obtain hinj | hinj := em' <| Injective v
--   · refine iff_of_false (fun hli ↦ hinj fun i j hij ↦ ?_) fun h ↦ hinj h.1
--     simp [← hli.injective.eq_iff, rectVandermondeTop, funext_iff, hij]
--   obtain hlt | hle := lt_or_le (n : ℕ∞) (ENat.card α)
--   · refine iff_of_false (fun hli ↦ hlt.not_le ?_) (by simp [hlt.not_le])
--     simpa using hli.enatCard_le_toENat_rank
--   simp only [hinj, hle, and_self, iff_true]
--   have hfin : Finite α := by
--     rw [← not_infinite_iff_finite, ← ENat.card_eq_top]
--     exact fun h ↦ by simp [h] at hle
--   have _ := Fintype.ofFinite α
--   rw [ENat.card_eq_coe_fintype_card, Nat.cast_le] at hle
--   obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (α := α) (β := Fin n) (by simpa)
--   suffices
--   -- have := det_vandermondeTop_ne_zero_iff.2 hinj


--     -- have hle : Cardinal.mk α ≤ n := by simpa using hli.cardinal_lift_le_rank
--     -- have := (@OrderHom.mono (Cardinal.{u_2}) ℕ∞ _ _ Cardinal.toENat) hle
--     -- rw [@OrderHomClass.coe_coe] at this


--   sorry

-- lemma rectVandermonde_linearIndepOn_iff (v : α → R) (s : Finset α) :
--     LinearIndepOn R (rectVandermonde v n) s ↔ Set.InjOn v s ∧ s.card ≤ n := by
--   _




-- theorem rectVandermonde_linearIndependent_rows [Fintype α] {v : α → K} (hv : Injective v)
--     (hn : Fintype.card α ≤ n) : LinearIndependent K (rectVandermonde v n).rowFun := by
--   apply rows_linearIndependent_of_submatrix (Fintype.equivFin α).symm (Fin.castLE hn)
--   rw [linearIndependent_rows_iff_isUnit]
--   exact vandermonde_isUnit_iff.2 (hv.comp (Fintype.equivFin α).symm.injective)

-- theorem rectVandermonde_linearIndependent_cols [Fintype α] {v : α → K} (hv : Injective v)
--     (hn : n ≤ Fintype.card α) : LinearIndependent K (rectVandermonde v n).colFun := by
--   rw [← Fintype.card_fin n] at hn
--   obtain ⟨g⟩ := Embedding.nonempty_of_card_le hn
--   apply cols_linearIndependent_of_submatrix g (Equiv.refl _)
--   rw [linearIndependent_cols_iff_isUnit]
--   exact vandermonde_isUnit_iff.2 (hv.comp g.injective)

-- /-- A rectangular Vandermonde matrix with possible extra rows equal to `(0,0, ..., 1)`,
-- indexed by the `a` for which `v a = none`. These rows can be thought of projectively
-- as 'infinity' rows.  -/
-- def rectProjVandermonde (v : α → Option R) (n : ℕ) : Matrix α (Fin n) R :=
--   Matrix.of (fun a ↦ (v a).casesOn
--     (n.casesOn finZeroElim (fun n ↦ Pi.single (Fin.last n) 1)) (fun x i ↦ x^(i : ℕ)))

-- theorem rectProjVandermonde_apply_some {v : α → Option R} {n : ℕ} {a : α} {x : R}
--     (hx : v a = some x) (i : Fin n) : rectProjVandermonde v n a i = x^(i : ℕ) := by
--    simp [rectProjVandermonde, hx]

-- theorem rectProjVandermonde_apply_none_cast {v : α → Option R} (ha : v a = none) (i : Fin n) :
--     rectProjVandermonde v (n+1) a (Fin.castSucc i) = 0 := by
--   simp only [rectProjVandermonde, Nat.zero_eq, Nat.rec_add_one, of_apply, ha, ne_eq,
--     Pi.single_apply, if_neg (Fin.castSucc_lt_last i).ne]

-- theorem rectProjVandermonde_apply_none_last {v : α → Option R} (ha : v a = none) :
--     rectProjVandermonde v (n+1) a (Fin.last n) = 1 := by
--   simp only [rectProjVandermonde, Nat.zero_eq, Nat.rec_add_one, of_apply, ha, ne_eq,
--     Pi.single_apply, if_true]

-- /-- If there are no infinity rows, then `rectProjVandermonde` is equal to `rectVandermonde`. -/
-- theorem rectProjVandermonde_eq_rectVandermonde {v : α → Option R} (hv : ∀ i, v i ≠ none) :
--     rectProjVandermonde v n = rectVandermonde
--       ( fun i ↦ (v i).get (Option.ne_none_iff_isSome.1 (hv i)) ) n  := by
--   ext a i
--   simp_rw [Option.ne_none_iff_exists'] at hv
--   obtain ⟨x, hx⟩ := hv a
--   rw [rectProjVandermonde_apply_some hx, rectVandermonde_apply]
--   simp [hx]

-- /-- If `v` is injective, projective Vandermonde matrices have linearly independent rows. -/
-- theorem rectProjVandermonde_linearIndependent_rows [Fintype α] {v : α → Option K}
--     (hv : Injective v) (hn : Fintype.card α ≤ n) :
--     LinearIndependent K (rectProjVandermonde v n).rowFun := by
--   classical
--   obtain (rfl | n) := n
--   · have : IsEmpty α := by
--       rwa [Nat.le_zero, Fintype.card_eq_zero_iff] at hn
--     apply linearIndependent_empty_type

--   obtain (h0 | ⟨a0, ha0⟩) := em' (∃ a, v a = none)
--   · push_neg at h0
--     rw [rectProjVandermonde_eq_rectVandermonde h0]
--     apply rectVandermonde_linearIndependent_rows (fun x y hxy ↦ ?_) hn
--     simp_rw [Option.ne_none_iff_exists'] at h0
--     obtain ⟨ix,hix⟩ := h0 x; obtain ⟨iy,hiy⟩ := h0 y
--     apply_fun v using hv
--     simp only [hix, Option.get_some, hiy] at hxy
--     rw [hiy, hix, hxy]
--   apply rows_linearIndependent_union_of_upper_zero_block (s := {a0}) (t := {Fin.last n})
--   · apply linearIndependent_unique _ (fun h0 ↦ ?_)
--     replace h0 := congr_fun h0 ⟨_,rfl⟩
--     simp only [default_coe_singleton, submatrix_apply, Pi.zero_apply] at h0
--     rw [rectProjVandermonde_apply_none_last ha0] at h0
--     exact one_ne_zero h0
--   · set fn : Fin n → ↑({last n} : Set _)ᶜ := fun i ↦ ⟨castSucc i, (Fin.castSucc_lt_last i).ne⟩
--     set s' := ↑({a0} : Set _)ᶜ
--     have _ : Fintype s' := inferInstance
--     have hcard : Fintype.card s' ≤ n := by
--       rw [Fintype.card_compl_set, Fintype.card_ofSubsingleton]
--       exact Nat.sub_le_of_le_add hn
--     set v' : s' → K := fun a ↦ (v a).get
--       ( by rw [← Option.ne_none_iff_isSome]; refine fun h ↦ a.prop <| hv (by rw [h, ha0]) )
--     have hv' : ∀ i, some (v' i) = v i := by simp [v']
--     have hv'_inj : Injective v' := by
--       intro i j h
--       apply_fun (↑) using Subtype.coe_injective
--       apply_fun v using hv
--       apply_fun some at h
--       rwa [hv', hv'] at h
--     apply rows_linearIndependent_of_submatrix (Equiv.refl _) fn
--     convert rectVandermonde_linearIndependent_rows (v := v') hv'_inj hcard
--     ext a j
--     simp only [Equiv.coe_refl, submatrix_apply, id_eq, rectVandermonde_apply]
--     rw [rectProjVandermonde_apply_some (hv' _).symm]
--     rfl
--   ext ⟨a,rfl⟩ ⟨i,(hi : i ≠ Fin.last _)⟩
--   simp only [submatrix_apply, zero_apply]
--   obtain (hicon | ⟨i, rfl⟩) := i.eq_castSucc_or_eq_last.symm; exact (hi hicon).elim
--   rw [rectProjVandermonde_apply_none_cast ha0]

-- theorem rectProjVandermonde_rowSet_linearIndependent_iff {v : α → Option K} {n : ℕ}
--     (hv : v.Injective) (s : Set α) :
--     LinearIndependent K (s.restrict (rectProjVandermonde v n).rowFun) ↔ s.encard ≤ n := by
--   refine ⟨fun h ↦ le_of_not_lt (fun hlt ↦ ?_), fun h ↦ ?_⟩
--   · obtain ⟨t, hts, ht⟩ := exists_subset_encard_eq <| ENat.add_one_le_of_lt hlt
--     have _ := (finite_of_encard_eq_coe ht).fintype
--     replace h := LinearIndependent.mono_index _ h hts
--     have hc := h.fintype_card_le_finrank
--     rw [FiniteDimensional.finrank_fintype_fun_eq_card, Fintype.card_fin,
--       ← Nat.cast_le (α := ℕ∞), ← toFinset_card, ← encard_eq_coe_toFinset_card, ht,
--       ENat.add_one_le_iff (by simp)] at hc
--     simp at hc
--   rw [encard_le_coe_iff_finite_ncard_le] at h
--   have _ := h.1.fintype
--   rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at h
--   exact rectProjVandermonde_linearIndependent_rows hv.injOn.injective h.2
