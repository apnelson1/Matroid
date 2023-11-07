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

theorem rectProjVandermonde_apply_some {f : α → Option R} {n : ℕ} {a : α} {x : R}
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

theorem rectProjVandermonde_eq_rectVandermonde {v : α → Option K} (hv : ∀ i, v i ≠ none) :
    rectProjVandermonde v n = rectVandermonde
      (fun a ↦ (v a).get
        (by rw [←Option.ne_none_iff_isSome]; exact fun h ↦ hv a h)) n  := by
  ext a i
  simp_rw [Option.ne_none_iff_exists'] at hv
  obtain ⟨x, hx⟩ := hv a
  rw [rectProjVandermonde_apply_some hx, rectVandermonde_apply]
  simp [hx]


theorem foo (v : α → Option K) (n : ℕ) :
    (rectProjVandermonde v (n+1)).submatrix (↑) (Fin.castSucc (n := n)) =
    rectVandermonde
      (fun a ↦ (v a).get (Option.ne_none_iff_isSome.1 a.2) : {a : α // v a ≠ none} → K) n := by
  ext ⟨a,ha⟩ j
  simp only [ne_eq, submatrix_apply, rectVandermonde_apply]
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 ha
  rw [rectProjVandermonde_apply_some hx]
  simp [hx]

theorem rectProjVandermonde_linearIndependent_rows [Fintype α] {v : α → Option K}
    (hv : Injective v) (hn : Fintype.card α ≤ n) :
    LinearIndependent K (rectProjVandermonde v n).rowFun := by
  obtain (rfl | n) := n
  · have : IsEmpty α
    · rwa [Nat.le_zero, Fintype.card_eq_zero_iff] at hn
    apply linearIndependent_empty_type
  classical

  obtain (h0 | ⟨a0, ha0⟩) := em' (∃ a, v a = none)
  · push_neg at h0
    rw [rectProjVandermonde_eq_rectVandermonde h0]
    apply rectVandermonde_linearIndependent_rows (fun x y hxy ↦ ?_) hn
    simp_rw [Option.ne_none_iff_exists'] at h0
    obtain ⟨ix,hix⟩ := h0 x; obtain ⟨iy,hiy⟩ := h0 y
    apply_fun v using hv
    simp only [hix, Option.get_some, hiy] at hxy
    rw [hiy, hix, hxy]



  have hA : LinearIndependent K <| submatrix (rectProjVandermonde v (n + 1)) Subtype.val Fin.castSucc
  · rw [foo]
    apply rectVandermonde_linearIndependent_rows


  have := foo v n

  -- set eα : α ≃ {x : Option α // x ≠ none} := Equiv.optionSubtype none ⟨Equiv.refl _, rfl⟩
  -- set eα' : {x : Option α // x ≠ none} ≃ {x : Option α // ∃ i, x = some i} :=
  --   (Equiv.subtypeEquiv (Equiv.refl _) (fun _ ↦ Option.ne_none_iff_exists'))
  set v' : {x : α // ∃ a, v x = some a} → K := fun x ↦ (v x).get sorry
  have hv' : Injective v' := sorry
  set fn : Fin n → {a // a < Fin.last n} := fun i ↦ ⟨i,sorry⟩

  set e_row := Equiv.sumCompl (fun x ↦ ∃ a, v x = some a)
  set e : ↑(({Fin.last n} : Set (Fin (n+1))))ᶜ ⊕ ({Fin.last n} : Set (Fin (n+1))) ≃ Fin (n+1) :=
  (by
    have := Equiv.sumCompl (fun x ↦ x ≠ Fin.last n)
    simp only [ne_eq, not_not] at this
    exact this )

  -- set e_col : ↑(({Fin.last n} : Set (Fin (n+1))))ᶜ ⊕ ({Fin.last n} : Set (Fin (n+1))) ≃ Fin (n+1) := Equiv.sumCompl sorry

  apply rows_linearIndependent_of_reindex e_row e_col
  set V := (rectProjVandermonde v (n+1)).submatrix e_row e_col with hV

  convert linearIndependent_rows_of_upper_tri V.toBlocks₁₁ V.toBlocks₁₂ V.toBlocks₂₂ _ _
  · ext (i | i) (j | j); rfl; rfl;
    · simp only [ne_eq, submatrix_apply, fromBlocks_apply₂₁, zero_apply]
      rw [rectProjVandermonde_apply_none_zero]
      · refine by_contra fun h ↦ i.prop ?_
        rw [← ne_eq, Option.ne_none_iff_exists'] at h
        exact h
      obtain ⟨⟨j,hjn⟩, hj⟩:= j
      simp [Fin.last] at hj ⊢
      exact hj
    rfl

  · refine rows_linearIndependent_of_submatrix (Equiv.refl _) fn  ?_
    have := rectVandermonde_linearIndependent_rows hv' (n := n) sorry
    convert this
    ext
    simp





  -- · apply rows_linearIndependent_of_submatrix (eα'.symm.trans eα.symm)




      -- simp only [ne_eq, submatrix_apply, fromBlocks_apply₁₂]
      -- rw [rectProjVandermonde_apply_none_zero]






  -- apply rows_linearIndependent_union_of_zero_block (s := {a | v a = none}) (t := {Fin.last n})
  -- · have _ : Subsingleton {a | v a = none} := sorry
  --   rw [linearIndependent_subsingleton_index]
  --   rintro ⟨a,(ha : v a = none)⟩ h0
  --   replace h0 := congr_fun h0 ⟨Fin.last n, rfl⟩
  --   simp only [coe_setOf, mem_setOf_eq, submatrix_apply, Pi.zero_apply] at h0
  --   rw [rectProjVandermonde_apply_none_one _ _ ha] at h0
  --   · exact one_ne_zero h0
  --   simp [Fin.last]
  -- ·




    -- rw [rectProjVandermonde_apply_none_one]
