import Mathlib.LinearAlgebra.Vandermonde
import Matroid.ForMathlib.LinearAlgebra.Matrix.Rowspace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Set Function Fin

namespace Matrix

variable {R α K : Type*} [CommRing R] [Field K] {n : ℕ} {a : α} {f v : α → R}

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
  rw [← Fintype.card_fin n] at hn
  obtain ⟨g⟩ := Embedding.nonempty_of_card_le hn
  apply cols_linearIndependent_of_submatrix g (Equiv.refl _)
  rw [linearIndependent_cols_iff_isUnit]
  exact vandermonde_isUnit_iff.2 (hv.comp g.injective)

/-- A rectangular Vandermonde matrix with possible extra rows equal to `(0,0, ..., 1)`,
indexed by the `a` for which `v a = none`. These rows can be thought of projectively
as 'infinity' rows.  -/
def rectProjVandermonde (v : α → Option R) (n : ℕ) : Matrix α (Fin n) R :=
  Matrix.of (fun a ↦ (v a).casesOn
    (n.casesOn finZeroElim (fun n ↦ Pi.single (Fin.last n) 1)) (fun x i ↦ x^(i : ℕ)))

theorem rectProjVandermonde_apply_some {v : α → Option R} {n : ℕ} {a : α} {x : R}
    (hx : v a = some x) (i : Fin n) : rectProjVandermonde v n a i = x^(i : ℕ) := by
   simp [rectProjVandermonde, hx]

theorem rectProjVandermonde_apply_none_cast {v : α → Option R} (ha : v a = none) (i : Fin n) :
    rectProjVandermonde v (n+1) a (Fin.castSucc i) = 0 := by
  simp only [rectProjVandermonde, Nat.zero_eq, Nat.rec_add_one, of_apply, ha, ne_eq,
    Pi.single_apply, if_neg (Fin.castSucc_lt_last i).ne]

theorem rectProjVandermonde_apply_none_last {v : α → Option R} (ha : v a = none) :
    rectProjVandermonde v (n+1) a (Fin.last n) = 1 := by
  simp only [rectProjVandermonde, Nat.zero_eq, Nat.rec_add_one, of_apply, ha, ne_eq,
    Pi.single_apply, if_true]

/-- If there are no infinity rows, then `rectProjVandermonde` is equal to `rectVandermonde`. -/
theorem rectProjVandermonde_eq_rectVandermonde {v : α → Option R} (hv : ∀ i, v i ≠ none) :
    rectProjVandermonde v n = rectVandermonde
      ( fun i ↦ (v i).get (Option.ne_none_iff_isSome.1 (hv i)) ) n  := by
  ext a i
  simp_rw [Option.ne_none_iff_exists'] at hv
  obtain ⟨x, hx⟩ := hv a
  rw [rectProjVandermonde_apply_some hx, rectVandermonde_apply]
  simp [hx]

/-- If `v` is injective, projective Vandermonde matrices have linearly independent rows. -/
theorem rectProjVandermonde_linearIndependent_rows [Fintype α] {v : α → Option K}
    (hv : Injective v) (hn : Fintype.card α ≤ n) :
    LinearIndependent K (rectProjVandermonde v n).rowFun := by
  obtain (rfl | n) := n
  · have : IsEmpty α := by
      rwa [Nat.le_zero, Fintype.card_eq_zero_iff] at hn
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
  apply rows_linearIndependent_union_of_upper_zero_block (s := {a0}) (t := {Fin.last n})
  · apply linearIndependent_unique _ (fun h0 ↦ ?_)
    replace h0 := congr_fun h0 ⟨_,rfl⟩
    simp only [default_coe_singleton, submatrix_apply, Pi.zero_apply] at h0
    rw [rectProjVandermonde_apply_none_last ha0] at h0
    exact one_ne_zero h0
  · set fn : Fin n → ↑({last n} : Set _)ᶜ := fun i ↦ ⟨castSucc i, (Fin.castSucc_lt_last i).ne⟩
    set s' := ↑({a0} : Set _)ᶜ
    have _ : Fintype s' := inferInstance
    have hcard : Fintype.card s' ≤ n := by
      rw [Fintype.card_compl_set, Fintype.card_ofSubsingleton]
      exact Nat.sub_le_of_le_add hn
    set v' : s' → K := fun a ↦ (v a).get
      ( by rw [← Option.ne_none_iff_isSome]; refine fun h ↦ a.prop <| hv (by rw [h, ha0]) )
    have hv' : ∀ i, some (v' i) = v i := by simp [v']
    have hv'_inj : Injective v' := by
      intro i j h
      apply_fun (↑) using Subtype.coe_injective
      apply_fun v using hv
      apply_fun some at h
      rwa [hv', hv'] at h
    apply rows_linearIndependent_of_submatrix (Equiv.refl _) fn
    convert rectVandermonde_linearIndependent_rows (v := v') hv'_inj hcard
    ext a j
    simp only [Equiv.coe_refl, submatrix_apply, id_eq, rectVandermonde_apply]
    rw [rectProjVandermonde_apply_some (hv' _).symm]
    rfl
  ext ⟨a,rfl⟩ ⟨i,(hi : i ≠ Fin.last _)⟩
  simp only [submatrix_apply, zero_apply]
  obtain (hicon | ⟨i, rfl⟩) := i.eq_castSucc_or_eq_last.symm; exact (hi hicon).elim
  rw [rectProjVandermonde_apply_none_cast ha0]

theorem rectProjVandermonde_rowSet_linearIndependent_iff {v : α → Option K} {n : ℕ}
    (hv : v.Injective) (s : Set α) :
    LinearIndependent K (s.restrict (rectProjVandermonde v n).rowFun) ↔ s.encard ≤ n := by
  refine ⟨fun h ↦ le_of_not_lt (fun hlt ↦ ?_), fun h ↦ ?_⟩
  · obtain ⟨t, hts, ht⟩ := exists_subset_encard_eq <| ENat.add_one_le_of_lt hlt
    have _ := (finite_of_encard_eq_coe ht).fintype
    replace h := LinearIndependent.mono_index _ h hts
    have hc := h.fintype_card_le_finrank
    rw [FiniteDimensional.finrank_fintype_fun_eq_card, Fintype.card_fin,
      ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, ncard_def, ht,
      ENat.toNat_add (by simp) (ENat.coe_toNat_eq_self.mp rfl),
      ENat.toNat_coe, _root_.map_one, add_le_iff_nonpos_right] at hc
    simp at hc
  rw [encard_le_coe_iff_finite_ncard_le] at h
  have _ := h.1.fintype
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at h
  exact rectProjVandermonde_linearIndependent_rows (hv.injOn _).injective h.2
