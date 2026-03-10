import Matroid.Graph.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
import Mathlib.LinearAlgebra.Matrix.Adjugate

open Set Matrix Function Classical

-- Golfed AI slop (Thanks, Gemini 3.1 pro). It looks good enough?

variable {R : Type*} [CommRing R] {n m : ℕ}

lemma det_eq_of_row_eq_single (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i j : Fin (n + 1)) (c : R)
    (h : ∀ j', A i j' = if j' = j then c else 0) :
    A.det = (-1) ^ (i + j : ℕ) * c * (A.submatrix i.succAbove j.succAbove).det := by
  rw [det_succ_row A i, Finset.sum_eq_single j]
  · simp [h j]
  · intro j' _ hj'
    simp [h j', hj']
  · simp

lemma isTotallyUnimodular_of_row_eq_single (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (i j : Fin (n + 1)) (c : R) (hc : c ∈ Set.range (SignType.cast : SignType → R))
    (h : ∀ j', A i j' = if j' = j then c else 0)
    (h_sub : (A.submatrix i.succAbove j.succAbove).det ∈ Set.range (SignType.cast : SignType → R)) :
    A.det ∈ Set.range (SignType.cast : SignType → R) := by
  rw [det_eq_of_row_eq_single A i j c h]
  rcases hc with ⟨sc, rfl⟩
  rcases h_sub with ⟨ssub, h_ssub⟩
  use ((-1) ^ (i + j : ℕ) * sc * ssub : SignType)
  rw [← h_ssub]
  push_cast
  rfl

def allOnes (n : Type*) [Fintype n] : Matrix n n R := fun _ _ ↦ 1

lemma det_eq_zero_of_sum_rows_eq_zero {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n R) (h : ∀ i, ∑ j, A i j = 0) : Matrix.det A = 0 := by
  have h1 : A * allOnes n = 0 := by
    ext i j
    simp [allOnes, Matrix.mul_apply, h]
  apply_fun (Matrix.adjugate A * ·) at h1
  rw [← mul_assoc, adjugate_mul, mul_zero, smul_mul, one_mul] at h1
  apply_fun (· (Classical.arbitrary n) (Classical.arbitrary n)) at h1
  simpa [allOnes] using h1

def IsIncidenceRow {n : ℕ} (row : Fin n → R) : Prop :=
  ∃ j1 j2 : Option (Fin n), ∀ j, row j =
    (if some j = j1 then (-1 : R) else 0) + (if some j = j2 then (1 : R) else 0)

lemma sum_eq_zero_or_exists_single_of_incidence_row {n : ℕ} (row : Fin n → R)
    (h : IsIncidenceRow row) : (∑ j, row j = 0) ∨
    (∃ j c, c ∈ Set.range (SignType.cast : _ → R) ∧ ∀ j', row j' = if j' = j then c else 0) := by
  rcases h with ⟨j1, j2, h_row⟩
  cases j1 <;> cases j2 <;> simp_all [Finset.sum_add_distrib] <;> right <;> rename_i x
  · exact ⟨x, 1, by simp⟩
  · exact ⟨x, -1, by simp⟩

noncomputable def f_inv {A B : Type*} (f : A → B) (x : Option B) : Option A :=
  match x with
  | none => none
  | some x => if h : ∃ j, f j = x then some (Classical.choose h) else none

lemma f_inv_eq {A B : Type*} (f : A → B) (hf : Function.Injective f) (x : Option B) (j : A) :
    (some j = f_inv f x) ↔ (some (f j) = x) := by
  cases x with
  | none => simp [f_inv]
  | some x =>
    simp only [f_inv]
    split_ifs with h
    · have h_choose := Classical.choose_spec h
      rw [Option.some.injEq, Option.some.injEq, ← hf.eq_iff, h_choose]
    · simp_all

lemma IsIncidenceRow_comp (row : Fin n → R) (f : Fin m → Fin n) (hf : Function.Injective f)
    (h : IsIncidenceRow row) : IsIncidenceRow (row ∘ f) := by
  rcases h with ⟨j1, j2, h_row⟩
  refine ⟨f_inv f j1, f_inv f j2, fun j ↦ ?_⟩
  simp [Function.comp_apply, h_row, f_inv_eq f hf]

lemma isTotallyUnimodular_of_incidence_matrix (k : ℕ) (A : Matrix (Fin k) (Fin k) R)
    (h : ∀ i, IsIncidenceRow (A i)) : A.det ∈ Set.range (SignType.cast : SignType → R) := by
  induction k with
  | zero => exact ⟨1, by simp [Matrix.det_isEmpty]⟩
  | succ k ih =>
    by_cases h_sum : ∀ i, ∑ j, A i j = 0
    · rw [det_eq_zero_of_sum_rows_eq_zero A h_sum]
      exact ⟨0, rfl⟩
    obtain ⟨i, hi⟩ := by simpa using h_sum
    obtain h_zero | ⟨j, c, hc, h_single⟩ :=
      sum_eq_zero_or_exists_single_of_incidence_row (A i) (h i)
    · contradiction
    exact isTotallyUnimodular_of_row_eq_single A i j c hc h_single <| ih _ fun i' ↦
    IsIncidenceRow_comp (A (i.succAbove i')) j.succAbove Fin.succAbove_right_injective
    <| h (i.succAbove i')

variable {α β : Type*} {G : Graph α β} {x y z u v w : α} {e f : β} {F : Set β} {X Y : Set α}

namespace Graph

structure orientation (G : Graph α β) where
  dInc : E(G) → V(G) × V(G)
  isLink_of_dInc : ∀ e, G.IsLink e.val (dInc e).1 (dInc e).2

def signedIncMatrix [DecidableEq V(G)] (D : orientation G) (𝔽 : Type*) [Ring 𝔽] :
    Matrix E(G) V(G) 𝔽 :=
  Matrix.of fun e ↦ Pi.single (D.dInc e).1 (-1 : 𝔽) + Pi.single (D.dInc e).2 (1 : 𝔽)

variable {𝔽 : Type*} [CommRing 𝔽] [DecidableEq V(G)]

lemma support_signedIncMatrix_subset (D : orientation G) (𝔽 : Type*) [Ring 𝔽] (e : E(G)) :
    (signedIncMatrix D 𝔽 e).support ⊆ {(D.dInc e).1, (D.dInc e).2} := by
  intro x hx
  simp only [signedIncMatrix, mem_support, of_apply, Pi.add_apply, Pi.single_apply] at hx
  split_ifs at hx
  · exact Or.inl (by assumption)
  · exact Or.inl (by assumption)
  · exact Or.inr (by assumption)
  · exact (hx (add_zero 0)).elim

lemma signedIncMatrix_support_eq_endSet (D : orientation G) (𝔽 : Type*) [Ring 𝔽] [Nontrivial 𝔽]
    {e : E(G)} (he : (D.dInc e).1 ≠ (D.dInc e).2) :
    (signedIncMatrix D 𝔽 e).support = Subtype.val ⁻¹' G.endSet e := by
  ext z
  simp only [signedIncMatrix, mem_support, of_apply, Pi.add_apply, Pi.single_apply,
    (D.isLink_of_dInc e).endSet_eq, mem_preimage, mem_insert_iff, Subtype.val_inj,
    mem_singleton_iff]
  split_ifs with h1 h2 h2
  · exact (he (h1.symm.trans h2)).elim
  all_goals simp [h1, h2]

lemma signedIncMatrix_row_support_card_two (D : orientation G) (𝔽 : Type*) [Ring 𝔽] (e : E(G)) :
    ((signedIncMatrix D 𝔽) e).support.ncard ≤ 2 := by
  refine (ncard_le_ncard (support_signedIncMatrix_subset D 𝔽 e) (toFinite _)).trans ?_
  by_cases h_eq : (D.dInc e).1 = (D.dInc e).2
  · rw [h_eq, pair_eq_singleton, ncard_singleton]
    exact Nat.le_succ 1
  rw [ncard_pair h_eq]

lemma signedIncMatrix_row_isIncidenceRow (D : orientation G) (e : E(G)) {g : Fin n → V(G)}
    (hg : Function.Injective g) : IsIncidenceRow (fun j => signedIncMatrix D 𝔽 e (g j)) := by
  refine ⟨f_inv g (some (D.dInc e).1), f_inv g (some (D.dInc e).2), fun j ↦ ?_⟩
  simp [signedIncMatrix, of_apply, Pi.add_apply, Pi.single_apply, f_inv_eq g hg]

lemma signedIncMatrix_isTotallyUnimodular (D : orientation G) :
    (signedIncMatrix D 𝔽).IsTotallyUnimodular := by
  rw [Matrix.isTotallyUnimodular_iff]
  rintro k f g
  by_cases hg : Function.Injective g
  · exact isTotallyUnimodular_of_incidence_matrix _ _
      fun i ↦ signedIncMatrix_row_isIncidenceRow D (f i) hg
  obtain ⟨j1, j2, h_eq, h_ne⟩ := Function.not_injective_iff.1 hg
  use 0
  rw [SignType.coe_zero, eq_comm]
  exact det_zero_of_column_eq h_ne fun k' ↦ by simp [h_eq]

end Graph
