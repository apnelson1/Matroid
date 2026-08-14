module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Complex.Exponential
public import Mathlib.Data.Set.Card
public import Matroid.ForMathlib.Card
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.IsBase

@[expose] public section

universe u1 u2 u3 u4

variable {α : Type u1} {ι : Type u2} {σ : Type u3} {R : Type u4} [CommRing R]

namespace ZeroPattern

open Real Norm

lemma Finsupp.card_antidiagonal {k : ℕ} (m : Fin k →₀ ℕ) :
    (Finset.antidiagonal m).card = 2 ^ (m.sum (fun _ ↦ id)) := by
  sorry

lemma norm_mul_le {m : ℕ} {a b : ℝ} (f g : MvPolynomial (Fin m) ℝ)
    (hf : ∀ m, |f.coeff m| ≤ a) (hg : ∀ m, |g.coeff m| ≤ b)  :
    ∀ mn, |(f * g).coeff mn| ≤ a * b * 2 ^ ((f * g).totalDegree) := by
  have ha : 0 ≤ a := le_trans (by simp) (hf 0)
  have hb : 0 ≤ b := le_trans (by simp) (hg 0)
  intro mn
  rw [MvPolynomial.coeff_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  -- simp_rw [abs_mul]
  have h1 : ∀ x ∈ Finset.antidiagonal mn, |f.coeff x.1 * g.coeff x.2| ≤ a * b :=
    fun x _ ↦ (abs_mul _ _).trans_le (mul_le_mul (hf x.1) (hg x.2) (by simp) ha)

  have h2 : ((Finset.antidiagonal mn).card : ℝ) ≤ 2 ^ (f * g).totalDegree := by
    obtain rfl | hne := eq_or_ne mn 0
    · simp
      sorry
    rw [Finsupp.card_antidiagonal]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    refine pow_right_mono₀ (by simp) ?_
    rw [MvPolynomial.totalDegree_eq, Finset.le_sup_iff]
    · simp
      refine ⟨mn, ?_⟩
      rw [MvPolynomial.coeff_eq_zero_of_totalDegree_lt]


    sorry
    simp


  refine (Finset.sum_le_sum h1).trans ?_

  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [mul_comm (a * b)]
  apply mul_le_mul_of_nonneg_right h2 (mul_nonneg ha hb)






def Realisable (f : ι → MvPolynomial σ ℤ) (S : Set ι) : Prop :=
  ∃ (𝔽 : Type u4) (_ : Field 𝔽) (u : σ → 𝔽),
    ∀ i, ((f i).map <| Int.castRingHom 𝔽).eval u = 0 ↔ i ∈ S

theorem card_bound {m N k : ℕ} (c d : ℕ) (f : Fin N → MvPolynomial (Fin m) ℤ)
    (hfd : ∀ i, (f i).totalDegree ≤ d) (hfc : ∀ i m, (f i).coeff m ≤ d)
    (hk : ((N * d + m).choose m) * (logb 2 (3 * k) + N * logb 2 (c * (exp d) * N ^ d)) < k) :
    {S : Finset (Fin N) | Realisable f S}.encard < k := by
  rw [← not_le, ← Fin.nonempty_embedding_iff_le_encard]
  rintro ⟨T⟩
  set g : Fin k → MvPolynomial (Fin m) ℤ := fun s ↦ ∏ i ∈ (T s).1, f i with hg_def
  have hdeg : ∀ s, (g s).totalDegree ≤ N * d := by
    intro hdeg
    simp [hg_def]
    refine (MvPolynomial.totalDegree_finset_prod _ _).trans ?_
    refine (Finset.sum_le_sum (fun i _ ↦ hfd i)).trans ?_
    rw [Finset.sum_const, smul_eq_mul]
    exact mul_le_mul_right' (card_finset_fin_le _)  _



  -- set g := ∏ i
