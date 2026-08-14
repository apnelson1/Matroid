module

public import Matroid.Representation.Projective
public import Matroid.ForMathlib.LinearAlgebra.Vandermonde

@[expose] public section

variable {α β W W' 𝔽 R : Type*} {e f x : α} {I E B X Y : Set α} {M : Matroid α} [Field 𝔽]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']

open Set Matrix

namespace Matroid

namespace Representable

lemma encard_le_of_unifOn_two (h : (unifOn E 2).Representable 𝔽) : E.encard ≤ ENat.card 𝔽 + 1 := by
  obtain hlt | hle := lt_or_ge E.encard (2 : ℕ)
  · exact (show E.encard ≤ 1 from Order.le_of_lt_add_one hlt).trans (by simp)
  have hbound := h.encard_le_of_simple
  simp only [unifOn_ground_eq] at hbound
  rwa [unifOn_rank_eq hle, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one,
    add_comm (1 : ℕ∞)] at hbound


lemma encard_le_of_unif_two {a : ℕ} (h : (unif 2 a).Representable 𝔽) : a ≤ ENat.card 𝔽 + 1 :=  by
  simpa using h.encard_le_of_unifOn_two

@[simp] lemma removeLoops_representable_iff :
    M.removeLoops.Representable 𝔽 ↔ M.Representable 𝔽 := by
  refine ⟨fun ⟨v⟩ ↦ ?_, fun ⟨v⟩ ↦ ?_⟩
  · rw [← M.eq_restrict_removeLoops]
    exact (v.restrict M.E).representable
  rw [removeLoops_eq_restrict]
  exact (v.restrict _).representable

lemma noUniformMinor [Fintype 𝔽] (h : M.Representable 𝔽) :
    M.NoUniformMinor 2 (Fintype.card 𝔽 + 2) := by
  by_contra hcon
  obtain ⟨hm⟩ := not_noUniformMinor_iff.1 hcon
  have hcon := (h.isoMinor hm).encard_le_of_unif_two
  simp only [Nat.cast_add, Nat.cast_ofNat, ENat.card_eq_coe_fintype_card] at hcon
  rw [show (2 : ℕ∞) = 1 + 1 from rfl, ← add_assoc, ENat.add_one_le_iff] at hcon
  · simp at hcon
  exact ne_of_beq_false rfl

end Representable

def unifOn_rep (emb : α ↪ Option 𝔽) (a : ℕ) : (unifOn (univ : Set α) a).Rep 𝔽 (Fin a → 𝔽) where
  to_fun := rectVandermonde (fun i ↦ (emb i).elim 1 id) (fun i ↦ (emb i).elim 0 1) a
  indep_iff' I := by
    rw [rectVandermonde_linearIndepOn_iff₀]
    · simp only [unifOn_indep_iff, subset_univ, and_true, iff_self_and]
      refine fun _ i j hi hj heq ↦ (emb.apply_eq_iff_eq ..).1 <| ?_
      obtain hi' | ⟨x, hix⟩ := (emb i).eq_none_or_eq_some
      · obtain hj' | ⟨y, hjy⟩ := (emb j).eq_none_or_eq_some
        · rw [hi', hj']
        simp [hi', hjy] at heq
      obtain hj' | ⟨y, hjx⟩ := (emb j).eq_none_or_eq_some
      · simp [hj', hix] at heq
      obtain rfl : y = x := by simpa [hix, hjx] using heq
      rw [hjx, hix]
    refine fun i hi ↦ ?_
    obtain hi' | ⟨x, hi'⟩ := (emb i).eq_none_or_eq_some <;>
    simp [hi']

-- lemma unif_representable {a b : ℕ} (hb : b ≤ ENat.card 𝔽 + 1) : (unif a b).Representable 𝔽 := by
--   rw [← ENat.card_option, ← Fintype.card_fin b, ← ENat.card_eq_coe_fintype_card] at hb
--   rw? at hb

-- def unif_rep {a b : ℕ} (hb : b ≤ ENat.card 𝔽 + 1) : (unif a b).Rep 𝔽 (Fin a → 𝔽) where
--   to_fun i := by
--     rw [card_option]
--   indep_iff' := _
