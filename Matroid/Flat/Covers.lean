import Matroid.Minor.Rank
import Matroid.Uniform
import Matroid.Simple
import Matroid.Minor.Iso
import Mathlib.Tactic.Linarith
import Matroid.Flat.LowRank

variable {α : Type*} {M N M' : Matroid α} {I F X Y F' F₀ F₁ F₂ P L H H₁ H₂ H' B C D K : Set α} {e f : α}
variable {l r : ℕ}

open Set
namespace Matroid

@[simp]
lemma loopyOn.rank : M = loopyOn M.E ↔ M.eRank = 0 := by
  refine ⟨ ?_, ?_ ⟩
  · --exact fun h ↦ rank_eq_zero_iff.mpr h
    intro h
    rw[h]
    exact eRank_loopyOn M.E
  intro h
  apply eq_loopyOn_iff.2
  refine ⟨rfl, ?_ ⟩
  intro X hX hXI
  have : M.eRk X = 0 := by
    have : M.eRk X ≤ 0 := by
      grw [←h, eRk_le_eRank M X]
    exact nonpos_iff_eq_zero.mp this
  have h0 : X.encard = 0 := by
    rw[←this]
    exact (Indep.eRk_eq_encard hXI).symm
  exact encard_eq_zero.mp h0


-- lemma IsNonloop.contraction_points (he : M.IsNonloop e ) :
--         M.simplification.E.encard = (∑ M.IsLine L ∧ e ∈ L, L.encard) + 1

theorem kung_bound [RankFinite M]
    (hNoUnif : ∀ N : Matroid α, N ≤m M → N = (unifOn (N.E ) 2 ) → N.E.encard < l + 2) :
    --(hNoUnif : ¬ Nonempty ((unifOn (Set.univ : Set (Fin (l + 2))) 2) ≤i M)) :
    {P : Set α | M.IsPoint P}.encard ≤ (l ^ (M.rank ) - 1)/(l - 1) := by
    --M.simplification.E.encard ≤ (l ^ (M.rank ) - 1)/(l - 1) := by
  suffices hn : ∀ n : ℕ, M.rank = n → {P : Set α | M.IsPoint P}.encard ≤ (l ^ n - 1)/(l - 1)
  · exact hn M.rank rfl
  intro n hn
  induction n generalizing M with
  | zero =>
  -- We need a Thm that says that M has a non-loop element iff r(M)>0.
  -- Apparently the matroid of all loops is the called loopyOn. So I added the Lemma
  sorry
  | succ n ih =>
    have ⟨ e, he ⟩ : ∃ e, ¬ M.IsLoop e := by
      -- use loopyOn_isLoop_iff
      sorry
-- eq_unifOn_of_eRank_le_two will be useful
    --have hsum : {P : Set α | M.IsPoint P}.encard = (∑ L ∈ {L : Set α | M.IsLine L ∧ e ∈ L}, (L.encard)) + 1 := by sorry

    sorry


def IsUniform_minor_free (M : Matroid α) ( a b : ℕ ) :=
    ∀ N : Matroid α, N ≤m M → N = (unifOn (N.E ) (a + 1) ) → N.E.encard < b
