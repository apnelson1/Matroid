import Matroid.Minor.Rank
import Matroid.Uniform
import Matroid.Simple
import Matroid.Minor.Iso
import Mathlib.Tactic.Linarith

variable {α : Type*} {M N M' : Matroid α} {I F X Y F' F₀ F₁ F₂ P L H H₁ H₂ H' B C D K : Set α} {e f : α}
variable {l r : ℕ}

open Set
namespace Matroid

@[simp]
lemma loopyOn.rank : M = loopyOn M.E ↔ M.rank = 0 := by
    sorry

-- lemma IsNonloop.contraction_points (he : M.IsNonloop e ) :
--         M.simplification.E.encard = (∑ M.IsLine L ∧ e ∈ L, L.encard) + 1

theorem kung_bound [RankFinite M]
        (hNoUnif : ∀ N : Matroid α, N ≤m M → l + 2 ≤ N.E.encard → N ≠ (unifOn (N.E ) 2 )) :
        --(hNoUnif : ¬ Nonempty ((unifOn (Set.univ : Set (Fin (l + 2))) 2) ≤i M)) :
        M.simplification.E.encard ≤ (l ^ (M.rank ) - 1)/(l - 1) := by
    suffices hn : ∀ n : ℕ, M.rank = n → M.simplification.E.encard ≤ (l ^ n - 1)/(l - 1)
    · exact hn M.rank rfl
    intro n hn
    induction n generalizing M with
    | zero =>
    -- We need a Thm that says that M has a non-loop element iff r(M)>0.
    -- Apparently the matroid of all loops is the called loopyOn. So I added the Lemma
    sorry
    | succ n ih =>
    have ⟨ e, he ⟩ : ∃ e, ¬ M.IsLoop e := by sorry

    --have hih : ¬ Nonempty ((unifOn (Set.univ : Set (Fin (l + 2))) 2) ≤i (M ／ {e})) := by sorry

    sorry
