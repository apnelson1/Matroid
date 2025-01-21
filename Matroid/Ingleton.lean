import Matroid.Paving
import Matroid.Rank.Nat

open Set

namespace Matroid

variable {α : Type*}

def Ingleton (M : Matroid α) : Prop :=
  ∀ (A B C D : Set α), (A ∪ B ∪ C ∪ D).Finite →
    M.r A + M.r B + M.r (A ∪ B ∪ C) + M.r (A ∪ B ∪ D) + M.r (C ∪ D) ≤
      M.r (A ∪ B) + M.r (A ∪ C) + M.r (A ∪ D) + M.r (B ∪ C) + M.r (B ∪ D)

instance : MinorClosed Ingleton := sorry

theorem foo : ∃ S : Finset (Matroid (Fin 8)), S.card = 41 ∧
  ∀ (M : Matroid α), M.Finite → ((M.Ingleton ∧ M.SparsePaving) ↔ ¬ ∃ N ∈ S, N ≤i M) := sorry
