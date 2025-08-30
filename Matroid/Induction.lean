import Mathlib.Combinatorics.Matroid.Circuit
import Mathlib.Data.Matrix.Rank

variable {α : Type*} {M : Matroid α} {X Y : Set α} {e f : α}

open Set

namespace Matroid

protected lemma strongInductionGround {P : Matroid α → Prop} {M : Matroid α} [M.Finite]
    (ih : ∀ M : Matroid α, M.Finite → (∀ N : Matroid α, N.E ⊂ M.E → P N) → P M) : P M := by
  obtain h_empt | ⟨e, he⟩ := M.E.eq_empty_or_nonempty
  · exact ih _ (by assumption) fun N hN ↦ by simp [h_empt, ssubset_iff_exists] at hN
  apply ih _ (by assumption) fun N hN ↦ ?_
  have : N.E.encard < M.E.encard := M.ground_finite.encard_lt_encard hN
  have : N.Finite := ⟨M.ground_finite.subset hN.subset⟩
  apply Matroid.strongInductionGround (M := N) ih
termination_by M.E.encard
