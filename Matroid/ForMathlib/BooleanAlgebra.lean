
import Mathlib.Data.Set.Basic

lemma sdiff_le_sdiff_iff_le {α : Type*} [GeneralizedBooleanAlgebra α] {s t r : α} (hs : s ≤ r) (ht : t ≤ r) :
    r \ s ≤ r \ t ↔ t ≤ s := by
  refine ⟨fun h ↦ ?_, sdiff_le_sdiff_left⟩
  rw [← sdiff_sdiff_eq_self hs, ← sdiff_sdiff_eq_self ht]
  exact sdiff_le_sdiff_left h

theorem diff_subset_diff_iff_subset {α : Type*} {s t r : Set α} (hs : s ⊆ r) (ht : t ⊆ r) :
    r \ s ⊆ r \ t ↔ t ⊆ s :=
  sdiff_le_sdiff_iff_le hs ht
