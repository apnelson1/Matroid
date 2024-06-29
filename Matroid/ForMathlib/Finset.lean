import Mathlib.Data.Finset.Basic

variable {α : Type*} {s t r : Finset α}

namespace Finset

lemma sdiff_erase_not_mem [DecidableEq α] {a : α} (h : a ∉ s) :
    s \ t.erase a = s \ t := by
  rw [sdiff_eq_sdiff_iff_inter_eq_inter, inter_erase, erase_eq_of_not_mem (by simp [h])]

lemma sdiff_subset_iff [DecidableEq α] : s \ t ⊆ r ↔ s ⊆ t ∪ r := by
  simp [← coe_subset, Set.diff_subset_iff]
