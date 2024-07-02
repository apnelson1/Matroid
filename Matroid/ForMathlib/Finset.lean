import Mathlib.Data.Finset.Basic

variable {α : Type*} {s t r : Finset α} {a b : α}

namespace Finset

variable [DecidableEq α]

lemma sdiff_erase_not_mem (h : a ∉ s) : s \ t.erase a = s \ t := by
  rw [sdiff_eq_sdiff_iff_inter_eq_inter, inter_erase, erase_eq_of_not_mem (by simp [h])]

lemma sdiff_subset_iff : s \ t ⊆ r ↔ s ⊆ t ∪ r := by
  simp [← coe_subset, Set.diff_subset_iff]

lemma pair_diff_left (hne : a ≠ b) : ({a, b} : Finset α) \ ({a} : Finset α) = ({b} : Finset α) := by
  aesop

lemma pair_diff_right (hne : a ≠ b) : ({a, b} : Finset α) \ ({b} : Finset α) = ({a} : Finset α) :=
  Finset.pair_comm a b ▸ Finset.pair_diff_left hne.symm


lemma insert_sdiff_self_of_not_mem (h : a ∉ s) : insert a s \ {a} = s := by
  rw []
  ext1 x
  simp_all only [mem_sdiff, mem_insert, mem_singleton]
  refine ⟨fun ⟨h, h'⟩ ↦ (false_or_iff _).mp ((eq_false h') ▸ h),
     fun hx ↦ ⟨Or.inr hx, ne_eq x a ▸ ?_⟩⟩
  contrapose! h
  exact h ▸ hx
