import Mathlib.Data.Set.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Algebra.Group.Int
import Mathlib.Algebra.Ring.Int

variable {α β : Type*} {s t r : Finset α} {a b : α}

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

lemma erase_eq_empty_of_mem [DecidableEq α] {s : Finset α} {a : α} (h : a ∈ s) :
    Finset.erase s a = ∅ ↔ s = {a} := by
  rw [Finset.erase_eq_empty_iff, or_iff_right_iff_imp]
  aesop

lemma coe_card_inter [DecidableEq α] (s : Finset α) (t : Finset α) :
    (s ∩ t).card = (s.card : ℤ) + t.card - (s ∪ t).card := by
  rw [Finset.card_inter, Nat.cast_sub, Nat.cast_add]
  exact card_union_le s t

lemma singleton_subset_inter_and_union_subset_singleton [DecidableEq α] {s t : Finset α} {e : α}
    (h : {e} ⊆ s ∩ t) (h' : s ∪ t ⊆ {e}) : s = {e} ∧ t = {e} := by
  refine ⟨?_, ?_⟩
  · exact Subset.antisymm (Finset.union_subset_left h') (h.trans Finset.inter_subset_left)
  · exact Subset.antisymm (Finset.union_subset_right h') (h.trans Finset.inter_subset_right)

lemma singleton_of_mem_card_le_one {e : α} {s : Finset α} (hs : s.card ≤ 1)
    (he : e ∈ s) : s = {e} := by
  ext x; refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp_rw [(card_le_one_iff.mp hs) he h, mem_singleton]
  rwa [mem_singleton.mp h]

lemma inter_ssubset_of_not_subset_left {s t : Finset α} (h : ¬s ⊆ t) : s ∩ t ⊂ s := by
  refine ssubset_iff_subset_ne.mpr ⟨inter_subset_left, ?_⟩
  contrapose! h
  rwa [inter_eq_left] at h

lemma inter_ssubset_of_not_subset_right {s t : Finset α} (h : ¬t ⊆ s) : s ∩ t ⊂ t := by
  rw [inter_comm]; exact inter_ssubset_of_not_subset_left h

lemma exists_minimal_satisfying_subset (P : Finset α → Prop) {s : Finset α}
    {e : Finset α} (he : e ⊆ s) (hP : P e) : ∃ a ⊆ s, P a ∧ ∀ a' ⊆ a, P a' → a' = a := by
  set S := {a | a ⊆ s ∧ P a}
  have h_fin : Set.Finite S := s.powerset.finite_toSet.subset (by
    intro a ha; simp only [mem_coe, mem_powerset]; exact ha.1)
  have : Set.Nonempty S := by use e; exact ⟨he, hP⟩
  obtain ⟨a, h₁, h₂⟩ := h_fin.toFinset.exists_minimal (h_fin.toFinset_nonempty.mpr this)
  simp only [Set.Finite.mem_toFinset, lt_eq_subset, S, Set.mem_setOf_eq, and_imp] at h₁ h₂
  use a
  refine ⟨h₁.1, h₁.2, fun a' ha' h ↦ ?_⟩
  specialize h₂ a' (ha'.trans h₁.1) h
  rw [Finset.ssubset_def] at h₂
  push_neg at h₂
  exact Subset.antisymm ha' (h₂ ha')
