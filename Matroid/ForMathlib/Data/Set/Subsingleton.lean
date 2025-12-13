import Mathlib.Data.Set.Subsingleton

variable {α : Type*} {x y z : α} {s t : Set α}

namespace Set

lemma Subsingleton.elim {x y} {s : Set α} (hs : s.Subsingleton) (hxs : x ∈ s) (hys : y ∈ s) :
    x = y := by
  obtain rfl | ⟨a, rfl⟩ := hs.eq_empty_or_singleton <;> simp_all

lemma Nontrivial.diff_singleton_nonempty (hs : s.Nontrivial) (x : α) : (s \ {x}).Nonempty := by
  rw [nonempty_iff_ne_empty]
  intro hs'
  obtain ⟨y, hys⟩ := hs.exists_ne x
  rw [Ne, ← mem_singleton_iff, ← mem_diff, hs'] at hys
  simp at hys

lemma Subsingleton.subset_or_disjoint (hs : s.Subsingleton) (t : Set α) : s ⊆ t ∨ Disjoint s t := by
  obtain rfl | ⟨e, rfl⟩ := hs.eq_empty_or_singleton <;> simp [em]

lemma Subsingleton.subset_of_nonempty_inter (hs : s.Subsingleton) (hst : (s ∩ t).Nonempty) :
    s ⊆ t := by
  obtain rfl | ⟨e, rfl⟩ := hs.eq_empty_or_singleton
  · simp at hst
  simpa using hst

lemma Subsingleton.disjoint_iff_left (hs : s.Subsingleton) : Disjoint s t ↔ (s ⊆ t → s = ∅) := by
  obtain rfl | ⟨e, rfl⟩ := hs.eq_empty_or_singleton <;> simp

lemma Subsingleton.disjoint_iff_right (hs : s.Subsingleton) : Disjoint t s ↔ (s ⊆ t → s = ∅) := by
  rw [disjoint_comm, hs.disjoint_iff_left]
