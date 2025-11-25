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
