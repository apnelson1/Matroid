import Mathlib

variable {α : Type*}

class HasDelete (α β : Type*) where
  del : α → β → α

infixl:75 " ＼ " => HasDelete.del

def setDelete (s t : Set α) : Set α := s \ t

instance setDel {α : Type*} : HasDelete (Set α) (Set α) :=
  ⟨setDelete⟩

@[simp] lemma setdelete_eq_diff (s t : Set α) : s ＼ t = s \ t := rfl

/-- Can this be an abbrev? -/
instance elemDelete {α : Type*} : HasDelete (Set α) α := ⟨fun s x ↦ setDelete s {x}⟩


example : ({1,2,3} : Set ℕ) ＼ ({3} : Set ℕ) = {1,2} := by
  ext x
  simp [setDelete, Set.mem_diff_singleton]


example : ({1,2,3} : Set ℕ) ＼ 3 = {1,2} := by
  sorry
