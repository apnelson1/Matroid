import Mathlib

example {α β : Type} (A : Set α) (f : α → Set β) (x : β) (h : x ∈ ⋃ a ∈ A, f a) :
    ∃ a ∈ A, x ∈ f a := by
  simpa using h
