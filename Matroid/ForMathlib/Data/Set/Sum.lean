import Mathlib.Data.Set.Image

open Set

namespace Sum

variable {α β γ : Type*}

@[simp]
lemma image_elim_image_inl (f : α → γ) (g : β → γ) (s : Set α) :
    Sum.elim f g '' (.inl '' s) = f '' s := by
  simp [← image_comp]

@[simp]
lemma image_elim_image_inr (f : α → γ) (g : β → γ) (s : Set β) :
    Sum.elim f g '' (.inr '' s) = g '' s := by
  simp [← image_comp]
