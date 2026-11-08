module

public import Mathlib.Data.Set.Image
public import Mathlib.Data.Sum.Basic

@[expose] public section

open Set

namespace Sum

variable {α β γ : Type*}

@[simp]
lemma preimage_image_inr (X : Set β) : Sum.inr ⁻¹' (Sum.inr '' X : Set (α ⊕ β)) = X :=
  preimage_image_eq X Sum.inr_injective

@[simp]
lemma preimage_image_inl (X : Set α) : Sum.inl ⁻¹' (Sum.inl '' X : Set (α ⊕ β)) = X :=
  preimage_image_eq X Sum.inl_injective

@[simp]
lemma image_elim_image_inl (f : α → γ) (g : β → γ) (s : Set α) :
    Sum.elim f g '' (.inl '' s) = f '' s := by
  simp [← image_comp]

@[simp]
lemma image_elim_image_inr (f : α → γ) (g : β → γ) (s : Set β) :
    Sum.elim f g '' (.inr '' s) = g '' s := by
  simp [← image_comp]
