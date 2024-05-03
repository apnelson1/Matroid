
import Mathlib.Data.Set.Subset

open Function Set.Notation

variable {α β γ : Type*}

namespace Set

attribute [simp] Set.preimage_val_image_val_eq_self

@[simp] theorem image_val_image_val_eq (f : α → β) (s : Set α) (x : Set s) :
    (↑) '' ((fun x : s ↦ (⟨f x, mem_image_of_mem _ x.2⟩ : f '' s)) '' x) = f '' x := by
  aesop

@[simp] theorem image_val_image_eq_image_image_val (s : Set α) (t : Set β) (f : s → t) (x : Set s) :
    ↑((f '' (s ↓∩ x))) = f '' ↑(s ↓∩ x) := by
  aesop

-- @[simp] theorem image_val_eq (s : Set α) (x : Set s) : Subtype.val '' x = ↑x := rfl

theorem image_val_eq_coe (s : Set α) (x : Set s) : (fun a : s ↦ a.1) '' x = ↑x := rfl


@[simp] theorem image_val_image_eq (s : Set α) (t : Set s) (f : α → β) :
    (fun (x : s) ↦ f ↑x) '' t = f '' (↑t) := by
  ext; simp

theorem image_val_image_eq' (s : Set α) (t : Set s) (f : s → β) :
    (fun (x : s) ↦ f ↑x) '' t = f '' (↑t) := by
  ext; simp

theorem eq_image_val_of_subset {s x : Set α} (hsx : x ⊆ s) : ∃ (y : Set s), x = ↑y :=
  ⟨s ↓∩ x, by simpa⟩

theorem image_val_preimage_val_of_subset {s x : Set α} (hsx : x ⊆ s) : ↑(s ↓∩ x) = x := by
  simpa
