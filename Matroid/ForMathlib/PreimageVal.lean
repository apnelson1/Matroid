
import Mathlib.Data.Set.Subset

open Function Set.Notation

variable {α β γ : Type*}

namespace Set

-- attribute [simp] Set.preimage_val_image_val_eq_self

@[simp] theorem image_val_image_val_eq (f : α → β) (s : Set α) (x : Set s) :
    (↑) '' ((fun x : s ↦ (⟨f x, mem_image_of_mem _ x.2⟩ : f '' s)) '' x) = f '' x := by
  aesop

-- @[simp] theorem image_val_image_eq_image_image_val (s : Set α) (t : Set β) (f : s → t) (x : Set s) :
--     ↑((f '' (s ↓∩ x))) = f '' ↑(s ↓∩ x) := by
--   rfl
--   -- aesop

-- @[simp] theorem image_val_eq (s : Set α) (x : Set s) : Subtype.val '' x = ↑x := rfl

theorem image_val_eq_coe (s : Set α) (x : Set s) : (fun a : s ↦ a.1) '' x = ↑x := rfl

@[simp] theorem image_val_image_eq (s : Set α) (t : Set s) (f : α → β) :
    (fun (x : s) ↦ f ↑x) '' t = f '' (↑t) :=
  Eq.symm (image_image f Subtype.val t)

theorem Subset.eq_image_val {s x : Set α} (hsx : x ⊆ s) : ∃ (y : Set s), x = ↑y :=
  ⟨s ↓∩ x, by simpa⟩

theorem Subset.image_val_preimage_val_eq {s x : Set α} (hsx : x ⊆ s) : ↑(s ↓∩ x) = x := by
  simpa

end Set
-- theorem forall_setSubtype_pred_iff {s : Set α} {P : Set α → Prop} :
--     (∀ (x : Set s), P (↑x)) ↔ ∀ x ⊆ s, P x :=
--   ⟨ fun h x hx ↦ by simpa [image_val_preimage_val_of_subset hx] using h (s ↓∩ x),
--     fun h x ↦ h ↑x (by simp) ⟩

-- theorem exists_setSubtype_pred_iff {s : Set α} {P : Set α → Prop} :
--     (∃ (x : Set s), P (↑x)) ↔ ∃ x ⊆ s, P x :=
--   ⟨ fun ⟨x,hx⟩ ↦ ⟨x, by simp, hx⟩,
--     fun ⟨x, hxs, hx⟩ ↦ ⟨s ↓∩ x, by rwa [image_val_preimage_val_of_subset hxs]⟩ ⟩
