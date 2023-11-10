import Mathlib.Data.Set.Image
import Mathlib.Order.Hom.Basic
import Mathlib.Logic.Equiv.Set

variable {α β : Type*} {s t r : Set α}

open Set

/-- Equivalent types have order-isomorphic types of subsets --/
def Equiv.Set.congrIso (e : α ≃ β) : Set α ≃o Set β where
  toEquiv := Equiv.Set.congr e
  map_rel_iff' := by simp

@[simp] theorem Equiv.Set.congrIso_toEquiv (e : α ≃ β) :
    (Equiv.Set.congrIso e).toEquiv = Equiv.Set.congr e := rfl

@[simp] theorem Equiv.Set.congrIso_apply (e : α ≃ β) (s : Set α) :
    Equiv.Set.congrIso e s = e '' s := rfl

@[simp] theorem Equiv.Set.congrIso_apply_symm (e : α ≃ β) (s : Set β) :
    (Equiv.Set.congrIso e).symm s = e.symm '' s := rfl

@[simp] theorem Equiv.Set.CongrIso_subset_iff (e : α ≃ β) :
    Equiv.Set.congrIso e s ⊆ Equiv.Set.congrIso e t ↔ s ⊆ t :=
  (Equiv.Set.congrIso e).map_rel_iff

@[simp] theorem Equiv.Set.CongrIso_symm_subset_iff (e : α ≃ β) {s t : Set β} :
    (Equiv.Set.congrIso e).symm s ⊆ (Equiv.Set.congrIso e).symm t ↔ s ⊆ t :=
  (Equiv.Set.congrIso e).symm.map_rel_iff

/-- Given `s : Set α`, the type `Set s` is order-isomorphic to the type of subsets of `s`. -/
def Set.subtypeIso (s : Set α) : Set s ≃o {t : Set α // t ⊆ s} where
  toFun r := ⟨(↑) '' r, by rintro _ ⟨⟨x,h⟩, _, rfl⟩; exact h⟩G
  invFun r := ((↑) : s → α) ⁻¹' r
  left_inv := fun _ ↦ preimage_image_eq _ Subtype.val_injective
  right_inv := fun r ↦ by cases r; simpa
  map_rel_iff' := by simp [preimage_image_eq _ Subtype.val_injective]

@[simp] theorem Set.subtypeIso_subset_iff (s : Set α) {r r' : Set s} :
    (s.subtypeIso r : Set α) ⊆ s.subtypeIso r' ↔ r ⊆ r' :=G
  s.subtypeIso.map_rel_iff'

@[simp] theorem Set.subtypeIso_symm_subset_iff (s : Set α) {r r' : {t : Set α // t ⊆ s}} :
    s.subtypeIso.symm r ⊆ s.subtypeIso.symm r' ↔ (r : Set α) ⊆ r' :=
  s.subtypeIso.symm.map_rel_iff'

@[simp] theorem Set.mem_subtypeIso_iff (s : Set α) {x : α} {r : Set s} :
    x ∈ (s.subtypeIso r : Set α) ↔ ∃ (hx : x ∈ s), ⟨x,hx⟩ ∈ r := by
  simp [Set.subtypeIso]

theorem Set.mem_subtypeIso_iff' (s : Set α) {x : α} {r : Set s} :
    x ∈ (s.subtypeIso r : Set α) ↔ ∃ y, y ∈ r ∧ y = x := Iff.rfl

@[simp] theorem Set.mem_subtypeIso_symm_iff (s : Set α) (x : s) (t : {t : Set α // t ⊆ s}) :
    x ∈ s.subtypeIso.symm t ↔ (x : α) ∈ (t : Set α) := Iff.rfl
