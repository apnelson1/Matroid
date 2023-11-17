import Mathlib.Data.Set.Image
import Mathlib.Order.Hom.Basic
import Mathlib.Logic.Equiv.Set

open Set

variable {α β : Type*} {s t r : Set α}
/-- Equivalent types have order-isomorphic types of subsets. --/
def Equiv.setOrderIso (e : α ≃ β) : Set α ≃o Set β where
  toEquiv := Equiv.Set.congr e
  map_rel_iff' := by simp

@[simp] theorem Equiv.setOrderIso_toEquiv (e : α ≃ β) :
    e.setOrderIso.toEquiv = Equiv.Set.congr e := rfl

@[simp] theorem Equiv.setOrderIso_apply (e : α ≃ β) (s : Set α) :
    e.setOrderIso s = e '' s := rfl

@[simp] theorem Equiv.setOrderIso_apply_symm (e : α ≃ β) (s : Set β) :
    e.setOrderIso.symm s = e.symm '' s := rfl

@[simp] theorem Equiv.setOrderIso_subset_iff (e : α ≃ β) :
    e.setOrderIso s ⊆ e.setOrderIso t ↔ s ⊆ t :=
  e.setOrderIso.map_rel_iff

@[simp] theorem Equiv.setOrderIso_symm_subset_iff (e : α ≃ β) {s t : Set β} :
    e.setOrderIso.symm s ⊆ e.setOrderIso.symm t ↔ s ⊆ t :=
  e.setOrderIso.symm.map_rel_iff

/-- An injection from `α` to `β` gives one from `Set α` to `Set β`.  -/
def Function.Embedding.setEmbedding (f : α ↪ β) : Set α ↪ Set β where
  toFun := Set.image f
  inj' := Set.image_injective.2 f.injective

@[simp] theorem Function.Embedding.setEmbedding_apply (f : α ↪ β) (s : Set α) :
    f.setEmbedding s = f '' s := rfl

/-- An injection from `α` to `β` gives an order embedding from `Set α` to `Set β`.  -/
def Function.Embedding.setOrderEmbedding (f : α ↪ β) : Set α ↪o Set β where
  toEmbedding := f.setEmbedding
  map_rel_iff' := fun {_} {_} ↦ Set.image_subset_image_iff f.injective

@[simp] theorem Function.Embedding.setOrderEmbedding_apply (f : α ↪ β) (s : Set α) :
    f.setOrderEmbedding s = f '' s := rfl

@[simp] theorem Function.Embedding.setOrderEmbedding_toEmbedding (f : α ↪ β) :
    f.setOrderEmbedding.toEmbedding = f.setEmbedding := rfl

/-- Given `s : Set α`, the natural order-embedding from `Set s` to `Set α`. -/
def Set.subtypeOrderEmbedding (s : Set α) : Set s ↪o Set α :=
  (Function.Embedding.subtype _).setOrderEmbedding

theorem Set.subtypeOrderEmbedding_apply (s : Set α) (t : Set s) :
    (s.subtypeOrderEmbedding t : Set α) = (fun (x : s) ↦ (x : α)) '' t := rfl

theorem Set.subtypeOrderEmbedding_coe (s : Set α) :
    (s.subtypeOrderEmbedding : Set s → Set α) = (fun x ↦ (↑) '' x) := rfl

@[simp] theorem Set.mem_subtypeOrderEmbedding_iff (s : Set α) {x : α} {r : Set s} :
    x ∈ (s.subtypeOrderEmbedding r : Set α) ↔ ∃ (hx : x ∈ s), ⟨x,hx⟩ ∈ r := by
  simp [Set.subtypeOrderEmbedding]

@[simp] theorem Set.subtypeOrderEmbedding_subset_iff (s : Set α) {r r' : Set s} :
    (s.subtypeOrderEmbedding r : Set α) ⊆ s.subtypeOrderEmbedding r' ↔ r ⊆ r' :=
  s.subtypeOrderEmbedding.map_rel_iff'

/-- Given `s : Set α`, the type `Set s` is order-isomorphic to the type of subsets of `s`. -/
def Set.subtypeOrderIso (s : Set α) : Set s ≃o {t : Set α // t ⊆ s} where
  toFun r := ⟨(fun (x : s) ↦ (x : α)) '' r, by rintro _ ⟨⟨x,h⟩, _, rfl⟩; exact h⟩
  invFun r := (fun (x : s) ↦ (x : α)) ⁻¹' r
  left_inv := fun _ ↦ preimage_image_eq _ Subtype.val_injective
  right_inv := fun r ↦ by cases r; simpa
  map_rel_iff' := by simp [preimage_image_eq _ Subtype.val_injective]

theorem Set.subtypeOrderIso_apply (s : Set α) (t : Set s) :
    (s.subtypeOrderIso t : Set α) = (fun (x : s) ↦ (x : α)) '' t := rfl

theorem Set.subtypeOrderIso_apply_symm {s : Set α} (t : {r : Set α // r ⊆ s}) :
    s.subtypeOrderIso.symm t = (fun (x : s) ↦ (x : α)) ⁻¹' t := rfl

@[simp] theorem Set.subtypeOrderIso_subset_iff (s : Set α) {r r' : Set s} :
    (s.subtypeOrderIso r : Set α) ⊆ s.subtypeOrderIso r' ↔ r ⊆ r' :=
  s.subtypeOrderIso.map_rel_iff'

@[simp] theorem Set.subtypeOrderIso_symm_subset_iff (s : Set α) {r r' : {t : Set α // t ⊆ s}} :
    s.subtypeOrderIso.symm r ⊆ s.subtypeOrderIso.symm r' ↔ (r : Set α) ⊆ r' :=
  s.subtypeOrderIso.symm.map_rel_iff'

@[simp] theorem Set.mem_subtypeOrderIso_iff (s : Set α) {x : α} {r : Set s} :
    x ∈ (s.subtypeOrderIso r : Set α) ↔ ∃ (hx : x ∈ s), ⟨x,hx⟩ ∈ r := by
  simp [Set.subtypeOrderIso]

@[simp] theorem Set.mem_subtypeOrderIso_iff' (s : Set α) {x : α} {r : Set s} :
    x ∈ (s.subtypeOrderIso r : Set α) ↔ ∃ y, y ∈ r ∧ y = x := Iff.rfl

@[simp] theorem Set.mem_subtypeOrderIso_symm_iff (s : Set α) (x : s) (t : {t : Set α // t ⊆ s}) :
    x ∈ s.subtypeOrderIso.symm t ↔ (x : α) ∈ (t : Set α) := Iff.rfl
