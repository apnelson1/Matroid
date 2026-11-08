module

public import Mathlib.Data.PFun

@[expose] public section

namespace PFun

open Set

variable {α β γ : Type*} (f : α →. β) {φ : β → γ} {S T : Set β} {a b : α} {x y : β}

attribute [simp, grind →] Part.get_mem
attribute [grind <=] Part.mem_unique
attribute [grind <=] Part.mem_right_unique
attribute [simp, grind .] preimage_subset_dom
attribute [gcongr] preimage_mono

-- strictly stronger than preimage_inter
theorem preimage_inter' (s t : Set β) :
    f.preimage (s ∩ t) = f.preimage s ∩ f.preimage t := by grind

attribute [simp] preimage_univ

----------------------------------------------------

attribute [grind =] dom_coe ran_coe

lemma mem_preimage_self (h : a ∈ f.Dom) : a ∈ f.preimage {(f a).get h} := by
  simp only [mem_preimage, mem_singleton_iff, exists_eq_left]
  exact Part.get_mem h

@[simp]
lemma mem_image_iff {S : Set α} : x ∈ f.image S ↔ ∃ a ∈ S, x ∈ f a := by
  simp [image, graph']

def codRestrict (f : α →. β) (S : Set β) : α →. β :=
  f.restrict (preimage_subset_dom f S)

@[simp, grind =]
lemma mem_codRestrict : x ∈ (f.codRestrict S) a ↔ x ∈ f a ∧ x ∈ S := by
  simp only [codRestrict, mem_restrict, mem_preimage]
  grind

@[simp, grind =]
lemma ran_codRestrict : (f.codRestrict S).ran = f.ran ∩ S := by
  ext x
  simp only [ran, codRestrict, mem_restrict]
  grind

@[simp, grind =]
lemma dom_codRestrict : (f.codRestrict S).Dom = f.Dom ∩ f.preimage S := by
  ext a
  simp only [codRestrict, mem_dom, mem_restrict, mem_inter_iff]
  grind

@[simp] lemma preimage_codRestrict : (f.codRestrict S).preimage T = f.preimage (T ∩ S) := by grind

@[simp]
lemma codRestrict_codRestrict :
    (f.codRestrict S).codRestrict T = f.codRestrict (T ∩ S) := by
  unfold codRestrict
  rw [restrict_restrict]
  congr
  grind [preimage_restrict]
