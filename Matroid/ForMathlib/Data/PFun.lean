import Mathlib.Data.PFun

namespace PFun

open Set Part

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

@[simp]
theorem preimage_empty : f.preimage ∅ = ∅ := by ext; simp [mem_preimage]

theorem disjoint_preimage_of_disjoint {s t : Set β} (h : Disjoint s t) :
    Disjoint (f.preimage s) (f.preimage t) := by
  rw [Set.disjoint_iff_inter_eq_empty] at h ⊢
  rw [← preimage_inter', h]
  simp [preimage]

----------------------------------------------------

attribute [grind =] dom_coe

lemma mem_preimage_self (h : a ∈ f.Dom) : a ∈ f.preimage {(f a).get h} := by
  simp only [mem_preimage, mem_singleton_iff, exists_eq_left]
  exact Part.get_mem h

@[simp]
lemma mem_image_iff {S : Set α} : x ∈ f.image S ↔ ∃ a ∈ S, x ∈ f a := by
  simp [image, graph']

lemma image_subset_ran {S : Set α} : f.image S ⊆ f.ran := by
  intro a
  simp only [mem_image_iff, ran, mem_setOf_eq, forall_exists_index, and_imp]
  grind

@[simp, grind =]
lemma ran_coe (f : α → β) : (PFun.lift f).ran = range f := by
  ext x
  simp [ran, eq_comm]

@[simp]
lemma dom_restrict {S : Set α} (hS : S ⊆ f.Dom) : (f.restrict hS).Dom = S := by
  ext a
  simp only [mem_dom, mem_restrict, exists_and_left, and_iff_left_iff_imp]
  exact fun haS ↦ Part.dom_iff_mem.mp (hS haS)

@[simp]
lemma ran_restrict {S : Set α} (hS : S ⊆ f.Dom) : (f.restrict hS).ran = f.image S := by
  ext a
  simp [ran]

@[simp]
lemma preimage_restrict {S : Set α} (hS : S ⊆ f.Dom) :
    (f.restrict hS).preimage T = f.preimage T ∩ S := by
  ext a
  simp only [mem_preimage, mem_restrict]
  grind

@[simp]
lemma restrict_restrict {S T : Set α} (hS : S ⊆ f.Dom) (hT : T ⊆ (f.restrict hS).Dom) :
    (f.restrict hS).restrict hT = f.restrict (p := S ∩ T) (by grind) := by
  ext a x
  grind [mem_restrict]

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
lemma codRestrict_codRestrict : (f.codRestrict S).codRestrict T = f.codRestrict (T ∩ S) := by
  simp only [codRestrict, restrict_restrict]
  congr
  grind [preimage_restrict]

@[simp]
lemma dom_map : (PFun.map φ f).Dom = f.Dom := by
  ext a
  simp only [mem_dom, PFun.map, Part.mem_map_iff]
  grind

@[simp]
lemma mem_map (a : α) (c : γ) : c ∈ (PFun.map φ f) a ↔ ∃ b ∈ f a, φ b = c := by
  simp [PFun.map]

@[simp]
lemma ran_map : (PFun.map φ f).ran = φ '' f.ran := by
  ext c
  simp only [ran, mem_map]
  grind

@[simp]
lemma preimage_map (S : Set γ) : (PFun.map φ f).preimage S = f.preimage (φ ⁻¹' S) := by
  ext a
  simp only [mem_preimage, mem_map]
  grind

@[simp]
lemma ran_eq_empty_iff_dom_eq_empty (f : α →. β) : f.ran = ∅ ↔ f.Dom = ∅ := by
  simp only [ran, Set.ext_iff, mem_setOf_eq, mem_empty_iff_false, mem_dom]
  grind
