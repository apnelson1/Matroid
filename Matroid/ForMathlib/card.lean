import Mathlib.SetTheory.Cardinal.Finite

theorem PartENat.card_sum (α β : Type _) :
    PartENat.card (α ⊕ β) = PartENat.card α + PartENat.card β := by
  simp only [PartENat.card, Cardinal.mk_sum, map_add, Cardinal.toPartENat_lift]

namespace Set

variable {s t : Set α}

noncomputable def encard (s : Set α) := PartENat.withTopEquiv (PartENat.card s)

@[simp] theorem encard_eq_zero : s.encard = 0 ↔ s = ∅ := by
  rw [encard, ←PartENat.withTopEquiv.symm.injective.eq_iff, Equiv.symm_apply_apply, 
    PartENat.withTopEquiv_symm_zero, PartENat.card_eq_zero_iff_empty, isEmpty_subtype, 
    eq_empty_iff_forall_not_mem]
  
@[simp] theorem encard_empty : (∅ : Set α).encard = 0 := by 
  rw [encard_eq_zero]

@[simp] theorem encard_singleton (e : α) : ({e} : Set α).encard = 1 := by 
  rw [encard, ←PartENat.withTopEquiv.symm.injective.eq_iff, Equiv.symm_apply_apply, 
    PartENat.card_eq_coe_fintype_card, Fintype.card_ofSubsingleton, Nat.cast_one]; rfl 
  
theorem encard_union_eq (h : Disjoint s t) : (s ∪ t).encard = s.encard + t.encard := by 
  classical
  have e := (Equiv.Set.union (by rwa [subset_empty_iff, ←disjoint_iff_inter_eq_empty])).symm
  simp [encard, ←PartENat.card_congr e, PartENat.card_sum, PartENat.withTopEquiv]
  
theorem encard_le_of_subset (h : s ⊆ t) : s.encard ≤ t.encard := by
  rw [←union_diff_cancel h, encard_union_eq disjoint_sdiff_right]; exact le_self_add
  
theorem encard_insert_of_not_mem (has : a ∉ s) : (insert a s).encard = s.encard + 1 := by 
  rw [←union_singleton, encard_union_eq (by simpa), encard_singleton]
  
theorem Finite.encard_lt_top (h : s.Finite) : s.encard < ⊤ := by
  refine' h.induction_on (by simpa using WithTop.zero_lt_top) _
  rintro a t hat _ ht'
  rw [encard_insert_of_not_mem hat]
  exact lt_tsub_iff_right.1 ht'

theorem Infinite.encard_eq (h : s.Infinite) : s.encard = ⊤ := by 
  
  
  


end Set

