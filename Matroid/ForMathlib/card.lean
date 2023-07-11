import Mathlib.SetTheory.Cardinal.Finite

theorem ENat.le_coe_iff {n : ℕ∞} {k : ℕ} : n ≤ ↑k ↔ ∃ (n₀ : ℕ), n = n₀ ∧ n₀ ≤ k :=
  WithTop.le_coe_iff

theorem ENat.exists_eq_top_or_coe (n : ℕ∞) : n = ⊤ ∨ ∃ (n₀ : ℕ), n = n₀ := by
  obtain (rfl | n) := n; exact Or.inl rfl; exact Or.inr ⟨_,rfl⟩

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

theorem Finite.encard_eq_coe (h : s.Finite) : s.encard = ENat.toNat s.encard :=
  (ENat.coe_toNat h.encard_lt_top.ne).symm

theorem Finite.exists_encard_eq_coe (h : s.Finite) : ∃ (n : ℕ), s.encard = n := 
  ⟨_, h.encard_eq_coe⟩ 

theorem Infinite.encard_eq {s : Set α} (h : s.Infinite) : s.encard = ⊤ := by 
  have := h.to_subtype
  rw [encard, ←PartENat.withTopEquiv.symm.injective.eq_iff, Equiv.symm_apply_apply, 
    PartENat.withTopEquiv_symm_top, PartENat.card_eq_top_of_infinite]

@[simp] theorem encard_lt_top_iff : s.encard < ⊤ ↔ s.Finite :=
  ⟨fun h ↦ by_contra fun h' ↦ h.ne (Infinite.encard_eq h'), Finite.encard_lt_top⟩

@[simp] theorem encard_ne_top_iff : s.encard ≠ ⊤ ↔ s.Finite := by 
  rw [←WithTop.lt_top_iff_ne_top, encard_lt_top_iff]
  
@[simp] theorem encard_eq_top_iff : s.encard = ⊤ ↔ s.Infinite := by 
  rw [←not_iff_not, ←Ne.def, encard_ne_top_iff, not_infinite]

theorem encard_diff_add_encard_of_subset (h : s ⊆ t) : (t \ s).encard + s.encard = t.encard := by 
  rw [←encard_union_eq disjoint_sdiff_left, diff_union_self, union_eq_self_of_subset_right h]

theorem exists_subset_encard_eq (hk : k ≤ s.encard) : ∃ t, t ⊆ s ∧ t.encard = k := by 
  obtain (rfl | ⟨n, hkn⟩) := k.exists_eq_top_or_coe
  · refine' ⟨_, Subset.rfl, _⟩; rw [top_le_iff, encard_eq_top_iff] at hk; exact hk.encard_eq
  obtain (rfl | n) := n
  · refine' ⟨_, empty_subset _, by simp [hkn]⟩
  have hdecr : n < ENat.toNat k := by simp only [hkn, Nat.cast_succ]; exact Nat.lt.base n 
  have hnle : n ≤ encard s
  · subst hkn; rw [Nat.cast_succ] at hk; exact le_of_add_le_left hk
  obtain ⟨t₀, ht₀s, ht₀⟩ := exists_subset_encard_eq (k := (n : ℕ∞)) hnle
  subst hkn
  have hne : t₀ ≠ s
  · rintro rfl
    rw [ht₀, Nat.cast_succ, ←Nat.cast_one, ←Nat.cast_add, Nat.cast_le] at hk
    simp at hk
  obtain ⟨e, he⟩ := exists_of_ssubset (ht₀s.ssubset_of_ne hne)
  refine' ⟨insert e t₀, insert_subset he.1 ht₀s, _⟩ 
  rw [encard_insert_of_not_mem he.2, ht₀, Nat.cast_succ]
termination_by _ => ENat.toNat k

theorem exists_supset_subset_ncard_eq (hst : s ⊆ t) (hsk : s.encard ≤ k) (hkt : k ≤ t.encard) : 
    ∃ r, s ⊆ r ∧ r ⊆ t ∧ r.encard = k := by 
  obtain (hs | hs) := eq_or_ne s.encard ⊤
  · rw [hs, top_le_iff] at hsk; subst hsk; exact ⟨s, Subset.rfl, hst, hs⟩ 
  obtain ⟨k, rfl⟩ := exists_add_of_le hsk
  obtain ⟨k', hk'⟩ := exists_add_of_le hkt
  have hk : k ≤ encard (t \ s)
  · rw [←encard_diff_add_encard_of_subset hst, add_comm] at hkt
    exact WithTop.le_of_add_le_add_right hs hkt   
  obtain ⟨r', hr', rfl⟩ := exists_subset_encard_eq hk
  refine' ⟨s ∪ r', subset_union_left _ _, union_subset hst (hr'.trans (diff_subset _ _)), _⟩ 
  rw [encard_union_eq (disjoint_of_subset_right hr' disjoint_sdiff_right)]

  
      --   have hc : ENat.toNat (s \ {e}).encard < ENat.toNat s.encard
      --   · 
      --   , Infinite.encard_eq (h.diff (finite_singleton e)), top_add]
      
      -- termination_by _ => ENat.toNat s.encard
      -- decreasing_by exact hc



  

--   have hc : ENat.toNat (s \ {e}).encard < ENat.toNat s.encard
--   · 
--   , Infinite.encard_eq (h.diff (finite_singleton e)), top_add]

-- termination_by _ => ENat.toNat s.encard
-- decreasing_by exact hc
  
  
  

  
  
  


end Set

