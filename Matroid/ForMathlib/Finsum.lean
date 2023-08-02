import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Ncard

open Set Function 

variable {ι N : Type _} {f g : ι → N} {s : Set ι}

@[to_additive]
theorem finprod_mem_le_finprod_mem [OrderedCommMonoid N] (hs : s.Finite) (h : ∀ i ∈ s, f i ≤ g i) : 
    ∏ᶠ (i ∈ s), f i ≤ ∏ᶠ (i ∈ s), g i := by 
  revert h
  apply @Finite.induction_on _ _ _ hs (by simp)
  intro a s has hs IH hle
  rw [finprod_mem_insert _ has hs, finprod_mem_insert _ has hs]
  exact mul_le_mul' (hle _ (mem_insert _ _)) (IH fun i hi ↦ hle i (mem_insert_of_mem _ hi))

@[to_additive]
theorem finprod_mem_le_finprod_mem' [OrderedCommMonoid N] (hf : (s ∩ mulSupport f).Finite) 
    (hg : (s ∩ mulSupport g).Finite) (h : ∀ i ∈ s, f i ≤ g i) : 
    ∏ᶠ (i ∈ s), f i ≤ ∏ᶠ (i ∈ s), g i := by 
  set s' := s ∩ (mulSupport f ∪ mulSupport g) with hs'
  have hs'fin : s'.Finite := by rw [hs', inter_distrib_left]; exact hf.union hg
  rw [finprod_mem_inter_mulSupport_eq f s s', finprod_mem_inter_mulSupport_eq g s s']
  · exact finprod_mem_le_finprod_mem hs'fin (fun i hi ↦ h i hi.1)
  · rw [hs', inter_assoc, inter_eq_self_of_subset_right (subset_union_right _ _)]
  rw [hs', inter_assoc, inter_eq_self_of_subset_right (subset_union_left _ _)]
  
@[to_additive]
theorem eq_of_finprod_mem_ge_finprod_mem_of_forall_le [OrderedCancelCommMonoid N]
    (hs : s.Finite) (h_le : ∀ i ∈ s, f i ≤ g i) (h_ge : ∏ᶠ i ∈ s, g i ≤ ∏ᶠ i ∈ s, f i) {a : ι} 
    (ha : a ∈ s) : f a = g a := by
  rw [show s = insert a (s \ {a}) by rw [insert_diff_singleton, insert_eq_of_mem ha], 
    finprod_mem_insert _ (fun h ↦ h.2 rfl) (hs.diff {a}), 
    finprod_mem_insert _ (fun h ↦ h.2 rfl) (hs.diff {a})] at h_ge
  exact (h_le a ha).antisymm (le_of_mul_le_mul_right' (h_ge.trans 
      (mul_le_mul_left' (finprod_mem_le_finprod_mem (hs.diff {a}) (fun i hi ↦ h_le i hi.1)) (f a))))
  
@[to_additive]
theorem eq_of_finprod_mem_ge_finprod_mem_of_forall_le' [OrderedCancelCommMonoid N]
    (hf : (s ∩ mulSupport f).Finite) (hg : (s ∩ mulSupport g).Finite) (h_le : ∀ i ∈ s, f i ≤ g i)
    (h_ge : ∏ᶠ i ∈ s, g i ≤ ∏ᶠ i ∈ s, f i) {a : ι} (ha : a ∈ s) : f a = g a := by
  set s' := s ∩ (mulSupport f ∪ mulSupport g) with hs'
  have hs'fin : s'.Finite := by rw [hs', inter_distrib_left]; exact hf.union hg
  rw [finprod_mem_inter_mulSupport_eq f s s', finprod_mem_inter_mulSupport_eq g s s'] at h_ge
  · obtain (h' | h') := em (a ∈ s')
    · exact eq_of_finprod_mem_ge_finprod_mem_of_forall_le hs'fin (fun i hi ↦ h_le i hi.1) h_ge h' 
    simp_rw [hs', mem_inter_iff, and_iff_right ha, mem_union, mem_mulSupport, not_or, not_not] at h'
    rw [h'.1, h'.2]
  · rw [hs', inter_assoc, inter_eq_self_of_subset_right (subset_union_right _ _)]
  rw [hs', inter_assoc, inter_eq_self_of_subset_right (subset_union_left _ _)]
    
@[to_additive]
theorem finprod_le_finprod_of_subset [CanonicallyOrderedMonoid N] (h : s ⊆ t) (ht : t.Finite) :
    ∏ᶠ x ∈ s, f x ≤ ∏ᶠ x ∈ t, f x := by
  rw [←inter_union_diff t s, inter_eq_right_iff_subset.mpr h,
    finprod_mem_union (@disjoint_sdiff_self_right _ s t _) (ht.subset h) (ht.diff _)]
  exact le_mul_right rfl.le

@[to_additive]
theorem finprod_le_finprod_of_subset' [CanonicallyOrderedMonoid N] (h : s ⊆ t) 
    (ht : (t ∩ mulSupport f).Finite) : ∏ᶠ x ∈ s, f x ≤ ∏ᶠ x ∈ t, f x := by
  rw [←finprod_mem_inter_mulSupport, ←finprod_mem_inter_mulSupport (s := t)]
  apply finprod_le_finprod_of_subset (inter_subset_inter_left _ h) ht

@[to_additive] 
theorem mem_le_finprod [CanonicallyOrderedMonoid N] (ha : a ∈ s) (hs : s.Finite) : 
    f a ≤ ∏ᶠ x ∈ s, f x := by 
  rw [←finprod_mem_singleton (f := f) (a := a)]
  exact finprod_le_finprod_of_subset (singleton_subset_iff.2 ha) hs
    
@[to_additive] 
theorem mem_le_finprod' [CanonicallyOrderedMonoid N] (ha : a ∈ s) (hs : (s ∩ mulSupport f).Finite) : 
    f a ≤ ∏ᶠ x ∈ s, f x := by 
  rw [←finprod_mem_singleton (f := f) (a := a)]
  exact finprod_le_finprod_of_subset' (singleton_subset_iff.2 ha) hs

@[to_additive, simp] 
theorem finprod_mem_const_eq [CommMonoid N] (s : Set α) (c : N) :
    ∏ᶠ x ∈ s, c = c ^ s.ncard := by 
  obtain (rfl | hc) := eq_or_ne c 1; simp
  obtain (hs | hs) := s.finite_or_infinite 
  · apply @Finite.induction_on _ _ _ hs (by simp)
    rintro a s has hs' IH
    rw [ncard_insert_of_not_mem has hs', finprod_mem_insert _ has hs', mul_comm, IH, pow_succ']
  rw [hs.ncard, pow_zero, finprod_mem_eq_one_of_infinite]
  rwa [mulSupport_const hc, inter_univ]

@[to_additive, simp] 
theorem finprod_const_eq [CommMonoid N] (ι : Type _) (c : N) :
    ∏ᶠ (_ : ι), c = c ^ (Nat.card ι) := by 
  rw [←finprod_mem_univ, finprod_mem_const_eq, ncard_univ]

attribute [simp] finsum_mem_const_eq finsum_const_eq

theorem finsum_mem_one_eq (s : Set α) : ∑ᶠ x ∈ s, 1 = s.ncard := by
  simp

theorem finsum_encard (c : Set (Set α)) (hfin : c.Finite) (hc : c.PairwiseDisjoint id) : 
    ∑ᶠ s ∈ c, s.encard = (⋃₀ c).encard := by 
  revert hc
  apply @Finite.induction_on _ _ _ hfin
  simp only [ mem_empty_iff_false, finsum_false, finsum_zero]
  · rw [sUnion_empty, encard_empty]; exact fun _ ↦ rfl
  intro a s has hs IH hdj
  rw [finsum_mem_insert _ has hs, IH (hdj.subset (subset_insert _ _)), sUnion_insert, 
    encard_union_eq]
  rw [disjoint_sUnion_right]
  exact fun t hts (hdj (mem_insert _ _ ) _)



-- theorem finsum_mem_sUnion' {t : Set (Set α)} (h : t.PairwiseDisjoint id) 
--     (ht : (t ∩ support f).Finite) (ht₁ : ∀ x ∈ t,  )

-- theorem finsum_foo (c : Set (Set α)) (hc : c.PairwiseDisjoint id) (hfin : ∀ s ∈ c, s.Finite) : 
--     ∑ᶠ s ∈ c, s.ncard = (⋃₀ c).ncard := by 
--   suffices h' : ∀ (c' : Set (Set α)) (hc' : c'.PairwiseDisjoint id) (hfin : ∀ s ∈ c', s.Finite)
--     (hne : ∀ s ∈ c', s.Nonempty), ∑ᶠ s ∈ c', s.ncard = (⋃₀ c').ncard
--   · rw [←finsum_mem_inter_support, h' (c ∩ support ncard) (hc.subset (inter_subset_left _ _)) 
--       (fun x hx ↦ hfin x hx.1) (fun x ⟨hxc,hx⟩ ↦ ?_ )]
--     congr
--     simp_rw [Set.ext_iff, mem_sUnion, mem_inter_iff, mem_support, ne_eq, and_assoc]
--     refine' fun x ↦ ⟨fun ⟨t, ht, _, hxt⟩ ↦ ⟨t, ht, hxt⟩, fun ⟨t, ht, hxt⟩ ↦ ⟨t, ht, _, hxt⟩⟩
--     rw [ncard_eq_zero (hfin _ ht), ←ne_eq, ←nonempty_iff_ne_empty]
--     exact ⟨_, hxt⟩ 
--     rwa [mem_support, ne_eq, ncard_eq_zero (hfin _ hxc), ←ne_eq, ←nonempty_iff_ne_empty] at hx 
--   intro c' hc' hc'fin hc'ne
--   obtain (h | h) := c'.finite_or_infinite
--   · revert hc'fin hc' hc'ne
--     apply @Finite.induction_on _ _ _ h
--     · simp only [ mem_empty_iff_false, finsum_false, finsum_zero]
--       rw [sUnion_empty, ncard_empty]; exact fun _ _ _ ↦ rfl
--     rintro a s has hs IH hdj hfin hc'ne
--     rw [finsum_mem_insert _ has hs, sUnion_insert, ncard_union_eq _ _ _, add_left_cancel_iff, IH]
--     · exact hdj.subset (subset_insert _ _)  
--     · exact fun x hx ↦ hfin _ (Or.inr hx)
--     · exact fun x hx ↦ hc'ne _ (Or.inr hx)
--     · sorry
--     · exact hfin _ (Or.inl rfl)
--     · sorry  


--   obtain (h | h) := (c ∩ support ncard).finite_or_infinite
--   · rw [←finsum_mem_inter_support, ← finsum_mem_one_eq, ← finsum_mem_one_eq] 
--   rw [←finsum_mem_one_eq, eq_comm,  ← finsum_mem_inter_support]
--   change ∑ᶠ (s ∈ c ∩ support ncard), s.ncard = _
  
--   obtain (h | h) := (c ∩ support ncard).finite_or_infinite
--   · rw [←finsum_mem_one_eq]
--     have := @finsum_mem_sUnion (Set α) ℕ _ ncard  
--     have' := @finsum_mem_sUnion (t := c ∩ support ncard) _ _ ncard
--     rw [←finsum_mem_one_eq]
--   obtain (h | h) := (⋃₀ c).finite_or_infinite
--   rw [←finsum_mem_one_eq, finsum_mem_sUnion hc]
  




-- theorem finsum_comm  [AddCommMonoid N] {α β : Type _} {f : α → β → N}: 
--     ∑ᶠ (a : α) (b : β), f a b = ∑ᶠ (b : β) (a : α), f a b := by
  

-- theorem finsum_inter_fiber_eq (hs : s.Finite) (f : ι → α) : 
--     ∑ᶠ (a : α), (s ∩ f ⁻¹' {a}).ncard = s.ncard := by 
  
--   rw [←finsum_congr (fun a ↦ finsum_mem_one_eq (s ∩ f ⁻¹' {a})), mem_inter_iff, ←finsum_mem_univ]
  
--   apply @Finite.induction_on _ _ _ hs (by simp)


--   rintro i s has hs' IH

  

  
  


--     have' := le_of_mul_le_mul_right' h_ge
  
  
--   have' := finprod_mem_insert f (not_mem_diff_ of_mem rfl : a ∉ s \ {a}) (hs.diff {a})
--   simp_rw [insert_diff_singleton, insert_eq_of_mem ha] at this
--   revert h_le h_ge ha a
--   apply @Finite.induction_on _ _ _ hs
--   · simp
--   rintro a s has hs IH hle hge x hx
--   rw [finprod_mem_insert, finprod_mem_insert] at hge
  




-- @[to_additive]

-- lemma finsum_mem_le_finsum_mem' [OrderedAddCommMonoid N] (hf : (s ∩ support f).Finite) 
--     (hg : (s ∩ support g).Finite) (h : ∀ i ∈ s, f i ≤ g i) : 
--     ∑ᶠ (i ∈ s), f i ≤ ∑ᶠ (i ∈ s), g i := by 
--   set s' := (s ∩ support f) ∪ (s ∩ support g) with hs'
--   rw [finsum_mem_inter_support_eq f s s', finsum_mem_inter_support_eq g s s']
--   · exact finsum_mem_le_finsum_mem (hf.union hg) 
--       (fun i hi ↦ h i (Or.elim hi And.left And.left))
--   · rw [hs', ←inter_distrib_left, inter_assoc, 
--       inter_eq_self_of_subset_right (subset_union_right _ _)]
--   rw [hs', ←inter_distrib_left, inter_assoc, inter_eq_self_of_subset_right (subset_union_left _ _)]
    
-- theorem finsum_le_finsum [OrderedAddCommMonoid N] (hf : (support f).Finite) 
--     (hg : (support g).Finite) (h : ∀ i, f i ≤ g i) : ∑ᶠ i, f i ≤ ∑ᶠ i, g i := by
--   rw [←finsum_mem_univ, ←finsum_mem_univ (f := g)]
--   apply finsum_mem_le_finsum_mem' <;> simpa 

    
--   have := finsum_mem_inter_support_eq f s ((s ∩ support f) \)
--   convert finsum_mem_le_finsum_mem (f := f) (g := g) (hf.union hg) 
--       (fun i hi ↦ h i (Or.elim hi And.left And.left)) using 1
--   · rw [←finsum_mem_inter_support_eq, eq_comm, ←finsum_mem_inter_support_eq (s := s)]
--     · rw [←inter_distrib_left, inter_assoc, inter_eq_self_of_subset_right (subset_union_left _ _)]
--     rw [←inter_distrib_left, inter_assoc, inter_eq_self_of_subset_right (subset_union_left _ _)]
  
    
    
    
    
--   rw [←finsum_mem_inter_support_eq f s]


--   · 
