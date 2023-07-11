import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Nat.Cast.WithTop

instance : WellFoundedRelation ℕ∞ where
  rel := (· < ·)
  wf := IsWellFounded.wf

theorem ENat.le_coe_iff {n : ℕ∞} {k : ℕ} : n ≤ ↑k ↔ ∃ (n₀ : ℕ), n = n₀ ∧ n₀ ≤ k :=
  WithTop.le_coe_iff

theorem ENat.exists_eq_top_or_coe (n : ℕ∞) : n = ⊤ ∨ ∃ (n₀ : ℕ), n = n₀ := by
  obtain (rfl | n) := n; exact Or.inl rfl; exact Or.inr ⟨_,rfl⟩

theorem PartENat.card_sum (α β : Type _) :
    PartENat.card (α ⊕ β) = PartENat.card α + PartENat.card β := by
  simp only [PartENat.card, Cardinal.mk_sum, map_add, Cardinal.toPartENat_lift]

theorem WithTop.add_right_cancel_iff {α : Type _} [Add α] [LE α] {a b c : WithTop α} 
    [IsRightCancelAdd α] (ha : a ≠ ⊤) : b + a = c + a ↔ b = c := by
  lift a to α using ha
  obtain rfl | hb := (eq_or_ne b ⊤)
  · rw [top_add, eq_comm, WithTop.add_coe_eq_top_iff, eq_comm]
  lift b to α using hb
  simp_rw [←WithTop.coe_add, eq_comm, WithTop.add_eq_coe, coe_eq_coe, exists_and_left, 
    exists_eq_left, add_left_inj, exists_eq_right, eq_comm]
  
theorem WithTop.add_right_cancel {α : Type _} [Add α] [LE α] {a b c : WithTop α} 
    [IsRightCancelAdd α] (ha : a ≠ ⊤) (hle : b + a = c + a) : b = c :=
  (WithTop.add_right_cancel_iff ha).1 hle

theorem WithTop.add_left_cancel_iff {α : Type _} [Add α] [LE α] {a b c : WithTop α} 
    [IsLeftCancelAdd α] (ha : a ≠ ⊤) : a + b = a + c ↔ b = c := by
  lift a to α using ha
  obtain rfl | hb := (eq_or_ne b ⊤)
  · rw [add_top, eq_comm, WithTop.coe_add_eq_top_iff, eq_comm]
  lift b to α using hb
  simp_rw [←WithTop.coe_add, eq_comm, WithTop.add_eq_coe, eq_comm, coe_eq_coe, 
    exists_and_left, exists_eq_left', add_right_inj, exists_eq_right']

theorem WithTop.add_left_cancel {α : Type _} [Add α] [LE α] {a b c : WithTop α} 
    [IsLeftCancelAdd α] (ha : a ≠ ⊤) (hle : a + b = a + c) : b = c :=
  (WithTop.add_left_cancel_iff ha).1 hle

namespace Set

theorem Function.invFunOn_injOn_image [Nonempty α] (f : α → β) (s : Set α) : 
    Set.InjOn (Function.invFunOn f s) (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ he
  rw [←Function.invFunOn_apply_eq (f := f) hx, he, Function.invFunOn_apply_eq (f := f) hx']

theorem Function.invFunOn_image_image_subset [Nonempty α] (f : α → β) (s : Set α) : 
    (Function.invFunOn f s) '' (f '' s) ⊆ s := by 
  rintro _ ⟨_, ⟨x,hx,rfl⟩, rfl⟩; exact Function.invFunOn_apply_mem hx

theorem Function.injOn_iff_invFunOn_image_image_eq_self [Nonempty α] {f : α → β} {s : Set α} : 
    InjOn f s ↔ (Function.invFunOn f s) '' (f '' s) = s := by 
  refine' ⟨fun h ↦ _, fun h ↦ _⟩
  · rw [h.invFunOn_image Subset.rfl]
  rw [InjOn, ←h]
  rintro _ ⟨_, ⟨x,hx,rfl⟩, rfl⟩ _ ⟨_, ⟨x',hx',rfl⟩, rfl⟩ h
  rw [Function.invFunOn_apply_eq (f := f) hx, Function.invFunOn_apply_eq (f := f) hx'] at h
  rw [h]

variable {s t : Set α}

noncomputable def encard (s : Set α) := PartENat.withTopEquiv (PartENat.card s)

@[simp] theorem encard_eq_zero : s.encard = 0 ↔ s = ∅ := by
  rw [encard, ←PartENat.withTopEquiv.symm.injective.eq_iff, Equiv.symm_apply_apply, 
    PartENat.withTopEquiv_symm_zero, PartENat.card_eq_zero_iff_empty, isEmpty_subtype, 
    eq_empty_iff_forall_not_mem]
  
@[simp] theorem encard_empty : (∅ : Set α).encard = 0 := by 
  rw [encard_eq_zero]

theorem nonempty_of_encard_ne_zero (h : s.encard ≠ 0) : s.Nonempty := by 
  rwa [nonempty_iff_ne_empty, Ne.def, ←encard_eq_zero]

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

@[simp] theorem one_le_encard_iff_nonempty : 1 ≤ s.encard ↔ s.Nonempty := by 
  rw [nonempty_iff_ne_empty, Ne.def, ←encard_eq_zero, ENat.one_le_iff_ne_zero]
   
@[simp] theorem encard_pos_iff_nonempty : 0 < s.encard ↔ s.Nonempty := by 
  rw [←ENat.one_le_iff_pos, one_le_encard_iff_nonempty]

theorem encard_diff_add_encard_inter (s t : Set α) :
    (s \ t).encard + (s ∩ t).encard = s.encard := by
  rw [←encard_union_eq (disjoint_of_subset_right (inter_subset_right _ _) disjoint_sdiff_left),
    diff_union_inter]

theorem encard_union_add_encard_inter (s t : Set α) :
    (s ∪ t).encard + (s ∩ t).encard = s.encard + t.encard :=
by rw [←diff_union_self, encard_union_eq disjoint_sdiff_left, add_right_comm,
  encard_diff_add_encard_inter]

theorem encard_union_le (s t : Set α) : (s ∪ t).encard ≤ s.encard + t.encard := by
  rw [←encard_union_add_encard_inter]; exact le_self_add

theorem finite_iff_finite_of_encard_eq_encard (h : s.encard = t.encard) : s.Finite ↔ t.Finite := by
  rw [←encard_lt_top_iff, ←encard_lt_top_iff, h]

theorem infinite_iff_infinite_of_encard_eq_encard (h : s.encard = t.encard) :
    s.Infinite ↔ t.Infinite := by rw [←encard_eq_top_iff, h, encard_eq_top_iff]

theorem Finite.finite_of_encard_le (hs : s.Finite) (h : t.encard ≤ s.encard) : t.Finite :=
  encard_lt_top_iff.1 (h.trans_lt hs.encard_lt_top)

theorem Finite.eq_of_subset_of_encard_le (ht : t.Finite) (hst : s ⊆ t) (hts : t.encard ≤ s.encard) :
    s = t := by
  rw [←zero_add (a := encard s), ←encard_diff_add_encard_of_subset hst] at hts
  have hdiff := WithTop.le_of_add_le_add_right (ht.subset hst).encard_lt_top.ne hts
  rw [nonpos_iff_eq_zero, encard_eq_zero, diff_eq_empty] at hdiff
  exact hst.antisymm hdiff
  
theorem Finite.eq_of_subset_of_encard_le' (hs : s.Finite) (hst : s ⊆ t)
    (hts : t.encard ≤ s.encard) : s = t :=
  (hs.finite_of_encard_le hts).eq_of_subset_of_encard_le hst hts
  
theorem encard_insert_le (s : Set α) (x : α) : (insert x s).encard ≤ s.encard + 1 := by 
  rw [←union_singleton, ←encard_singleton x]; apply encard_union_le 

theorem encard_singleton_inter (s : Set α) (x : α) : ({x} ∩ s).encard ≤ 1 := by 
  rw [←encard_singleton x]; exact encard_le_of_subset (inter_subset_left _ _)

theorem tsub_encard_le_encard_diff (s t : Set α) : s.encard - t.encard ≤ (s \ t).encard := by 
  obtain (h | h) := eq_or_ne (s \ (t ∩ s)).encard ⊤ 
  · rw [←diff_inter_self_eq_diff, h]; exact le_top 
  rw [←diff_inter_self_eq_diff, ←encard_diff_add_encard_of_subset (inter_subset_right t s), 
    tsub_le_iff_right, WithTop.add_le_add_iff_left h]
  exact encard_le_of_subset (inter_subset_left _ _)

theorem encard_diff_singleton_add_one_of_mem (h : a ∈ s) :
    (s \ {a}).encard + 1 = s.encard := by 
  rw [←encard_insert_of_not_mem (fun h ↦ h.2 rfl), insert_diff_singleton, insert_eq_of_mem h]

theorem encard_diff_singleton_of_mem (h : a ∈ s) : 
    (s \ {a}).encard = s.encard - 1 := by 
  rw [←encard_diff_singleton_add_one_of_mem h, ←WithTop.add_right_cancel_iff WithTop.one_ne_top, 
    tsub_add_cancel_of_le (self_le_add_left _ _)]
  
theorem encard_tsub_one_le_encard_diff_singleton (s : Set α) (x : α) : 
    s.encard - 1 ≤ (s \ {x}).encard := by 
  rw [←encard_singleton x]; apply tsub_encard_le_encard_diff

theorem encard_exchange (ha : a ∉ s) (hb : b ∈ s) : (insert a (s \ {b})).encard = s.encard := by 
  rw [encard_insert_of_not_mem, encard_diff_singleton_add_one_of_mem hb]
  simp_all only [not_true, mem_diff, mem_singleton_iff, false_and, not_false_eq_true]

theorem encard_exchange' (ha : a ∉ s) (hb : b ∈ s) : (insert a s \ {b}).encard = s.encard := by 
  rw [←insert_diff_singleton_comm (by rintro rfl; exact ha hb), encard_exchange ha hb]

theorem encard_pair (hne : x ≠ y) : ({x,y} : Set α).encard = 2 := by
  rw [encard_insert_of_not_mem (by simpa), ←one_add_one_eq_two, 
    WithTop.add_right_cancel_iff WithTop.one_ne_top, encard_singleton]

theorem encard_eq_one : s.encard = 1 ↔ ∃ x, s = {x} := by
  refine' ⟨fun h ↦ _, fun ⟨x, hx⟩ ↦ by rw [hx, encard_singleton]⟩
  obtain ⟨x, hx⟩ := nonempty_of_encard_ne_zero (s := s) (by rw [h]; simp)
  exact ⟨x, ((finite_singleton x).eq_of_subset_of_encard_le' (by simpa) (by simp [h])).symm⟩ 
  
theorem encard_eq_two : s.encard = 2 ↔ ∃ x y, x ≠ y ∧ s = {x,y} := by 
  refine' ⟨fun h ↦ _, fun ⟨x, y, hne, hs⟩ ↦ by rw [hs, encard_pair hne]⟩
  obtain ⟨x, hx⟩ := nonempty_of_encard_ne_zero (s := s) (by rw [h]; simp) 
  rw [←insert_eq_of_mem hx, ←insert_diff_singleton, encard_insert_of_not_mem (fun h ↦ h.2 rfl), 
    ←one_add_one_eq_two, WithTop.add_right_cancel_iff (WithTop.one_ne_top), encard_eq_one] at h
  obtain ⟨y, h⟩ := h
  refine' ⟨x, y, by rintro rfl; exact (h.symm.subset rfl).2 rfl, _⟩
  rw [←h, insert_diff_singleton, insert_eq_of_mem hx]
   
theorem encard_eq_three {α : Type u_1} {s : Set α} :
    encard s = 3 ↔ ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ s = {x, y, z} := by 
  refine' ⟨fun h ↦ _, fun ⟨x, y, z, hxy, hyz, hxz, hs⟩ ↦ _⟩
  · obtain ⟨x, hx⟩ := nonempty_of_encard_ne_zero (s := s) (by rw [h]; simp) 
    rw [←insert_eq_of_mem hx, ←insert_diff_singleton, 
      encard_insert_of_not_mem (fun h ↦ h.2 rfl), (by exact rfl : (3 : ℕ∞) = 2 + 1), 
      WithTop.add_right_cancel_iff WithTop.one_ne_top, encard_eq_two] at h
    obtain ⟨y,z,hne, hs⟩ := h
    refine' ⟨x,y,z, _, _, hne, _⟩ 
    · rintro rfl; exact (hs.symm.subset (Or.inl rfl)).2 rfl
    · rintro rfl; exact (hs.symm.subset (Or.inr rfl)).2 rfl
    rw [←hs, insert_diff_singleton, insert_eq_of_mem hx]
  rw [hs, encard_insert_of_not_mem, encard_insert_of_not_mem, encard_singleton] <;> aesop

theorem exists_subset_encard_eq (hk : k ≤ s.encard) : ∃ t, t ⊆ s ∧ t.encard = k := by 
  revert hk
  refine' ENat.nat_induction k (fun _ ↦ ⟨∅, empty_subset _, by simp⟩) (fun n IH hle ↦ _) _
  · obtain ⟨t₀, ht₀s, ht₀⟩ := IH (le_trans (by simp) hle)
    simp only [Nat.cast_succ] at *
    have hne : t₀ ≠ s
    · rintro rfl; rw [ht₀, ←Nat.cast_one, ←Nat.cast_add, Nat.cast_le] at hle; simp at hle
    obtain ⟨x, hx⟩ := exists_of_ssubset (ht₀s.ssubset_of_ne hne)
    exact ⟨insert x t₀, insert_subset hx.1 ht₀s, by rw [encard_insert_of_not_mem hx.2, ht₀]⟩ 
  simp only [top_le_iff, encard_eq_top_iff]
  exact fun _ hi ↦ ⟨s, Subset.rfl, hi⟩  
  
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

theorem encard_image_of_injOn (h : InjOn f s) : (f '' s).encard = s.encard := by 
  rw [encard, PartENat.card_image_of_injOn h, encard]
  
theorem encard_image_of_injective (hf : f.Injective) : (f '' s).encard = s.encard :=
  encard_image_of_injOn (hf.injOn s)

theorem encard_le_image (f : α → β) (s : Set α) : (f '' s).encard ≤ s.encard := by 
  obtain (h | h) := isEmpty_or_nonempty α 
  · rw [s.eq_empty_of_isEmpty]; simp
  rw [←encard_image_of_injOn (Function.invFunOn_injOn_image f s)]
  apply encard_le_of_subset
  exact Function.invFunOn_image_image_subset f s
  
theorem Finite.injOn_of_ncard_image_eq (hs : s.Finite) (h : (f '' s).encard = s.encard) :
    InjOn f s := by 
  obtain (h' | hne) := isEmpty_or_nonempty α 
  · rw [s.eq_empty_of_isEmpty]; simp
  rw [←encard_image_of_injOn (Function.invFunOn_injOn_image f s)] at h
  rw [Function.injOn_iff_invFunOn_image_image_eq_self]
  exact hs.eq_of_subset_of_encard_le (Function.invFunOn_image_image_subset f s) h.symm.le
  
theorem encard_preimage_of_injective_subset_range (hf : f.Injective) (hs : s ⊆ range f) : 
    (f ⁻¹' s).encard = s.encard := by 
  rw [←encard_image_of_injective hf]
  
  
  

  
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

