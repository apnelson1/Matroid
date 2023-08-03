import Mathlib.Data.Setoid.Partition


open Set

theorem symm_iff_of (r : α → α → Prop) [IsSymm α r] {x y : α} : r x y ↔ r y x := 
  ⟨fun h ↦ symm_of r h, fun h ↦ symm_of r h⟩ 

namespace PSetoid

variable {α : Type _} {c : Set (Set α)}

/-- `c` is a collection of disjoint nonempty sets with union `s`. -/
def IsPartition (c : Set (Set α)) (s : Set α) := 
  ∅ ∉ c ∧ (∀ t ∈ c, t ⊆ s) ∧ ∀ a ∈ s, ∃! b, b ∈ c ∧ a ∈ b

theorem IsPartition.pairwiseDisjoint (hc : IsPartition c s) : 
    c.PairwiseDisjoint id := 
  fun t htc t' htc' hne ↦ disjoint_iff_forall_ne.mpr 
    (fun x hx y hy hxy ↦ hne ((hc.2.2 _ (hc.2.1 _ htc hx)).unique ⟨htc, hx⟩ ⟨htc', by rwa [hxy]⟩))
  
theorem IsPartition.sUnion_eq (hc : IsPartition c s) : ⋃₀ c = s :=
  subset_antisymm (sUnion_subset hc.2.1) 
    (fun _ hx ↦ (hc.2.2 _ hx).exists.elim fun _ ht ↦ mem_sUnion_of_mem ht.2 ht.1)

theorem IsPartition.nonempty_of_mem (hc : IsPartition c s) (ht : t ∈ c) : t.Nonempty := by 
  rw [nonempty_iff_ne_empty]; rintro rfl; exact hc.1 ht

theorem IsPartition.subset_of_mem (hc : IsPartition c s) (ht : t ∈ c) : t ⊆ s := 
  hc.2.1 _ ht

theorem IsPartition.exists_of_mem (hc : IsPartition c s) (hx : x ∈ s) : ∃! b, b ∈ c ∧ x ∈ b := 
  hc.2.2 x hx

theorem IsPartition.eq_of_mem_of_mem (hc : IsPartition c s) (ht : t ∈ c) (ht' : t' ∈ c) 
    (hxt : x ∈ t) (hxt' : x ∈ t') : t = t' := 
  by_contra fun hne ↦ disjoint_iff_forall_ne.1 (hc.pairwiseDisjoint ht ht' hne) hxt hxt' rfl

theorem IsPartition.finite_of_finite (hc : IsPartition c s) (hs : s.Finite) : c.Finite := by 
  set f : c → s := fun t ↦ ⟨_, hc.subset_of_mem t.prop (hc.nonempty_of_mem t.prop).some_mem⟩ 
  have hf : f.Injective
  · rintro ⟨t,ht⟩ ⟨t',ht'⟩ htt'
    simp only [Subtype.mk.injEq] at *
    exact hc.eq_of_mem_of_mem ht ht' ((hc.nonempty_of_mem ht).some_mem)
      (by rw [htt']; exact (hc.nonempty_of_mem ht').some_mem)  
  have' := @Finite.of_injective _ _ hs.to_subtype f hf
  apply toFinite

theorem IsPartition.finite_mem_of_finite (hc : IsPartition c s) (hs : s.Finite) (ht : t ∈ c) : 
    t.Finite :=
  hs.subset (hc.subset_of_mem ht)

variable {r : α → α → Prop}

/-- The collection of classes of mutually related elements. -/
def classes (r : α → α → Prop) : Set (Set α) := (fun z ↦ {x | r z x}) '' {x | r x x}
  
/-- A symmetric and transitive relation gives a partition of the elements on which it is 
  reflexive into classes -/
theorem classes_partition (r : α → α → Prop) [IsSymm α r] [IsTrans α r] : 
    IsPartition (classes r) {x | r x x} := by 
  refine ⟨fun ⟨x, hx, h⟩ ↦ not_mem_empty x (h.subset hx), ?_, ?_⟩  
  · rintro t ⟨y, -, rfl⟩ z (hz : r _ _)
    exact trans_of r (symm_of r hz) hz
  refine fun x (h : r x x) ↦ ⟨{z | r x z}, ⟨⟨_,h,rfl⟩,h⟩, ?_⟩ 
  rintro _ ⟨⟨z, -, rfl⟩, (h : r _ _ )⟩ 
  simp only [Set.ext_iff, mem_setOf_eq]
  refine fun y ↦ ⟨fun hzy ↦ (trans_of r (symm_of r h) hzy), 
    fun hxy ↦ IsTrans.trans _ _ _ h hxy⟩

variable {r : α → α → Prop} [IsSymm α r] [IsTrans α r] {c : Set (Set α)} {s : Set α}

theorem eqv_class_comm (x : α) : {y | r x y} = {y | r y x} := by
  simp_rw [symm_iff_of]
  
theorem rel_iff_eqv_class_eq_right (hy : r y y) : r x y ↔ {z | r x z} = {z | r y z} := by 
  simp_rw [Set.ext_iff, mem_setOf]
  refine' ⟨fun hxy z ↦ ⟨fun hxz ↦ trans_of r (symm_of r hxy) hxz, 
    fun hyz ↦ trans_of r hxy hyz⟩, fun h ↦ by rwa [h]⟩
  
theorem rel_iff_eqv_class_eq_left (hx : r x x) : r x y ↔ {z | r x z} = {z | r y z} := by 
  rw [symm_iff_of r, rel_iff_eqv_class_eq_right hx, eq_comm]
  
theorem eqv_class_mem (h : r x x) : {y | r x y} ∈ classes r :=
  ⟨x, h, rfl⟩ 

theorem mem_classes_iff : 
    t ∈ classes r ↔ ∃ x, r x x ∧ t = {y | r x y} := by 
  simp_rw [eq_comm (a := t)]; rfl



/-- Given a collection `c` of sets, a relation in which two elements are related 
  if and only if they are both in some set in `c`, 
  and no set in `c` contains exactly one of them. 
  This is one of a few ways to define the 'partial equivalence relation'
  associated with `c` when the sets in `c` are disjoint; 
  this definition is chosen so that `rel_of` is both symmetric and transitive 
  without additional assumptions, which allows `IsTrans` and `IsSymm` to be instances.  -/
def rel_of (c : Set (Set α)) : α → α → Prop := 
  fun x y ↦ (∃ t ∈ c, x ∈ t ∧ y ∈ t) ∧ (∀ ⦃t⦄, t ∈ c → (x ∈ t ↔ y ∈ t))

instance {c : Set (Set α)} : IsSymm α (rel_of c) :=
  ⟨fun x y ⟨⟨t, htc, hxt, hyt⟩, h⟩ ↦ ⟨⟨t, htc, hyt, hxt⟩, fun t' ht' ↦ by rw [h ht']⟩⟩  

instance {c : Set (Set α)} : IsTrans α (rel_of c) := 
  ⟨fun x y z ⟨⟨t, htc, hxt, hyt⟩, hxy⟩ ⟨⟨_, _, _, _⟩, hyz⟩ ↦ 
    ⟨⟨t,htc,hxt, by rwa [←hyz htc]⟩, fun t₀ ht₀ ↦ by rw [hxy ht₀, hyz ht₀]⟩⟩ 
  
theorem rel_of.rel_self_of_mem (ht : t ∈ c) (hx : x ∈ t) : (rel_of c) x x :=
  ⟨⟨t, ht, hx, hx⟩, fun _ _ ↦ Iff.rfl⟩ 

theorem rel_of.forall (h : rel_of c x y) (htc : t ∈ c) : x ∈ t ↔ y ∈ t :=
  h.2 htc

theorem rel_of.exists (h : rel_of c x y) : ∃ t ∈ c, x ∈ t ∧ y ∈ t := 
  h.1 
  
theorem rel_of_iff_exists (hc : IsPartition c s) : 
    rel_of c x y ↔ ∃ t ∈ c, x ∈ t ∧ y ∈ t := by 
  refine ⟨fun h ↦ h.1, fun ⟨t, htc, hxt, hyt⟩ ↦ 
    ⟨⟨t, htc, hxt, hyt⟩, fun t' ht'c ↦ ⟨fun hxt' ↦ ?_, fun hyt' ↦ ?_⟩⟩⟩ 
  rwa [←hc.eq_of_mem_of_mem htc ht'c hxt hxt']
  rwa [hc.eq_of_mem_of_mem ht'c htc hyt' hyt]
  
theorem classes_rel_of_eq (hc : IsPartition c s) : classes (rel_of c) = c := by 
  refine subset_antisymm ?_ (fun t (htc : t ∈ c) ↦ ?_)
  · rintro _ ⟨x, ⟨⟨t, htc, hxt, -⟩, -⟩, rfl⟩
    convert htc
    refine subset_antisymm (fun y ↦ ?_) (fun y hyt ↦ (rel_of_iff_exists hc).2 ⟨t, htc, hxt, hyt⟩)
    rw [mem_setOf_eq]; rintro ⟨-,h⟩; rwa [←h htc]
  obtain ⟨x, hx⟩ := hc.nonempty_of_mem htc
  convert eqv_class_mem (rel_of.rel_self_of_mem htc hx)
  exact subset_antisymm (fun y hyt ↦ (rel_of_iff_exists hc).2 ⟨t, htc, hx, hyt⟩) 
    (fun y ⟨_,hy⟩ ↦ by rwa [←hy htc])
 


   

    



    

