import Mathlib.Data.Setoid.Partition

open Set

theorem symm_iff_of (r : α → α → Prop) [IsSymm α r] {x y : α} : r x y ↔ r y x := 
  ⟨fun h ↦ symm_of r h, fun h ↦ symm_of r h⟩ 

namespace PSetoid

variable {α : Type _}

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

theorem IsPartition.exists_of_mem (hc : IsPartition c s) (hx : x ∈ s) : ∃! b, b ∈ c ∧ x ∈ b := 
  hc.2.2 x hx

theorem IsPartition.eq_of_mem_of_mem (hc : IsPartition c s) (ht : t ∈ c) (ht' : t' ∈ c) 
    (hxt : x ∈ t) (hxt' : x ∈ t') : t = t' := 
  by_contra fun hne ↦ disjoint_iff_forall_ne.1 (hc.pairwiseDisjoint ht ht' hne) hxt hxt' rfl

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

/-- Given a collection `c` of sets, a relation in which two elements are related if and only if 
  they are both in some set in `c`, and no set in `c` contains exactly one of them. This is one 
  of a few ways to define the 'partial equivalence relation' associated with `c` when the sets in 
  `c` are disjoint; this definition is chosen so that `rel_of` is both symmetric and transitive 
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
  

   

    

    



-- theorem exists_of_mem_partition (hc : IsPartition c s) (hs : s ∈ c) : 
--   ∃ x, s = 


-- theorem rel_iff : r x y ↔ 

  -- refine ⟨fun h ↦ h.2 rfl, ?_,?_⟩ 
  -- · rintro t ⟨⟨y, hy, rfl⟩,-⟩ z hz
  --   exact IsTrans.trans _ _ _ (IsSymm.symm _ _ hz) hz
  -- refine fun x (h : r x x) ↦ ⟨{z | r x z},⟨⟨⟨_,rfl⟩,?_⟩,h⟩,?_⟩ 
  
  
   




-- section Partition

-- /- ./././Mathport/Syntax/Translate/Basic.lean:628:2:
-- -- warning: expanding binder collection (b «expr ∈ » c) -/
-- /-- A collection `c : Set (Set α)` of sets is a partition of `α` into pairwise
-- disjoint sets if `∅ ∉ c` and each element `a : α` belongs to a unique set `b ∈ c`. -/
-- def IsPartition (c : Set (Set α)) :=
--   ∅ ∉ c ∧ ∀ a, ∃! (b : _) (_ : b ∈ c), a ∈ b
-- #align setoid.is_partition Setoid.IsPartition

-- /-- A partition of `α` does not contain the empty set. -/
-- theorem nonempty_of_mem_partition {c : Set (Set α)} (hc : IsPartition c) {s} (h : s ∈ c) :
--     s.Nonempty :=
--   Set.nonempty_iff_ne_empty.2 fun hs0 => hc.1 <| hs0 ▸ h
-- #align setoid.nonempty_of_mem_partition Setoid.nonempty_of_mem_partition

-- theorem isPartition_classes (r : Setoid α) : IsPartition r.classes :=
--   ⟨empty_not_mem_classes, classes_eqv_classes⟩
-- #align setoid.is_partition_classes Setoid.isPartition_classes

-- theorem IsPartition.pairwiseDisjoint {c : Set (Set α)} (hc : IsPartition c) :
--     c.PairwiseDisjoint id :=
--   eqv_classes_disjoint hc.2
-- #align setoid.is_partition.pairwise_disjoint Setoid.IsPartition.pairwiseDisjoint

-- theorem IsPartition.sUnion_eq_univ {c : Set (Set α)} (hc : IsPartition c) : ⋃₀ c = Set.univ :=
--   Set.eq_univ_of_forall fun x =>
--     Set.mem_sUnion.2 <|
--       let ⟨t, ht⟩ := hc.2 x
--       ⟨t, by
--         simp only [exists_unique_iff_exists] at ht
--         tauto⟩
-- #align setoid.is_partition.sUnion_eq_univ Setoid.IsPartition.sUnion_eq_univ

-- /-- All elements of a partition of α are the equivalence class of some y ∈ α. -/
-- theorem exists_of_mem_partition {c : Set (Set α)} (hc : IsPartition c) {s} (hs : s ∈ c) :
--     ∃ y, s = { x | (mkClasses c hc.2).Rel x y } :=
--   let ⟨y, hy⟩ := nonempty_of_mem_partition hc hs
--   ⟨y, eq_eqv_class_of_mem hc.2 hs hy⟩
-- #align setoid.exists_of_mem_partition Setoid.exists_of_mem_partition

-- /-- The equivalence classes of the equivalence relation defined by a partition of α equal
--     the original partition. -/
-- theorem classes_mkClasses (c : Set (Set α)) (hc : IsPartition c) : (mkClasses c hc.2).classes = c :=
--   Set.ext fun s => ⟨fun ⟨y, hs⟩ => (hc.2 y).elim₂ fun b hm hb _hy => by
--     rwa [show s = b from hs.symm ▸ Set.ext fun x =>
--       ⟨fun hx => symm' (mkClasses c hc.2) hx b hm hb, fun hx b' hc' hx' =>
--           eq_of_mem_eqv_class hc.2 hm hx hc' hx' ▸ hb⟩],
--     exists_of_mem_partition hc⟩
-- #align setoid.classes_mk_classes Setoid.classes_mkClasses

-- /-- Defining `≤` on partitions as the `≤` defined on their induced equivalence relations. -/
-- instance Partition.le : LE (Subtype (@IsPartition α)) :=
--   ⟨fun x y => mkClasses x.1 x.2.2 ≤ mkClasses y.1 y.2.2⟩
-- #align setoid.partition.le Setoid.Partition.le

-- /-- Defining a partial order on partitions as the partial order on their induced
--     equivalence relations. -/
-- instance Partition.partialOrder : PartialOrder (Subtype (@IsPartition α))
--     where
--   le := (· ≤ ·)
--   lt x y := x ≤ y ∧ ¬y ≤ x
--   le_refl _ := @le_refl (Setoid α) _ _
--   le_trans _ _ _ := @le_trans (Setoid α) _ _ _ _
--   lt_iff_le_not_le _ _ := Iff.rfl
--   le_antisymm x y hx hy := by
--     let h := @le_antisymm (Setoid α) _ _ _ hx hy
--     rw [Subtype.ext_iff_val, ← classes_mkClasses x.1 x.2, ← classes_mkClasses y.1 y.2, h]
-- #align setoid.partition.partial_order Setoid.Partition.partialOrder

-- variable (α)

-- /-- The order-preserving bijection between equivalence relations on a type `α`, and
--   partitions of `α` into subsets. -/
-- protected def Partition.orderIso : Setoid α ≃o { C : Set (Set α) // IsPartition C }
--     where
--   toFun r := ⟨r.classes, empty_not_mem_classes, classes_eqv_classes⟩
--   invFun C := mkClasses C.1 C.2.2
--   left_inv := mkClasses_classes
--   right_inv C := by rw [Subtype.ext_iff_val, ← classes_mkClasses C.1 C.2]
--   map_rel_iff' {r s} := by
--     conv_rhs => rw [← mkClasses_classes r, ← mkClasses_classes s]
-- #align setoid.partition.order_iso Setoid.Partition.orderIso

-- variable {α}

-- /-- A complete lattice instance for partitions; there is more infrastructure for the
--     equivalent complete lattice on equivalence relations. -/
-- instance Partition.completeLattice : CompleteLattice (Subtype (@IsPartition α)) :=
--   GaloisInsertion.liftCompleteLattice <|
--     @OrderIso.toGaloisInsertion _ (Subtype (@IsPartition α)) _ (PartialOrder.toPreorder) <|
--       Partition.orderIso α
-- #align setoid.partition.complete_lattice Setoid.Partition.completeLattice

-- end Partition

-- /-- A finite setoid partition furnishes a finpartition -/
-- @[simps]
-- def IsPartition.finpartition {c : Finset (Set α)} (hc : Setoid.IsPartition (c : Set (Set α))) :
--     Finpartition (Set.univ : Set α) where
--   parts := c
--   supIndep := Finset.supIndep_iff_pairwiseDisjoint.mpr <| eqv_classes_disjoint hc.2
--   supParts := c.sup_id_set_eq_sUnion.trans hc.sUnion_eq_univ
--   not_bot_mem := hc.left
-- #align setoid.is_partition.finpartition Setoid.IsPartition.finpartition

-- end Setoid

-- /-- A finpartition gives rise to a setoid partition -/
-- theorem Finpartition.isPartition_parts {α} (f : Finpartition (Set.univ : Set α)) :
--     Setoid.IsPartition (f.parts : Set (Set α)) :=
--   ⟨f.not_bot_mem,
--     Setoid.eqv_classes_of_disjoint_union (f.parts.sup_id_set_eq_sUnion.symm.trans f.supParts)
--       f.supIndep.pairwiseDisjoint⟩
-- #align finpartition.is_partition_parts Finpartition.isPartition_parts

-- /-- Constructive information associated with a partition of a type `α` indexed by another type `ι`,
-- `s : ι → Set α`.

-- `IndexedPartition.index` sends an element to its index, while `IndexedPartition.some` sends
-- an index to an element of the corresponding set.

-- This type is primarily useful for definitional control of `s` - if this is not needed, then
-- `Setoid.ker index` by itself may be sufficient. -/
-- structure IndexedPartition {ι α : Type _} (s : ι → Set α) where
--   /-- two indexes are equal if they are equal in membership  -/
--   eq_of_mem : ∀ {x i j}, x ∈ s i → x ∈ s j → i = j
--   /-- sends an index to an element of the corresponding set-/
--   some : ι → α
--   /-- membership invariance for `some`-/
--   some_mem : ∀ i, some i ∈ s i
--   /-- index for type `α`-/
--   index : α → ι
--   /-- membership invariance for `index`-/
--   mem_index : ∀ x, x ∈ s (index x)
-- #align indexed_partition IndexedPartition

-- /-- The non-constructive constructor for `IndexedPartition`. -/
-- noncomputable def IndexedPartition.mk' {ι α : Type _} (s : ι → Set α)
--     (dis : ∀ i j, i ≠ j → Disjoint (s i) (s j)) (nonempty : ∀ i, (s i).Nonempty)
--     (ex : ∀ x, ∃ i, x ∈ s i) : IndexedPartition s
--     where
--   eq_of_mem {_x _i _j} hxi hxj := by_contradiction fun h => (dis _ _ h).le_bot ⟨hxi, hxj⟩
--   some i := (nonempty i).some
--   some_mem i := (nonempty i).choose_spec
--   index x := (ex x).choose
--   mem_index x := (ex x).choose_spec
-- #align indexed_partition.mk' IndexedPartition.mk'