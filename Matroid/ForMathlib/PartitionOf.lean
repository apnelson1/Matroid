import Mathlib.Data.Setoid.Partition

open Set

namespace Setoid

variable {α : Type _}


/-- `c` is a collection of disjoint nonempty sets with union `s`. -/
def IsPartitionOf (c : Set (Set α)) (s : Set α) := 
  ∅ ∉ c ∧ (∀ t ∈ c, t ⊆ s) ∧ ∀ a ∈ s, ∃! b, b ∈ c ∧ a ∈ b

theorem IsPartitionOf.pairwiseDisjoint (hc : IsPartitionOf c s) : 
    c.PairwiseDisjoint id := 
  fun t htc t' htc' hne ↦ disjoint_iff_forall_ne.mpr 
    (fun x hx y hy hxy ↦ hne ((hc.2.2 _ (hc.2.1 _ htc hx)).unique ⟨htc, hx⟩ ⟨htc', by rwa [hxy]⟩))
  
theorem IsPartitionOf.sUnion_eq (hc : IsPartitionOf c s) : ⋃₀ c = s :=
  subset_antisymm (sUnion_subset hc.2.1) 
    (fun _ hx ↦ (hc.2.2 _ hx).exists.elim fun _ ht ↦ mem_sUnion_of_mem ht.2 ht.1)

theorem IsPartitionOf.nonempty_of_mem (hc : IsPartitionOf c s) (ht : t ∈ c) : t.Nonempty := by 
  rw [nonempty_iff_ne_empty]; rintro rfl; exact hc.1 ht

def support_of (r : α → α → Prop) : Set α := 
  {x | r x x}  

def class_of (r : α → α → Prop) (x : α) := 
  {y | r x y}

def classes_of (r : α → α → Prop) : Set (Set α) := 
  (class_of r) '' (support_of r)
  
theorem isPartitionOf_of_symm_of_trans (r : α → α → Prop) [IsSymm α r] [IsTrans α r] : 
    IsPartitionOf (classes_of r) (support_of r) := by 
  refine ⟨fun ⟨x, hx, h⟩ ↦ not_mem_empty x (h.subset hx), ?_, ?_⟩  
  · rintro t ⟨y, -, rfl⟩ z (hz : r _ _)
    exact IsTrans.trans _ _ _ (IsSymm.symm _ _ hz) hz
  refine fun x (h : r x x) ↦ ⟨{z | r x z}, ⟨⟨_,h,rfl⟩,h⟩, ?_⟩ 
  rintro _ ⟨⟨z, -, rfl⟩, (h : r _ _ )⟩ 
  simp only [Set.ext_iff, mem_setOf_eq]
  refine fun y ↦ ⟨fun hzy ↦ (IsTrans.trans _ _ _ (IsSymm.symm _ _ h) hzy), 
    fun hxy ↦ IsTrans.trans _ _ _ h hxy⟩


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
