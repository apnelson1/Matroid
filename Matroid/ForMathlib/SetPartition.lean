import Mathlib.Data.Setoid.Partition
import Mathlib.Data.SetLike.Basic

open Set

variable {α : Type*} [CompleteLattice α] {s x y : α}

structure Partition (s : α) :=
  parts : Set α
  pairwiseDisjoint : parts.PairwiseDisjoint id
  bot_not_mem : ⊥ ∉ parts
  sSup_eq' : sSup parts = s

namespace Partition

section Basic

variable {P : Partition s}

instance {α : Type*} [CompleteLattice α] {s : α} : SetLike (Partition s) α where
  coe := Partition.parts
  coe_injective' p p' h := by cases p; cases p'; simpa using h

@[simp] theorem mem_parts {x : α} : x ∈ P.parts ↔ x ∈ (P : Set α) := Iff.rfl

@[ext] theorem Partition.ext {P Q : Partition s} (hP : ∀ x, x ∈ P ↔ x ∈ Q) : P = Q := by
  cases P
  cases Q
  simp only [mk.injEq]
  ext x
  simpa using hP x

theorem disjoint (hx : x ∈ P) (hy : y ∈ P) (hxy : x ≠ y) :
    Disjoint x y :=
  P.pairwiseDisjoint hx hy hxy

theorem ne_bot_of_mem (hx : x ∈ P) : x ≠ ⊥ :=
  fun h ↦ P.bot_not_mem <| h ▸ hx

theorem bot_lt_of_mem (hx : x ∈ P) : ⊥ < x :=
  bot_lt_iff_ne_bot.2 <| P.ne_bot_of_mem hx

theorem iSup_eq (P : Partition s) : ⨆ x ∈ P, x = s := by
  simp_rw [← P.sSup_eq', sSup_eq_iSup]
  rfl

theorem sSup_eq (P : Partition s) : sSup P = s :=
  P.sSup_eq'

theorem le_of_mem (P : Partition s) (hx : x ∈ P) : x ≤ s :=
  (le_sSup hx).trans_eq P.sSup_eq

theorem parts_nonempty (P : Partition s) (hs : s ≠ ⊥) : (P : Set α).Nonempty :=
  nonempty_iff_ne_empty.2 fun hP ↦ by simp [← P.sSup_eq, hP, sSup_empty] at hs

/-- A collection of disjoint elements gives a partition of their supremum. -/
@[simps] def ofDisjoint {u : Set α} (hs : u.PairwiseDisjoint id) (hbot : ⊥ ∉ u) :
    Partition (sSup u) where
  parts := u
  pairwiseDisjoint := hs
  bot_not_mem := hbot
  sSup_eq' := rfl

/-- The partition with no parts. -/
@[simps] def ofBot (α : Type*) [CompleteLattice α] : Partition (⊥ : α) where
  parts := ∅
  pairwiseDisjoint := by simp
  bot_not_mem := by simp
  sSup_eq' := by simp

/-- The one-part partition. -/
@[simps] def indiscrete (s : α) (hs : s ≠ ⊥) : Partition s where
  parts := {s}
  pairwiseDisjoint := by simp
  bot_not_mem := by simpa using hs.symm
  sSup_eq' := sSup_singleton

@[simps] protected def congr {t : α} (P : Partition s) (hst : s = t) : Partition t where
  parts := P.parts
  pairwiseDisjoint := P.pairwiseDisjoint
  bot_not_mem := P.bot_not_mem
  sSup_eq' := hst ▸ P.sSup_eq'

end Basic

section Refinement

instance {α : Type*} [CompleteLattice α] {s : α} : PartialOrder (Partition s) where
  le P Q := ∀ x ∈ P, ∃ y ∈ Q, x ≤ y
  lt := _
  le_refl P x hx := by
    refine ⟨x,hx,rfl.le⟩
  le_trans P Q R hPQ hQR x hxP := by
    obtain ⟨y, hy, hxy⟩ := hPQ x hxP
    obtain ⟨z, hz, hyz⟩ := hQR y hy
    exact ⟨z, hz, hxy.trans hyz⟩
  le_antisymm P Q hp hq := by
    refine Partition.ext fun x ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · obtain ⟨y, hy, hxy⟩ := hp x h
      obtain ⟨x', hx', hyx'⟩ := hq y hy
      obtain rfl := P.pairwiseDisjoint.eq_of_le h hx' (P.ne_bot_of_mem h) (hxy.trans hyx')
      rwa [hxy.antisymm hyx']
    obtain ⟨y, hy, hxy⟩ := hq x h
    obtain ⟨x', hx', hyx'⟩ := hp y hy
    obtain rfl := Q.pairwiseDisjoint.eq_of_le h hx' (Q.ne_bot_of_mem h) (hxy.trans hyx')
    rw [hxy.antisymm hyx']
    exact hy

end Refinement

section Set

variable {s t u : Set α} {P : Partition s} {x : α}

@[simp] protected theorem sUnion_eq (P : Partition s) : ⋃₀ P = s :=
  P.sSup_eq

theorem nonempty_of_mem (ht : t ∈ P) : t.Nonempty :=
  nmem_singleton_empty.1 <| P.ne_bot_of_mem ht

theorem subset_of_mem (ht : t ∈ P) : t ⊆ s :=
  P.le_of_mem ht

theorem eq_of_mem_inter (ht : t ∈ P) (hu : u ∈ P) (hx : x ∈ t ∩ u) : t = u :=
  P.pairwiseDisjoint.elim ht hu fun (hdj : Disjoint t u) ↦ by simp [hdj.inter_eq] at hx

theorem eq_of_mem_of_mem (ht : t ∈ P) (hu : u ∈ P) (hxt : x ∈ t) (hxu : x ∈ u) : t = u :=
  eq_of_mem_inter ht hu ⟨hxt, hxu⟩

theorem exists_unique_of_mem_set (hx : x ∈ s) : ∃! t, t ∈ P ∧ x ∈ t := by
  rw [← P.sUnion_eq, mem_sUnion] at hx
  obtain ⟨t, hxt⟩ := hx
  exact ⟨t, hxt, fun u ⟨huP, hxu⟩ ↦ eq_of_mem_inter huP hxt.1 ⟨hxu, hxt.2⟩⟩

theorem finite_of_finite (P : Partition s) (hs : s.Finite) : (P : Set (Set α)).Finite :=
  hs.finite_subsets.subset fun _ ↦ subset_of_mem

end Set

section Rel

variable {s t : Set α} {a b : α} {P : Partition s}

theorem symm_iff_of {α : Type*} (r : α → α → Prop) [IsSymm α r] {x y : α} : r x y ↔ r y x :=
  ⟨fun h ↦ symm_of r h, fun h ↦ symm_of r h⟩

/-- A transitive, symmetric binary relation `r` induces a partition of the set of elements on
  which it is reflexive. -/
@[simps] def ofRel (r : α → α → Prop) [IsTrans α r] [IsSymm α r] : Partition {x | r x x} where
  parts := ((fun a ↦ {x | r a x}) '' {x | r x x})
  pairwiseDisjoint := by
    rintro _ ⟨i, -, rfl⟩ _ ⟨j, -,rfl⟩ hij
    refine disjoint_iff_forall_ne.2 ?_
    rintro a (ha : r _ _) _ (hb : r _ _) rfl
    simp only [ne_eq, ext_iff, mem_setOf_eq, not_forall] at hij
    obtain ⟨y, hy⟩ := hij
    exact hy ⟨fun hiy ↦ trans_of r hb (trans_of r (symm_of r ha) hiy),
      fun hjy ↦ trans_of r ha (trans_of r (symm_of r hb) hjy)⟩
  bot_not_mem := by
    simp only [bot_eq_empty, mem_image, mem_setOf_eq, eq_empty_iff_forall_not_mem, not_exists,
      not_and, not_forall, not_not]
    exact fun x hx ↦ ⟨x,hx⟩
  sSup_eq' := by
    rw [sSup_eq_sUnion, subset_antisymm_iff]
    simp only [sUnion_image, mem_setOf_eq, iUnion_subset_iff, setOf_subset_setOf]
    refine ⟨fun i _ a ha ↦ trans_of r (symm_of r ha) ha, fun i (hi : r i i) ↦ ?_⟩
    simp only [mem_iUnion, mem_setOf_eq, exists_prop]
    exact ⟨i, hi, hi⟩

@[simps!] def ofRel' (r : α → α → Prop) [IsTrans α r] [IsSymm α r] (hs : s = {x | r x x}) :=
  (ofRel r).congr hs.symm

variable {r : α → α → Prop} [IsSymm α r] [IsTrans α r]  {s : Set α}

theorem eqv_class_comm (x : α) : {y | r x y} = {y | r y x} := by
  simp_rw [symm_iff_of]

theorem rel_iff_eqv_class_eq_right (hy : r y y) : r x y ↔ {z | r x z} = {z | r y z} := by
  simp_rw [Set.ext_iff, mem_setOf]
  refine' ⟨fun hxy z ↦ ⟨fun hxz ↦ trans_of r (symm_of r hxy) hxz,
    fun hyz ↦ trans_of r hxy hyz⟩, fun h ↦ by rwa [h]⟩

theorem rel_iff_eqv_class_eq_left (hx : r x x) : r x y ↔ {z | r x z} = {z | r y z} := by
  rw [symm_iff_of r, rel_iff_eqv_class_eq_right hx, eq_comm]

theorem eqv_class_mem_ofRel (h : r x x) : {y | r x y} ∈ ofRel r :=
  ⟨x, h, rfl⟩

theorem mem_ofRel_iff {t : Set α} :
    t ∈ ofRel r ↔ ∃ x, r x x ∧ t = {y | r x y} := by
  simp_rw [eq_comm (a := t)]; rfl

theorem class_nonempty {t : Set α} (ht : t ∈ ofRel r) : t.Nonempty := by
  obtain ⟨x, hx, rfl⟩ := ht; exact ⟨x, hx⟩

/-- Every partition of `s` induces a transitive, symmetric binary relation whose equivalence
  classes are the parts of `P`. The relation is irreflexive outside `s`.  -/
def Rel (P : Partition s) (a b : α) : Prop :=
  ∃ t ∈ P, a ∈ t ∧ b ∈ t

theorem Rel.exists (h : P.Rel x y) : ∃ t ∈ P, x ∈ t ∧ y ∈ t :=
  h

theorem Rel.forall (h : P.Rel x y) (ht : t ∈ P) : x ∈ t ↔ y ∈ t := by
  obtain ⟨t', ht', hx, hy⟩ := h
  exact ⟨fun h ↦ by rwa [P.eq_of_mem_of_mem ht ht' h hx],
    fun h ↦ by rwa [P.eq_of_mem_of_mem ht ht' h hy]⟩

theorem rel_of_mem_of_mem (ht : t ∈ P) (ha : a ∈ t) (hb : b ∈ t) : P.Rel a b :=
  ⟨t, ht, ha, hb⟩

theorem rel_self_of_mem (ht : t ∈ P) (hx : x ∈ t) : P.Rel x x :=
  rel_of_mem_of_mem ht hx hx

instance (P : Partition s) : IsSymm α P.Rel where
  symm _ _ := fun ⟨t, ht, ha, hb⟩ ↦ ⟨t, ht, hb, ha⟩

instance (P : Partition s) : IsTrans α P.Rel where
  trans a b c := fun ⟨t, htP, ha, hb⟩ ⟨t', ht'P, hb', hc'⟩ ↦
    ⟨t, htP, ha, by rwa [eq_of_mem_of_mem htP ht'P hb hb']⟩

theorem rel_iff_exists : P.Rel x y ↔ ∃ t ∈ P, x ∈ t ∧ y ∈ t := Iff.rfl

theorem setOf_rel_self_eq (P : Partition s) : {x | P.Rel x x} = s := by
  refine subset_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · obtain ⟨t, ht, hxP, -⟩ := hx
    exact subset_of_mem ht hxP
  obtain ⟨t, ⟨ht, hxt⟩, -⟩ := P.exists_unique_of_mem_set hx
  exact ⟨t, ht, hxt, hxt⟩

theorem ofRel_rel_eq (P : Partition s) : ofRel' P.Rel P.setOf_rel_self_eq.symm = P := by
  sorry

-- theorem classes_rel_of_eq (hc : IsPartition c s) : classes (rel_of c) = c := by
--   refine subset_antisymm ?_ (fun t (htc : t ∈ c) ↦ ?_)
--   · rintro _ ⟨x, ⟨⟨t, htc, hxt, -⟩, -⟩, rfl⟩
--     convert htc
--     refine subset_antisymm (fun y ↦ ?_) (fun y hyt ↦ (rel_of_iff_exists hc).2 ⟨t, htc, hxt, hyt⟩)
--     rw [mem_setOf_eq]; rintro ⟨-,h⟩; rwa [←h htc]
--   obtain ⟨x, hx⟩ := hc.nonempty_of_mem htc
--   convert eqv_class_mem (rel_of.rel_self_of_mem htc hx)
--   exact subset_antisymm (fun y hyt ↦ (rel_of_iff_exists hc).2 ⟨t, htc, hx, hyt⟩)
--     (fun y ⟨_,hy⟩ ↦ by rwa [←hy htc])

end Rel
