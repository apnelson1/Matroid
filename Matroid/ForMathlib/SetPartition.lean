import Mathlib.Data.Setoid.Partition
import Mathlib.Data.SetLike.Basic

open Set

variable {α : Type*} [CompleteLattice α] {s x y z : α}

@[simp] theorem setIndependent_singleton {α : Type*} [CompleteLattice α] (s : α) :
    CompleteLattice.SetIndependent {s} := by
  simp [CompleteLattice.SetIndependent]

structure Partition (s : α) :=
  parts : Set α
  setIndependent : CompleteLattice.SetIndependent parts
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
  P.setIndependent.pairwiseDisjoint hx hy hxy

theorem pairwiseDisjoint : Set.PairwiseDisjoint (P : Set α) id :=
  fun _ hx _ hy hxy ↦ P.disjoint hx hy hxy

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
@[simps] def ofIndependent {u : Set α} (hs : CompleteLattice.SetIndependent u) (hbot : ⊥ ∉ u) :
    Partition (sSup u) where
  parts := u
  setIndependent := hs
  bot_not_mem := hbot
  sSup_eq' := rfl

/-- The partition with no parts. -/
@[simps] def ofBot (α : Type*) [CompleteLattice α] : Partition (⊥ : α) where
  parts := ∅
  setIndependent := by simp
  bot_not_mem := by simp
  sSup_eq' := by simp

/-- The one-part partition. -/
@[simps] def indiscrete (s : α) (hs : s ≠ ⊥) : Partition s where
  parts := {s}
  setIndependent := by simp
  bot_not_mem := by simpa using hs.symm
  sSup_eq' := sSup_singleton

@[simps] protected def congr {t : α} (P : Partition s) (hst : s = t) : Partition t where
  parts := P.parts
  setIndependent := P.setIndependent
  bot_not_mem := P.bot_not_mem
  sSup_eq' := hst ▸ P.sSup_eq'

@[simp] theorem coe_congr_eq {t : α} {P : Partition s} (hst : s = t) :
    (P.congr hst : Set α) = P := rfl

@[simp] theorem mem_congr_iff {t x : α} {P : Partition s} (hst : s = t) :
    x ∈ P.congr hst ↔ x ∈ P := Iff.rfl

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
      obtain rfl := PairwiseDisjoint.eq_of_le P.pairwiseDisjoint h hx' (P.ne_bot_of_mem h)
        (hxy.trans hyx')
      rwa [hxy.antisymm hyx']
    obtain ⟨y, hy, hxy⟩ := hq x h
    obtain ⟨x', hx', hyx'⟩ := hp y hy
    obtain rfl := PairwiseDisjoint.eq_of_le Q.pairwiseDisjoint h hx' (Q.ne_bot_of_mem h)
      (hxy.trans hyx')
    rwa [hxy.antisymm hyx']

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
  PairwiseDisjoint.elim P.pairwiseDisjoint ht hu fun
    (hdj : Disjoint t u) ↦ by simp [hdj.inter_eq] at hx

theorem eq_of_mem_of_mem (ht : t ∈ P) (hu : u ∈ P) (hxt : x ∈ t) (hxu : x ∈ u) : t = u :=
  eq_of_mem_inter ht hu ⟨hxt, hxu⟩

theorem exists_unique_of_mem_set (P : Partition s) (hx : x ∈ s) : ∃! t, t ∈ P ∧ x ∈ t := by
  rw [← P.sUnion_eq, mem_sUnion] at hx
  obtain ⟨t, hxt⟩ := hx
  exact ⟨t, hxt, fun u ⟨huP, hxu⟩ ↦ eq_of_mem_inter huP hxt.1 ⟨hxu, hxt.2⟩⟩

theorem finite_of_finite (P : Partition s) (hs : s.Finite) : (P : Set (Set α)).Finite :=
  hs.finite_subsets.subset fun _ ↦ subset_of_mem

@[simps] def ofPairwiseDisjoint {p : Set (Set α)} (h : p.PairwiseDisjoint id) (h_empty : ∅ ∉ p):
    Partition (⋃₀ p) where
  parts := p
  setIndependent := PairwiseDisjoint.setIndependent h
  bot_not_mem := h_empty
  sSup_eq' := rfl

@[simps] def ofPairwiseDisjoint' {s : Set α} {parts : Set (Set α)}
  (pairwiseDisjoint : parts.PairwiseDisjoint id)
  (forall_nonempty : ∀ s ∈ parts, s.Nonempty) (eq_sUnion : s = ⋃₀ parts) :
    Partition s where
  parts := parts
  setIndependent := pairwiseDisjoint.setIndependent
  bot_not_mem := fun h ↦ by simpa using forall_nonempty _ h
  sSup_eq' := eq_sUnion.symm

@[simp] theorem mem_ofPairwiseDisjoint' {s : Set α} {parts : Set (Set α)} (pairwiseDisjoint)
    (forall_nonempty) (eq_sUnion) {x : Set α} :
  x ∈ ofPairwiseDisjoint' (s := s) (parts := parts) pairwiseDisjoint forall_nonempty eq_sUnion ↔
    x ∈ parts := Iff.rfl


end Set

section Rel

variable {s t : Set α} {a b : α} {P : Partition s}

theorem symm_iff_of {α : Type*} (r : α → α → Prop) [IsSymm α r] {x y : α} : r x y ↔ r y x :=
  ⟨fun h ↦ symm_of r h, fun h ↦ symm_of r h⟩

theorem refl_of_rel {α : Type*} (r : α → α → Prop) [IsSymm α r] [IsTrans α r] {x y : α}
    (h : r x y) : r x x :=
  trans_of r h (symm_of r h)


/-- A transitive, symmetric binary relation `r` induces a partition of the set of elements on
  which it is reflexive. -/
@[simps] def ofRel (r : α → α → Prop) [IsTrans α r] [IsSymm α r] : Partition {x | r x x} where
  parts := ((fun a ↦ {x | r a x}) '' {x | r x x})
  setIndependent := by
    apply PairwiseDisjoint.setIndependent
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

/-- A version of `Partition.ofRel` with alternative definitional properties. -/
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

@[simp] theorem mem_ofRel_iff {t : Set α} :
    t ∈ ofRel r ↔ ∃ x, r x x ∧ t = {y | r x y} := by
  simp_rw [eq_comm (a := t)]; rfl

@[simp] theorem mem_ofRel'_iff {t : Set α} (hs : s = {x | r x x}):
    t ∈ ofRel' r hs ↔ ∃ x ∈ s, t = {y | r x y} := by
  subst hs
  simp [ofRel', mem_congr_iff, mem_ofRel_iff]

  -- simp_rw [eq_comm (a := t)]; rfl

theorem class_nonempty {t : Set α} (ht : t ∈ ofRel r) : t.Nonempty := by
  obtain ⟨x, hx, rfl⟩ := ht; exact ⟨x, hx⟩

/-- Every partition of `s : Set α` induces a transitive, symmetric binary relation on `α`
  whose equivalence classes are the parts of `P`. The relation is irreflexive outside `s`.  -/
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

theorem Rel.symm {P : Partition s} (h : P.Rel x y) : P.Rel y x :=
  symm_of P.Rel h

theorem Rel.trans {P : Partition s} (hxy : P.Rel x y) (hyz : P.Rel y z) : P.Rel x z :=
  trans_of P.Rel hxy hyz

theorem rel_iff_exists : P.Rel x y ↔ ∃ t ∈ P, x ∈ t ∧ y ∈ t := Iff.rfl

theorem setOf_rel_self_eq (P : Partition s) : {x | P.Rel x x} = s := by
  refine subset_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · obtain ⟨t, ht, hxP, -⟩ := hx
    exact subset_of_mem ht hxP
  obtain ⟨t, ⟨ht, hxt⟩, -⟩ := P.exists_unique_of_mem_set hx
  exact ⟨t, ht, hxt, hxt⟩

theorem setOf_rel_eq (ht : t ∈ P) (hx : x ∈ t) : {y | P.Rel x y} = t :=
  Set.ext fun y ↦ ⟨fun ⟨t', ht', hx', hy'⟩ ↦ by rwa [P.eq_of_mem_of_mem ht ht' hx hx'],
    fun h ↦ ⟨t, ht, hx, h⟩⟩

theorem setOf_rel_mem (P : Partition s) (hx : x ∈ s) : {y | P.Rel x y} ∈ P := by
  obtain ⟨t, ⟨ht,hp⟩, -⟩ := P.exists_unique_of_mem_set hx
  rwa [setOf_rel_eq ht hp]

theorem ofRel_rel_eq (P : Partition s) : ofRel' P.Rel P.setOf_rel_self_eq.symm = P := by
  ext a
  simp only [mem_ofRel'_iff]
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨x,hx, rfl⟩
    exact setOf_rel_mem _ hx
  obtain ⟨x, hx⟩ := P.nonempty_of_mem h
  exact ⟨x, (P.subset_of_mem h) hx, by rwa [setOf_rel_eq _ hx]⟩

@[simp] theorem rel_ofRel_eq (r : α → α → Prop) [IsTrans α r] [IsSymm α r] : (ofRel r).Rel = r := by
  ext a b
  simp only [Rel, mem_ofRel_iff]
  refine ⟨?_, fun h ↦ ⟨_, ⟨a, refl_of_rel r h, rfl⟩, refl_of_rel r h, h⟩⟩
  rintro ⟨_, ⟨x, -, rfl⟩, ha, hb⟩
  exact trans_of r (symm_of r ha) hb

end Rel
