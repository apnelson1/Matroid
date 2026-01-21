import Matroid.ForMathlib.Partition.Induce

open Set Function Relation

variable {α β ι ι' : Type*} {r : α → α → Prop} {f : ι → α} {x y z : α}

namespace Partition

section Set

variable {s t u : Set α} {S T : Set (Set α)} {P Q : Partition (Set α)}

@[simp] protected lemma sUnion_eq (P : Partition (Set α)) : ⋃₀ P = P.supp :=
  P.sSup_eq

lemma nonempty_of_mem (ht : t ∈ P) : t.Nonempty :=
  notMem_singleton_empty.1 <| P.ne_bot_of_mem ht

lemma empty_not_mem : ∅ ∉ P := P.bot_not_mem

lemma subset_of_mem (ht : t ∈ P) : t ⊆ P.supp :=
  P.le_supp_of_mem ht

lemma mem_supp_iff : x ∈ P.supp ↔ ∃ t ∈ P, x ∈ t := by
  refine ⟨fun hx ↦ ?_, fun ⟨t, htP, hxt⟩ ↦ subset_of_mem htP hxt⟩
  rwa [← P.sUnion_eq, mem_sUnion] at hx

lemma eq_of_mem_inter (ht : t ∈ P) (hu : u ∈ P) (hx : x ∈ t ∩ u) : t = u :=
  PairwiseDisjoint.elim P.pairwiseDisjoint ht hu fun
    (hdj : Disjoint t u) ↦ by simp [hdj.inter_eq] at hx

lemma eq_of_mem_of_mem (ht : t ∈ P) (hu : u ∈ P) (hxt : x ∈ t) (hxu : x ∈ u) : t = u :=
  eq_of_mem_inter ht hu ⟨hxt, hxu⟩

lemma exists_unique_of_mem_supp (hx : x ∈ P.supp) : ∃! t, t ∈ P ∧ x ∈ t := by
  rw [← P.sUnion_eq, mem_sUnion] at hx
  obtain ⟨t, hxt⟩ := hx
  exact ⟨t, hxt, fun u ⟨huP, hxu⟩ ↦ eq_of_mem_inter huP hxt.1 ⟨hxu, hxt.2⟩⟩

lemma mem_supp_iff_unique : x ∈ P.supp ↔ ∃! t, t ∈ P ∧ x ∈ t :=
  ⟨exists_unique_of_mem_supp, fun ⟨_, ⟨htP, hxt⟩, _⟩ ↦ subset_of_mem htP hxt⟩

lemma subset_sUnion_and_mem_iff_mem (hSP : S ⊆ P.parts) :
    t ⊆ ⋃₀ S ∧ t ∈ P ↔ t ∈ S := by
  refine ⟨fun ⟨htsu, htP⟩ ↦ ?_, fun htS ↦ ⟨subset_sUnion_of_mem htS, hSP htS⟩⟩
  obtain ⟨x, hxt⟩ := nonempty_of_mem htP
  obtain ⟨s, hsS, hxs⟩ := htsu hxt
  obtain rfl := eq_of_mem_of_mem htP (hSP hsS) hxt hxs
  exact hsS

@[simp]
lemma subset_sUnion_iff_mem (ht : t ∈ P) (hSP : S ⊆ P.parts) :
    t ⊆ ⋃₀ S ↔ t ∈ S := by
  rw [← subset_sUnion_and_mem_iff_mem hSP]
  simp [ht]

lemma IsPartition.nonempty_not_mem (hS : IsPartition S) (hx : t ∈ S) : t.Nonempty := by
  obtain ⟨P, rfl⟩ := hS
  exact P.nonempty_of_mem hx

lemma IsPartition.empty_not_mem (hS : IsPartition S) : ∅ ∉ S := hS.bot_not_mem

lemma IsPartition.eq_of_mem_inter (hS : IsPartition S) (ht : t ∈ S) (hu : u ∈ S) (hx : x ∈ t ∩ u) :
    t = u := by
  obtain ⟨P, rfl⟩ := hS
  exact P.eq_of_mem_inter ht hu hx

lemma IsPartition.eq_of_mem_of_mem (hS : IsPartition S) (ht : t ∈ S) (hu : u ∈ S) (hxt : x ∈ t)
    (hxu : x ∈ u) : t = u := by
  obtain ⟨P, rfl⟩ := hS
  exact P.eq_of_mem_of_mem ht hu hxt hxu

end Set

section Rel

variable {S T : Set α} {a b c : α} {P Q : Partition (Set α)}

/-- Every partition of `s : Set α` induces a transitive, symmetric Binary relation on `α`
  whose equivalence classes are the parts of `P`. The relation is irreflexive outside `s`.  -/
def Rel (P : Partition (Set α)) (a b : α) : Prop :=
  ∃ t ∈ P, a ∈ t ∧ b ∈ t

private lemma le_of_rel_le' (h : P.Rel ≤ Q.Rel) : P ≤ Q := by
  intro S hS
  obtain ⟨x, hxS⟩ := nonempty_of_mem hS
  obtain ⟨T, hT, hxT, -⟩ := h x x ⟨S, hS, hxS, hxS⟩
  use T, hT
  rintro a haS
  obtain ⟨T', hT', haT', hxT'⟩ := h a x ⟨S, hS, haS, hxS⟩
  obtain rfl := eq_of_mem_of_mem hT hT' hxT hxT'
  exact haT'

instance : FunLike (Partition (Set α)) α (α → Prop) where
  coe := Rel
  coe_injective' _ _ h := le_antisymm (le_of_rel_le' h.le) (le_of_rel_le' h.ge)

lemma Rel.exists (h : P x y) : ∃ t ∈ P, x ∈ t ∧ y ∈ t :=
  h

lemma Rel.forall (h : P x y) (ht : T ∈ P) : x ∈ T ↔ y ∈ T := by
  obtain ⟨t, ht', hx, hy⟩ := h
  exact ⟨fun h ↦ by rwa [P.eq_of_mem_of_mem ht ht' h hx],
    fun h ↦ by rwa [P.eq_of_mem_of_mem ht ht' h hy]⟩

lemma rel_of_mem_of_mem (ht : T ∈ P) (ha : a ∈ T) (hb : b ∈ T) : P a b :=
  ⟨T, ht, ha, hb⟩

lemma rel_self_of_mem (ht : T ∈ P) (hx : x ∈ T) : P x x :=
  rel_of_mem_of_mem ht hx hx

lemma rel_self_of_mem_supp (hx : x ∈ P.supp) : P x x := by
  obtain ⟨t, ht, hxt⟩ := mem_supp_iff.mp hx
  exact rel_self_of_mem ht hxt

lemma rel_symmectric (P : Partition (Set α)) : Symmetric P :=
  fun _ _ ⟨t, ht, ha, hb⟩ ↦ ⟨t, ht, hb, ha⟩

instance (P : Partition (Set α)) : Std.Symm P where
  symm := P.rel_symmectric

lemma rel_transitive (P : Partition (Set α)) : Transitive P := by
  intro _ _ _ ⟨t, ht, ha, hb⟩ ⟨t', ht', hb', hc⟩
  exact ⟨t, ht, ha, by rwa [eq_of_mem_of_mem ht ht' hb hb']⟩

instance (P : Partition (Set α)) : IsTrans α P where
  trans := P.rel_transitive

lemma Rel.symm (h : P x y) : P y x :=
  symm_of P h

lemma rel_comm : P x y ↔ P y x :=
  ⟨Rel.symm, Rel.symm⟩

lemma Rel.trans (hxy : P x y) (hyz : P y z) : P x z :=
  trans_of P hxy hyz

lemma Rel.left_mem (h : P x y) : x ∈ P.supp := by
  obtain ⟨t, htP, hxt, -⟩ := h
  exact subset_of_mem htP hxt

lemma Rel.right_mem (h : P x y) : y ∈ P.supp :=
  h.symm.left_mem

lemma rel_iff_exists : P x y ↔ ∃ t ∈ P, x ∈ t ∧ y ∈ t := Iff.rfl

lemma rel_iff_right_mem_of_mem (ht : T ∈ P) (hx : x ∈ T) : P x y ↔ y ∈ T := by
  refine ⟨fun ⟨t, ht', hxt, hyt⟩ => ?_, fun hyt => ?_⟩
  · obtain rfl := P.eq_of_mem_of_mem ht ht' hx hxt
    exact hyt
  · exact ⟨T, ht, hx, hyt⟩

lemma rel_iff_left_mem_of_mem (ht : T ∈ P) (hy : y ∈ T) : P x y ↔ x ∈ T := by
  rw [rel_comm]
  exact rel_iff_right_mem_of_mem ht hy

lemma rel_eq_exists : ⇑P = fun x y => ∃ t ∈ P, x ∈ t ∧ y ∈ t := rfl

lemma mem_iff_forall_rel {t : Set α} : t ∈ P ↔ ∃ h : t.Nonempty, ∀ x, P h.some x ↔ x ∈ t := by
  refine ⟨fun ht => ?_, fun ⟨h, hrel⟩ => ?_⟩
  · have h := Set.nonempty_iff_ne_empty.mpr <| P.ne_bot_of_mem ht
    refine ⟨h, fun x => ⟨fun ⟨s, hs, hhs, hxs⟩ => ?_, (⟨t, ht, h.some_mem, ·⟩)⟩⟩
    obtain rfl := P.eq_of_mem_of_mem hs ht hhs h.some_mem
    exact hxs
  · obtain ⟨s, hs, hhs, _⟩ := (hrel h.some).mpr h.some_mem
    suffices s = t by subst s; assumption
    apply subset_antisymm
    · exact fun x hx ↦ (hrel x).mp <| rel_of_mem_of_mem hs hhs hx
    · intro x hx
      have hrelx : P h.some x := (hrel x).mpr hx
      obtain ⟨u, huP, hhu, hxu⟩ := hrelx
      obtain rfl : s = u := P.eq_of_mem_of_mem hs huP hhs hhu
      exact hxu

lemma rel_self_iff_mem_supp : P x x ↔ x ∈ P.supp :=
  ⟨fun h ↦ h.left_mem, fun h ↦ rel_self_of_mem_supp h⟩

lemma Rel.left_rfl (h : P x y) : P x x :=
  rel_self_iff_mem_supp.mpr h.left_mem

lemma Rel.right_rfl (h : P x y) : P y y :=
  h.symm.left_rfl

@[simp]
lemma rel_bot : ⇑(⊥ : Partition (Set α)) = fun _ _ => False := by
  ext x y
  simp [rel_iff_exists]

@[simp]
lemma rel_top : ⇑(⊤ : Partition (Set α)) = fun _ _ => True := by
  obtain h | h := isEmpty_or_nonempty α <;> ext x y
  · exact h.elim x
  simp [rel_iff_exists]

@[simp]
lemma domain_rel : domain P = P.supp := by
  ext x
  simp only [mem_domain_iff, mem_supp_iff]
  exact ⟨fun ⟨y, S, hS, hxS, _⟩ => ⟨S, hS, hxS⟩, fun ⟨S, hS, hxS⟩ => ⟨x, S, hS, hxS, hxS⟩⟩

@[simp]
lemma codomain_rel : codomain P = P.supp := by
  rw [← domain_eq_codomain, domain_rel]

lemma rel_le_of_le (h : P ≤ Q) : ⇑P ≤ ⇑Q := by
  intro x y ⟨S, hS, hxS, hyS⟩
  obtain ⟨T, hT, hST⟩ := h S hS
  exact ⟨T, hT, hST hxS, hST hyS⟩

lemma le_of_rel_le (h : ⇑P ≤ ⇑Q) : P ≤ Q :=
  le_of_rel_le' h

lemma rel_le_iff_le : ⇑P ≤ ⇑Q ↔ P ≤ Q :=
  ⟨le_of_rel_le, rel_le_of_le⟩

lemma rel_inj (h : ⇑P = ⇑Q) : P = Q :=
  le_antisymm (le_of_rel_le h.le) (le_of_rel_le h.ge)

lemma rel_inj_iff : ⇑P = ⇑Q ↔ P = Q :=
  ⟨fun h => rel_inj h, fun h => h ▸ rfl⟩

lemma rel_le_of_isInducedSubpartition (h : P ≤ip Q) : ⇑P ≤ ⇑Q :=
  rel_le_of_le h.le

lemma rel_le_of_subset (h : P ⊆ Q) : ⇑P ≤ ⇑Q :=
  rel_le_of_le <| le_of_subset h

/-- A transitive, symmetric Binary relation `r` induces a partition of the set of elements on
  which it is reflexive. -/
@[simps] def ofRel (r : α → α → Prop) [IsTrans α r] [Std.Symm r] : Partition (Set α) where
  parts := fibers r
  indep := PairwiseDisjoint.sSupIndep fibers_pairwiseDisjoint
  bot_not_mem := emptySet_notMem_fibers r

@[simp]
lemma ofRel_supp {r : α → α → Prop} [Std.Symm r] [IsTrans α r] : (ofRel r).supp = domain r :=
  sUnion_fibers r

@[simp]
lemma rel_ofRel_eq {r : α → α → Prop} [IsTrans α r] [Std.Symm r] : ofRel r = r := by
  ext a b
  exact ⟨fun ⟨S, ⟨c, ⟨d, hdc⟩, heq⟩, haS, hbS⟩ => trans' (heq ▸ haS) (symm (heq ▸ hbS)),
    fun hab => ⟨fiber r b, fiber_mem_fibers hab, hab, refl_of_right hab⟩⟩

lemma ofRel_rel_eq (P : Partition (Set α)) : ofRel P = P := by
  apply rel_inj
  rw [rel_ofRel_eq]

lemma fibers_rel_eq : fibers P = P.parts := by
  rw [Set.ext_iff]
  exact (ofRel P).ext_iff.mp <| ofRel_rel_eq P

@[ext] theorem eq_of_rel_iff_rel {P P' : Partition (Set α)} (h : ∀ x y, P x y ↔ P' x y) :
    P = P' := by
  rw [← ofRel_rel_eq P, ← ofRel_rel_eq P']
  congr 1
  ext
  exact h _ _

@[simps!]
def ofRel' (r : α → α → Prop) : Partition (Set α) :=
  ofRel (Relation.TransClosure <| Relation.SymmClosure r)

@[simp]
lemma ofRel'_supp {r : α → α → Prop} : (ofRel' r).supp = domain r ∪ codomain r := by
  simp [ofRel']

@[simp]
lemma rel_ofRel'_eq {r : α → α → Prop} :
    ⇑(ofRel' r) = Relation.TransClosure (Relation.SymmClosure r) := by
  simp [ofRel']

lemma le_ofRel' (r : α → α → Prop) : r ≤ ofRel' r := by
  intro a b hab
  simp only [ofRel', rel_ofRel_eq]
  exact TransClosure.le_closure (SymmClosure r) a b <| SymmClosure.le_closure r a b hab


/-- The part containing a given element of the set being partitioned. If `x ∉ s`, then `∅`.  -/
def partOf (P : Partition (Set α)) (x : α) : Set α :=
  fiber P x

lemma partOf_subset_supp : P.partOf x ⊆ P.supp := by
  rintro y ⟨t, ht, hxt, hyt⟩
  exact subset_of_mem ht hxt

lemma exists_partOf_iff_mem : S ∈ P ↔ ∃ x ∈ P.supp, partOf P x = S := by
  rw [← mem_parts, ← fibers_rel_eq, mem_fibers_iff, codomain_rel]
  rfl

lemma partOf_mem (hx : x ∈ P.supp) : P.partOf x ∈ P := by
  rw [exists_partOf_iff_mem]
  use x

lemma partOf_eq_empty (P : Partition (Set α)) (hx : x ∉ P.supp) : P.partOf x = ∅ :=
  fiber_empty.mpr (by simpa)

@[simp]
lemma partOf_ne_bot_iff : P.partOf x ≠ ⊥ ↔ x ∈ P.supp := by
  refine ⟨fun h => ?_, fun h => P.ne_bot_of_mem (partOf_mem h)⟩
  obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr h
  exact Rel.right_mem hy

@[simp]
lemma partOf_eq_empty_iff : P.partOf x = ∅ ↔ x ∉ P.supp := by
  rw [← partOf_ne_bot_iff]
  tauto

lemma mem_partOf (hx : x ∈ P.supp) : x ∈ P.partOf x :=
  (mem_fiber_iff _).mpr <| rel_self_of_mem_supp hx

@[simp] lemma mem_partOf_iff : y ∈ P.partOf x ↔ P y x := mem_fiber_iff _

lemma eq_partOf_of_mem (ht : T ∈ P) (hxt : x ∈ T) : T = P.partOf x := by
  obtain ⟨y, hy, rfl⟩ := exists_partOf_iff_mem.mp ht
  exact fiber_eq_of_mem (by exact hxt) <| rel_of_mem_of_mem ht hxt hxt

lemma eq_partOf_iff_mem (hxT : x ∈ T) : T = P.partOf x ↔ T ∈ P := by
  refine ⟨?_, (eq_partOf_of_mem · hxT)⟩
  rintro rfl
  apply partOf_mem
  rw [mem_partOf_iff] at hxT
  exact rel_self_iff_mem_supp.mp hxT

lemma rel_iff_of_partOf_mem {Q : Partition (Set α)} (h : P.partOf x ∈ Q) : P x y ↔ Q x y := by
  simp_rw [rel_iff_exists]
  refine ⟨fun ⟨t, htP, hxt, hyt⟩ => ⟨t, ?_, hxt, hyt⟩, fun ⟨t, htQ, hxt, hyt⟩ => ⟨t, ?_, hxt, hyt⟩⟩
  · obtain rfl := P.eq_partOf_of_mem htP hxt
    exact h
  have hxP : x ∈ P.supp := by
    obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr <| Q.ne_bot_of_mem h
    exact Rel.right_mem hy
  obtain rfl := Q.eq_partOf_of_mem htQ hxt
  obtain heq := Q.eq_of_mem_of_mem h htQ (mem_partOf hxP) hxt
  exact heq.symm ▸ (partOf_mem hxP)

lemma partOf_mem_iff_rel_iff {Q : Partition (Set α)} :
    P.partOf x ∈ Q ↔ x ∈ P.supp ∧ ∀ y, P x y ↔ Q x y := by
  refine ⟨fun h => ⟨partOf_ne_bot_iff.mp (Q.ne_bot_of_mem h), fun y ↦ rel_iff_of_partOf_mem h⟩,
    fun ⟨hx, hrel⟩ => ?_⟩
  rw [exists_partOf_iff_mem]
  use x, rel_self_iff_mem_supp.mp <| (hrel x).mp (rel_self_iff_mem_supp.mpr hx), ?_
  ext y
  simp only [partOf, mem_fiber_iff]
  rw [rel_comm, ← hrel y, rel_comm]

@[simp]
lemma indiscrete_rel (hS : S ≠ ∅) : ⇑(Partition.indiscrete S hS) = fun x y ↦ x ∈ S ∧ y ∈ S := by
  ext x y
  simp [rel_iff_exists]

@[simp]
lemma indiscrete'_rel : ⇑(Partition.indiscrete' S) = fun x y ↦ x ∈ S ∧ y ∈ S := by
  ext x y
  simp only [rel_iff_exists, mem_indiscrete'_iff, bot_eq_empty, ne_eq, ← nonempty_iff_ne_empty,
    existsAndEq, and_true, and_iff_right_iff_imp, and_imp]
  rintro hx hy
  use x

@[simp]
lemma induce_rel (P : Partition (Set α)) {S : Set α} :
    ⇑(P.induce S) = fun x y ↦ x ∈ S ∧ y ∈ S ∧ P x y := by
  ext x y
  simp only [rel_iff_exists, mem_induce_iff]
  refine ⟨fun ⟨t, ⟨htne, t', ht'P, heq⟩, hxt, hyt⟩ ↦ ?_,
    fun ⟨hxS, hyS, t, htP, hxt, hyt⟩ ↦ ⟨S ∩ t, ⟨?_, t, htP, rfl⟩, ⟨hxS, hxt⟩, ⟨hyS, hyt⟩⟩⟩
  · subst t
    exact ⟨hxt.1, hyt.1, t', ht'P, hxt.2, hyt.2⟩
  rw [bot_eq_empty, ← nonempty_iff_ne_empty, inter_nonempty]
  use x

@[simp]
lemma induce_apply (P : Partition (Set α)) {S : Set α} :
    P.induce S x y ↔ x ∈ S ∧ y ∈ S ∧ P x y := by rw [induce_rel]

lemma isInducedSubpartition_iff_rel (P Q : Partition (Set α)) :
    P ≤ip Q ↔ (fun x y ↦ x ∈ P.supp ∧ y ∈ P.supp ∧ Q x y) = ⇑P := by
  rw [isInducedSubpartition_iff, ← rel_inj_iff, induce_rel]

lemma isInducedSubpartition.rel (h : P ≤ip Q) : ⇑P = fun x y ↦ x ∈ P.supp ∧ y ∈ P.supp ∧ Q x y :=
  (P.isInducedSubpartition_iff_rel Q).mp h |>.symm

lemma restrict_rel (P : Partition (Set α)) {S : Set (Set α)} (hS : S ⊆ P.parts) :
    ⇑(P.restrict S hS) = fun x y ↦ x ∈ ⋃₀ S ∧ P x y := by
  ext x y
  simp only [rel_iff_exists, mem_restrict_iff, mem_sUnion]
  refine ⟨fun ⟨t, htS, hxt, hyt⟩ ↦ ⟨⟨t, htS, hxt⟩, t, hS htS, hxt, hyt⟩,
    fun ⟨⟨s, hsS, hxs⟩, t, htP, hxt, hyt⟩ ↦ ⟨t, ?_, hxt, hyt⟩⟩
  obtain rfl := eq_of_mem_of_mem htP (hS hsS) hxt hxs
  exact hsS

@[simp]
lemma restrict_apply (P : Partition (Set α)) {S : Set (Set α)} (hS : S ⊆ P.parts) :
    P.restrict S hS x y ↔ x ∈ ⋃₀ S ∧ P x y := by rw [P.restrict_rel hS]

lemma rel_of_restrict_rel (P : Partition (Set α)) {S : Set (Set α)} (hS : S ⊆ P.parts)
    (hx : x ∈ ⋃₀ S) (hxy : P x y) : P.restrict S hS x y := by
  rw [restrict_rel]
  exact ⟨hx, hxy⟩

@[simp]
lemma delete_rel (P : Partition (Set α)) (S : Set (Set α)) :
    ⇑(P \ S) = fun x y ↦ ∃ t ∈ P \ S, x ∈ t ∧ y ∈ t := rfl

-- I am not really happy with this simplification route.
lemma cover_rel (P : Partition (Set α)) (S : Set α) :
    ⇑(P.cover S) = Relation.Domp P (P.induce S) := by
  ext x y
  simp only [cover, mem_parts, not_disjoint_iff, restrict_apply, mem_sUnion, mem_setOf_eq,
    induce_rel]
  refine ⟨fun ⟨⟨s, ⟨hsP, z, hzS, hzs⟩, hxs⟩, t, htP, hxt, hyt⟩ ↦ ?_,
    fun ⟨a, hxa, b, ⟨hbS, haS, hba⟩, hby⟩ ↦ ⟨?_, (hxa.trans (hba.symm)).trans hby⟩⟩
  · obtain rfl := P.eq_of_mem_of_mem hsP htP hxs hxt
    use z, (by use s), z, ⟨hzS, hzS, (by use s)⟩, (by use s)
  obtain ⟨t, htP, hxt, hat⟩ := hxa
  exact ⟨t, ⟨htP, by use a⟩, hxt⟩

@[simp]
lemma cover_rel_of_left_mem (P : Partition (Set α)) (hx : x ∈ S) : P.cover S x y ↔ P x y := by
  simp only [cover, mem_parts, not_disjoint_iff, restrict_apply, mem_sUnion, mem_setOf_eq,
    and_assoc, and_iff_right_iff_imp]
  rintro ⟨t, ht, hxt, hyt⟩
  use t, ht, by use x

@[simp]
lemma cover_rel_of_right_mem (P : Partition (Set α)) (hy : y ∈ S) : P.cover S x y ↔ P x y := by
  rw [rel_comm, cover_rel_of_left_mem P hy, rel_comm]

lemma subset_cover_supp (h : S ⊆ P.supp) : S ⊆ (P.cover S).supp := by
  rintro x hxS
  obtain ⟨t, ht, hxt⟩ := h hxS
  simp only [cover_supp, mem_parts, sSup_eq_sUnion, mem_sUnion, mem_setOf_eq,
    and_assoc, not_disjoint_iff]
  use t, ht, ?_
  use x

lemma rel_of_subset_mem (hPQ : P ⊆ Q) (hx : x ∈ P.supp) (hxy : Q x y) : P x y := by
  obtain ⟨S, hS, rfl⟩ := subset_iff_restrict.mp hPQ
  exact Q.rel_of_restrict_rel hPQ hx hxy

lemma subset_iff_rel : P ⊆ Q ↔ ∀ ⦃x y⦄, x ∈ P.supp → (P x y ↔ Q x y) := by
  refine ⟨fun h x y hx => ⟨rel_le_of_subset h x y, rel_of_subset_mem h hx⟩, fun h s hs => ?_⟩
  rw [← fibers_rel_eq, mem_fibers_iff] at hs ⊢
  obtain ⟨x, hx, rfl⟩ := hs
  have hxsupp := codomain_rel ▸ hx
  have ⟨y, hyx⟩ := hx
  use x, ⟨y, symm <| (h hxsupp).mp hyx.symm⟩
  ext z
  simp [(rel_comm.trans <| h hxsupp).trans rel_comm]

lemma agree_iff_rel : P.Agree Q ↔ ∀ x y, x ∈ P.supp → x ∈ Q.supp → (P x y ↔ Q x y) := by
  rw [agree_iff_mem_of_not_disjoint]
  refine ⟨fun h x y hxP hxQ => rel_iff_of_partOf_mem (h _ (partOf_mem hxP)
    <| Set.not_disjoint_iff.mpr ⟨x, hxQ, mem_partOf hxP⟩), fun h s hsP hndisj => ?_⟩
  rw [Set.not_disjoint_iff] at hndisj
  obtain ⟨x, hx, hndisj⟩ := hndisj
  obtain rfl := P.eq_partOf_of_mem hsP hndisj
  rw [partOf_mem_iff_rel_iff]
  have hxP : x ∈ P.supp := rel_self_iff_mem_supp.mp hndisj
  exact ⟨hxP, fun y ↦ h x y hxP hx⟩

lemma Agree.rel_of_left_of_mem (h : P.Agree Q) (hx : x ∈ Q.supp) (hxy : P x y) : Q x y := by
  rw [agree_iff_rel] at h
  exact h x y hxy.left_mem hx |>.mp hxy

lemma Agree.rel_of_right_of_mem (h : P.Agree Q) (hy : x ∈ P.supp) (hxy : Q x y) : P x y := by
  rw [agree_iff_rel] at h
  exact h x y hy hxy.left_mem |>.mpr hxy

lemma Agree.trans_left (h : P.Agree Q) (hab : P a b) (hbc : Q b c) : P a c :=
  trans' hab <| h.rel_of_right_of_mem hab.right_mem hbc

lemma Agree.trans_right (h : P.Agree Q) (hab : P a b) (hbc : Q b c) : Q a c :=
  trans' (h.rel_of_left_of_mem hbc.left_mem hab.symm).symm hbc

lemma Agree.sup_rel_trans (h : P.Agree Q) (hab : (⇑P ⊔ ⇑Q) a b) (hbc : (⇑P ⊔ ⇑Q) b c) :
    (⇑P ⊔ ⇑Q) a c := by
  obtain (hP1 | hQ1) := hab <;> obtain (hP2 | hQ2) := hbc
  · left
    exact Rel.trans hP1 hP2
  · left
    exact h.trans_left hP1 hQ2
  · right
    exact h.symm.trans_left hQ1 hP2
  · right
    exact Rel.trans hQ1 hQ2

lemma inf_rel_trans (hab : (⇑P ⊓ ⇑Q) a b) (hbc : (⇑P ⊓ ⇑Q) b c) : (⇑P ⊓ ⇑Q) a c :=
  ⟨trans' hab.1 hbc.1, trans' hab.2 hbc.2⟩

end Rel

section Discrete

variable {α : Type*} {S T : Set α} {a b : α} {P Q : Partition (Set α)}

/-- The discrete partition -/
@[simps]
protected def discrete (S : Set α) : Partition (Set α) where
  parts := singleton '' S
  indep := by
    rintro _ ⟨a, haS, rfl⟩ T hTa hT
    have hS : sSup (singleton '' S \ {{a}}) = S \ {a} := by
      ext x
      simp +contextual only [sSup_eq_sUnion, mem_sUnion, mem_diff, mem_image, mem_singleton_iff,
        iff_def, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, singleton_eq_singleton_iff,
        not_false_eq_true, and_self, implies_true, true_and]
      rintro hxS hne
      use {x}
      simp [hxS, hne]
    rw [hS] at hT
    suffices Disjoint (S \ {a}) {a} by exact this hT hTa
    simp
  bot_not_mem := by
    rintro ⟨a, ha, heq⟩
    simp at heq

@[simp] lemma supp_discrete (S : Set α) : (Partition.discrete S).supp = S := by
  simp [Partition.discrete, supp]

@[simp] lemma mem_discrete_iff : T ∈ (Partition.discrete S) ↔ ∃ a ∈ S, {a} = T := by
  rw [← mem_parts]
  simp [Partition.discrete]

lemma mem_discrete_of_mem_supp {x : α} (h : x ∈ S) : {x} ∈ Partition.discrete S := by
  use x

lemma rel_discrete_eq' : Partition.discrete S = fun a b => a = b ∧ b ∈ S := by
  ext a b
  rw [and_comm]
  simp [Partition.discrete, rel_iff_exists, ← mem_parts]

@[simp]
lemma rel_discrete_eq : Partition.discrete S = fun a b => a = b ∧ a ∈ S := by
  ext a b
  rw [rel_discrete_eq', and_congr_right_iff]
  rintro rfl
  rfl

@[simp]
lemma rel_discrete_iff : Partition.discrete S a b ↔ a = b ∧ a ∈ S := by
  rw [rel_discrete_eq]

lemma eq_of_rel_of_left_singleton_mem (hab : P a b) (ha : {a} ∈ P) : a = b := by
  obtain ⟨t, htP, hat, hbt⟩ := hab
  obtain rfl := P.eq_of_mem_of_mem ha htP rfl hat
  simp_all

lemma eq_of_rel_of_right_singleton_mem (hab : P a b) (hb : {b} ∈ P) : a = b := by
  rw [rel_comm] at hab
  exact (eq_of_rel_of_left_singleton_mem hab hb).symm

@[simp]
lemma discrete_atomic (S : Set α) : (Partition.discrete S).Atomic := by
  rintro _ ⟨a, -, rfl⟩
  exact isAtom_singleton a

lemma Atomic.exists_singleton_of_mem (hP : Atomic P) {t : Set α} (htP : t ∈ P) : ∃ a, t = {a} :=
  Set.isAtom_iff.mp <| hP t htP

lemma atomic_iff_eq_discrete (P : Partition (Set α)) :
    P.Atomic ↔ P = Partition.discrete P.supp := by
  refine ⟨fun h => ?_, fun h => h ▸ discrete_atomic P.supp⟩
  apply Partition.ext fun x ↦ ?_
  refine ⟨fun hx => ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := h.exists_singleton_of_mem hx
    simp only [mem_discrete_iff, singleton_eq_singleton_iff, exists_eq_right]
    exact mem_supp_iff.mpr ⟨{a}, hx, rfl⟩
  rintro ⟨a, ⟨t, htP, hat⟩, rfl⟩
  obtain ⟨b, rfl⟩ := h.exists_singleton_of_mem htP
  obtain rfl := mem_singleton_iff.mp hat
  exact htP

@[simp]
lemma mem_atomic_iff (hP : P.Atomic) : S ∈ P ↔ ∃ a ∈ P.supp, {a} = S := by
  rw [atomic_iff_eq_discrete] at hP
  nth_rw 1 [hP]
  refine ⟨fun h => by simpa using h, ?_⟩
  rintro ⟨a, ha, rfl⟩
  simpa

lemma eq_discrete_iff : P = Partition.discrete S ↔ P.Atomic ∧ P.supp = S := by
  constructor
  · rintro rfl
    exact ⟨discrete_atomic S, supp_discrete S⟩
  rintro ⟨hP, rfl⟩
  exact (atomic_iff_eq_discrete P).mp hP

lemma eq_discrete_of (hP : Atomic P) (hS : P.supp = S) : P = Partition.discrete S :=
  eq_discrete_iff.mpr ⟨hP, hS⟩

lemma discrete_le_of_supp_eq (P : Partition (Set α)) : Partition.discrete P.supp ≤ P := by
  refine le_of_rel_le fun a b => ?_
  rw [rel_discrete_iff]
  rintro ⟨rfl, hb⟩
  exact rel_self_of_mem_supp hb

lemma atomic_iff_rel_le_eq (P : Partition (Set α)) : P.Atomic ↔ ⇑P ≤ Eq := by
  refine ⟨fun h x y ⟨t, htP, hxt, hyt⟩ ↦ ?_, fun h t htP ↦ ?_⟩
  · obtain ⟨a, rfl⟩ := Set.isAtom_iff.mp <| h t htP
    rw [mem_singleton_iff] at hxt hyt
    exact hxt.trans (symm hyt)
  rw [Set.isAtom_iff, Set.exists_eq_singleton_iff_nonempty_subsingleton]
  exact ⟨P.nonempty_of_mem htP, fun x hxt y hyt => h x y ⟨t, htP, hxt, hyt⟩⟩

lemma Atomic.eq_of_rel (hP : Atomic P) (hab : P a b) : a = b :=
  P.atomic_iff_rel_le_eq.mp hP _ _ hab

lemma Atomic.rel_eq (hP : Atomic P) : ⇑P = fun a b => a = b ∧ a ∈ P.supp := by
  ext a b
  refine ⟨fun hPab => ⟨hP.eq_of_rel hPab, hPab.left_mem⟩, ?_⟩
  rintro ⟨rfl, ha⟩
  exact rel_self_of_mem_supp ha

lemma discrete_of_le_discrete (hS : P ≤ Partition.discrete S) : P = Partition.discrete P.supp := by
  rw [← atomic_iff_eq_discrete]
  exact (discrete_atomic S).atomic_of_le hS

lemma discrete_subset_discrete_of_subset (hST : S ⊆ T) :
    Partition.discrete S ⊆ Partition.discrete T := by
  rintro s hsS
  obtain ⟨x, hx, rfl⟩ := hsS
  use x, hST hx

@[simp]
lemma discrete_subset_discrete_iff : Partition.discrete S ⊆ Partition.discrete T ↔ S ⊆ T :=
  ⟨fun h x => by simpa using @h {x}, discrete_subset_discrete_of_subset⟩

lemma discrete_mono (hST : S ⊆ T) : Partition.discrete S ≤ Partition.discrete T := by
  rw [← (discrete_atomic T).subset_iff_le]
  exact discrete_subset_discrete_of_subset hST

lemma discrete_subset_iff_rel : Partition.discrete S ⊆ P ↔ ∀ x y, x ∈ S → (x = y ↔ P x y) := by
  simp +contextual [subset_iff_rel]

@[simp]
lemma discrete_empty : Partition.discrete (∅ : Set α) = ⊥ := by
  ext x
  simp

lemma supp_singleton_iff (hP : P.supp = {a}) : P = Partition.discrete {a} := by
  simp only [← codomain_rel, Set.ext_iff, mem_codomain_iff, mem_singleton_iff] at hP
  rw [← Partition.rel_inj_iff]
  ext x y
  simp only [rel_discrete_iff, mem_singleton_iff]
  refine ⟨fun h => ?_, ?_⟩
  · obtain rfl := (hP y).mp ⟨x, h⟩
    obtain rfl := (hP x).mp ⟨y, symm h⟩
    simp
  rintro ⟨rfl, rfl⟩
  obtain ⟨a, ha⟩ := (hP x).mpr rfl
  exact refl_of_right ha

lemma atomic_of_supp_singleton (hP : P.supp = {a}) : P.Atomic := by
  rw [supp_singleton_iff hP]
  exact discrete_atomic {a}

@[simp]
lemma discrete_le_iff : Partition.discrete S ≤ P ↔ S ⊆ P.supp := by
  refine ⟨fun h x hx => ?_, fun h t ht => ?_⟩
  · obtain ⟨t, htP, hxt⟩ := h {x} (mem_discrete_of_mem_supp hx)
    simp only [le_eq_subset, singleton_subset_iff] at hxt
    exact mem_supp_iff.mpr ⟨t, htP, hxt⟩
  obtain ⟨a, haP, rfl⟩ := (by simpa using ht); clear ht
  exact ⟨P.partOf a, partOf_mem (h haP), by simp [rel_self_iff_mem_supp, h haP]⟩

@[simp]
lemma discrete_isInducedSubpartition_iff :
    Partition.discrete S ≤ip Q ↔ S ⊆ Q.supp ∧ Atomic (Q.induce S) := by
  simp only [isInducedSubpartition_iff, supp_discrete, atomic_iff_eq_discrete, ↓induce_supp',
    inf_eq_inter]
  refine ⟨fun h => ?_, fun ⟨hsu, heq⟩ => by rw [heq, inter_eq_left.mpr hsu]⟩
  have hsupp : S ⊆ Q.supp := by
    rw [← supp_discrete S, ← h]
    exact supp_le_of_le induce_le
  simpa [hsupp, inter_eq_left.mpr]

-- What is the full generality of this?
@[simp]
lemma agree_of_atomic (hP : P.Atomic) (hQ : Q.Atomic) : P.Agree Q := by
  unfold Agree
  rw [atomic_iff_eq_discrete] at hP hQ
  have hsSup : sSupIndep (P.parts ∪ Q.parts) := by
    rw [hP, hQ, discrete_parts, discrete_parts, ← Set.image_union]
    rintro s ⟨a, (haP | haQ), rfl⟩ <;> simp only [sSup_eq_sUnion, disjoint_singleton_left,
      mem_sUnion, mem_diff, mem_image, mem_union, mem_singleton_iff, not_exists, not_and, and_imp,
      forall_exists_index, forall_apply_eq_imp_iff₂, singleton_eq_singleton_iff]
    all_goals exact fun _ _ h1 h2 ↦ h1 h2.symm
  use ofIndependent hsSup (by rw [mem_union, not_or]; exact ⟨P.bot_not_mem, Q.bot_not_mem⟩), ?_ <;>
    rintro s hs <;> simp only [ofIndependent_parts, mem_union, mem_parts]
  · exact Or.inr hs
  exact Or.inl hs

end Discrete

section Flatten

variable [Order.Frame α] {P : Partition (Set α)} {Q : Partition α} (h : P.supp = Q.parts) {p q : α}

def flatten (P : Partition (Set α)) {Q : Partition α} (h : P.supp = Q.parts) : Partition α where
  parts := sSup '' P.parts
  indep := by
    rintro a ⟨F, hF, rfl⟩
    simp_rw [disjoint_sSup_iff, sSup_disjoint_iff]
    rintro _ ⟨⟨S, hSP, rfl⟩, hSF⟩ f hf
    rw [disjoint_sSup_iff]
    rintro s hs
    have hfs : f ≠ s := by
      rintro rfl
      obtain rfl := P.eq_of_mem_of_mem hSP hF hs hf
      simp at hSF
    refine Q.disjoint ?_ ?_ hfs <;> rw [← mem_parts, ← h, mem_supp_iff]
    · use F, hF
    · use S, hSP
  bot_not_mem := by
    rintro ⟨F, hF, hbot⟩
    obtain ⟨a, ha⟩ := P.nonempty_of_mem hF
    have hFa := Q.ne_bot_of_mem <| show a ∈ Q.parts from h ▸ ⟨F, hF, ha⟩
    rw [← bot_lt_iff_ne_bot, ← hbot] at hFa
    exact le_sSup ha |>.not_gt hFa

@[simp]
lemma flatten_parts (P : Partition (Set α)) (h : P.supp = Q.parts) :
    (flatten P h).parts = sSup '' P.parts := rfl

@[simp]
lemma flatten_supp (P : Partition (Set α)) (h : P.supp = Q.parts) :
    (flatten P h).supp = Q.supp := by
  simp only [supp, flatten, ← h, sSup_eq_sUnion]
  rw [sSup_image, sSup_sUnion]

lemma le_flatten (P : Partition (Set α)) (h : P.supp = Q.parts) : Q ≤ P.flatten h := by
  intro q hqQ
  rw [← mem_parts, ← h, mem_supp_iff] at hqQ
  obtain ⟨F, hF, hqF⟩ := hqQ
  use sSup F, (by use F, hF), le_sSup hqF



end Flatten


end Partition
