import Mathlib.Data.Setoid.Partition
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Set.Finite.Powerset
import Matroid.ForMathlib.Lattice
import Matroid.ForMathlib.Relation

open Set Function Relation

variable {α β : Type*} {s t x y z : α}

structure Partition (α : Type*) [CompleteLattice α] where
  parts : Set α
  indep : sSupIndep parts
  bot_notMem : ⊥ ∉ parts

namespace Partition

section Basic

variable [CompleteLattice α] {P Q : Partition α}

def supp (P : Partition α) : α := sSup P.parts

instance : SetLike (Partition α) α where
  coe := Partition.parts
  coe_injective' p p' h := by cases p; cases p'; simpa using h

@[simp] lemma mem_parts : x ∈ P.parts ↔ x ∈ (P : Set α) := Iff.rfl

@[ext] lemma ext (hP : ∀ x, x ∈ P ↔ x ∈ Q) : P = Q := by
  cases P
  cases Q
  simp only [mk.injEq]
  ext x
  simpa using hP x

instance : HasSubset (Partition α) where
  Subset P Q := P.parts ⊆ Q.parts

instance : IsPartialOrder (Partition (Set α)) (· ⊆ ·) where
  refl _ _ := id
  trans _ _ _ hPQ hQR _ h := hQR (hPQ h)
  antisymm _ _ hPQ hPQ' := by ext S; exact ⟨(hPQ ·), (hPQ' ·)⟩

lemma disjoint (hx : x ∈ P) (hy : y ∈ P) (hxy : x ≠ y) : Disjoint x y :=
  P.indep.pairwiseDisjoint hx hy hxy

lemma pairwiseDisjoint : Set.PairwiseDisjoint (P : Set α) id :=
  fun _ hx _ hy hxy ↦ P.disjoint hx hy hxy

lemma ne_bot_of_mem (hx : x ∈ P) : x ≠ ⊥ :=
  fun h ↦ P.bot_notMem <| h ▸ hx

lemma bot_lt_of_mem (hx : x ∈ P) : ⊥ < x :=
  bot_lt_iff_ne_bot.2 <| P.ne_bot_of_mem hx

lemma sSup_eq (P : Partition α) : sSup P = P.supp  := rfl

lemma iSup_eq (P : Partition α) : ⨆ x ∈ P, x = P.supp := by
  simp_rw [← P.sSup_eq, sSup_eq_iSup]
  rfl

lemma le_of_mem (P : Partition α) (hx : x ∈ P) : x ≤ P.supp :=
  (le_sSup hx).trans_eq P.sSup_eq

lemma parts_nonempty (P : Partition α) (hs : P.supp ≠ ⊥) : (P : Set α).Nonempty :=
  nonempty_iff_ne_empty.2 fun hP ↦ by simp [← P.sSup_eq, hP, sSup_empty] at hs

end Basic

section PairwiseDisjoint

variable {α : Type*} [Order.Frame α] {s t x y z : α} {parts : Set α}

@[simps] def ofPairwiseDisjoint (pairwiseDisjoint : parts.PairwiseDisjoint id)
    (forall_nonempty : ⊥ ∉ parts) : Partition α where
  parts := parts
  indep := sSupIndep_iff_pairwiseDisjoint.mpr pairwiseDisjoint
  bot_notMem := forall_nonempty

@[simp] lemma mem_ofPairwiseDisjoint (pairwiseDisjoint : parts.PairwiseDisjoint id)
    (forall_nonempty : ⊥ ∉ parts) :
  x ∈ ofPairwiseDisjoint pairwiseDisjoint forall_nonempty ↔ x ∈ parts := Iff.rfl

@[simp]
lemma supp_ofPairwiseDisjoint (pairwiseDisjoint : parts.PairwiseDisjoint id)
    (forall_nonempty : ⊥ ∉ parts) :
  (ofPairwiseDisjoint pairwiseDisjoint forall_nonempty).supp = sSup parts := rfl

@[simps] def ofPairwiseDisjoint' (pairwiseDisjoint : parts.PairwiseDisjoint id)
  (forall_nonempty : ∀ s ∈ parts, s ≠ ⊥) :
    Partition α where
  parts := parts
  indep := pairwiseDisjoint.sSupIndep
  bot_notMem := fun h ↦ by simpa using forall_nonempty _ h

@[simp]
lemma supp_ofPairwiseDisjoint' (pairwiseDisjoint : parts.PairwiseDisjoint id)
    (forall_nonempty : ∀ s ∈ parts, s ≠ ⊥) :
  (ofPairwiseDisjoint' pairwiseDisjoint forall_nonempty).supp = sSup parts := rfl

@[simp] lemma mem_ofPairwiseDisjoint' (pairwiseDisjoint) (forall_nonempty) {x : α} :
  x ∈ ofPairwiseDisjoint' (parts := parts) pairwiseDisjoint forall_nonempty ↔
    x ∈ parts := Iff.rfl

end PairwiseDisjoint

section indep

variable [CompleteLattice α] {u : Set α} {a : α}

/-- A `sSupIndep` collection not containing `⊥` gives a partition of its supremum. -/
@[simps] def ofIndependent {u : Set α} (hs : sSupIndep u) (hbot : ⊥ ∉ u) : Partition α where
  parts := u
  indep := hs
  bot_notMem := hbot

@[simp] lemma mem_ofIndependent_iff {u : Set α} (hu : sSupIndep u)
    (h : ⊥ ∉ u) {a : α} : a ∈ ofIndependent hu h ↔ a ∈ u := Iff.rfl

@[simp] lemma supp_ofIndependent {u : Set α} (hu : sSupIndep u) (hbot : ⊥ ∉ u) :
    (ofIndependent hu hbot).supp = sSup u := rfl

/-- A `sSupIndep` collection gives a partition of its supremum by removing `⊥`. -/
def ofIndependent' {u : Set α} (hs : sSupIndep u) : Partition α :=
  (ofIndependent (hs.mono (diff_subset (t := {⊥}))) (fun h ↦ h.2 rfl))

@[simp] lemma mem_ofIndependent'_iff {u : Set α} (hu : sSupIndep u) {a : α} :
  a ∈ ofIndependent' hu ↔ a ∈ u ∧ a ≠ ⊥ := Iff.rfl

@[simp] lemma supp_ofIndependent' {u : Set α} (hu : sSupIndep u) :
    (ofIndependent' hu).supp = sSup u := by
  show sSup (u \ {⊥}) = sSup u
  simp

/-- The subpartition with over a subset of the parts. -/
def restrict {P : Partition α} {s : Set α} (hs : s ⊆ P.parts) : Partition α where
  parts := s
  indep := P.indep.mono hs
  bot_notMem h := P.bot_notMem (hs h)

@[simp] lemma restrict_parts {P : Partition α} {s : Set α} (hs : s ⊆ P.parts) :
    (P.restrict hs).parts = s := rfl

@[simp] lemma mem_restrict_iff {P : Partition α} {s : Set α} (hs : s ⊆ P.parts) {a : α} :
    a ∈ P.restrict hs ↔ a ∈ s := Iff.rfl

/-- The partition with no parts. -/
@[simps] protected def empty (α : Type*) [CompleteLattice α] : Partition α where
  parts := ∅
  indep := by simp
  bot_notMem := by simp

@[simp] lemma empty_coe_eq (α : Type*) [CompleteLattice α] :
    (Partition.empty α : Set α) = ∅ := rfl

@[simp] lemma notMem_empty (α : Type*) [CompleteLattice α] {a : α} :
    a ∉ Partition.empty α := by
  rw [← SetLike.mem_coe, empty_coe_eq]
  simp

@[simp] lemma supp_empty (α : Type*) [CompleteLattice α] : (Partition.empty α).supp = ⊥ := by
  simp [Partition.empty, supp]

lemma eq_empty {P : Partition α} (hP : P.supp = ⊥) : P = Partition.empty α := by
  ext x
  have hsup := P.sSup_eq
  simp only [sSup_eq_bot, SetLike.mem_coe, hP] at hsup
  simp only [notMem_empty, iff_false]
  exact fun hx ↦ P.ne_bot_of_mem hx <| hsup x hx

@[simp]
lemma supp_eq_bot_iff {P : Partition α} : P.supp = ⊥ ↔ P = Partition.empty α := by
  refine ⟨eq_empty, ?_⟩
  rintro rfl
  exact supp_empty α

instance {α : Type*} [CompleteLattice α] [Subsingleton α] : Unique (Partition α) where
  default := Partition.empty α
  uniq P := eq_empty (by
    simp only [← P.sSup_eq, sSup_eq_bot, SetLike.mem_coe]
    exact fun a b ↦ Subsingleton.elim _ _)

/-- The one-part partition. -/
@[simps] def indiscrete (s : α) (hs : s ≠ ⊥) : Partition α where
  parts := {s}
  indep := by simp [sSupIndep]
  bot_notMem := by simpa using hs.symm

@[simp] lemma mem_indiscrete_iff (s : α) (hs : s ≠ ⊥) {a : α} :
    a ∈ Partition.indiscrete s hs ↔ a = s := Iff.rfl

@[simp]
lemma supp_indiscrete (s : α) (hs : s ≠ ⊥) : (Partition.indiscrete s hs).supp = s := by
  simp [Partition.indiscrete, supp]

noncomputable def indiscrete' (s : α) : Partition α :=
  let _ : Decidable (s = ⊥) := Classical.dec _
  if hs : s = ⊥ then Partition.empty α else indiscrete s hs

@[simp]
lemma indiscrete'_eq_empty : indiscrete' ⊥ = Partition.empty α := by
  simp [indiscrete']

@[simp]
lemma indiscrete'_eq_of_ne_bot {s : α} (hs : s ≠ ⊥) : indiscrete' s = indiscrete s hs := by
  simp only [indiscrete', hs, ↓reduceDIte]

@[simp]
lemma supp_indiscrete' {s : α} : (indiscrete' s).supp = s := by
  simp [indiscrete']
  split_ifs with hs
  · rw [supp_empty, hs]
  · rw [supp_indiscrete s hs]

@[simp]
lemma mem_indiscrete'_iff : a ∈ indiscrete' s ↔ a = s ∧ a ≠ ⊥ := by
  simp only [indiscrete', ne_eq]
  split_ifs with hs
  · subst s
    simp
  · simp only [mem_indiscrete_iff, iff_self_and]
    rintro rfl
    exact hs

lemma eq_of_mem_indiscrete' (has : a ∈ indiscrete' s) : a = s := by
  rw [mem_indiscrete'_iff] at has
  exact has.1

lemma ne_bot_of_mem_indiscrete' (has : a ∈ indiscrete' s) : a ≠ ⊥ := by
  rw [mem_indiscrete'_iff] at has
  exact has.2

end indep

section Order

variable {α : Type*} [CompleteLattice α] {s t a : α}

instance : PartialOrder (Partition α) where
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

instance : OrderTop (Partition α) where
  top := ofIndependent' (sSupIndep_singleton ⊤)
  le_top := by
    obtain (hs | hs) := eq_or_ne ⊤ (⊥ : α)
    · have : Subsingleton α := subsingleton_of_bot_eq_top hs.symm
      simp [hs]
    exact fun P x hx ↦ ⟨⊤, by simp [hs], by simp⟩

@[simp] lemma mem_top_iff {a : α} : a ∈ (⊤ : Partition α) ↔ a = ⊤ ∧ a ≠ ⊥ := by
  change a ∈ ofIndependent' (sSupIndep_singleton ⊤) ↔ _
  rw [mem_ofIndependent'_iff, mem_singleton_iff]

lemma top_eq_indiscrete (hs : ⊤ ≠ ⊥) : (⊤ : Partition α) = indiscrete ⊤ hs := by
  ext a
  rw [mem_top_iff, mem_indiscrete_iff, and_iff_left_iff_imp]
  rintro rfl; assumption

lemma parts_top_subset : ((⊤ : Partition α) : Set α) ⊆ {⊤} := by
  simp

instance : OrderBot (Partition α) where
  bot := Partition.empty α
  bot_le a s hs := by simp only [notMem_empty] at hs

@[simp] lemma notMem_bot {a : α} : a ∉ (⊥ : Partition α) := notMem_empty α

@[simp] lemma supp_bot : (⊥ : Partition α).supp = ⊥ := sSup_empty

lemma supp_le_of_le {P Q : Partition α} (h : P ≤ Q) : P.supp ≤ Q.supp :=
  sSup_le_sSup_of_forall_exists_le h

end Order

section Discrete

variable {α : Type*} [CompleteAtomicBooleanAlgebra α]

/-- The discrete partition -/
protected noncomputable def discrete (a : α) : Partition α :=
  let S := {b : α | IsAtom b ∧ b ≤ a}
  have hSatom : ∀ b ∈ S, IsAtom b := by
    simp only [mem_setOf_eq, and_imp, S]
    tauto
  { parts := S
    indep := sSupIndep_atoms hSatom
    bot_notMem h := by simpa using (hSatom ⊥ h).1}

@[simp] lemma supp_discrete (a : α) : (Partition.discrete a).supp = a :=
  sSup_atoms_le_eq a

@[simp] lemma mem_discrete_iff {a b : α} : b ∈ Partition.discrete a ↔ IsAtom b ∧ b ≤ a := by rfl

-- lemma discrete_le_of_supp_eq (P : Partition α) : Partition.discrete P.supp ≤ P := by
--   sorry

end Discrete

section Bind

variable {α : Type*} [CompleteDistribLattice α] {s : α}

@[simps] protected def bind (P : Partition α) (Qs : ∀ a ∈ P, Partition α)
    (hQs : ∀ a, (h : a ∈ P) → (Qs a h).supp = a) : Partition α where
  parts := ⋃ a : P, (Qs a a.prop)
  indep := by
    intro b hb
    simp only [mem_iUnion, SetLike.mem_coe, Subtype.exists] at hb
    obtain ⟨a, haP, hba : b ∈ Qs a haP⟩ := hb
    obtain hasupp := hQs a haP
    have hdj1 := (Qs a haP).indep hba
    have hdj2 := (hasupp ▸ P.indep haP).mono_left <| (Qs a haP).le_of_mem hba
    refine (hdj1.sup_right hdj2).mono_right ?_
    simp only [mem_iUnion, SetLike.mem_coe, Subtype.exists, sSup_le_iff, mem_diff,
      mem_singleton_iff, and_imp, forall_exists_index]

    rintro t' x hx (ht' : t' ∈ Qs x hx) hne
    obtain hxsupp := hQs x hx
    obtain (rfl | hne) := eq_or_ne x a
    · exact (le_sSup_of_le (show t' ∈ _ \ {b} from ⟨ht', hne⟩) rfl.le).trans le_sup_left
    refine le_trans (le_sSup_of_le ?_ ((Qs x hx).le_of_mem ht')) le_sup_right
    simp [hasupp, hxsupp, hne, hx]
  bot_notMem := by
    simp only [mem_iUnion, SetLike.mem_coe, Subtype.exists, not_exists]
    exact fun x hx ↦ (Qs x hx).bot_notMem

@[simp] lemma mem_bind_iff {P : Partition α} {Qs : ∀ a ∈ P, Partition α}
    (hQs : ∀ a, (h : a ∈ P) → (Qs a h).supp = a) {a : α} :
    a ∈ P.bind Qs hQs ↔ ∃ (b : α) (hb : b ∈ P), a ∈ Qs b hb := by
  change _ ∈ ⋃ _, _ ↔ _; simp

@[simp] lemma bind_le {α : Type*} [CompleteDistribLattice α] (P : Partition α)
    (Qs : ∀ a ∈ P, Partition α) (hQs : ∀ a, (h : a ∈ P) → (Qs a h).supp = a) :
    P.bind Qs hQs ≤ P := by
  intro t ht
  obtain ⟨b, hbp, h⟩ := (mem_bind_iff hQs).1 ht
  exact ⟨b, hbp, (hQs b hbp) ▸ Partition.le_of_mem _ h⟩

end Bind

section Set

variable {s t u : Set α} {P : Partition (Set α)} {x : α}

@[simp] protected lemma sUnion_eq (P : Partition (Set α)) : ⋃₀ P = P.supp :=
  P.sSup_eq

lemma nonempty_of_mem (ht : t ∈ P) : t.Nonempty :=
  notMem_singleton_empty.1 <| P.ne_bot_of_mem ht

lemma subset_of_mem (ht : t ∈ P) : t ⊆ P.supp :=
  P.le_of_mem ht

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

lemma subset_sUnion_and_mem_iff_mem {S : Set (Set α)} (hSP : S ⊆ P.parts) :
    t ⊆ ⋃₀ S ∧ t ∈ P ↔ t ∈ S := by
  refine ⟨fun ⟨htsu, htP⟩ ↦ ?_, fun htS ↦ ⟨subset_sUnion_of_mem htS, hSP htS⟩⟩
  obtain ⟨x, hxt⟩ := nonempty_of_mem htP
  obtain ⟨s, hsS, hxs⟩ := htsu hxt
  obtain rfl := eq_of_mem_of_mem htP (hSP hsS) hxt hxs
  exact hsS

@[simp]
lemma subset_sUnion_iff_mem {S : Set (Set α)} (ht : t ∈ P) (hSP : S ⊆ P.parts) :
    t ⊆ ⋃₀ S ↔ t ∈ S := by
  rw [← subset_sUnion_and_mem_iff_mem hSP]
  simp [ht]

end Set

section Rel

variable {S T : Set α} {a b : α} {P : Partition (Set α)}

-- lemma eqv_class_comm {r : α → α → Prop} [IsSymm α r] (x : α) : {y | r x y} = {y | r y x} := by
--   simp_rw [comm]

-- lemma rel_iff_eqv_class_eq_right (hy : r y y) : r x y ↔ {z | r x z} = {z | r y z} := by
--   simp_rw [Set.ext_iff, mem_setOf]
--   exact ⟨fun hxy z ↦ ⟨fun hxz ↦ trans_of r (symm_of r hxy) hxz,
--     fun hyz ↦ trans_of r hxy hyz⟩, fun h ↦ by rwa [h]⟩

-- lemma rel_iff_eqv_class_eq_left (hx : r x x) : r x y ↔ {z | r x z} = {z | r y z} := by
--   rw [comm_of r, rel_iff_eqv_class_eq_right hx, eq_comm]

-- lemma eqv_class_mem_ofRel (h : r x x) : {y | r x y} ∈ ofRel r :=
--   ⟨x, h, rfl⟩

-- @[simp] lemma mem_ofRel_iff {t : Set α} :
--     t ∈ ofRel r ↔ ∃ x, r x x ∧ t = {y | r x y} := by
--   simp_rw [eq_comm (a := t)]; rfl

-- @[simp] lemma mem_ofRel'_iff {t : Set α} (hs : s = {x | r x x}):
--     t ∈ ofRel' r hs ↔ ∃ x ∈ s, t = {y | r x y} := by
--   subst hs
--   simp [ofRel', mem_congr_iff, mem_ofRel_iff]

-- lemma class_nonempty {t : Set α} (ht : t ∈ ofRel r) : t.Nonempty :=
--   nonempty_of_mem_fibers ht

/-- Every partition of `s : Set α` induces a transitive, symmetric Binary relation on `α`
  whose equivalence classes are the parts of `P`. The relation is irreflexive outside `s`.  -/
def Rel (P : Partition (Set α)) (a b : α) : Prop :=
  ∃ t ∈ P, a ∈ t ∧ b ∈ t

lemma Rel.exists (h : P.Rel x y) : ∃ t ∈ P, x ∈ t ∧ y ∈ t :=
  h

lemma Rel.forall (h : P.Rel x y) (ht : T ∈ P) : x ∈ T ↔ y ∈ T := by
  obtain ⟨t, ht', hx, hy⟩ := h
  exact ⟨fun h ↦ by rwa [P.eq_of_mem_of_mem ht ht' h hx],
    fun h ↦ by rwa [P.eq_of_mem_of_mem ht ht' h hy]⟩

lemma rel_of_mem_of_mem (ht : T ∈ P) (ha : a ∈ T) (hb : b ∈ T) : P.Rel a b :=
  ⟨T, ht, ha, hb⟩

lemma rel_self_of_mem (ht : T ∈ P) (hx : x ∈ T) : P.Rel x x :=
  rel_of_mem_of_mem ht hx hx

lemma rel_self_of_mem_supp (hx : x ∈ P.supp) : P.Rel x x := by
  obtain ⟨t, ht, hxt⟩ := mem_supp_iff.mp hx
  exact rel_self_of_mem ht hxt

lemma rel_symmectric (P : Partition (Set α)) : Symmetric (P.Rel) :=
  fun _ _ ⟨t, ht, ha, hb⟩ ↦ ⟨t, ht, hb, ha⟩

instance (P : Partition (Set α)) : IsSymm α P.Rel where
  symm := P.rel_symmectric

lemma rel_transitive (P : Partition (Set α)) : Transitive (P.Rel) := by
  intro _ _ _ ⟨t, ht, ha, hb⟩ ⟨t', ht', hb', hc⟩
  exact ⟨t, ht, ha, by rwa [eq_of_mem_of_mem ht ht' hb hb']⟩

instance (P : Partition (Set α)) : IsTrans α P.Rel where
  trans := P.rel_transitive

lemma Rel.symm {P : Partition (Set α)} (h : P.Rel x y) : P.Rel y x :=
  symm_of P.Rel h

lemma rel_comm {P : Partition (Set α)} : P.Rel x y ↔ P.Rel y x :=
  ⟨Rel.symm, Rel.symm⟩

lemma Rel.trans {P : Partition (Set α)} (hxy : P.Rel x y) (hyz : P.Rel y z) : P.Rel x z :=
  trans_of P.Rel hxy hyz

lemma Rel.mem_left {P : Partition (Set α)} (h : P.Rel x y) : x ∈ P.supp := by
  obtain ⟨t, htP, hxt, -⟩ := h
  exact subset_of_mem htP hxt

lemma Rel.mem_right {P : Partition (Set α)} (h : P.Rel x y) : y ∈ P.supp :=
  h.symm.mem_left

lemma rel_iff_exists : P.Rel x y ↔ ∃ t ∈ P, x ∈ t ∧ y ∈ t := Iff.rfl

@[simp]
lemma domain_rel {P : Partition (Set α)} : domain P.Rel = P.supp := by
  ext x
  simp only [mem_domain_iff, Rel, mem_supp_iff]
  exact ⟨fun ⟨y, S, hS, hxS, _⟩ => ⟨S, hS, hxS⟩, fun ⟨S, hS, hxS⟩ => ⟨x, S, hS, hxS, hxS⟩⟩

@[simp]
lemma codomain_rel {P : Partition (Set α)} : codomain P.Rel = P.supp := by
  rw [← domain_eq_codomain, domain_rel]

lemma le_of_rel_le {P Q : Partition (Set α)} (h : P.Rel ≤ Q.Rel) : P ≤ Q := by
  intro S hS
  obtain ⟨x, hxS⟩ := nonempty_of_mem hS
  obtain ⟨T, hT, hxT, -⟩ := h x x (rel_self_of_mem hS hxS)
  use T, hT
  rintro a haS
  obtain ⟨T', hT', haT', hxT'⟩ := h a x ⟨S, hS, haS, hxS⟩
  obtain rfl := eq_of_mem_of_mem hT hT' hxT hxT'
  exact haT'

lemma rel_le_of_le {P Q : Partition (Set α)} (h : P ≤ Q) : P.Rel ≤ Q.Rel := by
  intro x y ⟨S, hS, hxS, hyS⟩
  obtain ⟨T, hT, hST⟩ := h S hS
  exact ⟨T, hT, hST hxS, hST hyS⟩

lemma rel_le_iff_le {P Q : Partition (Set α)} : P.Rel ≤ Q.Rel ↔ P ≤ Q :=
  ⟨le_of_rel_le, rel_le_of_le⟩

lemma rel_inj {P Q : Partition (Set α)} (h : P.Rel = Q.Rel) : P = Q :=
  le_antisymm (le_of_rel_le h.le) (le_of_rel_le h.ge)

lemma rel_inj_iff {P Q : Partition (Set α)} : P.Rel = Q.Rel ↔ P = Q :=
  ⟨fun h => rel_inj h, fun h => h ▸ rfl⟩

/-- A transitive, symmetric Binary relation `r` induces a partition of the set of elements on
  which it is reflexive. -/
@[simps] def ofRel (r : α → α → Prop) [IsTrans α r] [IsSymm α r] : Partition (Set α) where
  parts := fibers r
  indep := PairwiseDisjoint.sSupIndep fibers_pairwiseDisjoint
  bot_notMem := emptySet_notMem_fibers r

@[simp]
lemma ofRel_supp {r : α → α → Prop} [IsSymm α r] [IsTrans α r] : (ofRel r).supp = domain r :=
  sUnion_fibers r

lemma rel_ofRel_eq {r : α → α → Prop} [IsTrans α r] [IsSymm α r] : (ofRel r).Rel = r := by
  ext a b
  exact ⟨fun ⟨S, ⟨c, ⟨d, hdc⟩, heq⟩, haS, hbS⟩ => trans' (heq ▸ haS) (symm (heq ▸ hbS)),
    fun hab => ⟨fiber r b, fiber_mem_fibers hab, hab, refl_of_right hab⟩⟩

lemma ofRel_rel_eq (P : Partition (Set α)) : ofRel P.Rel = P := by
  apply rel_inj
  rw [rel_ofRel_eq]

lemma fibers_rel_eq : fibers P.Rel = P.parts := by
  rw [Set.ext_iff]
  exact (ofRel P.Rel).ext_iff.mp <| ofRel_rel_eq P

instance {S : Set (Partition (Set α))} : IsSymm α (sSup <| Partition.Rel '' S) where
  symm := sSup_symmtric (fun _ ⟨_, _, heq⟩ => heq ▸ inferInstance)

instance {S : Set (Partition (Set α))} : IsSymm α (sInf <| Partition.Rel '' S) where
  symm := sInf_symmtric (fun _ ⟨_, _, heq⟩ => heq ▸ inferInstance)

instance {S : Set (Partition (Set α))} : IsTrans α (sInf <| Partition.Rel '' S) where
  trans := sInf_transitive (fun _ ⟨_, _, heq⟩ => heq ▸ inferInstance)

instance : CompleteLattice (Partition (Set α)) where
  sup P Q := ofRel <| TransClosure (P.Rel ⊔ Q.Rel)
  le_sup_left P Q := by
    rw [← rel_le_iff_le, rel_ofRel_eq]
    exact le_trans le_sup_left (TransClosure.le_closure _)
  le_sup_right P Q := by
    rw [← rel_le_iff_le, rel_ofRel_eq]
    exact le_trans le_sup_right (TransClosure.le_closure _)
  sup_le r s t hrt hst := by
    rw [← rel_le_iff_le] at hrt hst
    rw [← rel_le_iff_le, rel_ofRel_eq]
    exact ClosureOperator.closure_min (sup_le hrt hst) t.rel_transitive
  inf P Q := ofRel <| P.Rel ⊓ Q.Rel
  inf_le_left P Q := by
    rw [← rel_le_iff_le, rel_ofRel_eq]
    exact inf_le_left
  inf_le_right P Q := by
    rw [← rel_le_iff_le, rel_ofRel_eq]
    exact inf_le_right
  le_inf P Q R hPQR hPQR' := by
    rw [← rel_le_iff_le] at hPQR hPQR'
    rw [← rel_le_iff_le, rel_ofRel_eq]
    exact le_inf hPQR hPQR'
  sSup s := ofRel (TransClosure (sSup <| Partition.Rel '' s))
  le_sSup S P hPS := by
    rw [← rel_le_iff_le, rel_ofRel_eq]
    exact le_trans (le_sSup <| mem_image_of_mem Partition.Rel hPS) (TransClosure.le_closure _)
  sSup_le S r hrS := by
    rw [← rel_le_iff_le, rel_ofRel_eq]
    refine TransClosure.closure_min (sSup_le ?_) r.rel_transitive
    rintro s ⟨s', hs', rfl⟩
    exact rel_le_iff_le.mpr (hrS s' hs')
  sInf S := ofRel (sInf <| Partition.Rel '' S)
  le_sInf S r hrS := by
    rw [← rel_le_iff_le, rel_ofRel_eq]
    refine le_sInf <| ?_
    rintro s ⟨s', hs', rfl⟩
    exact rel_le_iff_le.mpr <| hrS s' hs'
  sInf_le S r hrS := by
    rw [← rel_le_iff_le, rel_ofRel_eq]
    exact sInf_le <| mem_image_of_mem Partition.Rel hrS
  le_top r := by simp
  bot_le r := by simp

end Rel

section point

variable {S T : Set α} {a b : α} {P : Partition (Set α)}

/-- The part containing a given element of the set being partitioned. If `x ∉ s`, then `∅`.  -/
def partOf (P : Partition (Set α)) (x : α) : Set α :=
  fiber P.Rel x

lemma exists_partOf_iff_mem : S ∈ P ↔ ∃ x ∈ P.supp, partOf P x = S := by
  rw [← SetLike.mem_coe, ← mem_parts, ← fibers_rel_eq, mem_fibers_iff, codomain_rel]
  rfl

lemma partOf_mem (hx : x ∈ P.supp) : P.partOf x ∈ P := by
  rw [exists_partOf_iff_mem]
  use x

lemma partOf_eq_empty (P : Partition (Set α)) (hx : x ∉ P.supp) : P.partOf x = ∅ :=
  fiber_empty.mpr (by simpa)

lemma mem_partOf (hx : x ∈ P.supp) : x ∈ P.partOf x :=
  (mem_fiber_iff _).mpr <| rel_self_of_mem_supp hx

lemma eq_partOf_of_mem (ht : T ∈ P) (hxt : x ∈ T) : T = P.partOf x := by
  obtain ⟨y, hy, rfl⟩ := exists_partOf_iff_mem.mp ht
  exact fiber_eq_of_mem (by exact hxt) <| rel_of_mem_of_mem ht hxt hxt

/-- Noncomputably choose a representative from an equivalence class-/
noncomputable def rep (P : Partition (Set α)) (ht : T ∈ P) : α := (P.nonempty_of_mem ht).some

@[simp] lemma rep_mem (ht : T ∈ P) : P.rep ht ∈ T :=
  (P.nonempty_of_mem ht).some_mem

@[simp] lemma rep_mem' (ht : T ∈ P) : P.rep ht ∈ P.supp :=
  P.subset_of_mem ht <| rep_mem ht

@[simp] lemma partOf_rep (ht : T ∈ P) : P.partOf (P.rep ht) = T :=
  (eq_partOf_of_mem ht (P.rep_mem ht)).symm

lemma finite_of_finite (P : Partition (Set α)) (hs : P.supp.Finite) : (P : Set (Set α)).Finite :=
  hs.finite_subsets.subset fun _ ↦ subset_of_mem

lemma rel_iff_partOf_eq_partOf (P : Partition (Set α)) (hx : x ∈ P.supp) (hy : y ∈ P.supp) :
    P.Rel x y ↔ P.partOf x = P.partOf y := by
  refine ⟨fun ⟨t, htP, hxt, hyt⟩ ↦ ?_, fun h ↦ ⟨P.partOf x, P.partOf_mem hx, P.mem_partOf hx, ?_⟩⟩
  · rw [eq_partOf_of_mem (P.partOf_mem hx)]
    rwa [← eq_partOf_of_mem htP hxt]
  rw [h]
  exact mem_partOf hy

lemma rel_iff_partOf_eq_partOf' (P : Partition (Set α)) :
    P.Rel x y ↔ ∃ (_ : x ∈ P.supp) (_ : y ∈ P.supp), P.partOf x = P.partOf y :=
  ⟨fun h ↦ ⟨h.mem_left, h.mem_right, (P.rel_iff_partOf_eq_partOf h.mem_left h.mem_right).1 h⟩,
    fun ⟨hx,hy,h⟩ ↦ (P.rel_iff_partOf_eq_partOf hx hy).2 h⟩

lemma rel_iff_forall {P : Partition (Set α)} : P.Rel x y ↔ x ∈ P.supp ∧ ∀ t ∈ P, x ∈ t ↔ y ∈ t := by
  refine ⟨fun h ↦ ⟨h.mem_left, fun _ ↦ h.forall⟩,
    fun ⟨hxs, h⟩ ↦ ⟨P.partOf x, P.partOf_mem hxs, P.mem_partOf hxs, ?_⟩⟩
  rw [← h _ (P.partOf_mem hxs)]
  exact P.mem_partOf hxs

lemma setOf_rel_self_eq (P : Partition (Set α)) : {x | P.Rel x x} = P.supp := by
  refine subset_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · obtain ⟨t, ht, hxP, -⟩ := hx
    exact subset_of_mem ht hxP
  obtain ⟨t, ⟨ht, hxt⟩, -⟩ := P.exists_unique_of_mem_supp hx
  exact ⟨t, ht, hxt, hxt⟩

lemma rel_self_iff_mem {P : Partition (Set α)} : P.Rel x x ↔ x ∈ P.supp := by
  simp [← P.setOf_rel_self_eq]

lemma setOf_rel_eq (ht : T ∈ P) (hx : x ∈ T) : {y | P.Rel x y} = T :=
  Set.ext fun y ↦ ⟨fun ⟨t', ht', hx', hy'⟩ ↦ by rwa [P.eq_of_mem_of_mem ht ht' hx hx'],
    fun h ↦ ⟨T, ht, hx, h⟩⟩

lemma rep_rel (ht : T ∈ P) (hx : x ∈ T) : P.Rel x (P.rep ht) :=
  ⟨T, ht, hx, P.rep_mem ht⟩

@[simp] lemma rep_rel_self {P : Partition (Set α)} (ht : T ∈ P) : P.Rel (P.rep ht) (P.rep ht) :=
  rep_rel _ (P.rep_mem ht)

lemma setOf_rel_rep_eq (ht : T ∈ P) : {x | P.Rel (P.rep ht) x} = T :=
  setOf_rel_eq ht (P.rep_mem ht)

/-- The `partOf x` is the set of `y` related to `x`. True even if `x ∉ s`, since both are `∅`.-/
lemma setOf_rel_eq_partOf (P : Partition (Set α)) (x : α) : {y | P.Rel x y} = P.partOf x := by
  by_cases hx : x ∈ P.supp
  · rw [setOf_rel_eq (P.partOf_mem hx) (P.mem_partOf hx)]
  rw [partOf_eq_empty _ hx, eq_empty_iff_forall_notMem]
  exact fun y hxy ↦ hx <| Rel.mem_left hxy

lemma setOf_rel_mem (P : Partition (Set α)) (hx : x ∈ P.supp) : {y | P.Rel x y} ∈ P := by
  obtain ⟨t, ⟨ht,hp⟩, -⟩ := P.exists_unique_of_mem_supp hx
  rwa [setOf_rel_eq ht hp]

@[ext] theorem eq_of_rel_iff_rel {P P' : Partition (Set α)} (h : ∀ x y, P.Rel x y ↔ P'.Rel x y) :
    P = P' := by
  rw [← ofRel_rel_eq P, ← ofRel_rel_eq P']; congr; ext; exact h _ _

@[simp] lemma discrete.rel_iff_eq : (Partition.discrete S).Rel a b ↔ a = b ∧ a ∈ S := by
  simp only [Partition.discrete, isAtom_iff, le_eq_subset]
  refine ⟨fun ⟨_, ⟨⟨x, rfl⟩, hxs⟩, hax, hbx⟩ ↦ by simp_all, ?_⟩
  rintro ⟨rfl, has⟩
  rw [rel_self_iff_mem]
  exact ⟨{a}, ⟨⟨a, rfl⟩, singleton_subset_iff.mpr has⟩, rfl⟩

lemma discrete.rel_iff_eq_of_mem (ha : a ∈ P.supp) :
    (Partition.discrete P.supp).Rel a b ↔ a = b := by
  rw [discrete.rel_iff_eq, and_iff_left ha]

end point

section RepFun

variable {a b : α} {s : Set α} {P : Partition (Set α)}

structure RepFun (P : Partition (Set α)) where
  (toFun : α → α)
  (apply_eq_self_of_notMem : ∀ a ∉ P.supp, toFun a = a)
  (rel_apply_of_mem : ∀ a ∈ P.supp, P.Rel a (toFun a))
  (apply_eq_of_rel : ∀ a b, P.Rel a b → toFun a = toFun b)

instance : FunLike (RepFun P) α α where
  coe := RepFun.toFun
  coe_injective' f f' := by cases f; cases f'; simp

def RepFun.mk' (P : Partition (Set α)) (f : α → α) {p : α → Prop} (hP : ∀ {x}, x ∈ P.supp ↔ p x)
    (h₁ : ∀ a, ¬ p a → f a = a) (h₂ : ∀ a, p a → P.Rel a (f a))
    (h₃ : ∀ a b, P.Rel a b → f a = f b) : P.RepFun :=
  ⟨f, fun a ha ↦ h₁ a (hP.not.mp ha), fun a ha ↦ h₂ a (hP.mp ha), h₃⟩

@[simp] lemma RepFun.mk_apply (P : Partition (Set α)) (f) (h₁ : ∀ a ∉ P.supp, f a = a)
  (h₂ : ∀ a ∈ P.supp, P.Rel a (f a)) (h₃) (x : α) : (RepFun.mk f h₁ h₂ h₃) x = f x := rfl

lemma RepFun.apply_of_notMem (f : P.RepFun) (ha : a ∉ P.supp) : f a = a :=
  f.apply_eq_self_of_notMem a ha

lemma RepFun.rel_apply (f : P.RepFun) (ha : a ∈ P.supp) : P.Rel a (f a) :=
  f.rel_apply_of_mem a ha

lemma RepFun.rel_apply' (f : P.RepFun) {p : α → Prop} (hP : ∀ {x}, x ∈ P.supp ↔ p x) (ha : p a) :
    P.Rel a (f a) := f.rel_apply <| hP.mpr ha

lemma RepFun.apply_mem (f : P.RepFun) (ha : a ∈ P.supp) : f a ∈ P.supp :=
  (f.rel_apply ha).mem_right

lemma RepFun.apply_mem' (f : P.RepFun) {p : α → Prop} (hP : ∀ {x}, x ∈ P.supp ↔ p x) (ha : p a) :
    p (f a) := hP.mp <| f.apply_mem <| hP.mpr ha

lemma RepFun.apply_eq_apply (f : P.RepFun) (hab : P.Rel a b) : f a = f b :=
  f.apply_eq_of_rel a b hab

lemma RepFun.rel_of_apply_eq_apply (f : P.RepFun) (ha : a ∈ P.supp) (hab : f a = f b) :
    P.Rel a b := by
  refine (f.rel_apply ha).trans ?_
  rw [hab, P.rel_comm]
  refine f.rel_apply <| by_contra fun hb ↦ ?_
  rw [f.apply_of_notMem hb] at hab; rw [← hab] at hb
  exact hb <| f.apply_mem ha

lemma RepFun.rel_of_ne_of_apply_eq_apply (f : P.RepFun) (hne : a ≠ b) (hab : f a = f b) :
    P.Rel a b := by
  obtain (ha | ha) := em (a ∈ P.supp); exact f.rel_of_apply_eq_apply ha hab
  obtain (hb | hb) := em (b ∈ P.supp); exact (f.rel_of_apply_eq_apply hb hab.symm).symm
  rw [f.apply_of_notMem ha, f.apply_of_notMem hb] at hab; contradiction

lemma RepFun.apply_eq_apply_iff_rel (f : P.RepFun) (ha : a ∈ P.supp) : f a = f b ↔ P.Rel a b :=
  ⟨f.rel_of_apply_eq_apply ha, f.apply_eq_apply⟩

lemma RepFun.apply_eq_apply_iff_rel_of_ne (f : P.RepFun) (hne : a ≠ b) : f a = f b ↔ P.Rel a b :=
  ⟨f.rel_of_ne_of_apply_eq_apply hne, f.apply_eq_apply⟩

@[simp] lemma RepFun.idem (f : P.RepFun) (a : α) : f (f a) = f a := by
  obtain (ha | ha) := em (a ∈ P.supp)
  · rw [eq_comm, f.apply_eq_apply_iff_rel ha]
    exact f.rel_apply ha
  simp_rw [f.apply_of_notMem ha]

lemma RepFun.image_subset_self (f : P.RepFun) : f '' P.supp ⊆ P.supp := by
  rintro _ ⟨a,ha,rfl⟩; exact f.apply_mem ha

/-- Any partially defined `RepFun` extends to a complete one. -/
lemma exists_extend_partial_repFun (P : Partition (Set α)) {t : Set α} (f₀ : t → α)
    (h_notMem : ∀ x : t, x.1 ∉ P.supp → f₀ x = x) (h_mem : ∀ x : t, x.1 ∈ P.supp → P.Rel x (f₀ x))
    (h_eq : ∀ x y : t, P.Rel x y → f₀ x = f₀ y) : ∃ (f : P.RepFun), ∀ x : t, f x = f₀ x := by
  classical
  set f : α → α := fun a ↦ if ha : a ∈ P.supp then
    (if hb : ∃ b : t, P.Rel a b then f₀ hb.choose else P.rep (P.partOf_mem ha)) else a with hf
  refine ⟨RepFun.mk f (fun a ha ↦ by simp [hf, ha]) (fun a ha ↦ ?_) (fun a b hab ↦ ?_), fun a ↦ ?_⟩
  · simp only [hf, ha, ↓reduceDIte]
    split_ifs with h
    · exact h.choose_spec.trans <| h_mem h.choose h.choose_spec.mem_right
    push_neg at h
    exact P.rep_rel (P.partOf_mem ha) (P.mem_partOf ha)
  · simp_rw [hf, dif_pos hab.mem_left, dif_pos hab.mem_right]
    split_ifs with h₁ h₂ h₂
    · exact h_eq _ _ <| (hab.symm.trans h₁.choose_spec).symm.trans h₂.choose_spec
    · exact False.elim <| h₂ ⟨_, hab.symm.trans h₁.choose_spec⟩
    · exact False.elim <| h₁ ⟨_, hab.trans h₂.choose_spec⟩
    congr
    rwa [← rel_iff_partOf_eq_partOf _ hab.mem_left hab.mem_right]
  change f a = f₀ a
  obtain (ha | ha) := em (a.1 ∈ P.supp)
  · simp only [hf, ha, ↓reduceDIte]
    split_ifs with h
    · exact Eq.symm <| h_eq _ _ h.choose_spec
    exact False.elim <| h ⟨a, rel_self_iff_mem.2 ha⟩
  simp [hf, ha, h_notMem _ ha]

/-- For any set `t` containining no two distinct related elements, there is a `RepFun` equal to
the identity on `t`. -/
lemma exists_extend_partial_repFun' (P : Partition (Set α)) {t : Set α}
    (h : ∀ ⦃x y⦄, x ∈ t → y ∈ t → P.Rel x y → x = y) : ∃ (f : P.RepFun), EqOn f id t := by
  simpa using P.exists_extend_partial_repFun (fun x : t ↦ x) (by simp)
    (by simp [P.rel_self_iff_mem]) (fun x y ↦ h x.2 y.2)

lemma nonempty_repFun (P : Partition (Set α)) : Nonempty P.RepFun := by
  obtain ⟨f, -⟩ := P.exists_extend_partial_repFun' (t := ∅) (by simp)
  exact ⟨f⟩

@[simp] theorem repFun_repFun (f f' : P.RepFun) (x : α) : f (f' x) = f x := by
  obtain (hx | hx) := em (x ∈ P.supp)
  · exact f.apply_eq_apply (f'.rel_apply hx).symm
  rw [f'.apply_of_notMem hx, f.apply_of_notMem hx]

@[simp] lemma repFun_discrete_coeFun (s : Set α) (f : (Partition.discrete s).RepFun) :
    (f : α → α) = id := by
  ext x
  obtain (hx | hx) := em (x ∈ s)
  · have hx' := f.rel_apply (supp_discrete s ▸ hx)
    rw [discrete.rel_iff_eq] at hx'
    exact hx'.1.symm
  rw [f.apply_of_notMem (supp_discrete s |>.symm ▸ hx), id]

lemma RepFun.coeFun_eq_id_of_eq_discrete  (f : P.RepFun) (hP : P = Partition.discrete s) :
    (f : α → α) = id := by
  subst hP; exact repFun_discrete_coeFun s f


-- lemma RepFun.image_eq_of_forall_rel_imp_eq (h : ∀ ⦃x y⦄, x ∈ s → y ∈ s → P.Rel x y → x = y)







-- /-- If `a ∈ s`, noncomputably choose an element in the same cell of `P` as some `a : α`.
-- If `a ∉ s`, is equal to `a`. -/
-- noncomputable def rep' (P : Partition (Set α)) (a : α) : α :=
--     if h : a ∈ s then P.rep (P.partOf_mem h) else a

-- lemma rep'_eq_rep (P : Partition (Set α)) (ha : a ∈ s) : P.rep' a = P.rep (P.partOf_mem ha) := by
--   rw [rep', dif_pos ha]

-- lemma rel_rep' (P : Partition (Set α)) (ha : a ∈ s) : P.Rel a (P.rep' a) := by
--   rw [P.rep'_eq_rep ha]
--   exact P.rep_rel (P.partOf_mem ha) (P.mem_partOf ha)

-- lemma rep'_eq_self_of_notMem (P : Partition (Set α)) (ha : a ∉ s) : P.rep' a = a := by
--   rw [rep', dif_neg ha]

-- lemma rel_iff_rep'_eq_rep' (ha : a ∈ s) (hb : b ∈ s) : P.Rel a b ↔ P.rep' a = P.rep' b := by
--   refine ⟨fun h ↦ ?_, fun h ↦ (P.rel_rep' ha).trans (h.symm ▸ P.rel_rep' hb).symm ⟩
--   rw [P.rel_iff_partOf_eq_partOf ha hb] at h
--   rw [P.rep'_eq_rep ha, P.rep'_eq_rep hb]
--   congr




end RepFun


-- def Fiber (f : α → β) : Partition (univ : Set α) := Partition.ofRel' (Eq on f) <| by ext a; simp


-- lemma Fiber.mem_of_mem (h : x ∈ s) : x ∈ P.Fiber x := by
--   exact P.mem_partOf h

-- end Fiber
