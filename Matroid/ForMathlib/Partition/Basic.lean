import Mathlib.Order.CompactlyGenerated.Basic
import Mathlib.Tactic.ApplyFun
import Matroid.ForMathlib.Relation
import Matroid.ForMathlib.Function -- for Function.onFun_comp

open Set Function

variable {α β ι ι' : Type*} {r : α → α → Prop} {f : ι → α} {g : ι' → ι} {s t x y z : α}

lemma sSupIndep.image {α : Type*} [CompleteLattice α] {S : Set α} (hS : sSupIndep S) {f : α → α}
    (hf : ∀ i, f i ≤ i) : sSupIndep (f '' S) := by
  rintro t ⟨x, hxS, rfl⟩
  refine hS hxS |>.mono (hf x) ?_
  simp only [sSup_le_iff, mem_diff, mem_image, mem_singleton_iff, and_imp, forall_exists_index,
    forall_apply_eq_imp_iff₂]
  refine fun y hyS hne ↦ (hf y).trans <| le_sSup ?_
  simp only [mem_diff, hyS, mem_singleton_iff, true_and]
  rintro rfl
  simp at hne

lemma sSupIndep_subsingleton {α : Type*} [CompleteLattice α] {S : Set α} (hs : S.Subsingleton) :
    sSupIndep S := by
  obtain (rfl | ⟨a, rfl⟩) := hs.eq_empty_or_singleton
  · exact sSupIndep_empty
  exact sSupIndep_singleton a

structure Partition (α : Type*) [CompleteLattice α] where
  parts : Set α
  indep : sSupIndep parts
  bot_not_mem : ⊥ ∉ parts

namespace Partition

section Basic

variable [CompleteLattice α] {P Q : Partition α}

def supp (P : Partition α) : α := sSup P.parts

instance : SetLike (Partition α) α where
  coe := Partition.parts
  coe_injective' p p' h := by cases p; cases p'; simpa using h

@[simp] lemma mem_parts : x ∈ P.parts ↔ x ∈ P := Iff.rfl

lemma coe_eq (P : Partition α) : ↑P = P.parts := rfl

lemma ext_parts (hP : P.parts = Q.parts) : P = Q := by
  cases P
  cases Q
  simpa

lemma ext_iff_parts : P = Q ↔ P.parts = Q.parts :=
  ⟨fun h ↦ by rw [h], fun h ↦ ext_parts h⟩

@[ext] lemma ext (hP : ∀ x, x ∈ P ↔ x ∈ Q) : P = Q := by
  refine ext_parts ?_
  ext x
  simpa using hP x

def subset (P Q : Partition α) : Prop := P.parts ⊆ Q.parts

instance : HasSubset (Partition α) where
  Subset := subset

instance : IsPartialOrder (Partition α) (· ⊆ ·) where
  refl _ _ := id
  trans _ _ _ hPQ hQR _ h := hQR (hPQ h)
  antisymm _ _ hPQ hPQ' := by ext S; exact ⟨(hPQ ·), (hPQ' ·)⟩

instance : HasSSubset (Partition α) where
  SSubset P Q := P.parts ⊂ Q.parts

instance : IsStrictOrder (Partition α) (· ⊂ ·) where
  irrefl _ := not_ssubset_of_subset (α := Set α) fun _ a ↦ a
  trans _ _ _ := ssubset_trans (α := Set α)

instance : IsNonstrictStrictOrder (Partition α) (· ⊆ ·) (· ⊂ ·) where
  right_iff_left_not_left _ _ := Iff.rfl

lemma disjoint (hx : x ∈ P) (hy : y ∈ P) (hxy : x ≠ y) : Disjoint x y :=
  P.indep.pairwiseDisjoint hx hy hxy

lemma eq_or_disjoint (hx : x ∈ P) (hy : y ∈ P) : x = y ∨ Disjoint x y :=
  or_iff_not_imp_left.mpr (P.disjoint hx hy)

lemma pairwiseDisjoint : Set.PairwiseDisjoint (P : Set α) id :=
  fun _ hx _ hy hxy ↦ P.disjoint hx hy hxy

lemma eq_of_not_disjoint (hx : x ∈ P) (hy : y ∈ P) (hxy : ¬ Disjoint x y) : x = y := by
  by_contra hne
  exact hxy (P.disjoint hx hy hne)

lemma ne_bot_of_mem (hx : x ∈ P) : x ≠ ⊥ :=
  fun h ↦ P.bot_not_mem <| h ▸ hx

lemma bot_lt_of_mem (hx : x ∈ P) : ⊥ < x :=
  bot_lt_iff_ne_bot.2 <| P.ne_bot_of_mem hx

lemma sSup_eq (P : Partition α) : sSup P = P.supp  := rfl

lemma iSup_eq (P : Partition α) : ⨆ x ∈ P, x = P.supp := by
  simp_rw [← P.sSup_eq, sSup_eq_iSup]
  rfl

lemma le_supp_of_mem (hx : x ∈ P) : x ≤ P.supp :=
  (le_sSup hx).trans_eq P.sSup_eq

lemma parts_nonempty (hs : P.supp ≠ ⊥) : (P : Set α).Nonempty :=
  nonempty_iff_ne_empty.2 fun hP ↦ by simp [← P.sSup_eq, hP, sSup_empty] at hs

lemma supp_le_of_subset (h : P ⊆ Q) : P.supp ≤ Q.supp := by
  simp only [supp, sSup_le_iff, mem_parts]
  exact fun a haP => le_sSup (h haP)

lemma eq_of_subset_of_supp_eq (hsu : P ⊆ Q) (hsupp : P.supp = Q.supp) : P = Q := by
  rw [ext_iff_parts]
  by_contra! hne
  obtain ⟨t, htQ, htP⟩ := exists_of_ssubset (ssubset_of_ne_of_subset hne hsu)
  have hmono : P.supp ≤ _ := sSup_le_sSup <| subset_diff_singleton hsu htP
  conv_lhs at hmono => rw [hsupp, supp, ← insert_diff_self_of_mem htQ, sSup_insert]
  simp only [sup_le_iff, le_refl, and_true] at hmono
  simpa [Q.ne_bot_of_mem htQ] using Q.indep htQ le_rfl hmono

lemma mem_of_subset_of_not_disjoint (hPQ : P ⊆ Q) (hxQ : x ∈ Q) (hndisj : ¬ Disjoint P.supp x) :
    x ∈ P := by
  contrapose! hndisj
  exact Q.indep hxQ |>.symm.mono_left (sSup_le_sSup <| subset_diff_singleton hPQ hndisj)

lemma mem_iff_mem_of_parts_eq {S : Set α} (hP : P.parts = S) : x ∈ P ↔ x ∈ S := by
  rw [← mem_parts, hP]

end Basic

section PairwiseDisjoint

variable {α : Type*} [Order.Frame α] {s t x y z : α} {parts : Set α} {P Q : Partition α}

@[simps] def ofPairwiseDisjoint (pairwiseDisjoint : parts.PairwiseDisjoint id) : Partition α where
  parts := parts \ {⊥}
  indep := sSupIndep_iff_pairwiseDisjoint.mpr (pairwiseDisjoint.subset diff_subset)
  bot_not_mem := by simp

@[simp] lemma mem_ofPairwiseDisjoint (pairwiseDisjoint : parts.PairwiseDisjoint id) :
    x ∈ ofPairwiseDisjoint pairwiseDisjoint ↔ x ∈ parts \ {⊥} := Iff.rfl

@[simp]
lemma supp_ofPairwiseDisjoint (pairwiseDisjoint : parts.PairwiseDisjoint id) :
    (ofPairwiseDisjoint pairwiseDisjoint).supp = sSup parts := by simp [supp]

@[simps] def ofPairwiseDisjoint' (pairwiseDisjoint : parts.PairwiseDisjoint id)
  (forall_nonempty : ∀ s ∈ parts, s ≠ ⊥) :
    Partition α where
  parts := parts
  indep := pairwiseDisjoint.sSupIndep
  bot_not_mem := fun h ↦ by simpa using forall_nonempty _ h

@[simp]
lemma supp_ofPairwiseDisjoint' (pairwiseDisjoint : parts.PairwiseDisjoint id)
    (forall_nonempty : ∀ s ∈ parts, s ≠ ⊥) :
  (ofPairwiseDisjoint' pairwiseDisjoint forall_nonempty).supp = sSup parts := rfl

@[simp] lemma mem_ofPairwiseDisjoint' (pairwiseDisjoint) (forall_nonempty) :
  x ∈ ofPairwiseDisjoint' (parts := parts) pairwiseDisjoint forall_nonempty ↔
    x ∈ parts := Iff.rfl

lemma mem_of_mem_subset (hPQ : P ⊆ Q) (hx : x ∈ Q) (hsupp : ¬ Disjoint P.supp x) : x ∈ P := by
  contrapose! hsupp
  rw [supp, sSup_disjoint_iff]
  exact fun _ hyP ↦ Q.disjoint (hPQ hyP) hx fun h ↦ hsupp (h ▸ hyP)

end PairwiseDisjoint

section indep

variable [CompleteLattice α] {u : Set α} {a b : α} {P Q : Partition α}

/-- A `sSupIndep` collection not containing `⊥` gives a partition of its supremum. -/
@[simps] def ofIndependent (hs : sSupIndep u) (hbot : ⊥ ∉ u) : Partition α where
  parts := u
  indep := hs
  bot_not_mem := hbot

@[simp] lemma mem_ofIndependent_iff (hu : sSupIndep u) (h : ⊥ ∉ u) :
  a ∈ ofIndependent hu h ↔ a ∈ u := Iff.rfl

@[simp] lemma supp_ofIndependent (hu : sSupIndep u) (hbot : ⊥ ∉ u) :
    (ofIndependent hu hbot).supp = sSup u := rfl

/-- A `sSupIndep` collection gives a partition of its supremum by removing `⊥`. -/
@[simps!]
def ofIndependent' (hs : sSupIndep u) : Partition α :=
  (ofIndependent (hs.mono (diff_subset (t := {⊥}))) (fun h ↦ h.2 rfl))

@[simp] lemma mem_ofIndependent'_iff (hu : sSupIndep u) :
  a ∈ ofIndependent' hu ↔ a ∈ u ∧ a ≠ ⊥ := Iff.rfl

@[simp] lemma supp_ofIndependent' (hu : sSupIndep u) : (ofIndependent' hu).supp = sSup u := by
  show sSup (u \ {⊥}) = sSup u
  simp

/-- The partition with no parts. -/
@[simps] protected def empty (α : Type*) [CompleteLattice α] : Partition α where
  parts := ∅
  indep := by simp
  bot_not_mem := by simp

instance : Bot (Partition α) where
  bot := Partition.empty α

@[simp] lemma parts_bot (α : Type*) [CompleteLattice α] : (⊥ : Partition α).parts = ∅ := rfl

@[simp] lemma notMem_bot : a ∉ (⊥ : Partition α) := notMem_empty α

@[simp]
lemma parts_eq_empty_iff (P : Partition α) : P.parts = ∅ ↔ P = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  ext x
  rw [← mem_parts, h]
  simp

@[simp] lemma supp_bot : (⊥ : Partition α).supp = ⊥ := sSup_empty

@[simp] lemma bot_coe_eq (α : Type*) [CompleteLattice α] :
    ((⊥ : Partition α) : Set α) = ∅ := rfl

lemma eq_bot (hP : P.supp = ⊥) : P = ⊥ := by
  ext x
  have hsup := P.sSup_eq
  simp only [sSup_eq_bot, SetLike.mem_coe, hP] at hsup
  simp only [notMem_bot, iff_false]
  exact fun hx ↦ P.ne_bot_of_mem hx <| hsup x hx

@[simp↓]
lemma supp_eq_bot_iff : P.supp = ⊥ ↔ P = ⊥ := by
  refine ⟨eq_bot, ?_⟩
  rintro rfl
  exact supp_bot

@[simp]
lemma bot_subset (P : Partition α) : ⊥ ⊆ P :=
  fun _ hsP => hsP.elim

@[simp]
lemma exists_mem_iff_ne_bot (P : Partition α) : (∃ x, x ∈ P) ↔ P ≠ ⊥ := by
  refine ⟨?_, fun hP ↦ ?_⟩
  · rintro ⟨x, hx⟩ rfl
    exact notMem_bot hx
  change P.parts.Nonempty
  rw [nonempty_iff_ne_empty]
  rwa [ne_eq, ← parts_eq_empty_iff] at hP

instance {α : Type*} [CompleteLattice α] [Subsingleton α] : Unique (Partition α) where
  default := ⊥
  uniq P := eq_bot (by
    simp only [← P.sSup_eq, sSup_eq_bot, SetLike.mem_coe]
    exact fun a b ↦ Subsingleton.elim _ _)

/-- The one-part partition. -/
@[simps] def indiscrete (s : α) (hs : s ≠ ⊥) : Partition α where
  parts := {s}
  indep := by simp [sSupIndep]
  bot_not_mem := by simpa using hs.symm

@[simp] lemma mem_indiscrete_iff (hs : s ≠ ⊥) :
    a ∈ Partition.indiscrete s hs ↔ a = s := Iff.rfl

@[simp]
lemma supp_indiscrete (hs : s ≠ ⊥) : (Partition.indiscrete s hs).supp = s := by
  simp [Partition.indiscrete, supp]

@[simp]
lemma indiscrete_subset_iff (hs : s ≠ ⊥) : Partition.indiscrete s hs ⊆ P ↔ s ∈ P := by
  change (indiscrete s hs).parts ⊆ P.parts ↔ s ∈ P.parts
  simp

lemma indiscrete_eq_iff (hs : s ≠ ⊥) : Partition.indiscrete s hs = P ↔ {s} = P.parts := by
  rw [ext_iff_parts, indiscrete_parts]

/-- Similar to `indiscrete`, but in the case `s = ⊥` it returns the empty partition. -/
@[simps]
def indiscrete' (s : α) : Partition α where
  parts := {T | s ≠ ⊥ ∧ T = s}
  indep := sSupIndep_subsingleton <| by
    rintro x ⟨hx, rfl⟩ y ⟨hy, rfl⟩
    rfl
  bot_not_mem := by simp [ne_comm]

@[simp]
lemma mem_indiscrete'_iff : x ∈ indiscrete' s ↔ s ≠ ⊥ ∧ x = s := Iff.rfl

@[simp]
lemma indiscrete'_eq_empty : indiscrete' ⊥ = (⊥ : Partition α) :=
  eq_bot <| by simp [-supp_eq_bot_iff, supp, indiscrete']

@[simp]
lemma supp_indiscrete' : (indiscrete' s).supp = s := by
  by_cases hs : s = ⊥
  · subst s
    simp
  simp [supp, indiscrete', hs]

@[simp]
lemma indiscrete'_eq_of_ne_bot (hs : s ≠ ⊥) : indiscrete' s = indiscrete s hs := by
  ext x
  simp [hs]

lemma eq_of_mem_indiscrete' (has : a ∈ indiscrete' s) : a = s :=
  has.2

lemma ne_bot_of_mem_indiscrete' (has : a ∈ indiscrete' s) : a ≠ ⊥ :=
  has.2 ▸ has.1

end indep

section IsPartition

variable {α : Type*} [CompleteLattice α] {S T : Set α} {x y z : α} {P : Partition α}

def IsPartition (S : Set α) : Prop := ∃ P : Partition α, P.parts = S

namespace IsPartition

@[simp]
lemma indep (hS : IsPartition S) : sSupIndep S := by
  obtain ⟨P, rfl⟩ := hS
  exact P.indep

@[simp]
lemma bot_not_mem (hS : IsPartition S) : ⊥ ∉ S := by
  obtain ⟨P, rfl⟩ := hS
  exact P.bot_not_mem

lemma disjoint (hS : IsPartition S) (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) : Disjoint x y := by
  obtain ⟨P, rfl⟩ := hS
  exact P.disjoint hx hy hxy

@[simp]
lemma eq_or_disjoint (hS : IsPartition S) (hx : x ∈ S) (hy : y ∈ S) : x = y ∨ Disjoint x y := by
  obtain ⟨P, rfl⟩ := hS
  exact P.eq_or_disjoint hx hy

@[simp]
lemma pairwiseDisjoint (hS : IsPartition S) : Set.PairwiseDisjoint S id := by
  obtain ⟨P, rfl⟩ := hS
  exact P.pairwiseDisjoint

lemma eq_of_not_disjoint (hS : IsPartition S) (hx : x ∈ S) (hy : y ∈ S) (hxy : ¬ Disjoint x y) :
    x = y := by
  obtain ⟨P, rfl⟩ := hS
  exact P.eq_of_not_disjoint hx hy hxy

@[simp]
lemma ne_bot_of_mem (hS : IsPartition S) (hx : x ∈ S) : x ≠ ⊥ := by
  obtain ⟨P, rfl⟩ := hS
  exact P.ne_bot_of_mem hx

lemma bot_lt_of_mem (hS : IsPartition S) (hx : x ∈ S) : ⊥ < x := by
  obtain ⟨P, rfl⟩ := hS
  exact P.bot_lt_of_mem hx

lemma iff_exists : IsPartition S ↔ ∃ P : Partition α, P.parts = S := Iff.rfl

end IsPartition

@[simp]
lemma exists_subset_iff_isPartition : (∃ P : Partition α, S ⊆ P.parts) ↔ IsPartition S := by
  refine ⟨fun ⟨P, hP⟩ ↦ ?_, ?_⟩
  · use ofIndependent' (P.indep.mono hP)
    simp only [ofIndependent'_parts, sdiff_eq_left, disjoint_singleton_right]
    exact fun h ↦ P.bot_not_mem (hP h)
  · rintro ⟨P, rfl⟩
    exact ⟨P, by simp⟩

lemma IsPartition.subset (hS : IsPartition T) (hST : S ⊆ T) : IsPartition S := by
  rw [← exists_subset_iff_isPartition] at hS ⊢
  obtain ⟨P, hP⟩ := hS
  exact ⟨P, hST.trans hP⟩

lemma parts_isPartition (P : Partition α) : IsPartition P.parts := ⟨P, rfl⟩

lemma isPartition_of_subset (hS : S ⊆ P.parts) : IsPartition S := by
  rw [← exists_subset_iff_isPartition]
  exact ⟨P, hS⟩

lemma isPartition_of (h1 : sSupIndep S) (h2 : ⊥ ∉ S) : IsPartition S := by
  use ofIndependent h1 h2
  rfl

lemma isPartition_iff : IsPartition S ↔ sSupIndep S ∧ ⊥ ∉ S := by
  refine ⟨fun h ↦ ?_, fun ⟨h1, h2⟩ ↦ isPartition_of h1 h2⟩
  obtain ⟨P, rfl⟩ := h
  exact ⟨P.indep, P.bot_not_mem⟩

@[simp]
lemma isPartition_singleton_iff : IsPartition {x} ↔ x ≠ ⊥ := by
  rw [isPartition_iff]
  simp [eq_comm, sSupIndep_singleton]

lemma isPartition_pair_of_disjoint (hx : x ≠ ⊥) (hy : y ≠ ⊥) (hxy : Disjoint x y) :
    IsPartition {x, y} := by
  rw [isPartition_iff]
  simpa [hx.symm, hy.symm, sSupIndep_pair (hxy.ne hx)]

lemma isPartition_pair_of_mem (hx : x ∈ P) (hy : y ∈ P) : IsPartition {x, y} :=
  isPartition_of_subset (P := P) (by simp [hx, hy, pair_subset])

@[simp]
lemma isPartition_pair_iff : IsPartition {x, y} ↔ (x = y ∨ Disjoint x y) ∧ x ≠ ⊥ ∧ y ≠ ⊥ := by
  by_cases hxy : x = y
  · subst x
    simp
  rw [isPartition_iff]
  simp [eq_comm, sSupIndep_pair, hxy]

end IsPartition

lemma isPartition_iff_pairwiseDisjoint {S : Set α} [Order.Frame α] :
    IsPartition S ↔ S.PairwiseDisjoint id ∧ ⊥ ∉ S := by
  rw [isPartition_iff, sSupIndep_iff_pairwiseDisjoint]

section Order

variable {α : Type*} [CompleteLattice α] {P Q R : Partition α} {s t a : α}

instance : PartialOrder (Partition α) where
  le P Q := ∀ x ∈ P, ∃ y ∈ Q, x ≤ y
  lt := _
  le_refl P x hx := ⟨x,hx,rfl.le⟩
  le_trans P Q R hPQ hQR x hxP := by
    obtain ⟨y, hy, hxy⟩ := hPQ x hxP
    obtain ⟨z, hz, hyz⟩ := hQR y hy
    exact ⟨z, hz, hxy.trans hyz⟩
  le_antisymm P Q hp hq := by
    refine Partition.ext fun x ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · obtain ⟨y, hy, hxy⟩ := hp x h
      obtain ⟨x', hx', hyx'⟩ := hq y hy
      obtain rfl := P.pairwiseDisjoint.eq_of_le h hx' (P.ne_bot_of_mem h)
        (hxy.trans hyx')
      rwa [hxy.antisymm hyx']
    obtain ⟨y, hy, hxy⟩ := hq x h
    obtain ⟨x', hx', hyx'⟩ := hp y hy
    obtain rfl := Q.pairwiseDisjoint.eq_of_le h hx' (Q.ne_bot_of_mem h)
      (hxy.trans hyx')
    rwa [hxy.antisymm hyx']

lemma le_def : P ≤ Q ↔ ∀ x ∈ P, ∃ y ∈ Q, x ≤ y := Iff.rfl

lemma exists_le_of_mem_le {x : α} {P Q : Partition α} (h : P ≤ Q) (hx : x ∈ P) :
    ∃ y ∈ Q, x ≤ y := h x hx

lemma exists_unique_of_mem_le {x : α} {P Q : Partition α} (h : P ≤ Q) (hx : x ∈ P) :
    ∃! y ∈ Q, x ≤ y := by
  obtain ⟨y, hy, hxy⟩ := h x hx
  refine ⟨y, ⟨hy, hxy⟩, fun z ⟨hz, hxz⟩ => Q.eq_of_not_disjoint hz hy ?_⟩
  have := P.ne_bot_of_mem hx
  contrapose! this
  exact le_bot_iff.mp (this hxz hxy)

lemma le_of_supp_le_part (ha : a ∈ P) (hQa : Q.supp ≤ a) : Q ≤ P :=
  fun _ hx ↦ ⟨a, ha, (Q.le_supp_of_mem hx).trans hQa⟩

instance : OrderTop (Partition α) where
  top := ofIndependent' (sSupIndep_singleton ⊤)
  le_top := by
    obtain (hs | hs) := eq_or_ne ⊤ (⊥ : α)
    · have : Subsingleton α := subsingleton_of_bot_eq_top hs.symm
      simp [hs]
    exact fun P x hx ↦ ⟨⊤, by simp [hs], by simp⟩

@[simp] lemma supp_top : (⊤ : Partition α).supp = ⊤ := by
  change (ofIndependent' (sSupIndep_singleton ⊤)).supp = ⊤
  simp

@[simp] lemma parts_top [Nontrivial α] : (⊤ : Partition α).parts = {⊤} := by
  change (ofIndependent' (sSupIndep_singleton ⊤)).parts = {⊤}
  rw [ofIndependent'_parts]
  simp

@[simp] lemma top_parts (hs : (⊤ : α) ≠ ⊥) : (⊤ : Partition α) = ({⊤} : Set α) := by
  change (ofIndependent' (sSupIndep_singleton ⊤)).parts = {⊤}
  simp [hs]

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
  bot_le _ _ hs := hs.elim

@[simp]
lemma bot_parts : (⊥ : Partition α).parts = ∅ := rfl

@[simp]
lemma bot_supp : (⊥ : Partition α).supp = ⊥ := by
  simp

lemma supp_le_of_le {P Q : Partition α} (h : P ≤ Q) : P.supp ≤ Q.supp :=
  sSup_le_sSup_of_isCofinalFor h

lemma le_of_subset {P Q : Partition α} (h : P ⊆ Q) : P ≤ Q :=
  fun x hx => ⟨x, h hx, le_rfl⟩

instance [Nontrivial α] : Nontrivial (Partition α) := by
  use ⊥, ⊤
  apply_fun (·.parts)
  simp only [parts_bot, parts_top, ne_eq]
  rw [← eq_comm]
  simp

end Order

section Atomic

variable {α : Type*} [CompleteLattice α] {P Q : Partition α}

def Atomic (P : Partition α) : Prop := ∀ x ∈ P, IsAtom x

lemma Atomic.subset_iff_le (hQ : Q.Atomic) : P ⊆ Q ↔ P ≤ Q := by
  refine ⟨le_of_subset, fun h x hxP ↦ ?_⟩
  obtain ⟨y, hy, hxy⟩ := h x hxP
  obtain rfl := hQ y hy |>.le_iff_eq (P.ne_bot_of_mem hxP) |>.mp hxy
  exact hy

lemma Atomic.atomic_of_subset (hPQ : P ⊆ Q) (hQ : Q.Atomic) : P.Atomic :=
  fun x hxP ↦ hQ x (hPQ hxP)

lemma Atomic.atomic_of_le (hPQ : P ≤ Q) (hQ : Q.Atomic) : P.Atomic :=
  hQ.atomic_of_subset <| hQ.subset_iff_le.mpr hPQ

@[simp]
lemma bot_atomic : (⊥ : Partition α).Atomic := by simp [Atomic]

lemma exists_atomic (s : α) [IsAtomistic α] [IsModularLattice α] [IsCompactlyGenerated α] :
    ∃ P : Partition α, P.Atomic ∧ P.supp = s := by
  obtain ⟨t, htindep, heq, hAtomic⟩ := exists_sSupIndep_of_sSup_atoms s (by
    simp_rw [and_comm]
    exact sSup_atoms_le_eq s)
  use ofIndependent' htindep
  simp [supp_ofIndependent', heq, Atomic]
  exact fun _ hx _ ↦ hAtomic hx

end Atomic
