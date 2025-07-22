import Mathlib.Data.Setoid.Partition
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Set.Finite.Powerset
import Mathlib.Order.CompactlyGenerated.Basic
import Matroid.ForMathlib.Lattice
import Matroid.ForMathlib.Relation
import Matroid.ForMathlib.Function -- for Function.onFun_comp
import Matroid.ForMathlib.Set

open Set Function Relation

section Pairwise

variable {α β ι ι' : Type*} {r : α → α → Prop} {f : ι → α} {x y : α}

lemma Pairwise.of_refl [IsRefl α r] (h : Pairwise (r on f)) (i j : ι) : r (f i) (f j) :=
  (eq_or_ne i j).elim (fun hij ↦ hij ▸ refl (f i)) fun hne ↦ h hne

lemma Pairwise.true_of_refl [IsRefl α r] (hr : Pairwise r) : r x y := by
  by_cases hf : x = y
  · exact hf ▸ refl x
  · exact hr hf

lemma true_pairwise : Pairwise (⊤ : α → α → _) := by tauto

lemma Pairwise.iff_top_of_refl [IsRefl α r] : Pairwise r ↔ r = ⊤ := by
  refine ⟨fun hr ↦ ?_, ?_⟩
  · ext x y
    simp [hr.true_of_refl]
  · rintro rfl
    exact fun ⦃i j⦄ a ↦ trivial

lemma Pairwise.iff_true_of_refl [IsRefl α r] : Pairwise r ↔ ∀ x y, r x y := by
  rw [iff_top_of_refl]
  aesop

lemma Pairwise.onFun_of_refl [IsRefl α r] (hr : Pairwise r) : Pairwise (r on f) := by
  rintro i j hne
  rw [Pairwise.iff_top_of_refl] at hr
  subst r
  trivial

lemma Set.Pairwise.range_of_injective (hf : Function.Injective f) :
    Pairwise (r on f) ↔ (range f).Pairwise r := by
  refine ⟨fun h ↦ ?_, fun h i j hne ↦ @h (f i) ⟨i, rfl⟩ (f j) ⟨j, rfl⟩ <| fun a ↦ hne (hf a)⟩
  rintro _ ⟨i, _, rfl⟩ _ ⟨j, _, rfl⟩ hne
  exact h fun a ↦ hne (congrArg f a)

lemma Pairwise.restrict {s : Set ι} : Pairwise (r on (f · : s → α)) ↔ s.Pairwise (r on f) :=
  ⟨fun h i his j hjs hne ↦ @h ⟨i, his⟩ ⟨j, hjs⟩ (by simpa),
  fun h i j hne ↦ h i.prop j.prop (by rwa [Subtype.coe_ne_coe])⟩

lemma Pairwise.sum_left {γ : Type*} {G : ι → γ} {H : ι' → γ} {r : γ → γ → Prop}
    (h : Pairwise (r on Sum.elim G H)) : Pairwise (r on G) := by
  rw [← Sum.elim_comp_inl G H, onFun_comp]
  exact h.comp_of_injective Sum.inl_injective

lemma Pairwise.sum_right {γ : Type*} {G : ι → γ} {H : ι' → γ} {r : γ → γ → Prop}
    (h : Pairwise (r on Sum.elim G H)) : Pairwise (r on H) := by
  rw [← Sum.elim_comp_inr G H, onFun_comp]
  exact h.comp_of_injective Sum.inr_injective

end Pairwise


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

lemma supp_le_of_subset (h : P ⊆ Q) : P.supp ≤ Q.supp := by
  simp only [supp, sSup_le_iff, mem_parts, SetLike.mem_coe]
  exact fun a haP => le_sSup (h haP)

end Basic

section PairwiseDisjoint

variable {α : Type*} [Order.Frame α] {s t x y z : α} {parts : Set α}

@[simps] def ofPairwiseDisjoint (pairwiseDisjoint : parts.PairwiseDisjoint id) : Partition α where
  parts := parts \ {⊥}
  indep := sSupIndep_iff_pairwiseDisjoint.mpr (pairwiseDisjoint.subset diff_subset)
  bot_notMem := by simp

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
  bot_notMem := fun h ↦ by simpa using forall_nonempty _ h

@[simp]
lemma supp_ofPairwiseDisjoint' (pairwiseDisjoint : parts.PairwiseDisjoint id)
    (forall_nonempty : ∀ s ∈ parts, s ≠ ⊥) :
  (ofPairwiseDisjoint' pairwiseDisjoint forall_nonempty).supp = sSup parts := rfl

@[simp] lemma mem_ofPairwiseDisjoint' (pairwiseDisjoint) (forall_nonempty) {x : α} :
  x ∈ ofPairwiseDisjoint' (parts := parts) pairwiseDisjoint forall_nonempty ↔
    x ∈ parts := Iff.rfl


lemma mem_of_mem_subset {P Q : Partition α} (hPQ : P ⊆ Q) (hx : x ∈ Q)
    (hsupp : ¬ Disjoint P.supp x) : x ∈ P := by
  contrapose! hsupp
  rw [supp, sSup_disjoint_iff]
  exact fun _ hyP ↦ Q.disjoint (hPQ hyP) hx fun h ↦ hsupp (h ▸ hyP)

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

/-- The partition with no parts. -/
@[simps] protected def empty (α : Type*) [CompleteLattice α] : Partition α where
  parts := ∅
  indep := by simp
  bot_notMem := by simp

instance : Bot (Partition α) where
  bot := Partition.empty α

@[simp] lemma notMem_bot {a : α} : a ∉ (⊥ : Partition α) := notMem_empty α

@[simp] lemma supp_bot : (⊥ : Partition α).supp = ⊥ := sSup_empty

@[simp] lemma bot_coe_eq (α : Type*) [CompleteLattice α] :
    ((⊥ : Partition α) : Set α) = ∅ := rfl

lemma eq_bot {P : Partition α} (hP : P.supp = ⊥) : P = ⊥ := by
  ext x
  have hsup := P.sSup_eq
  simp only [sSup_eq_bot, SetLike.mem_coe, hP] at hsup
  simp only [notMem_bot, iff_false]
  exact fun hx ↦ P.ne_bot_of_mem hx <| hsup x hx

@[simp]
lemma supp_eq_bot_iff {P : Partition α} : P.supp = ⊥ ↔ P = ⊥ := by
  refine ⟨eq_bot, ?_⟩
  rintro rfl
  exact supp_bot

instance {α : Type*} [CompleteLattice α] [Subsingleton α] : Unique (Partition α) where
  default := ⊥
  uniq P := eq_bot (by
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
  if hs : s = ⊥ then ⊥ else indiscrete s hs

@[simp]
lemma indiscrete'_eq_empty : indiscrete' ⊥ = (⊥ : Partition α) := by
  simp [indiscrete']

@[simp]
lemma indiscrete'_eq_of_ne_bot {s : α} (hs : s ≠ ⊥) : indiscrete' s = indiscrete s hs := by
  simp only [indiscrete', hs, ↓reduceDIte]

@[simp]
lemma supp_indiscrete' {s : α} : (indiscrete' s).supp = s := by
  simp [indiscrete']
  split_ifs with hs
  · rw [supp_bot, hs]
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
  le_refl P x hx := ⟨x,hx,rfl.le⟩
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
  bot_le a s hs := by simp only [notMem_bot] at hs

lemma supp_le_of_le {P Q : Partition α} (h : P ≤ Q) : P.supp ≤ Q.supp :=
  sSup_le_sSup_of_forall_exists_le h

lemma le_of_subset {P Q : Partition α} (h : P ⊆ Q) : P ≤ Q :=
  fun x hx => ⟨x, h hx, le_rfl⟩

end Order

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

section Restrict

variable {α : Type*} [CompleteLattice α] {s : Set α}

/-- The subpartition with over a subset of the parts. -/
@[simps]
def restrict (P : Partition α) (s : Set α) (hs : s ⊆ P.parts) : Partition α where
  parts := s
  indep := P.indep.mono hs
  bot_notMem h := P.bot_notMem (hs h)

@[simp] lemma mem_restrict_iff {P : Partition α} {s : Set α} (hs : s ⊆ P.parts) {a : α} :
    a ∈ P.restrict s hs ↔ a ∈ s := Iff.rfl

@[simp] lemma restrict_supp {P : Partition α} {s : Set α} (hs : s ⊆ P.parts) :
    (P.restrict s hs).supp = sSup s := by
  simp [restrict, supp]

lemma restrict_subset {P : Partition α} {s : Set α} (hs : s ⊆ P.parts) :
    (P.restrict s hs) ⊆ P := fun _ h ↦ hs h

lemma restrict_le {P : Partition α} {s : Set α} (hs : s ⊆ P.parts) :
    P.restrict s hs ≤ P := le_of_subset <|restrict_subset hs

lemma subset_iff_restrict {P Q : Partition α} :
    P ⊆ Q ↔ ∃ S, ∃ hS : S ⊆ Q.parts, Q.restrict S hS = P :=
  ⟨fun h ↦ ⟨P.parts, h, by ext; simp⟩, fun ⟨S, hS, heq⟩ ↦ heq ▸ restrict_subset hS⟩

@[simp]
lemma restrict_eq_self_iff {P : Partition α} {s : Set α} (hs : s ⊆ P.parts) :
    P.restrict s hs = P ↔ s = P.parts :=
  ⟨fun hP ↦ by rw [← hP]; simp, fun h ↦ h ▸ (by rfl)⟩

end Restrict

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

-- lemma exists_atomic (s : α) [IsAtomistic α] [IsModularLattice α] [IsCompactlyGenerated α] :
--     ∃ P : Partition α, P.Atomic ∧ P.supp = s := by
--   -- needs `lake update`
--   -- obtain ⟨t, htindep, heq, hAtomic⟩ := exists_sSupIndep_of_sSup_atoms s (sSup_atoms_le_eq s)
--   -- use ofIndependent' htindep, hAtomic, heq
--   sorry

end Atomic

section Set

variable {s t u : Set α} {S T : Set (Set α)} {P Q : Partition (Set α)} {x : α}

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

@[simps!]
def induce (P : Partition (Set α)) (S : Set α) : Partition (Set α) :=
  ofIndependent' (u := (S ∩ ·) '' P.parts) <|
  sSupIndep_iff_pairwiseDisjoint.mpr <| P.pairwiseDisjoint.image_of_le (fun _ _ ↦ by simp)

@[simp]
lemma induce_supp (P : Partition (Set α)) (S : Set α) : (induce P S).supp = S ∩ P.supp := by
  ext x
  simp [induce, mem_supp_iff]

@[simp]
lemma mem_induce_iff (P : Partition (Set α)) (S T : Set α) :
    T ∈ P.induce S ↔ T.Nonempty ∧ ∃ t ∈ P, S ∩ t = T := by
  simp [induce, and_comm, nonempty_iff_ne_empty]

@[simp]
lemma induce_empty (P : Partition (Set α)) : P.induce ∅ = ⊥ := by
  ext x
  simp only [mem_induce_iff, empty_inter, exists_and_right, notMem_bot, iff_false, not_and,
    forall_exists_index]
  rintro hx y hyP rfl
  simp at hx

lemma inter_mem_induce (hne : (s ∩ t).Nonempty) (ht : t ∈ P) :
    s ∩ t ∈ P.induce s := (P.mem_induce_iff s _).mpr ⟨hne, t, ht, rfl⟩

@[simp]
lemma induce_induce (P : Partition (Set α)) (S T : Set α) :
    induce (induce P S) T = induce P (S ∩ T) := by
  ext x
  simp +contextual only [induce, mem_ofIndependent'_iff, mem_image, mem_parts, SetLike.mem_coe,
    bot_eq_empty, ne_eq, iff_def, not_false_eq_true, and_true, and_imp, forall_exists_index,
    forall_apply_eq_imp_iff₂]
  constructor
  · rintro a haP - rfl -
    use a, haP, by ac_rfl
  rintro a haP rfl hSTa
  use (S ∩ a), ⟨⟨a, haP, rfl⟩, ?_⟩, by ac_rfl
  contrapose! hSTa
  ac_change T ∩ (S ∩ a) = _
  simp [hSTa]

@[simp]
lemma induce_eq_self_iff : P.induce s = P ↔ P.supp ⊆ s := by
  refine ⟨fun hP ↦ by rw [← hP]; simp, fun h ↦ ?_⟩
  ext x
  have : ∀ t ∈ P, s ∩ t = t := fun t htP ↦ inter_eq_right.mpr <| subset_trans (P.le_of_mem htP) h
  simp only [mem_induce_iff, nonempty_iff_ne_empty, ne_eq]
  exact ⟨fun ⟨hne, t, htP, heq⟩ ↦ (this t htP).symm.trans heq ▸ htP,
    fun hx ↦ ⟨P.ne_bot_of_mem hx, x, hx, this x hx⟩⟩

lemma induce_le : P.induce s ≤ P := by
  intro T hT
  obtain ⟨hne, t, htP, rfl⟩ := (by simpa only [mem_induce_iff, ne_eq] using hT); clear hT
  exact ⟨t, htP, inter_subset_right⟩

lemma induce_le_induce_iff : P.induce s ≤ P.induce t ↔ s ∩ P.supp ⊆ t ∩ P.supp := by
  refine ⟨fun h ↦ ?_, fun h T hT ↦ ?_⟩
  · rw [← induce_supp, ← induce_supp]
    exact supp_le_of_le h
  obtain ⟨hne, T, hTP, rfl⟩ := (by simpa only [mem_induce_iff, ne_eq] using hT); clear hT
  have hsu : s ∩ T ⊆ t ∩ T := fun x ⟨hxs, hxT⟩ => ⟨(h ⟨hxs, subset_of_mem hTP hxT⟩).1, hxT⟩
  use t ∩ T, ?_, hsu
  simp [hne.mono hsu]
  use T

lemma induce_mono (hST : s ⊆ t) : P.induce s ≤ P.induce t := by
  rw [induce_le_induce_iff]
  exact inter_subset_inter_left _ hST

lemma induce_eq_induce_iff : P.induce s = P.induce t ↔ s ∩ P.supp = t ∩ P.supp :=
  ⟨fun h ↦ by rw [← induce_supp, ← induce_supp, h],
    fun h ↦ (induce_le_induce_iff.mpr h.le).antisymm (induce_le_induce_iff.mpr h.ge)⟩

lemma induce_eq_of_subset (hPQ : P ⊆ Q) : Q.induce P.supp = P := by
  ext S
  rw [mem_induce_iff, nonempty_iff_ne_empty]
  refine ⟨?_, fun hS ↦ ⟨bot_eq_empty ▸ P.ne_bot_of_mem hS, S, hPQ hS,
    inter_eq_right.mpr <| P.le_of_mem hS⟩⟩
  rintro ⟨hne, t, htQ, rfl⟩
  rw [ne_eq, ← disjoint_iff_inter_eq_empty] at hne
  have htP := mem_of_mem_subset hPQ htQ hne
  rwa [inter_eq_right.mpr (subset_of_mem htP)]

lemma induce_mono_left {S : Set α} (hPQ : P ≤ Q) : P.induce S ≤ Q.induce S := by
  intro t ht
  obtain ⟨hne, t', ht'Q, rfl⟩ := (by simpa only [mem_induce_iff, ne_eq] using ht); clear ht
  obtain ⟨s, hsQ, ht's⟩ := hPQ t' ht'Q
  have hsu := inter_subset_inter_right S ht's
  use S ∩ s, inter_mem_induce (hne.mono hsu) hsQ, hsu

lemma le_induce_of_supp_le (hPQ : P ≤ Q) (hP : P.supp ⊆ s) :
    P ≤ Q.induce s := by
  rw [← induce_eq_self_iff.mpr hP]
  exact induce_mono_left hPQ

lemma induce_subset_induce_of_subset (hPQ : P ⊆ Q) : P.induce s ⊆ Q.induce s := by
  rintro t ⟨⟨t', ht'P, rfl⟩, hne⟩
  exact ⟨⟨t', hPQ ht'P, rfl⟩, hne⟩

lemma subset_induce_of_supp_le (hPQ : P ⊆ Q) (hP : P.supp ⊆ s) :
    P ⊆ Q.induce s := by
  rw [← induce_eq_self_iff.mpr hP]
  exact induce_subset_induce_of_subset hPQ

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

private lemma le_of_rel_le' {P Q : Partition (Set α)} (h : P.Rel ≤ Q.Rel) : P ≤ Q := by
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

instance (P : Partition (Set α)) : IsSymm α P where
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

lemma rel_self_iff_mem_supp : P x x ↔ x ∈ P.supp :=
  ⟨fun h ↦ h.left_mem, fun h ↦ rel_self_of_mem_supp h⟩

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

lemma rel_le_of_le {P Q : Partition (Set α)} (h : P ≤ Q) : ⇑P ≤ ⇑Q := by
  intro x y ⟨S, hS, hxS, hyS⟩
  obtain ⟨T, hT, hST⟩ := h S hS
  exact ⟨T, hT, hST hxS, hST hyS⟩

lemma le_of_rel_le {P Q : Partition (Set α)} (h : ⇑P ≤ ⇑Q) : P ≤ Q :=
  le_of_rel_le' h

lemma rel_le_iff_le {P Q : Partition (Set α)} : ⇑P ≤ ⇑Q ↔ P ≤ Q :=
  ⟨le_of_rel_le, rel_le_of_le⟩

lemma rel_inj {P Q : Partition (Set α)} (h : ⇑P = ⇑Q) : P = Q :=
  le_antisymm (le_of_rel_le h.le) (le_of_rel_le h.ge)

lemma rel_inj_iff {P Q : Partition (Set α)} : ⇑P = ⇑Q ↔ P = Q :=
  ⟨fun h => rel_inj h, fun h => h ▸ rfl⟩

lemma rel_le_of_subset {P Q : Partition (Set α)} (h : P ⊆ Q) : ⇑P ≤ ⇑Q :=
  rel_le_of_le <| le_of_subset h

/-- A transitive, symmetric Binary relation `r` induces a partition of the set of elements on
  which it is reflexive. -/
@[simps] def ofRel (r : α → α → Prop) [IsTrans α r] [IsSymm α r] : Partition (Set α) where
  parts := fibers r
  indep := PairwiseDisjoint.sSupIndep fibers_pairwiseDisjoint
  bot_notMem := emptySet_notMem_fibers r

@[simp]
lemma ofRel_supp {r : α → α → Prop} [IsSymm α r] [IsTrans α r] : (ofRel r).supp = domain r :=
  sUnion_fibers r

lemma rel_ofRel_eq {r : α → α → Prop} [IsTrans α r] [IsSymm α r] : ofRel r = r := by
  ext a b
  exact ⟨fun ⟨S, ⟨c, ⟨d, hdc⟩, heq⟩, haS, hbS⟩ => trans' (heq ▸ haS) (symm (heq ▸ hbS)),
    fun hab => ⟨fiber r b, fiber_mem_fibers hab, hab, refl_of_right hab⟩⟩

lemma ofRel_rel_eq (P : Partition (Set α)) : ofRel P = P := by
  apply rel_inj
  rw [rel_ofRel_eq]

lemma fibers_rel_eq : fibers P = P.parts := by
  rw [Set.ext_iff]
  exact (ofRel P).ext_iff.mp <| ofRel_rel_eq P

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

lemma rel_of_subset_mem {P Q : Partition (Set α)} (hPQ : P ⊆ Q) (hx : x ∈ P.supp) (hxy : Q x y) :
    P x y := by
  obtain ⟨S, hS, rfl⟩ := subset_iff_restrict.mp hPQ
  exact Q.rel_of_restrict_rel hPQ hx hxy

lemma subset_iff_rel {P Q : Partition (Set α)} : P ⊆ Q ↔ ∀ x y, x ∈ P.supp → (P x y ↔ Q x y) := by
  refine ⟨fun h x y hx => ⟨rel_le_of_subset h x y, rel_of_subset_mem h hx⟩, fun h s hs => ?_⟩
  rw [← fibers_rel_eq, mem_fibers_iff] at hs ⊢
  obtain ⟨x, hx, rfl⟩ := hs
  have hxsupp := codomain_rel ▸ hx
  have ⟨y, hyx⟩ := hx
  use x, ⟨y, symm <| (h x y hxsupp).mp hyx.symm⟩
  ext z
  simp [(rel_comm.trans <| h x z hxsupp).trans rel_comm]

lemma induce_rel (P : Partition (Set α)) {S : Set α} :
    ⇑(P.induce S) = fun x y ↦ x ∈ S ∧ y ∈ S ∧ P x y := by
  ext x y
  simp only [rel_iff_exists, mem_induce_iff]
  refine ⟨fun ⟨t, ⟨htne, t', ht'P, heq⟩, hxt, hyt⟩ ↦ ?_,
    fun ⟨hxS, hyS, t, htP, hxt, hyt⟩ ↦ ⟨S ∩ t, ⟨?_, t, htP, rfl⟩, ⟨hxS, hxt⟩, ⟨hyS, hyt⟩⟩⟩
  · subst t
    exact ⟨hxt.1, hyt.1, t', ht'P, hxt.2, hyt.2⟩
  use x, hxS

@[simp]
lemma induce_apply (P : Partition (Set α)) {S : Set α} :
    P.induce S x y ↔ x ∈ S ∧ y ∈ S ∧ P x y := by rw [induce_rel]

lemma induce_eq_iff_rel (P Q : Partition (Set α)) :
    P.induce Q.supp = Q ↔ (fun x y ↦ x ∈ Q.supp ∧ y ∈ Q.supp ∧ P x y) = ⇑Q := by
  rw [← rel_inj_iff, induce_rel]

instance {S : Set (Partition (Set α))} : IsSymm α (sSup <| (⇑) '' S) where
  symm := sSup_symmtric (fun _ ⟨_, _, heq⟩ => heq ▸ inferInstance)

instance {S : Set (Partition (Set α))} : IsSymm α (sInf <| (⇑) '' S) where
  symm := sInf_symmtric (fun _ ⟨_, _, heq⟩ => heq ▸ inferInstance)

instance {S : Set (Partition (Set α))} : IsTrans α (sInf <| (⇑) '' S) where
  trans := sInf_transitive (fun _ ⟨_, _, heq⟩ => heq ▸ inferInstance)

instance : CompleteLattice (Partition (Set α)) where
  sup P Q := ofRel <| TransClosure (P ⊔ Q)
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
  inf P Q := ofRel <| P ⊓ Q
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
  sSup s := ofRel (TransClosure (sSup <| (⇑) '' s))
  le_sSup S P hPS := by
    rw [← rel_le_iff_le, rel_ofRel_eq]
    exact le_trans (le_sSup <| mem_image_of_mem (⇑) hPS) (TransClosure.le_closure _)
  sSup_le S r hrS := by
    rw [← rel_le_iff_le, rel_ofRel_eq]
    refine TransClosure.closure_min (sSup_le ?_) r.rel_transitive
    rintro s ⟨s', hs', rfl⟩
    exact rel_le_iff_le.mpr (hrS s' hs')
  sInf S := ofRel (sInf <| (⇑) '' S)
  le_sInf S r hrS := by
    rw [← rel_le_iff_le, rel_ofRel_eq]
    refine le_sInf <| ?_
    rintro s ⟨s', hs', rfl⟩
    exact rel_le_iff_le.mpr <| hrS s' hs'
  sInf_le S r hrS := by
    rw [← rel_le_iff_le, rel_ofRel_eq]
    exact sInf_le <| mem_image_of_mem (⇑) hrS
  le_top r := by simp
  bot_le r := by simp

@[simp]
lemma sup_rel (P Q : Partition (Set α)) : ⇑(P ⊔ Q) = TransClosure (⇑P ⊔ ⇑Q) := by
  change ⇑(ofRel _) = _
  rw [rel_ofRel_eq]

@[simp]
lemma inf_rel (P Q : Partition (Set α)) : ⇑(P ⊓ Q) = ⇑P ⊓ ⇑Q := by
  change ⇑(ofRel _) = _
  rw [rel_ofRel_eq]

@[simp]
lemma sSup_rel (S : Set (Partition (Set α))) : ⇑(sSup S) = TransClosure (sSup <| (⇑) '' S) := by
  change ⇑(ofRel _) = _
  rw [rel_ofRel_eq]

@[simp]
lemma sInf_rel (S : Set (Partition (Set α))) : ⇑(sInf S) = sInf ((⇑) '' S) := by
  change ⇑(ofRel _) = _
  rw [rel_ofRel_eq]

@[simp]
lemma iSup_rel (ι : Type*) (G : ι → Partition (Set α)) :
    ⇑(⨆ i, G i) = TransClosure (⨆ i, ⇑(G i)) := by
  change ⇑(ofRel _) = _
  rw [rel_ofRel_eq, iSup, ← range_comp]
  rfl

@[simp]
lemma iInf_rel (ι : Type*) (G : ι → Partition (Set α)) :
    ⇑(⨅ i, G i) = ⨅ i, ⇑(G i) := by
  change ⇑(ofRel _) = _
  rw [rel_ofRel_eq, iInf, ← range_comp]
  rfl

end Rel

section Discrete

variable {α : Type*} {S T : Set α} {a b : α} {P : Partition (Set α)}

/-- The discrete partition -/
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
  bot_notMem := by
    rintro ⟨a, ha, heq⟩
    simp at heq

@[simp] lemma supp_discrete (S : Set α) : (Partition.discrete S).supp = S := by
  simp [Partition.discrete, supp]

@[simp] lemma mem_discrete_iff : T ∈ (Partition.discrete S) ↔ ∃ a ∈ S, {a} = T := by
  rw [← SetLike.mem_coe, ← mem_parts]
  simp [Partition.discrete]

lemma rel_discrete_eq' : Partition.discrete S = fun a b => a = b ∧ b ∈ S := by
  ext a b
  rw [and_comm]
  simp [Partition.discrete, rel_iff_exists, ← SetLike.mem_coe, ← mem_parts]

@[simp]
lemma rel_discrete_eq : Partition.discrete S = fun a b => a = b ∧ a ∈ S := by
  ext a b
  rw [rel_discrete_eq', and_congr_right_iff]
  rintro rfl
  rfl

@[simp]
lemma rel_discrete_iff : Partition.discrete S a b ↔ a = b ∧ a ∈ S := by
  rw [rel_discrete_eq]

lemma discrete_atomic (S : Set α) : (Partition.discrete S).Atomic := by
  rintro _ ⟨a, -, rfl⟩
  exact isAtom_singleton a

lemma atomic_iff_eq_discrete (P : Partition (Set α)) :
    P.Atomic ↔ P = Partition.discrete P.supp := by
  refine ⟨fun h => ?_, fun h => h ▸ discrete_atomic P.supp⟩
  ext x
  simp_rw [Atomic, Set.isAtom_iff] at h
  refine ⟨fun hx => ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := h x hx
    simp only [mem_discrete_iff, singleton_eq_singleton_iff, exists_eq_right]
    exact mem_supp_iff.mpr ⟨{a}, hx, rfl⟩
  rintro ⟨a, ⟨t, htP, hat⟩, rfl⟩
  obtain ⟨b, rfl⟩ := h t htP
  obtain rfl := mem_singleton_iff.mp hat
  exact htP

lemma discrete_le_of_supp_eq (P : Partition (Set α)) : Partition.discrete P.supp ≤ P := by
  refine le_of_rel_le fun a b => ?_
  rw [rel_discrete_iff]
  rintro ⟨rfl, hb⟩
  exact rel_self_of_mem_supp hb

-- lemma atomic_iff_rel_le_eq (P : Partition (Set α)) :
--     P.Atomic ↔ ⇑P ≤ Eq := by
--   refine ⟨fun h ↦ ?_, fun h ↦ rel_inj ?_⟩
--   · rw [← h, rel_discrete_eq]
--     tauto
--   ext x y
--   rw [rel_discrete_iff]
--   refine ⟨?_, fun hxy ↦ ⟨h x y hxy, codomain_rel ▸ ⟨y, symm hxy⟩⟩⟩
--   rintro ⟨rfl, h⟩
--   exact rel_self_of_mem_supp h

-- lemma discrete_of_le_discrete (hS : P ≤ Partition.discrete S) : Partition.discrete P.supp = P :=
--by
--   refine P.discrete_iff_rel_le_eq.mpr <| (rel_le_iff_le.mpr hS).trans ?_
--   rw [← discrete_iff_rel_le_eq]
--   simp

@[simp]
lemma discrete_empty : Partition.discrete (∅ : Set α) = ⊥ := by
  ext x
  simp

-- Compl does not exist

end Discrete

section point

variable {S T : Set α} {a b : α} {P : Partition (Set α)}

/-- The part containing a given element of the set being partitioned. If `x ∉ s`, then `∅`.  -/
def partOf (P : Partition (Set α)) (x : α) : Set α :=
  fiber P x

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

-- lemma restrict_iff_rel (P Q : Partition (Set α)) :
--     (∀ x y, x ∈ Q.supp ∧ P x y ↔ Q x y) ↔ (∃ h : Q ⊆ P, P.restrict Q.parts h = Q) := by
--   refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨h, heq⟩ x y ↦ by rw [← heq, restrict_rel]; simp⟩
--   on_goal 1 => rw [subset_iff_restrict]; use Q.parts, ?_
--   on_goal 2 =>
--     intro s hsQ

--     sorry
--   all_goals
--   · apply rel_inj
--     ext x y
--     rw [restrict_rel]
--     exact h x y

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
    P x y ↔ P.partOf x = P.partOf y := by
  refine ⟨fun ⟨t, htP, hxt, hyt⟩ ↦ ?_, fun h ↦ ⟨P.partOf x, P.partOf_mem hx, P.mem_partOf hx, ?_⟩⟩
  · rw [eq_partOf_of_mem (P.partOf_mem hx)]
    rwa [← eq_partOf_of_mem htP hxt]
  rw [h]
  exact mem_partOf hy

lemma rel_iff_partOf_eq_partOf' (P : Partition (Set α)) :
    P x y ↔ ∃ (_ : x ∈ P.supp) (_ : y ∈ P.supp), P.partOf x = P.partOf y :=
  ⟨fun h ↦ ⟨h.left_mem, h.right_mem, (P.rel_iff_partOf_eq_partOf h.left_mem h.right_mem).1 h⟩,
    fun ⟨hx,hy,h⟩ ↦ (P.rel_iff_partOf_eq_partOf hx hy).2 h⟩

lemma rel_iff_forall : P x y ↔ x ∈ P.supp ∧ ∀ t ∈ P, x ∈ t ↔ y ∈ t := by
  refine ⟨fun h ↦ ⟨h.left_mem, fun _ ↦ h.forall⟩,
    fun ⟨hxs, h⟩ ↦ ⟨P.partOf x, P.partOf_mem hxs, P.mem_partOf hxs, ?_⟩⟩
  rw [← h _ (P.partOf_mem hxs)]
  exact P.mem_partOf hxs

lemma setOf_rel_self_eq (P : Partition (Set α)) : {x | P x x} = P.supp := by
  refine subset_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · obtain ⟨t, ht, hxP, -⟩ := hx
    exact subset_of_mem ht hxP
  obtain ⟨t, ⟨ht, hxt⟩, -⟩ := P.exists_unique_of_mem_supp hx
  exact ⟨t, ht, hxt, hxt⟩

lemma rel_self_iff_mem : P x x ↔ x ∈ P.supp := by
  simp [← P.setOf_rel_self_eq]

lemma setOf_rel_eq (ht : T ∈ P) (hx : x ∈ T) : {y | P x y} = T :=
  Set.ext fun y ↦ ⟨fun ⟨t', ht', hx', hy'⟩ ↦ by rwa [P.eq_of_mem_of_mem ht ht' hx hx'],
    fun h ↦ ⟨T, ht, hx, h⟩⟩

lemma rep_rel (ht : T ∈ P) (hx : x ∈ T) : P x (P.rep ht) :=
  ⟨T, ht, hx, P.rep_mem ht⟩

@[simp] lemma rep_rel_self {P : Partition (Set α)} (ht : T ∈ P) : P (P.rep ht) (P.rep ht) :=
  rep_rel _ (P.rep_mem ht)

lemma setOf_rel_rep_eq (ht : T ∈ P) : {x | P (P.rep ht) x} = T :=
  setOf_rel_eq ht (P.rep_mem ht)

/-- The `partOf x` is the set of `y` related to `x`. True even if `x ∉ s`, since both are `∅`.-/
lemma setOf_rel_eq_partOf (P : Partition (Set α)) (x : α) : {y | P x y} = P.partOf x := by
  by_cases hx : x ∈ P.supp
  · rw [setOf_rel_eq (P.partOf_mem hx) (P.mem_partOf hx)]
  rw [partOf_eq_empty _ hx, eq_empty_iff_forall_notMem]
  exact fun y hxy ↦ hx <| Rel.left_mem hxy

lemma setOf_rel_mem (P : Partition (Set α)) (hx : x ∈ P.supp) : {y | P x y} ∈ P := by
  obtain ⟨t, ⟨ht,hp⟩, -⟩ := P.exists_unique_of_mem_supp hx
  rwa [setOf_rel_eq ht hp]

@[ext] theorem eq_of_rel_iff_rel {P P' : Partition (Set α)} (h : ∀ x y, P x y ↔ P' x y) :
    P = P' := by
  rw [← ofRel_rel_eq P, ← ofRel_rel_eq P']; congr; ext; exact h _ _

lemma discrete.rel_iff_eq_of_mem (ha : a ∈ P.supp) :
    (Partition.discrete P.supp) a b ↔ a = b := by
  rw [rel_discrete_iff, and_iff_left ha]

end point

section RepFun

variable {a b : α} {s : Set α} {P : Partition (Set α)}

structure RepFun (P : Partition (Set α)) where
  (toFun : α → α)
  (apply_eq_self_of_notMem : ∀ a ∉ P.supp, toFun a = a)
  (rel_apply_of_mem : ∀ a ∈ P.supp, P a (toFun a))
  (apply_eq_of_rel : ∀ a b, P a b → toFun a = toFun b)

instance : FunLike (RepFun P) α α where
  coe := RepFun.toFun
  coe_injective' f f' := by cases f; cases f'; simp

def RepFun.mk' (P : Partition (Set α)) (f : α → α) {p : α → Prop} (hP : ∀ {x}, x ∈ P.supp ↔ p x)
    (h₁ : ∀ a, ¬ p a → f a = a) (h₂ : ∀ a, p a → P a (f a))
    (h₃ : ∀ a b, P a b → f a = f b) : P.RepFun :=
  ⟨f, fun a ha ↦ h₁ a (hP.not.mp ha), fun a ha ↦ h₂ a (hP.mp ha), h₃⟩

@[simp] lemma RepFun.mk_apply (P : Partition (Set α)) (f) (h₁ : ∀ a ∉ P.supp, f a = a)
  (h₂ : ∀ a ∈ P.supp, P a (f a)) (h₃) (x : α) : (RepFun.mk f h₁ h₂ h₃) x = f x := rfl

lemma RepFun.apply_of_notMem (f : P.RepFun) (ha : a ∉ P.supp) : f a = a :=
  f.apply_eq_self_of_notMem a ha

lemma RepFun.rel_apply (f : P.RepFun) (ha : a ∈ P.supp) : P a (f a) :=
  f.rel_apply_of_mem a ha

lemma RepFun.rel_apply' (f : P.RepFun) {p : α → Prop} (hP : ∀ {x}, x ∈ P.supp ↔ p x) (ha : p a) :
    P a (f a) := f.rel_apply <| hP.mpr ha

lemma RepFun.apply_mem (f : P.RepFun) (ha : a ∈ P.supp) : f a ∈ P.supp :=
  (f.rel_apply ha).right_mem

lemma RepFun.apply_mem' (f : P.RepFun) {p : α → Prop} (hP : ∀ {x}, x ∈ P.supp ↔ p x) (ha : p a) :
    p (f a) := hP.mp <| f.apply_mem <| hP.mpr ha

lemma RepFun.apply_eq_apply (f : P.RepFun) (hab : P a b) : f a = f b :=
  f.apply_eq_of_rel a b hab

lemma RepFun.rel_of_apply_eq_apply (f : P.RepFun) (ha : a ∈ P.supp) (hab : f a = f b) :
    P a b := by
  refine (f.rel_apply ha).trans ?_
  rw [hab, P.rel_comm]
  refine f.rel_apply <| by_contra fun hb ↦ ?_
  rw [f.apply_of_notMem hb] at hab; rw [← hab] at hb
  exact hb <| f.apply_mem ha

lemma RepFun.rel_of_ne_of_apply_eq_apply (f : P.RepFun) (hne : a ≠ b) (hab : f a = f b) :
    P a b := by
  obtain (ha | ha) := em (a ∈ P.supp); exact f.rel_of_apply_eq_apply ha hab
  obtain (hb | hb) := em (b ∈ P.supp); exact (f.rel_of_apply_eq_apply hb hab.symm).symm
  rw [f.apply_of_notMem ha, f.apply_of_notMem hb] at hab; contradiction

lemma RepFun.apply_eq_apply_iff_rel (f : P.RepFun) (ha : a ∈ P.supp) : f a = f b ↔ P a b :=
  ⟨f.rel_of_apply_eq_apply ha, f.apply_eq_apply⟩

lemma RepFun.apply_eq_apply_iff_rel_of_ne (f : P.RepFun) (hne : a ≠ b) : f a = f b ↔ P a b :=
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
    (h_notMem : ∀ x : t, x.1 ∉ P.supp → f₀ x = x) (h_mem : ∀ x : t, x.1 ∈ P.supp → P x (f₀ x))
    (h_eq : ∀ x y : t, P x y → f₀ x = f₀ y) : ∃ (f : P.RepFun), ∀ x : t, f x = f₀ x := by
  classical
  set f : α → α := fun a ↦ if ha : a ∈ P.supp then
    (if hb : ∃ b : t, P a b then f₀ hb.choose else P.rep (P.partOf_mem ha)) else a with hf
  refine ⟨RepFun.mk f (fun a ha ↦ by simp [hf, ha]) (fun a ha ↦ ?_) (fun a b hab ↦ ?_), fun a ↦ ?_⟩
  · simp only [hf, ha, ↓reduceDIte]
    split_ifs with h
    · exact h.choose_spec.trans <| h_mem h.choose h.choose_spec.right_mem
    push_neg at h
    exact P.rep_rel (P.partOf_mem ha) (P.mem_partOf ha)
  · simp_rw [hf, dif_pos hab.left_mem, dif_pos hab.right_mem]
    split_ifs with h₁ h₂ h₂
    · exact h_eq _ _ <| (hab.symm.trans h₁.choose_spec).symm.trans h₂.choose_spec
    · exact False.elim <| h₂ ⟨_, hab.symm.trans h₁.choose_spec⟩
    · exact False.elim <| h₁ ⟨_, hab.trans h₂.choose_spec⟩
    congr
    rwa [← rel_iff_partOf_eq_partOf _ hab.left_mem hab.right_mem]
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
    (h : ∀ ⦃x y⦄, x ∈ t → y ∈ t → P x y → x = y) : ∃ (f : P.RepFun), EqOn f id t := by
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
    rw [rel_discrete_iff] at hx'
    exact hx'.1.symm
  rw [f.apply_of_notMem (supp_discrete s |>.symm ▸ hx), id]

lemma RepFun.coeFun_eq_id_of_eq_discrete  (f : P.RepFun) (hP : P = Partition.discrete s) :
    (f : α → α) = id := by
  subst hP; exact repFun_discrete_coeFun s f


-- lemma RepFun.image_eq_of_forall_rel_imp_eq (h : ∀ ⦃x y⦄, x ∈ s → y ∈ s → P x y → x = y)







-- /-- If `a ∈ s`, noncomputably choose an element in the same cell of `P` as some `a : α`.
-- If `a ∉ s`, is equal to `a`. -/
-- noncomputable def rep' (P : Partition (Set α)) (a : α) : α :=
--     if h : a ∈ s then P.rep (P.partOf_mem h) else a

-- lemma rep'_eq_rep (P : Partition (Set α)) (ha : a ∈ s) : P.rep' a = P.rep (P.partOf_mem ha) := by
--   rw [rep', dif_pos ha]

-- lemma rel_rep' (P : Partition (Set α)) (ha : a ∈ s) : P a (P.rep' a) := by
--   rw [P.rep'_eq_rep ha]
--   exact P.rep_rel (P.partOf_mem ha) (P.mem_partOf ha)

-- lemma rep'_eq_self_of_notMem (P : Partition (Set α)) (ha : a ∉ s) : P.rep' a = a := by
--   rw [rep', dif_neg ha]

-- lemma rel_iff_rep'_eq_rep' (ha : a ∈ s) (hb : b ∈ s) : P a b ↔ P.rep' a = P.rep' b := by
--   refine ⟨fun h ↦ ?_, fun h ↦ (P.rel_rep' ha).trans (h.symm ▸ P.rel_rep' hb).symm ⟩
--   rw [P.rel_iff_partOf_eq_partOf ha hb] at h
--   rw [P.rep'_eq_rep ha, P.rep'_eq_rep hb]
--   congr




end RepFun


-- def Fiber (f : α → β) : Partition (univ : Set α) := Partition.ofRel' (Eq on f) <| by ext a; simp


-- lemma Fiber.mem_of_mem (h : x ∈ s) : x ∈ P.Fiber x := by
--   exact P.mem_partOf h

-- end Fiber
