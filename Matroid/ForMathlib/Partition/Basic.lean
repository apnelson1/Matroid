import Mathlib.Order.CompactlyGenerated.Basic
import Matroid.ForMathlib.Lattice
import Matroid.ForMathlib.Relation
import Matroid.ForMathlib.Function -- for Function.onFun_comp

open Set Function

section Pairwise

variable {α β ι ι' : Type*} {r : α → α → Prop} {f : ι → α} {g : ι' → ι} {x y : α}

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

lemma Pairwise.onFun_of_refl [IsRefl α r] (hr : Pairwise r) (f : ι → α) : Pairwise (r on f) := by
  rintro i j hne
  rw [Pairwise.iff_top_of_refl] at hr
  subst r
  trivial

lemma Set.pairwise_image_of_refl {s : Set ι} [IsRefl α r] :
    (f '' s).Pairwise r ↔ s.Pairwise (r on f) :=
  ⟨fun h i hi j hj _ => h.of_refl (by use i : f i ∈ f '' s) (by use j : f j ∈ f '' s),
    Pairwise.image⟩

lemma Pairwise.onFun_comp_of_refl [IsRefl α r] (hr : Pairwise (r on f)) (g : ι' → ι) :
    Pairwise (r on (f ∘ g)) := Pairwise.onFun_of_refl hr g

instance [PartialOrder α] [OrderBot α] : IsSymm α Disjoint where
  symm := Disjoint.symm

lemma pairwiseDisjoint_pair {ι : Type*} {i j : ι} {f : ι → α} [PartialOrder α] [OrderBot α]
    (hab : (Disjoint on f) i j) : PairwiseDisjoint {i, j} f := by
  rintro a (rfl | rfl) b (rfl | rfl) <;> simp [hab, symm hab]

@[simp]
lemma Pairwise.const_of_refl [IsRefl α r] (x : α) : Pairwise (r on fun (_ : ι) ↦ x) := by
  simp [Pairwise, refl]

lemma pairwise_pair_of_symm [IsSymm α r] (hxy : r x y) : ({x, y} : Set α).Pairwise r := by
  rintro a (rfl | rfl) b (rfl | rfl) <;> simp [hxy, symm hxy]

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

-- lemma disjoint_sup [CompleteLattice α] {a : α} {s t : Set α} (hb : )


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

lemma pairwiseDisjoint : Set.PairwiseDisjoint (P : Set α) id :=
  fun _ hx _ hy hxy ↦ P.disjoint hx hy hxy

lemma eq_of_not_disjoint (hx : x ∈ P) (hy : y ∈ P) (hxy : ¬ Disjoint x y) : x = y := by
  by_contra hne
  exact hxy (P.disjoint hx hy hne)

lemma ne_bot_of_mem (hx : x ∈ P) : x ≠ ⊥ :=
  fun h ↦ P.bot_notMem <| h ▸ hx

lemma bot_lt_of_mem (hx : x ∈ P) : ⊥ < x :=
  bot_lt_iff_ne_bot.2 <| P.ne_bot_of_mem hx

lemma sSup_eq (P : Partition α) : sSup P = P.supp  := rfl

lemma iSup_eq (P : Partition α) : ⨆ x ∈ P, x = P.supp := by
  simp_rw [← P.sSup_eq, sSup_eq_iSup]
  rfl

lemma le_of_mem (hx : x ∈ P) : x ≤ P.supp :=
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
@[simps!]
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

instance : OrderBot (Partition α) where
  bot := Partition.empty α
  bot_le _ _ hs := hs.elim

@[simp] lemma parts_bot (α : Type*) [CompleteLattice α] : (⊥ : Partition α).parts = ∅ := rfl

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

@[simp]
lemma bot_subset (P : Partition α) : ⊥ ⊆ P :=
  fun _ hsP => hsP.elim

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

/-- Similar to `indiscrete`, but in the case `s = ⊥` it returns the empty partition. -/
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

def bipartition (a b : α) (ha : a ≠ ⊥) (hb : b ≠ ⊥) (hab : Disjoint a b) : Partition α :=
  ofIndependent (u := {a, b}) (by
    rintro x (rfl | rfl)
    · simpa [Set.diff_singleton_eq_self (show x ∉ {_} from hab.ne ha)]
    · rw [disjoint_comm] at hab
      simpa [Set.pair_comm, Set.diff_singleton_eq_self (show x ∉ {a} from hab.ne hb)])
    (by simp [ha.symm, hb.symm])

@[simp] lemma parts_bipartition {a b : α} (ha : a ≠ ⊥) (hb : b ≠ ⊥) (hab : Disjoint a b) :
    (bipartition a b ha hb hab).parts = {a, b} := rfl

@[simp] lemma mem_bipartition_iff {a b : α} (ha : a ≠ ⊥) (hb : b ≠ ⊥) (hab : Disjoint a b) :
    x ∈ bipartition a b ha hb hab ↔ x = a ∨ x = b := by
  simp [bipartition]

@[simp] lemma supp_bipartition {a b : α} (ha : a ≠ ⊥) (hb : b ≠ ⊥) (hab : Disjoint a b) :
    (bipartition a b ha hb hab).supp = a ⊔ b := by
  simp [bipartition]

lemma bipartition_comm {a b : α} (ha : a ≠ ⊥) (hb : b ≠ ⊥) (hab : Disjoint a b) :
    bipartition a b ha hb hab = bipartition b a hb ha hab.symm :=
  Partition.ext <| by simp [bipartition, pair_comm]

end indep

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

lemma le_of_supp_le_part (ha : a ∈ P) (hQa : Q.supp ≤ a) : Q ≤ P :=
  fun _ hx ↦ ⟨a, ha, (Q.le_of_mem hx).trans hQa⟩

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
  bot_le a s hs := by simp only [notMem_bot] at hs

lemma supp_le_of_le {P Q : Partition α} (h : P ≤ Q) : P.supp ≤ Q.supp :=
  sSup_le_sSup_of_isCofinalFor h

lemma le_of_subset {P Q : Partition α} (h : P ⊆ Q) : P ≤ Q :=
  fun x hx => ⟨x, h hx, le_rfl⟩

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
