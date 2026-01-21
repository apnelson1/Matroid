import Matroid.ForMathlib.Partition.Basic

variable {α β ι ι' : Type*} {s t S T : Set α} {a b c x y : α}

open Set Function

namespace Partition

section Induce

variable [CompleteLattice α] {P Q R : Partition α}

@[simps!]
protected def induce (P : Partition α) (a : α) : Partition α :=
  ofIndependent' (u := (a ⊓ ·) '' P.parts) <| P.indep.image (fun _ ↦ inf_le_right)

@[simp 80]
lemma induce_supp : (P.induce a).supp = ⨆ t ∈ P, a ⊓ t := by
  simp [Partition.induce, sSup_image]

@[simp]
lemma mem_induce_iff : x ∈ P.induce a ↔ x ≠ ⊥ ∧ ∃ t ∈ P, a ⊓ t = x := by
  simp [Partition.induce, and_comm]

lemma inf_mem_induce (h : x ∈ P) (hne : a ⊓ x ≠ ⊥) : a ⊓ x ∈ P.induce a := by
  exact mem_induce_iff.mpr ⟨hne, x, h, rfl⟩

@[simp]
lemma induce_empty : P.induce ⊥ = ⊥ := by
  ext x
  simp +contextual [eq_comm]

@[simp]
lemma induce_induce : Partition.induce (Partition.induce P a) b = Partition.induce P (b ⊓ a) := by
  ext x
  simp only [mem_induce_iff, and_congr_right_iff]
  refine fun hne => ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨t, ⟨htne, s, hs, rfl⟩, rfl⟩ := h
    exact ⟨s, hs, by rw [inf_assoc]⟩
  obtain ⟨t, ht, rfl⟩ := h
  exact ⟨a ⊓ t, ⟨fun h => by simp [inf_assoc, h] at hne, t, ht, rfl⟩, by rw [inf_assoc]⟩

@[simp]
lemma induce_eq_self_iff : P.induce a = P ↔ P.supp ≤ a := by
  refine ⟨fun hP ↦ by rw [← hP]; simp, fun h ↦ ?_⟩
  ext x
  rw [mem_induce_iff]
  have : ∀ t ∈ P, a ⊓ t = t := fun t htP ↦ inf_eq_right.mpr <| le_trans (P.le_supp_of_mem htP) h
  exact ⟨fun ⟨hne, t, htP, heq⟩ ↦ (this t htP).symm.trans heq ▸ htP,
    fun hx ↦ ⟨P.ne_bot_of_mem hx, x, hx, this x hx⟩⟩

@[simp]
lemma induce_self : P.induce P.supp = P := induce_eq_self_iff.mpr le_rfl

@[simp]
lemma induce_le : P.induce a ≤ P := by
  intro T hT
  obtain ⟨hne, t, htP, rfl⟩ := (by simpa only [mem_induce_iff] using hT); clear hT
  exact ⟨t, htP, inf_le_right⟩

lemma induce_le_induce_right (h : a ⊓ P.supp ≤ b ⊓ P.supp) : P.induce a ≤ P.induce b := by
  rintro x hxa
  simp_rw [mem_induce_iff] at hxa ⊢
  obtain ⟨hne, x, hxP, rfl⟩ := hxa
  have hsu : a ⊓ x ≤ b ⊓ x := le_inf (le_trans (inf_le_inf_left a <| P.le_supp_of_mem hxP) <|
    h.trans inf_le_left) inf_le_right
  use b ⊓ x, ?_
  use ne_bot_of_le_ne_bot hne hsu, x

lemma induce_le_induce_right_of_le (h : a ≤ b) : P.induce a ≤ P.induce b :=
  induce_le_induce_right <| inf_le_inf_right P.supp h

lemma induce_le_induce_left (hPQ : P ≤ Q) : P.induce a ≤ Q.induce a := by
  intro t ht
  simp_rw [mem_induce_iff] at ht ⊢
  obtain ⟨hne, t', ht'Q, rfl⟩ := ht
  obtain ⟨s, hsQ, ht's⟩ := hPQ t' ht'Q
  have hsu := inf_le_inf_left a ht's
  use a ⊓ s, ?_, hsu
  use ne_bot_of_le_ne_bot hne hsu, s

lemma le_induce_of_supp_le (hPQ : P ≤ Q) (hP : P.supp ≤ a) : P ≤ Q.induce a := by
  rw [← induce_eq_self_iff.mpr hP]
  exact induce_le_induce_left hPQ

lemma induce_subset_induce_of_subset (hPQ : P ⊆ Q) (a : α) : P.induce a ⊆ Q.induce a := by
  rintro t ⟨⟨t', ht'P, rfl⟩, hne⟩
  exact ⟨⟨t', hPQ ht'P, rfl⟩, hne⟩

lemma subset_induce_of_supp_le (hPQ : P ⊆ Q) (hP : P.supp ≤ a) : P ⊆ Q.induce a := by
  rw [← induce_eq_self_iff.mpr hP]
  exact induce_subset_induce_of_subset hPQ a

lemma induce_eq_induce_right (h : a ⊓ P.supp = b ⊓ P.supp) : P.induce a = P.induce b :=
  (induce_le_induce_right h.le).antisymm (induce_le_induce_right h.ge)


def isInducedSubpartition (P Q : Partition α) : Prop :=
  Q.induce P.supp = P

scoped infixl:50 " ≤ip " => isInducedSubpartition

lemma isInducedSubpartition_iff : P ≤ip Q ↔ Q.induce P.supp = P := Iff.rfl

lemma isInducedSubpartition.le (h : P ≤ip Q) : P ≤ Q := by
  rw [← h]
  exact induce_le

lemma isInducedSubpartition.supp_le (h : P ≤ip Q) : P.supp ≤ Q.supp :=
  supp_le_of_le h.le

lemma isInducedSubpartition_of_subset (hPQ : P ⊆ Q) : P ≤ip Q := by
  ext S
  rw [mem_induce_iff]
  refine ⟨?_, fun hS ↦ ⟨P.ne_bot_of_mem hS, S, hPQ hS, inf_eq_right.mpr <| P.le_supp_of_mem hS⟩⟩
  rintro ⟨hne, t, htQ, rfl⟩
  rw [ne_eq, ← disjoint_iff] at hne
  have htP := mem_of_subset_of_not_disjoint hPQ htQ hne
  rwa [inf_eq_right.mpr (P.le_supp_of_mem htP)]

lemma isInducedSubpartition.eq_of_supp_le (hPQ : P ≤ip Q) (hQP : Q.supp ≤ P.supp) : P = Q := by
  rwa [← hPQ, induce_eq_self_iff]

@[simp]
lemma isInducedSubpartition_rfl : P ≤ip P := by
  simp [isInducedSubpartition]

instance : Std.Refl (isInducedSubpartition : Partition α → Partition α → Prop) where
  refl _ := isInducedSubpartition_rfl

lemma isInducedSubpartition.antisymm (hPQ : P ≤ip Q) (hQP : Q ≤ip P) : P = Q :=
  hPQ.eq_of_supp_le hQP.supp_le

instance : Std.Antisymm (isInducedSubpartition : Partition α → Partition α → Prop) where
  antisymm _ _ := isInducedSubpartition.antisymm

end Induce

section InduceFrame

-- lemmas related to `induce` under `Order.Frame α` assumptions

variable [Order.Frame α] {P Q R : Partition α} {a b c x y : α}

@[simp↓]
lemma induce_supp' (P : Partition α) (a : α) : (Partition.induce P a).supp = a ⊓ P.supp := by
  simp only [Partition.induce, supp_ofIndependent']
  rw [sSup_image, ← inf_sSup_eq]
  rfl

lemma induce_le_induce_iff : P.induce a ≤ P.induce b ↔ a ⊓ P.supp ≤ b ⊓ P.supp := by
  refine ⟨fun h ↦ ?_, induce_le_induce_right⟩
  rw [← induce_supp', ← induce_supp']
  exact supp_le_of_le h

lemma induce_eq_induce_iff : P.induce a = P.induce b ↔ a ⊓ P.supp = b ⊓ P.supp :=
  ⟨fun h ↦ by rw [← induce_supp', ← induce_supp', h], induce_eq_induce_right⟩

lemma inter_mem_induce (hne : ¬ Disjoint a b) (ht : b ∈ P) : a ⊓ b ∈ P.induce a :=
  P.mem_induce_iff.mpr ⟨by rwa [disjoint_iff_inf_le, le_bot_iff] at hne, b, ht, rfl⟩

lemma isInducedSubpartition.trans (hPQ : P ≤ip Q) (hQR : Q ≤ip R) : P ≤ip R := by
  rw [← hPQ, ← hQR, induce_induce, inf_eq_left.mpr hPQ.supp_le, isInducedSubpartition, induce_supp',
    inf_eq_left.mpr (hPQ.supp_le.trans hQR.supp_le)]

lemma isInducedSubpartition.of_supp_le (hPQ : P.supp ≤ Q.supp) (hPR : P ≤ip R) (hQR : Q ≤ip R) :
    P ≤ip Q := by
  rw [← hPR, ← hQR, isInducedSubpartition_iff, induce_supp', induce_induce,
    induce_eq_induce_iff]
  ac_nf
  rw [← inf_assoc, inf_eq_left.mpr hPQ]

end InduceFrame

section Restrict

variable [CompleteLattice α] {P Q R : Partition α}

/-- `P \ s` is the subpartition of `P` with parts `P.parts \ s`. -/
@[simps]
def delete (P : Partition α) (s : Set α) : Partition α where
  parts := P.parts \ s
  indep := P.indep.mono diff_subset
  bot_not_mem h := P.bot_not_mem h.1

scoped infixl:65 " \\ " => Partition.delete

@[simp] lemma mem_delete_iff : x ∈ delete P s ↔ x ∈ P ∧ x ∉ s := Iff.rfl

@[simp] lemma delete_supp : (delete P s).supp = sSup (P.parts \ s) := by
  simp [delete, supp]

lemma delete_subset (s : Set α) : (delete P s) ⊆ P := fun _ h ↦ h.1

lemma delete_le (s : Set α) : delete P s ≤ P :=
  le_of_subset <| delete_subset (P := P) s

@[simp] lemma delete_empty : delete P (∅ : Set α) = P := by
  ext a
  simp [mem_delete_iff]

@[simp] lemma delete_univ : delete P (Set.univ : Set α) = ⊥ := by
  ext a
  simp [mem_delete_iff]

@[simp] lemma delete_self : delete P P.parts = ⊥ := by
  ext a
  simp [mem_delete_iff, mem_parts]

@[simp] lemma delete_delete : delete (delete P s) t = delete P (s ∪ t) := by
  ext a
  classical
  constructor
  · intro h
    rcases (mem_delete_iff.mp h) with ⟨hPs, ha_not_t⟩
    rcases hPs with ⟨haP, ha_not_s⟩
    refine mem_delete_iff.mpr ?_
    refine ⟨haP, ?_⟩
    simpa [mem_union, not_or] using And.intro ha_not_s ha_not_t
  · intro h
    rcases (mem_delete_iff.mp h) with ⟨haP, ha_not_union⟩
    have hns_ht : a ∉ s ∧ a ∉ t := by
      simpa [mem_union, not_or] using ha_not_union
    exact mem_delete_iff.mpr ⟨⟨haP, hns_ht.1⟩, hns_ht.2⟩

lemma delete_subset_delete_of_subset (h : s ⊆ t) : delete P t ⊆ delete P s := by
  intro a ha
  exact ⟨ha.1, fun hs => ha.2 (h hs)⟩

lemma delete_le_delete_of_subset (h : s ⊆ t) : delete P t ≤ delete P s :=
  le_of_subset <| delete_subset_delete_of_subset (P := P) h

lemma delete_subset_of_subset (hPQ : P ⊆ Q) : delete P s ⊆ delete Q s := by
  intro a ha
  exact ⟨hPQ ha.1, ha.2⟩

lemma delete_supp_le : (delete P s).supp ≤ P.supp := by
  exact supp_le_of_le (delete_le (P := P) s)


/-- The subpartition with over a subset of the parts. -/
@[simps]
def restrict (P : Partition α) (s : Set α) (hs : s ⊆ P.parts) : Partition α where
  parts := s
  indep := P.indep.mono hs
  bot_not_mem h := P.bot_not_mem (hs h)

@[simp] lemma mem_restrict_iff (hs : s ⊆ P.parts) :
    a ∈ P.restrict s hs ↔ a ∈ s := Iff.rfl

@[simp] lemma restrict_supp (hs : s ⊆ P.parts) : (P.restrict s hs).supp = sSup s := by
  simp [restrict, supp]

lemma restrict_subset (hs : s ⊆ P.parts) : (P.restrict s hs) ⊆ P := fun _ h ↦ hs h

lemma restrict_le (hs : s ⊆ P.parts) : P.restrict s hs ≤ P := le_of_subset <| restrict_subset hs

lemma subset_iff_restrict : P ⊆ Q ↔ ∃ S, ∃ hS : S ⊆ Q.parts, Q.restrict S hS = P :=
  ⟨fun h ↦ ⟨P.parts, h, by ext; simp⟩, fun ⟨S, hS, heq⟩ ↦ heq ▸ restrict_subset hS⟩

@[simp]
lemma restrict_eq_self_iff (hs : s ⊆ P.parts) : P.restrict s hs = P ↔ s = P.parts :=
  ⟨fun hP ↦ by rw [← hP]; simp, fun h ↦ h ▸ (by rfl)⟩


@[simps! parts]
def cover (P : Partition α) (a : α) : Partition α :=
  P.restrict {s | s ∈ P.parts ∧ ¬ Disjoint a s} (fun x ↦ by aesop)

@[simp] lemma mem_cover_iff : x ∈ P.cover a ↔ x ∈ P ∧ ¬ Disjoint a x := Iff.rfl

@[simp]
lemma cover_supp : (P.cover a).supp = sSup {s | s ∈ P.parts ∧ ¬ Disjoint a s} := by
  simp [cover, supp]

lemma cover_supp_le : (P.cover a).supp ≤ P.supp := by
  simp +contextual [cover, le_supp_of_mem]

lemma cover_supp_eq_self : P.cover P.supp = P := by
  ext x
  simp only [cover, mem_parts, mem_restrict_iff, mem_setOf_eq, and_iff_left_iff_imp]
  rintro hxP hdisj
  obtain rfl := hdisj.symm.eq_bot_of_le (le_supp_of_mem hxP)
  exact P.bot_not_mem hxP

lemma cover_subset (a : α) : P.cover a ⊆ P := restrict_subset _

lemma cover_le_of_le (h : Q ≤ P) : Q.cover a ≤ P.cover a := by
  rintro x ⟨hxQ, hdisj⟩
  obtain ⟨y, hyP, hxy⟩ := h x hxQ
  refine ⟨y, ⟨hyP, ?_⟩, hxy⟩
  contrapose! hdisj
  exact hdisj.mono_right hxy

@[simp]
lemma cover_eq_self_iff : P.cover a = P ↔ ∀ x ∈ P, ¬ Disjoint a x := by
  refine ⟨fun hP ↦ by rw [← hP]; simp, fun h ↦ ?_⟩
  ext x
  simp only [mem_cover_iff, and_iff_left_iff_imp]
  exact h x

lemma induce_le_cover (P : Partition α) (a : α) : P.induce a ≤ P.cover a := by
  rintro x ⟨hxP, hdisj⟩
  obtain ⟨y, hyP, rfl⟩ := hxP
  simp only [mem_parts] at hyP
  simp only [mem_singleton_iff, mem_cover_iff, and_assoc, disjoint_iff] at hdisj ⊢
  use y, hyP, hdisj, inf_le_right

def avoid (P : Partition α) (a : α) : Partition α :=
  P.restrict {s | s ∈ P.parts ∧ Disjoint a s} (fun x ↦ by aesop)

@[simp] lemma mem_avoid_iff : x ∈ P.avoid a ↔ x ∈ P ∧ Disjoint a x := Iff.rfl

@[simp]
lemma avoid_supp : (P.avoid a).supp = sSup {s | s ∈ P.parts ∧ Disjoint a s} := by
  simp [avoid, supp]

lemma avoid_supp_le : (P.avoid a).supp ≤ P.supp := by
  simp +contextual [avoid, le_supp_of_mem]

lemma avoid_supp_eq_self : P.avoid ⊥ = P := by
  ext x
  simp

lemma avoid_subset (a : α) : P.avoid a ⊆ P := restrict_subset _

@[simp]
lemma avoid_eq_self_iff : P.avoid a = P ↔ ∀ x ∈ P, Disjoint a x := by
  refine ⟨fun hP ↦ by rw [← hP]; simp, fun h ↦ ?_⟩
  ext x
  simp only [mem_avoid_iff, and_iff_left_iff_imp]
  exact h x


def Agree (P Q : Partition α) : Prop := ∃ S : Partition α, P ⊆ S ∧ Q ⊆ S

lemma agree_of_subset_subset {P₀ Q₀ : Partition α} (hP : P₀ ⊆ P) (hQ : Q₀ ⊆ P) :
    P₀.Agree Q₀ := ⟨P, hP, hQ⟩

@[simp]
lemma Agree.rfl : P.Agree P := ⟨P, subset_rfl, subset_rfl⟩

instance : Std.Refl (Agree : Partition α → Partition α → Prop) where
  refl _ := Agree.rfl

lemma Agree.symm (h : P.Agree Q) : Q.Agree P := by
  obtain ⟨S, hPS, hQS⟩ := h
  exact ⟨S, hQS, hPS⟩

instance : Std.Symm (Agree : Partition α → Partition α → Prop) where
  symm _ _ := Agree.symm

lemma agree_comm : P.Agree Q ↔ Q.Agree P := ⟨Agree.symm, Agree.symm⟩

-- not transitive

@[simp]
lemma Agree.mem_of_mem (h : P.Agree Q) (hx : a ∈ P) (hndisj : ¬ Disjoint Q.supp a) :
    a ∈ Q := by
  obtain ⟨S, hPS, hQS⟩ := h
  exact mem_of_subset_of_not_disjoint hQS (hPS hx) hndisj

lemma Agree.eq_of_not_disjoint (h : P.Agree Q) (ha : a ∈ P) (hb : b ∈ Q) (hndisj : ¬ Disjoint a b) :
    a = b := by
  refine P.eq_of_not_disjoint ha (h.symm.mem_of_mem hb ?_) hndisj
  contrapose! hndisj
  exact hndisj.mono_left <| P.le_supp_of_mem ha

lemma Agree.mem_or_disjoint (h : P.Agree Q) (ha : a ∈ P) : a ∈ Q ∨ Disjoint Q.supp a := by
  obtain ⟨S, hPS, hQS⟩ := h
  rw [or_iff_not_imp_right]
  exact mem_of_subset_of_not_disjoint hQS (hPS ha)

lemma Agree.mono_left {P₀ : Partition α} (h : P.Agree Q) (hP : P₀ ⊆ P) : P₀.Agree Q := by
  obtain ⟨S, hPS, hQS⟩ := h
  exact ⟨S, hP.trans hPS, hQS⟩

lemma Agree.mono_right {Q₀ : Partition α} (h : P.Agree Q) (hQ : Q₀ ⊆ Q) : P.Agree Q₀ := by
  obtain ⟨S, hPS, hQS⟩ := h
  exact ⟨S, hPS, hQ.trans hQS⟩

lemma Agree.mono {P₀ Q₀ : Partition α} (h : P.Agree Q) (hP : P₀ ⊆ P) (hQ : Q₀ ⊆ Q) :
    P₀.Agree Q₀ := by
  obtain ⟨S, hPS, hQS⟩ := h
  exact ⟨S, hP.trans hPS, hQ.trans hQS⟩

@[simp]
lemma indiscrete_agree_indiscrete_iff (ha : a ≠ ⊥) (hb : b ≠ ⊥) :
    (indiscrete a ha).Agree (indiscrete b hb) ↔ (a = b ∨ Disjoint a b) := by
  refine ⟨fun ⟨S, hPS, hQS⟩ => ?_, ?_⟩
  · rw [indiscrete_subset_iff] at hPS hQS
    exact or_iff_not_imp_right.mpr <| S.eq_of_not_disjoint hPS hQS
  rintro (rfl | hdisj)
  · simp
  obtain ⟨P, hP⟩ := isPartition_pair_of_disjoint ha hb hdisj
  use P, ?_ <;> simp [mem_iff_mem_of_parts_eq hP]

@[simp]
lemma agree_on_indiscrete'_iff : (Agree on indiscrete') a b ↔ a = b ∨ Disjoint a b := by
  obtain rfl | hnea := eq_or_ne a ⊥ <;> obtain rfl | hneb := eq_or_ne b ⊥
  · simp
  · simp only [disjoint_bot_left, or_true, iff_true]
    use indiscrete' b
    simp
  · simp only [disjoint_bot_right, or_true, iff_true]
    use indiscrete' a
    simp
  · convert indiscrete_agree_indiscrete_iff hnea hneb <;> simp [hnea, hneb]

end Restrict

section RestrictFrame

-- stuff that needs `Order.Frame α`

variable [Order.Frame α] {P Q : Partition α}

@[simp]
lemma cover_eq_bot_iff : P.cover a = ⊥ ↔ ∀ x ∈ P, Disjoint a x := by
  simp only [← supp_eq_bot_iff, cover_supp, mem_parts, sSup_eq_bot, mem_setOf_eq, and_imp]
  refine ⟨fun h b hbP ↦ ?_, fun h b hbP hndj ↦ (hndj <| h b hbP).elim⟩
  by_contra! hndisj
  exact P.ne_bot_of_mem hbP <| h b hbP hndisj

lemma induce_sSup_eq_restrict (P : Partition α) (a : α) :
    P.induce (sSup {s | s ∈ P.parts ∧ ¬ Disjoint a s}) =
    P.restrict {s | s ∈ P.parts ∧ ¬ Disjoint a s} (fun x ↦ by aesop) := by
  ext x
  simp only [mem_parts, mem_induce_iff, ne_eq, mem_restrict_iff, mem_setOf_eq]
  refine ⟨?_, fun ⟨hxP, hax⟩ => ⟨P.ne_bot_of_mem hxP, x, hxP, inf_eq_right.mpr <|
    le_sSup_of_le (by use hxP) le_rfl⟩⟩
  rintro ⟨hne, t, htP, rfl⟩
  rw [← disjoint_iff, sSup_disjoint_iff] at hne
  obtain ⟨s, hsP, hdisjas, hdisjst⟩ := (by simpa using hne); clear hne
  obtain rfl := P.eq_of_not_disjoint hsP htP hdisjst
  rw [inf_eq_right.mpr <| le_sSup_of_le (by use htP) le_rfl]
  exact ⟨hsP, hdisjas⟩

lemma agree_iff_union_pairwiseDisjoint : P.Agree Q ↔ (P.parts ∪ Q.parts).PairwiseDisjoint id :=
  Iff.trans ⟨fun ⟨S, hPS, hQS⟩ => S.indep.mono (union_subset_iff.mpr ⟨hPS, hQS⟩),
    fun h => ⟨ofIndependent h (·.elim P.bot_not_mem Q.bot_not_mem),
    (fun x hx ↦ by simp [ofIndependent, hx]), (fun x hx ↦ by simp [ofIndependent, hx])⟩⟩
    sSupIndep_iff_pairwiseDisjoint

lemma sSupIndep_parts_union_of_mem_of_not_disjoint (h : ∀ x ∈ P, ¬ Disjoint Q.supp x → x ∈ Q) :
    sSupIndep (P.parts ∪ Q.parts) := by
  simp_rw [sSupIndep, union_diff_distrib, sSup_union, disjoint_sup_right]
  rintro s (hsP | hsQ)
  · use P.indep hsP, disjoint_sSup_iff.mpr ?_
    rintro t ⟨htQ, hts⟩
    by_cases hQsdisj : Disjoint Q.supp s
    · exact hQsdisj.symm.mono_right (le_sSup htQ)
    exact Q.disjoint (h s hsP hQsdisj) htQ (Ne.symm hts)
  use disjoint_sSup_iff.mpr ?_, Q.indep hsQ
  rintro t ⟨htP, hts⟩
  by_cases hQtdisj : Disjoint Q.supp t
  · exact hQtdisj.mono_left (le_sSup hsQ)
  exact Q.disjoint (h t htP hQtdisj) hsQ hts |>.symm

lemma agree_of_mem_of_not_disjoint (h : ∀ x ∈ P, ¬ Disjoint Q.supp x → x ∈ Q) : P.Agree Q := by
  have hindep : sSupIndep (P.parts ∪ Q.parts) := sSupIndep_parts_union_of_mem_of_not_disjoint h
  let R : Partition α := ofIndependent hindep (by simp [P.bot_not_mem, Q.bot_not_mem])
  use R, subset_union_left, subset_union_right

lemma agree_iff_mem_of_not_disjoint: P.Agree Q ↔ ∀ x ∈ P, ¬ Disjoint Q.supp x → x ∈ Q :=
  ⟨fun ⟨_, hPR, hQR⟩ _ hxP ↦ mem_of_subset_of_not_disjoint hQR (hPR hxP),
    fun h ↦ agree_of_mem_of_not_disjoint h⟩

lemma agree_of_supp_disjoint (h : Disjoint P.supp Q.supp) : P.Agree Q := by
  rw [agree_iff_mem_of_not_disjoint]
  rintro x hxP hndisj
  exact (hndisj <| h.symm.mono_right (P.le_supp_of_mem hxP)).elim

lemma set_pairwise_agree_iff_sUnion_pairwiseDisjoint {Ps : Set (Partition α)} :
    Ps.Pairwise Agree ↔ (⋃ P ∈ Ps, P.parts).PairwiseDisjoint id := by
  refine ⟨fun h a ha b hb hne => ?_, fun h P hP Q hQ hne => ?_⟩
  · simp only [mem_iUnion, mem_parts, exists_prop] at ha hb
    obtain ⟨Pa, hPa, haPa⟩ := ha
    obtain ⟨Pb, hPb, hbPb⟩ := hb
    contrapose! hne
    exact (h.of_refl hPa hPb).eq_of_not_disjoint haPa hbPb hne
  rw [agree_iff_union_pairwiseDisjoint]
  apply h.subset
  simp [hP, hQ, subset_biUnion_of_mem]

def ofSetPairwiseAgree (Ps : Set (Partition α)) (h : Ps.Pairwise Agree) : Partition α :=
  ofPairwiseDisjoint (set_pairwise_agree_iff_sUnion_pairwiseDisjoint.mp h)

@[simp]
lemma ofSetPairwiseAgree_parts {Ps : Set (Partition α)} (h : Ps.Pairwise Agree) :
    (ofSetPairwiseAgree Ps h).parts = ⋃ P ∈ Ps, P.parts := by
  simp only [ofSetPairwiseAgree, ofPairwiseDisjoint_parts, sdiff_eq_left, disjoint_singleton_right,
    mem_iUnion, mem_parts, exists_prop, not_exists, not_and]
  rintro P hP
  exact P.bot_not_mem

@[simp]
lemma ofSetPairwiseAgree_supp {Ps : Set (Partition α)} (h : Ps.Pairwise Agree) :
    (ofSetPairwiseAgree Ps h).supp = ⨆ P ∈ Ps, P.supp := by
  simp only [supp, ofSetPairwiseAgree, ofPairwiseDisjoint_parts, sSup_diff_singleton_bot]
  rw [← sUnion_image, sSup_sUnion, iSup_image]

lemma ofSetPairwiseAgree_subset_of_mem {Ps : Set (Partition α)} (h : Ps.Pairwise Agree)
    (hP : P ∈ Ps) : P ⊆ ofSetPairwiseAgree Ps h := by
  change P.parts ⊆ (ofSetPairwiseAgree Ps h).parts
  simp only [ofSetPairwiseAgree_parts]
  exact subset_biUnion_of_mem hP

end RestrictFrame
