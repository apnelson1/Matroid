import Matroid.ForMathlib.Partition.Basic
import Mathlib.Data.Set.Lattice.Image

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
  have : ∀ t ∈ P, a ⊓ t = t := fun t htP ↦ inf_eq_right.mpr <| le_trans (P.le_of_mem htP) h
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
  have hsu : a ⊓ x ≤ b ⊓ x := le_inf (le_trans (inf_le_inf_left a <| P.le_of_mem hxP) <|
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
  refine ⟨?_, fun hS ↦ ⟨P.ne_bot_of_mem hS, S, hPQ hS, inf_eq_right.mpr <| P.le_of_mem hS⟩⟩
  rintro ⟨hne, t, htQ, rfl⟩
  rw [ne_eq, ← disjoint_iff] at hne
  have htP := mem_of_subset_of_not_disjoint hPQ htQ hne
  rwa [inf_eq_right.mpr (P.le_of_mem htP)]

lemma isInducedSubpartition.eq_of_supp_le (hPQ : P ≤ip Q) (hQP : Q.supp ≤ P.supp) : P = Q := by
  rwa [← hPQ, induce_eq_self_iff]

@[simp]
lemma isInducedSubpartition_rfl : P ≤ip P := by
  simp [isInducedSubpartition]

instance : IsRefl (Partition α) isInducedSubpartition where
  refl _ := isInducedSubpartition_rfl

lemma isInducedSubpartition.antisymm (hPQ : P ≤ip Q) (hQP : Q ≤ip P) : P = Q :=
  hPQ.eq_of_supp_le hQP.supp_le

instance : IsAntisymm (Partition α) isInducedSubpartition where
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
  bot_notMem h := P.bot_notMem h.1

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
  bot_notMem h := P.bot_notMem (hs h)

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


def cover (P : Partition α) (a : α) : Partition α :=
  P.restrict {s | s ∈ P.parts ∧ ¬ Disjoint a s} (fun x ↦ by aesop)

@[simp] lemma mem_cover_iff : x ∈ P.cover a ↔ x ∈ P ∧ ¬ Disjoint a x := Iff.rfl

@[simp]
lemma cover_supp : (P.cover a).supp = sSup {s | s ∈ P.parts ∧ ¬ Disjoint a s} := by
  simp [cover, supp]

lemma cover_supp_le : (P.cover a).supp ≤ P.supp := by
  simp +contextual [cover, le_of_mem]

lemma cover_supp_eq_self : P.cover P.supp = P := by
  ext x
  simp only [cover, mem_parts, mem_restrict_iff, mem_setOf_eq, and_iff_left_iff_imp]
  rintro hxP hdisj
  obtain rfl := hdisj.symm.eq_bot_of_le (le_of_mem hxP)
  exact P.bot_notMem hxP

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
  simp +contextual [avoid, le_of_mem]

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

instance : IsRefl (Partition α) Agree where
  refl _ := Agree.rfl

lemma Agree.symm (h : P.Agree Q) : Q.Agree P := by
  obtain ⟨S, hPS, hQS⟩ := h
  exact ⟨S, hQS, hPS⟩

instance : IsSymm (Partition α) Agree where
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
  exact hndisj.mono_left <| P.le_of_mem ha

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

end Restrict

lemma induce_sSup_eq_restrict [Order.Frame α] (P : Partition α) (a : α) :
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


section RestrictDistrib

-- stuff that needs `CompleteDistribLattice α`

variable [CompleteDistribLattice α] {P Q : Partition α}

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
  let R : Partition α := ofIndependent hindep (by simp [P.bot_notMem, Q.bot_notMem])
  use R, subset_union_left, subset_union_right

lemma agree_iff_mem_of_not_disjoint: P.Agree Q ↔ ∀ x ∈ P, ¬ Disjoint Q.supp x → x ∈ Q :=
  ⟨fun ⟨_, hPR, hQR⟩ _ hxP ↦ mem_of_subset_of_not_disjoint hQR (hPR hxP),
    fun h ↦ agree_of_mem_of_not_disjoint h⟩

end RestrictDistrib

section Bind

variable [CompleteDistribLattice α] {P Q R : Partition α} {Qs : ∀ a ∈ P, Partition α}

@[simps] protected def bind (P : Partition α) (Qs : ∀ a ∈ P, Partition α)
    (hQs : ∀ a, (h : a ∈ P) → (Qs a h).supp ≤ a) : Partition α where
  parts := ⋃ a : P, (Qs a a.prop)
  indep := by
    intro b hb
    simp only [mem_iUnion, SetLike.mem_coe, Subtype.exists] at hb
    obtain ⟨a, haP, hba : b ∈ Qs a haP⟩ := hb
    obtain hasupp := hQs a haP
    have hdj1 := (Qs a haP).indep hba
    have hdj2 := (P.indep haP).mono_left <| ((Qs a haP).le_of_mem hba).trans hasupp
    refine (hdj1.sup_right hdj2).mono_right ?_
    simp only [mem_iUnion, SetLike.mem_coe, Subtype.exists, sSup_le_iff, mem_diff,
      mem_singleton_iff, and_imp, forall_exists_index]
    rintro t' x hx (ht' : t' ∈ Qs x hx) hne
    obtain hxsupp := hQs x hx
    obtain (rfl | hne) := eq_or_ne x a
    · exact (le_sSup_of_le (show t' ∈ _ \ {b} from ⟨ht', hne⟩) rfl.le).trans le_sup_left
    exact le_trans (le_sSup_of_le (mem_diff_of_mem hx hne) <|
      (Qs x hx).le_of_mem ht' |>.trans hxsupp) le_sup_right
  bot_notMem := by
    simp only [mem_iUnion, SetLike.mem_coe, Subtype.exists, not_exists]
    exact fun x hx ↦ (Qs x hx).bot_notMem

@[simp] lemma mem_bind_iff (hQs : ∀ a, (h : a ∈ P) → (Qs a h).supp ≤ a) :
    a ∈ P.bind Qs hQs ↔ ∃ (b : α) (hb : b ∈ P), a ∈ Qs b hb := by
  change _ ∈ ⋃ _, _ ↔ _; simp

lemma mem_bind_of_mem (hQs : ∀ a, (h : a ∈ P) → (Qs a h).supp ≤ a) (hb : b ∈ P) (h : a ∈ Qs b hb) :
    a ∈ P.bind Qs hQs := by
  rw [mem_bind_iff hQs]
  use b, hb

@[simp]
lemma bind_le_iff (hQs : ∀ a, (h : a ∈ P) → (Qs a h).supp ≤ a) :
    P.bind Qs hQs ≤ Q ↔ ∀ a, (h : a ∈ P) → (Qs a h) ≤ Q := by
  simp_rw [le_def, mem_bind_iff hQs, forall_exists_index]
  tauto

@[simp]
lemma bind_le (hQs : ∀ a, (h : a ∈ P) → (Qs a h).supp ≤ a) : P.bind Qs hQs ≤ P := by
  rw [bind_le_iff hQs]
  exact fun a haP ↦ le_of_supp_le_part haP (hQs a haP)

@[simp]
lemma le_bind_iff (hQs : ∀ a, (h : a ∈ P) → (Qs a h).supp ≤ a) :
    Q ≤ P.bind Qs hQs ↔ Q ≤ P ∧ ∀ a, (h : a ∈ P) → Q.induce a ≤ Qs a h := by
  refine ⟨fun h ↦ ⟨h.trans (bind_le hQs), fun a haP b hbQsa ↦ ?_⟩, fun ⟨hQP, h⟩ a haQ ↦ ?_⟩
  · obtain ⟨hcnea, c, hcQ, rfl⟩ := (by simpa using hbQsa); clear hbQsa
    obtain ⟨d, hd, hcd⟩ := h c hcQ
    obtain ⟨e, heP, hdQse⟩ := (by simpa using hd); clear hd
    have hne : ¬Disjoint a e := by
      contrapose! hcnea
      have hce := hcd.trans <| (le_of_mem hdQse).trans <| hQs e heP
      exact disjoint_iff.mp (hcnea.mono_right hce)
    obtain rfl := (P.eq_of_not_disjoint haP heP hne)
    exact ⟨d, hdQse, inf_le_of_right_le hcd⟩
  obtain ⟨p, hpP, hap⟩ := hQP a haQ
  obtain ⟨q, hqQsp, haq⟩ := h p hpP (p ⊓ a) <| inf_mem_induce haQ <| by
    simp [hap, Q.ne_bot_of_mem haQ]
  simp only [hap, inf_of_le_right] at haq
  exact ⟨q, (mem_bind_iff hQs).mpr ⟨p, hpP, hqQsp⟩, haq⟩

end Bind

section Union

variable [CompleteLattice α] {P Q R : Partition α} {P' : ι → Partition α} {S : Set (Partition α)}

@[simps!]
def union (P Q : Partition α) (hPQ : P.Agree Q) : Partition α :=
  hPQ.choose.restrict (P.parts ∪ Q.parts) (union_subset_iff.mpr hPQ.choose_spec)

@[simp]
lemma union_supp (hPQ : P.Agree Q) : (P.union Q hPQ).supp = P.supp ⊔ Q.supp := by
  simp only [supp, union, restrict_parts]
  rw [sSup_union]

protected lemma subset_union_left (hPQ : P.Agree Q) : P ⊆ P.union Q hPQ :=
  fun _ hx ↦ by simp [hx]

protected lemma subset_union_right (hPQ : P.Agree Q) : Q ⊆ P.union Q hPQ :=
  fun _ hx ↦ by simp [hx]

protected lemma union_subset_iff (hPQ : P.Agree Q) : P.union Q hPQ ⊆ R ↔ P ⊆ R ∧ Q ⊆ R := by
  refine ⟨fun h ↦ ⟨subset_trans (Partition.subset_union_left hPQ) h,
    subset_trans (Partition.subset_union_right hPQ) h⟩, fun ⟨hP, hQ⟩ s ↦ ?_⟩
  simp only [union_parts, mem_union, mem_parts]
  exact (Or.elim · (hP ·) (hQ ·))

end Union

section Inter

variable [CompleteLattice α] {P Q R : Partition α}

/-!
# Inter

Partition has 2 different orderings, `⊆` and `≤`.
Due to this, there are 3 different 'intersections' of partitions defined in this file:

- `P ∩ Q` is the maximal partition s.t. `P ∩ Q ⊆ P` and `P ∩ Q ⊆ Q`
- `P.infer Q` is the maximal partition s.t. `P.infer Q ⊆ P` and `P.infer Q ≤ Q`
- `P ⊓ Q` is the maximal partition s.t. `P ⊓ Q ≤ P` and `P ⊓ Q ≤ Q`
-/

protected def sInter (S : Set (Partition α)) (hS : S.Nonempty) : Partition α :=
  hS.some.restrict (⋂₀ (Partition.parts '' S)) (by
    rw [sInter_image]
    exact biInter_subset_of_mem hS.some_mem)

lemma sInter_parts_eq_sInter {S : Set (Partition α)} (hS : S.Nonempty) :
    Partition.sInter S hS = ⋂₀ (Partition.parts '' S) := rfl

@[simp]
lemma sInter_parts {S : Set (Partition α)} (hS : S.Nonempty) :
    Partition.sInter S hS = ⋂ s ∈ S, s.parts := by
  ext a
  simp [sInter_parts_eq_sInter hS]

@[simp]
lemma mem_sInter_iff {S : Set (Partition α)} (hS : S.Nonempty) :
    a ∈ Partition.sInter S hS ↔ ∀ P ∈ S, a ∈ P := by
  simp [Partition.sInter]

lemma sInter_subset {S : Set (Partition α)} (hS : S.Nonempty) (hP : P ∈ S) :
    Partition.sInter S hS ⊆ P := by
  simp only [Partition.sInter, sInter_image]
  exact biInter_subset_of_mem hP

protected lemma subset_sInter_iff {S : Set (Partition α)} (hS : S.Nonempty) {Q : Partition α} :
    Q ⊆ Partition.sInter S hS ↔ ∀ P ∈ S, Q ⊆ P := by
  refine ⟨fun h P hP ↦ h.trans (sInter_subset hS hP), fun h x hx ↦ ?_⟩
  simp only [mem_parts, mem_sInter_iff]
  exact fun P a ↦ h P a hx

@[simp]
lemma sInter_singleton (P : Partition α) :
    Partition.sInter ({P} : Set (Partition α)) ⟨P, by simp⟩ = P := by
  ext a
  simp [mem_sInter_iff]

protected def iInter [Nonempty ι] (f : ι → Partition α) : Partition α :=
  Partition.sInter (range f) (range_nonempty _)

@[simp]
lemma mem_iInter_iff [Nonempty ι] {f : ι → Partition α} :
    a ∈ Partition.iInter f ↔ ∀ i, a ∈ f i := by
  simp [Partition.iInter, mem_sInter_iff]

@[simp]
protected lemma iInter_subset [Nonempty ι] (f : ι → Partition α) (i : ι) :
    Partition.iInter f ⊆ f i := fun _ hx ↦ (mem_iInter_iff.mp hx) i

@[simp]
protected lemma subset_iInter_iff [Nonempty ι] {f : ι → Partition α} {Q : Partition α} :
    Q ⊆ Partition.iInter f ↔ ∀ i, Q ⊆ f i := by
  simp_rw [Partition.iInter, Partition.subset_sInter_iff (range_nonempty f)]
  simp

@[simp]
lemma iInter_const [Nonempty ι] (P : Partition α) : Partition.iInter (fun _ : ι => P) = P := by
  ext a
  simp [mem_iInter_iff]

def inter (P Q : Partition α) : Partition α where
  parts := P.parts ∩ Q.parts
  indep x hx := by
    refine P.indep hx.1 |>.mono_right (sSup_le_sSup ?_)
    simp only [diff_singleton_subset_iff, insert_diff_singleton]
    exact inter_subset_left.trans <| subset_insert x P.parts
  bot_notMem h := P.bot_notMem h.1

instance : Inter (Partition α) where
  inter := inter

@[simp] lemma inter_parts : (P ∩ Q).parts = P.parts ∩ Q.parts := rfl

@[simp] protected lemma mem_inter_iff : a ∈ P ∩ Q ↔ a ∈ P ∧ a ∈ Q := Iff.rfl

protected lemma inter_comm : P ∩ Q = Q ∩ P := by
  ext x
  simp [and_comm]

protected lemma inter_subset_left (P Q : Partition α) : P ∩ Q ⊆ P := fun _ ↦ And.left

protected lemma inter_subset_right (P Q : Partition α) : P ∩ Q ⊆ Q := fun _ ↦ And.right

protected lemma subset_inter_iff {R P Q : Partition α} : R ⊆ P ∩ Q ↔ R ⊆ P ∧ R ⊆ Q :=
  ⟨fun h ↦ ⟨h.trans (P.inter_subset_left Q), h.trans (P.inter_subset_right Q)⟩,
    fun ⟨hP, hQ⟩ _ hx ↦ ⟨hP hx, hQ hx⟩⟩

@[simp] protected lemma inter_self (P : Partition α) : P ∩ P = P := by ext; simp

protected lemma inter_assoc (P Q R : Partition α) : (P ∩ Q) ∩ R = P ∩ (Q ∩ R) := by
  ext; simp [and_assoc]

@[simp]
protected lemma sInter_pair (P Q : Partition α) :
    Partition.sInter ({P, Q} : Set (Partition α)) ⟨P, by simp⟩ = P ∩ Q := by
  ext a
  simp [mem_sInter_iff]


@[simps!]
def infer (P Q : Partition α) : Partition α :=
  P.restrict {a | a ∈ P ∧ ∃ x ∈ Q, a ≤ x} (by
    rintro a ⟨haP, t, htQ, hta⟩
    simp [haP])

-- not associative or commutative

@[simp] lemma mem_infer_iff : a ∈ infer P Q ↔ a ∈ P ∧ ∃ x ∈ Q, a ≤ x := Iff.rfl

@[simp]
lemma infer_subset : infer P Q ⊆ P := by
  rintro a ⟨haP, t, htQ, hta⟩
  simp [haP]

@[simp]
lemma infer_le : infer P Q ≤ Q := by
  rintro a ⟨haP, t, htQ, hta⟩
  use t

@[simp]
lemma subset_infer_iff : R ⊆ infer P Q ↔ R ⊆ P ∧ R ≤ Q :=
  ⟨fun h => ⟨h.trans infer_subset, (le_of_subset h).trans infer_le⟩,
    fun ⟨hP, hQ⟩ a haR => ⟨hP haR, hQ a haR⟩⟩

@[simp]
lemma infer_subset_induce : infer P Q ⊆ P.induce Q.supp := by
  rintro a ⟨haP, t, htQ, hta⟩
  simp only [induce_parts, mem_diff, mem_image, mem_parts, mem_singleton_iff, P.ne_bot_of_mem haP,
    not_false_eq_true, and_true]
  exact ⟨a, haP, inf_eq_right.mpr <| le_trans hta <| le_of_mem htQ⟩

@[simp]
lemma inter_subset_infer : P ∩ Q ⊆ infer P Q := by
  rintro a ⟨haP, haQ⟩
  rw [infer_parts]
  use haP, a, haQ, le_rfl

end Inter

section Inf

/-!
# Inf

Unlike other two operations, `inf` requires `CompleteDistribLattice α` assumption.
-/

variable [CompleteDistribLattice α] {P Q R : Partition α}

def inf (P Q : Partition α) : Partition α :=
  Partition.bind P (fun a haP ↦ Q.induce a) (by simp)

instance : SemilatticeInf (Partition α) where
  inf := inf
  inf_le_left P Q := bind_le (by simp)
  inf_le_right P Q := by
    rw [inf, bind_le_iff (by simp)]
    intro a haP
    simp
  le_inf P Q R hPQ hPR := by
    rw [inf, le_bind_iff (by simp)]
    exact ⟨hPQ, fun a haQ ↦ induce_le_induce_left hPR⟩

@[simp]
lemma inf_parts : (P ⊓ Q) = {x | x ≠ ⊥ ∧ ∃ a ∈ P, ∃ b ∈ Q, a ⊓ b = x} := by
  change (P.bind _ _).parts = _
  ext x
  simp

lemma inf_parts_eq_biUnion : (P ⊓ Q) = (⋃ a ∈ P, ⋃ b ∈ Q, {a ⊓ b}) \ {⊥} := by
  rw [inf_parts]
  ext x
  simp [and_comm, eq_comm]

@[simp]
lemma mem_inf_iff : x ∈ P ⊓ Q ↔ x ≠ ⊥ ∧ ∃ a ∈ P, ∃ b ∈ Q, a ⊓ b = x := by
  change _ ∈ (P.bind _ _).parts ↔ _
  simp

end Inf
