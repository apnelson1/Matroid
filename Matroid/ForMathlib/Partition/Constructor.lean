import Matroid.ForMathlib.Partition.Set

open Set Function Relation

variable {α β ι ι' : Type*} {r : α → α → Prop} {f : ι → α} {a b c x y z : α} {A B : Set α}



lemma Set.left_nonempty_of_not_disjoint {s t : Set α} (h : ¬ Disjoint s t) : s.Nonempty := by
  obtain ⟨u, hu, hsu⟩ := not_disjoint_iff.mp h
  use u

lemma Set.right_nonempty_of_not_disjoint {s t : Set α} (h : ¬ Disjoint s t) : t.Nonempty := by
  obtain ⟨u, hu, htu⟩ := not_disjoint_iff.mp h
  use u

lemma left_ne_bot_of_not_disjoint {s t : α} [PartialOrder α] [OrderBot α] (h : ¬ Disjoint s t) :
    s ≠ ⊥ := by
  by_contra hne
  exact h (by simp [hne])

lemma right_ne_bot_of_not_disjoint {s t : α} [PartialOrder α] [OrderBot α] (h : ¬ Disjoint s t) :
    t ≠ ⊥ := by
  by_contra hne
  exact h (by simp [hne])

namespace Partition

section Pair

variable [CompleteLattice α] {a b : α}

@[simps]
noncomputable def pair (a b : α) : Partition α where
  parts :=
    let : Decidable (¬ Disjoint a b) := Classical.dec _
    if ¬ Disjoint a b then {a ⊔ b} else {a, b} \ {⊥}
  indep x := by
    split_ifs with h
    · simp only [mem_diff, mem_insert_iff, mem_singleton_iff, and_imp]
      rw [diff_diff_comm]
      rintro (rfl | rfl) hbot
      · simpa [h.ne hbot]
      · simp [(h.symm.ne hbot).symm, h.symm]
    · rintro rfl
      simp
  bot_not_mem h := by
    split_ifs at h with H
    · simp at h
    · refine H ?_
      rw [disjoint_iff, eq_bot_iff, h]
      exact inf_left_le_sup_left

@[simp]
lemma pair_parts_of_not_disjoint (h : ¬ Disjoint a b) : (pair a b).parts = {a ⊔ b} := by
  simp [pair, h]

@[simp]
lemma mem_pair_iff_of_not_disjoint (h : ¬ Disjoint a b) : c ∈ pair a b ↔ c = a ⊔ b := by
  rw [← mem_parts, pair_parts_of_not_disjoint h, mem_singleton_iff]

@[simp]
lemma pair_parts_of_disjoint (h : Disjoint a b) : (pair a b).parts = {a, b} \ {⊥} := by
  simp [pair, h]

@[simp]
lemma mem_pair_iff_of_disjoint (h : Disjoint a b) : c ∈ pair a b ↔ (c = a ∨ c = b) ∧ c ≠ ⊥ := by
  rw [← mem_parts, pair_parts_of_disjoint h]
  simp

@[simp]
lemma pair_parts_eq_pair_iff_isPartition : IsPartition {a, b} ↔ (pair a b).parts = {a, b} := by
  refine ⟨fun h ↦ ?_, fun _ ↦ by use pair a b⟩
  have habot := h.ne_bot_of_mem (by simp : a ∈ _)
  have hbbot := h.ne_bot_of_mem (by simp : b ∈ _)
  by_cases hab : a = b
  · simp [hbbot, hab]
  rw [pair_parts_of_disjoint <| h.disjoint (by simp) (by simp) hab]
  simp [habot.symm, hbbot]

@[simp]
lemma pair_supp : (pair a b).supp = a ⊔ b := by
  simp only [supp, pair, Classical.ite_not]
  split_ifs with h <;> simp

lemma pair_comm : pair a b = pair b a := by
  ext x
  simp only [← mem_parts, pair_parts, Classical.ite_not]
  rw [Set.pair_comm, sup_comm, disjoint_comm]

@[simp]
lemma indiscrete'_le_left (a b : α) : indiscrete' a ≤ pair a b := by
  rintro x
  simp only [mem_indiscrete'_iff, ne_eq, and_imp]
  rintro habot rfl
  by_cases hab : Disjoint x b
  · use x
    simpa [← mem_parts, hab]
  simp [← mem_parts, hab]

@[simp]
lemma indiscrete'_le_right (a b : α) : indiscrete' b ≤ pair a b := by
  rintro x
  simp only [mem_indiscrete'_iff, ne_eq, and_imp]
  rintro habot rfl
  by_cases hab : Disjoint a x
  · use x
    simpa [← mem_parts, hab]
  simp [← mem_parts, hab]

@[simp↓]
lemma pair_self_eq_indiscrete' (a : α) : pair a a = indiscrete' a := by
  apply le_antisymm ?_ (indiscrete'_le_left a a)
  intro x
  by_cases h : Disjoint a a
  · rw [mem_pair_iff_of_disjoint h]
    simp +contextual
  rw [mem_pair_iff_of_not_disjoint h]
  simp_all +contextual

lemma pair_parts_nontrivial_iff :
    (pair a b).parts.Nontrivial ↔ IsPartition {a, b} ∧ a ≠ b := by
  rw [pair_parts_eq_pair_iff_isPartition]
  refine ⟨fun ⟨x, hx, y, hy, hne⟩ ↦ ?_, fun ⟨h, hne⟩ ↦ ⟨a, h ▸ (by simp), b, h ▸ (by simp), hne⟩⟩
  obtain (hab | hab) := (em <| Disjoint a b).symm
  · simp_all
  simp only [pair_parts, hab, not_true_eq_false, ↓reduceIte, mem_diff, mem_insert_iff,
    mem_singleton_iff, sdiff_eq_left, disjoint_singleton_right, not_or, ← ne_eq] at hx hy ⊢
  obtain ⟨(rfl | rfl), hx⟩ := hx <;> obtain ⟨(rfl | rfl), hy⟩ := hy <;>
    simp [hx.symm, hy.symm, hne, hne.symm] <;> simp at hne

noncomputable def pairLeft (a b : α) : α :=
  have : Decidable (Disjoint a b) := Classical.dec _
  if Disjoint a b then a else a ⊔ b

@[simp]
lemma pairLeft_bot : pairLeft ⊥ b = ⊥ := by
  simp [pairLeft]

@[simp]
lemma pairLeft_mem_of_not_bot (ha : a ≠ ⊥) : pairLeft a b ∈ pair a b := by
  by_cases hab : Disjoint a b
  · simpa [pairLeft, hab]
  · simp [pairLeft, hab]

@[simp]
lemma left_le_pairLeft : a ≤ pairLeft a b := by
  by_cases hab : Disjoint a b <;>simp [pairLeft, hab]

@[simp]
lemma pairLeft_eq_sup_of_not_disjoint (hab : ¬ Disjoint a b) : pairLeft a b = a ⊔ b := by
  rw [← mem_singleton_iff, ← pair_parts_of_not_disjoint hab]
  exact pairLeft_mem_of_not_bot (left_ne_bot_of_not_disjoint hab)

@[simp]
lemma pairLeft_eq_left_of_disjoint (hab : Disjoint a b) : pairLeft a b = a := by
  simp [pairLeft, hab]

@[simp]
lemma IsPartition.pairLeft_eq_left (h : IsPartition {a, b}) : pairLeft a b = a := by
  rw [isPartition_pair_iff] at h
  obtain ⟨rfl | hxy, ha, hb⟩ := h
  · simp [pairLeft]
  exact pairLeft_eq_left_of_disjoint hxy

@[simp]
lemma pairLeft_self : pairLeft a a = a := by
  simp [pairLeft]

noncomputable def pairRight (a b : α) : α := pairLeft b a

@[simp]
lemma pairRight_bot : pairRight a ⊥ = ⊥ := pairLeft_bot

@[simp]
lemma pairRight_mem_of_not_bot (hb : b ≠ ⊥) : pairRight a b ∈ pair a b := by
  rw [pair_comm]
  exact pairLeft_mem_of_not_bot hb

@[simp]
lemma right_le_pairRight : b ≤ pairRight a b := left_le_pairLeft

@[simp]
lemma pairRight_eq_sup_of_not_disjoint (hab : ¬ Disjoint a b) : pairRight a b = a ⊔ b := by
  rw [← mem_singleton_iff, ← pair_parts_of_not_disjoint hab]
  exact pairRight_mem_of_not_bot (right_ne_bot_of_not_disjoint hab)

@[simp]
lemma pairRight_eq_right_of_disjoint (hab : Disjoint a b) : pairRight a b = b := by
  simp [pairRight, pairLeft, hab.symm]

@[simp]
lemma IsPartition.pairRight_eq_right (h : IsPartition {a, b}) : pairRight a b = b := by
  rw [isPartition_pair_iff] at h
  obtain ⟨rfl | hxy, ha, hb⟩ := h
  · simp [pairRight, pairLeft]
  exact pairRight_eq_right_of_disjoint hxy

@[simp]
lemma pairRight_self : pairRight a a = a := by
  simp [pairRight]

end Pair

section Bind

variable [Order.Frame α] {P Q R : Partition α} {Qs : ∀ a ∈ P, Partition α}

@[simps] protected def bind (P : Partition α) (Qs : ∀ a ∈ P, Partition α)
    (hQs : ∀ a, (h : a ∈ P) → (Qs a h).supp ≤ a) : Partition α where
  parts := ⋃ a : P, (Qs a a.prop).parts
  indep := by
    intro b hb
    simp only [mem_iUnion, Subtype.exists] at hb
    obtain ⟨a, haP, hba : b ∈ Qs a haP⟩ := hb
    obtain hasupp := hQs a haP
    have hdj1 := (Qs a haP).indep hba
    have hdj2 := (P.indep haP).mono_left <| ((Qs a haP).le_supp_of_mem hba).trans hasupp
    refine (hdj1.sup_right hdj2).mono_right ?_
    simp only [mem_iUnion, Subtype.exists, sSup_le_iff, mem_diff,
      mem_singleton_iff, and_imp, forall_exists_index]
    rintro t' x hx (ht' : t' ∈ Qs x hx) hne
    obtain hxsupp := hQs x hx
    obtain (rfl | hne) := eq_or_ne x a
    · exact (le_sSup_of_le (show t' ∈ _ \ {b} from ⟨ht', hne⟩) rfl.le).trans le_sup_left
    exact le_trans (le_sSup_of_le (mem_diff_of_mem hx hne) <|
      (Qs x hx).le_supp_of_mem ht' |>.trans hxsupp) le_sup_right
  bot_not_mem := by
    simp only [mem_iUnion, Subtype.exists, not_exists]
    exact fun x hx ↦ (Qs x hx).bot_not_mem

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
      have hce := hcd.trans <| (le_supp_of_mem hdQse).trans <| hQs e heP
      exact disjoint_iff.mp (hcnea.mono_right hce)
    obtain rfl := (P.eq_of_not_disjoint haP heP hne)
    exact ⟨d, hdQse, inf_le_of_right_le hcd⟩
  obtain ⟨p, hpP, hap⟩ := hQP a haQ
  obtain ⟨q, hqQsp, haq⟩ := h p hpP (p ⊓ a) <| inf_mem_induce haQ <| by
    simp [hap, Q.ne_bot_of_mem haQ]
  simp only [hap, inf_of_le_right] at haq
  exact ⟨q, (mem_bind_iff hQs).mpr ⟨p, hpP, hqQsp⟩, haq⟩

end Bind

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
lemma iInter_parts [Nonempty ι] (f : ι → Partition α) :
    (Partition.iInter f).parts = ⋂ i, (f i).parts := by
  rw [← Partition.coe_eq]
  simp [Partition.iInter]

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
  bot_not_mem h := P.bot_not_mem h.1

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
  exact ⟨a, haP, inf_eq_right.mpr <| le_trans hta <| le_supp_of_mem htQ⟩

@[simp]
lemma inter_subset_infer : P ∩ Q ⊆ infer P Q := by
  rintro a ⟨haP, haQ⟩
  rw [infer_parts]
  use haP, a, haQ, le_rfl

end Inter

@[simp]
lemma inter_rel (P Q : Partition (Set α)) : ⇑(P ∩ Q) = fun x y ↦ ∃ s ∈ P ∩ Q, x ∈ s ∧ y ∈ s := by
  ext x y
  rw [rel_iff_exists]

@[simp]
lemma infer_rel (P Q : Partition (Set α)) :
    ⇑(P.infer Q) = fun x y ↦ ∃ t ∈ P, x ∈ t ∧ y ∈ t ∧ ∃ x ∈ Q, t ⊆ x := by
  ext x y
  rw [rel_iff_exists]
  simp only [mem_infer_iff, le_eq_subset]
  tauto

section Inf

/-!
# Inf

Unlike other two operations, `inf` requires `Order.Frame α` assumption.
-/

variable [Order.Frame α] {P Q R : Partition α}

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
lemma inf_parts : (P ⊓ Q) = {x | (∃ a ∈ P, ∃ b ∈ Q, a ⊓ b = x) ∧ x ≠ ⊥} := by
  change (P.bind _ _).parts = _
  ext x
  simp

lemma inf_parts_eq_biUnion : (P ⊓ Q) = (⋃ a ∈ P, ⋃ b ∈ Q, {a ⊓ b}) \ {⊥} := by
  rw [inf_parts]
  ext x
  simp [and_comm, eq_comm]

@[simp]
lemma mem_inf_iff : x ∈ P ⊓ Q ↔ (∃ a ∈ P, ∃ b ∈ Q, a ⊓ b = x) ∧ x ≠ ⊥ := by
  change _ ∈ (P.bind _ _).parts ↔ _
  simp

def sInf' (P : Set (Partition α)) : Partition α :=
  ofIndependent (u := iInf '' (Set.pi univ (fun p : P => p.val.parts)) \ {⊥}) (by
    rintro _ ⟨⟨f, hf, rfl⟩, hne⟩
    simp only [mem_pi, mem_univ, mem_parts, forall_const, Subtype.forall,
      mem_singleton_iff] at hf hne
    rw [disjoint_sSup_iff]
    rintro _ ⟨⟨⟨g, hg, rfl⟩, hng⟩, hgf⟩
    simp only [mem_pi, mem_univ, mem_parts, forall_const, Subtype.forall,
      mem_singleton_iff, ← ne_eq] at hg hng hgf
    have hfg : f ≠ g := by
      rintro rfl
      simp at hgf
    contrapose! hfg
    ext P₁
    specialize hf P₁ P₁.prop
    specialize hg P₁ P₁.prop
    refine P₁.val.eq_of_not_disjoint hf hg ?_
    contrapose! hfg
    exact hfg.mono (iInf_le_iff.mpr fun b a ↦ a P₁) (iInf_le_iff.mpr fun b a ↦ a P₁))
    (notMem_diff_of_mem rfl)

lemma exists_mem_sInf'_iff {Ps : Set (Partition α)} {q : α → Prop} :
    (∃ a ∈ sInf' Ps, q a) ↔ ∃ f, iInf f ≠ ⊥ ∧ (∀ p : Ps, f p ∈ p.val) ∧ q (iInf f) := by
  simp only [sInf', mem_ofIndependent_iff, mem_diff, mem_image, mem_pi, mem_univ, mem_parts,
    forall_const, Subtype.forall, mem_singleton_iff, and_assoc, exists_exists_and_eq_and, ne_eq]
  tauto

@[simp]
lemma sInf'_empty : sInf' ∅ = (⊤ : Partition α) := by
  apply Partition.ext fun a ↦ ?_
  simp only [sInf', mem_ofIndependent_iff, mem_diff, mem_image, mem_pi, mem_univ, mem_parts,
    forall_const, IsEmpty.forall_iff, true_and, mem_singleton_iff, mem_top_iff, ne_eq,
    and_congr_left_iff]
  intro ha
  simp_rw [iInf_of_empty]
  simp [eq_comm]

lemma le_sInf' {Ps : Set (Partition α)} (Q : Partition α) (h : ∀ P ∈ Ps, Q ≤ P) : Q ≤ sInf' Ps := by
  intro a haQ
  simp_rw [exists_mem_sInf'_iff, le_iInf_iff]
  refine ⟨fun P ↦ (h P P.prop a haQ).choose, ne_bot_of_le_ne_bot (Q.ne_bot_of_mem haQ) ?_,
    forall_and.mp <| fun P : Ps ↦ (h P P.prop a haQ).choose_spec⟩
  simp [fun P hP ↦ (h P hP a haQ).choose_spec.2]

lemma sInf'_le {Ps : Set (Partition α)} (P : Partition α) (hP : P ∈ Ps) : sInf' Ps ≤ P := by
  intro a haPs
  obtain ⟨⟨f, hf, rfl⟩, habot⟩ := by simpa only [sInf', mem_ofIndependent_iff, mem_diff, mem_pi,
    mem_image, mem_univ, mem_parts, forall_const, Subtype.forall, mem_singleton_iff] using haPs
  use f ⟨P, hP⟩, hf P hP, iInf_le_iff.mpr fun b a ↦ a ⟨P, hP⟩

end Inf

section disjParts
variable [CompleteLattice α] {P Q R : Partition α} {S T s t : Set α} {Ps : Set (Partition α)}

theorem eq_of_le_not_disjoint {x r : α} (hx : x ∈ R) (hxs : b ≤ x) (hr : r ∈ R) (hrs : c ≤ r)
    (hndisj : ¬Disjoint b c) : r = x := by
  refine R.eq_of_not_disjoint hr hx ?_
  contrapose! hndisj
  exact hndisj.symm.mono hxs hrs

def disjParts (S : Set α) : Partition (Set α) :=
  let A : Std.Symm α ((¬ Disjoint · ·) : α → α → Prop) := by
    refine ⟨fun x y h => ?_⟩
    contrapose! h
    exact h.symm
  ofRel (Relation.TransClosure <| Relation.restrict ((¬ Disjoint · ·) : α → α → Prop) S)

@[simp]
lemma sUnion_disjParts : ⋃₀ (disjParts S).parts = S \ {⊥} := by
  ext a
  simp +contextual only [disjParts, ofRel_parts, sUnion_fibers, transClosure_domain, mem_domain_iff,
    Relation.restrict, mem_diff, mem_singleton_iff, iff_def, forall_exists_index, true_and, and_imp]
  refine ⟨fun _ hdj _ _ => left_ne_bot_of_not_disjoint hdj, fun _ hbot => ?_⟩
  use a, ?_
  rwa [disjoint_self]

@[simp]
lemma disjParts_supp : (disjParts S).supp = S \ {⊥} := by
  rw [supp, sSup_eq_sUnion, sUnion_disjParts]

lemma mem_union_of_mem_mem_disjParts (hS : s ∈ disjParts S) (ha : a ∈ s) : a ∈ S := by
  suffices a ∈ S \ {⊥} by exact this.1
  rw [← sUnion_disjParts]
  use s, hS

lemma ne_bot_of_mem_mem_disjParts (hS : s ∈ disjParts S) (ha : a ∈ s) : a ≠ ⊥ := by
  suffices a ∈ S \ {⊥} by exact this.2
  rw [← sUnion_disjParts]
  use s, hS

@[simp]
lemma disjParts_empty : disjParts ∅ = (⊥ : Partition (Set α)) := by
  rw [← supp_eq_bot_iff, disjParts_supp]
  simp

@[simp]
lemma disjParts_singleton (h : a ≠ ⊥) : disjParts {a} = Partition.indiscrete {a} (by simp) := by
  ext x y
  simp only [disjParts, rel_ofRel_eq, indiscrete_rel, mem_singleton_iff]
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨_, _, rfl, _⟩ := Relation.transClosure_exists_single_head _ h
    obtain ⟨_, _, _, rfl⟩ := Relation.transClosure_exists_single_tail _ h
    tauto
  rintro ⟨rfl, rfl⟩
  apply Relation.TransGen.single
  simpa [Relation.restrict]

@[simp]
lemma disjParts_singleton_bot : disjParts {⊥} = (⊥ : Partition (Set α)) := by
  rw [← supp_eq_bot_iff, disjParts_supp]
  simp

@[simp]
lemma disjParts_insert_bot (S : Set α) : disjParts (insert ⊥ S) = disjParts S := by
  suffices Relation.restrict (fun x1 x2 ↦ ¬Disjoint x1 x2) (insert ⊥ S) =
    Relation.restrict (fun x1 x2 ↦ ¬Disjoint x1 x2) S by
    refine eq_of_rel_iff_rel ?_
    simp only [disjParts, this, rel_ofRel_eq, implies_true]
  ext x y
  simp only [Relation.restrict, mem_insert_iff, and_congr_right_iff]
  intro h
  simp [left_ne_bot_of_not_disjoint h, right_ne_bot_of_not_disjoint h]

@[simp]
lemma disjParts_diff_singleton_bot (S : Set α) : disjParts (S \ {⊥}) = disjParts S := by
  rw [← disjParts_insert_bot, insert_diff_singleton, disjParts_insert_bot]

lemma disjParts_indiscrete_of_top_mem [Nontrivial α] (h : ⊤ ∈ S) :
    disjParts S = indiscrete (S \ {⊥}) (Nonempty.ne_empty ⟨⊤, h, by simp⟩) := by
  ext x y
  simp only [disjParts, rel_ofRel_eq, indiscrete_rel]
  refine ⟨fun h => ?_, fun ⟨⟨hx, hxbot⟩, ⟨hy, hybot⟩⟩ => ?_⟩
  · obtain ⟨_, hxd, hx, -⟩ := Relation.transClosure_exists_single_head _ h
    obtain ⟨_, hyd, -, hy⟩ := Relation.transClosure_exists_single_tail _ h
    exact ⟨⟨hx, left_ne_bot_of_not_disjoint hxd⟩, ⟨hy, right_ne_bot_of_not_disjoint hyd⟩⟩
  apply Relation.TransGen.trans (b := ⊤) <;> apply Relation.TransGen.single
  · use (by simpa), hx, h
  · use (by simpa), h, hy

@[simp]
lemma disjParts_indiscrete'_of_top_mem  (h : ⊤ ∈ S) : disjParts S = indiscrete' (S \ {⊥}) := by
  ext x y
  simp only [disjParts, rel_ofRel_eq, indiscrete'_rel]
  refine ⟨fun h => ?_, fun ⟨⟨hx, hxbot⟩, ⟨hy, hybot⟩⟩ => ?_⟩
  · obtain ⟨_, hxd, hx, -⟩ := Relation.transClosure_exists_single_head _ h
    obtain ⟨_, hyd, -, hy⟩ := Relation.transClosure_exists_single_tail _ h
    exact ⟨⟨hx, left_ne_bot_of_not_disjoint hxd⟩, ⟨hy, right_ne_bot_of_not_disjoint hyd⟩⟩
  apply Relation.TransGen.trans (b := ⊤) <;> apply Relation.TransGen.single
  · use (by simpa), hx, h
  · use (by simpa), h, hy

lemma disjParts_eq_sUnion_of_agree (hPs : Ps.Pairwise Agree) :
    (disjParts (⋃ a ∈ Ps, a.parts)).parts = Set.singleton '' ⋃ a ∈ Ps, a.parts := by
  ext S
  have hr : Relation.restrict (¬Disjoint · ·) (⋃ a ∈ Ps, a.parts) ≤ (· = ·) := by
    rintro x y ⟨hxy, hx, hy⟩
    simp only [mem_iUnion, mem_parts, exists_prop] at hx hy
    obtain ⟨Px, hPx, hxPx⟩ := hx
    obtain ⟨Py, hPy, hyPy⟩ := hy
    exact (hPs.of_refl hPx hPy).eq_of_not_disjoint hxPx hyPy hxy
  simp only [disjParts, transClosure_eq_self_of_le_eq hr, ofRel_parts, mem_fibers_iff,
    mem_codomain_iff, Relation.restrict, mem_iUnion, mem_parts, exists_prop, fiber, Set.singleton,
    setOf_eq_eq_singleton, mem_image]
  refine exists_congr fun a => ?_
  have h1 : (∃ a_1, ¬Disjoint a_1 a ∧ (∃ i ∈ Ps, a_1 ∈ i) ∧ ∃ i ∈ Ps, a ∈ i) ↔ ∃ i ∈ Ps, a ∈ i := by
    refine ⟨fun ⟨b, hba, hb, ha⟩ => ha, fun h => ⟨a, ?_, h, h⟩⟩
    simp [h.choose.ne_bot_of_mem h.choose_spec.2]
  rw [h1]
  refine and_congr_right fun ha ↦ Eq.congr ?_ rfl
  simp only [ha, and_true, Set.ext_iff, mem_setOf_eq, mem_singleton_iff]
  obtain ⟨Pa, hPa, haPa⟩ := ha
  refine fun b => ⟨fun ⟨hba, Pb, hPb, hbPb⟩ => (hPs.of_refl hPb hPa).eq_of_not_disjoint hbPb haPa
    hba, ?_⟩
  rintro rfl
  simp only [disjoint_self, Pa.ne_bot_of_mem haPa, not_false_eq_true, true_and]
  use Pa

lemma singleton_mem_disjParts_iff :
    {a} ∈ disjParts S ↔ ∀ b, (¬Disjoint b a ∧ b ∈ S ∧ a ∈ S ↔ b = a) := by
  rw [← eq_partOf_iff_mem (show a ∈ {a} by rfl), eq_comm]
  simp only [partOf, fiber, disjParts, rel_ofRel_eq, Set.ext_iff, mem_setOf_eq, mem_singleton_iff]
  refine ⟨fun h b => ⟨fun hab => ?_, ?_⟩, fun h b => ⟨fun hba => ?_, ?_⟩⟩
  · exact (h _).mp (Relation.TransGen.single hab)
  · rintro rfl
    obtain ⟨c, hbc, hb, -⟩ := transClosure_exists_single_head _ ((h b).mpr rfl)
    simp [hb, left_ne_bot_of_not_disjoint hbc]
  · induction hba with
  | single hbb => exact (h _).mp hbb
  | tail _ h2 IH =>
    obtain rfl := (h _).mp h2
    exact IH h
  · rintro rfl
    obtain ⟨hbb, hb, -⟩ := (h b).mpr rfl
    apply Relation.TransGen.single
    use hbb

lemma sSup_le_of_mem_disjParts (h : ∀ s ∈ S, ∃ p ∈ P, s ≤ p) (hs : s ∈ disjParts S) (has : a ∈ s)
    (hbP : b ∈ P) (hab : a ≤ b) : sSup s ≤ b := by
  rw [sSup_le_iff]
  rintro c hcs
  have hac : (disjParts S) a c := by use s
  simp only [disjParts, rel_ofRel_eq] at hac
  induction hac with
  | single =>
    rename_i x hxc'
    obtain ⟨hndisj, -, -⟩ := hxc'
    obtain ⟨c', hc'P, hcc'⟩ := h _ <| mem_union_of_mem_mem_disjParts hs hcs
    convert hcc'
    apply eq_of_le_not_disjoint hc'P hcc' hbP hab
    exact fun A ↦ hndisj A.symm
  | tail =>
    rename_i x y hax hxy IH
    have Hax : (disjParts S) a x := by simpa [disjParts]
    have := Hax.forall hs |>.mp has
    obtain ⟨hndisj, hxS, -⟩ := hxy
    obtain ⟨c', hc'P, hcc'⟩ := h _ <| mem_union_of_mem_mem_disjParts hs hcs
    convert hcc'
    apply eq_of_le_not_disjoint hc'P hcc' hbP (IH this)
    exact fun A ↦ hndisj A.symm

end disjParts

section Sup

variable [Order.Frame α] {P Q R : Partition α} {P' : ι → Partition α} {Ps Qs : Set (Partition α)}
  {S T s t : Set α}

lemma sSup_injOn_disjParts : InjOn sSup (disjParts S).parts := by
  rintro s hs t ht hst
  have hSne := (disjParts S).nonempty_of_mem hs
  have hndisj : ¬ Disjoint (sSup s) (sSup t) := by
    rw [← hst, disjoint_self]
    exact ne_bot_of_le_ne_bot (ne_bot_of_mem_mem_disjParts hs hSne.some_mem) (le_sSup hSne.some_mem)
  obtain ⟨b, hbT, hndisj⟩ := by simpa [disjoint_sSup_iff] using hndisj
  obtain ⟨a, haS, hndisj⟩ := by simpa [disjoint_comm, disjoint_sSup_iff] using hndisj
  refine (disjParts S).eq_of_mem_of_mem hs ht haS <| Rel.forall ?_ ht |>.mp hbT
  simp only [disjParts, rel_ofRel_eq]
  exact TransGen.single ⟨hndisj, mem_union_of_mem_mem_disjParts ht hbT,
    mem_union_of_mem_mem_disjParts hs haS⟩

@[simps]
def sSup' (Ps : Set (Partition α)) : Partition α where
  parts := sSup '' (disjParts (⋃ a ∈ Ps, a.parts)).parts
  indep := by
    rintro _ ⟨S, hS, rfl⟩
    rw [← image_singleton, ← image_diff_of_injOn (sSup_injOn_disjParts) (by simpa),
      sSup_disjoint_iff]
    rintro a haS
    rw [disjoint_comm, sSup_disjoint_iff]
    rintro b ⟨s, ⟨hs, hsS⟩, rfl⟩
    refine sSup_disjoint_iff.mpr fun c hcs => ?_
    contrapose! hsS
    refine (disjParts (⋃ a ∈ Ps, a.parts)).eq_of_mem_of_mem hs hS hcs <| (Rel.forall ?_ hS).mpr haS
    simp only [disjParts, rel_ofRel_eq]
    refine TransGen.single ⟨hsS, ?_, ?_⟩
    · exact mem_union_of_mem_mem_disjParts hs hcs
    · exact mem_union_of_mem_mem_disjParts hS haS
  bot_not_mem := by
    rintro ⟨a, haS, heq⟩
    have hSne := (disjParts (⋃ a ∈ Ps, a.parts)).nonempty_of_mem haS
    rw [sSup_eq_bot] at heq
    exact (ne_bot_of_mem_mem_disjParts haS hSne.some_mem) <| heq hSne.some hSne.some_mem

lemma le_sSup' {Ps : Set (Partition α)} (P : Partition α) (hP : P ∈ Ps) : P ≤ sSup' Ps := by
  rintro a haP
  by_cases habot : a = ⊥
  · exact (P.bot_not_mem <| habot ▸ haP).elim
  have : a ∈ ⋃₀ (disjParts (⋃ a ∈ Ps, a.parts)).parts := by
    rw [sUnion_disjParts]
    simp only [mem_diff, mem_iUnion, mem_parts, exists_prop, mem_singleton_iff, habot,
      not_false_eq_true, and_true]
    use P
  obtain ⟨S, hS, haS⟩ := by simpa [← sUnion_disjParts] using this
  use sSup S, (by use S, hS), le_sSup haS

lemma sSup'_le {Ps : Set (Partition α)} (P : Partition α) (hP : ∀ b ∈ Ps, b ≤ P) :
    sSup' Ps ≤ P := by
  rintro a haPs
  by_cases habot : a = ⊥
  · subst a
    simp only [bot_le, and_true, exists_mem_iff_ne_bot]
    rintro rfl
    obtain (rfl | rfl) := subset_singleton_iff_eq.mp (show Ps ⊆ {⊥} by simpa using hP)
    <;> simp [sSup', ← mem_parts] at haPs
  obtain ⟨S, hS, rfl⟩ := haPs
  obtain ⟨x, hx⟩ := (disjParts (⋃ a ∈ Ps, a.parts)).nonempty_of_mem hS
  obtain ⟨Q, hQ, hxQ⟩ := by simpa using mem_union_of_mem_mem_disjParts hS hx
  obtain ⟨y, hyP, hxy⟩ := (hP Q hQ) x hxQ
  refine ⟨y, hyP, sSup_le_of_mem_disjParts ?_ hS hx hyP hxy⟩
  simp only [mem_iUnion, mem_parts, exists_prop, forall_exists_index, and_imp]
  exact fun z R hR ↦ hP R hR z

instance : CompleteLattice (Partition α) where
  sInf := sInf'
  sInf_le Ps := sInf'_le
  le_sInf Ps := le_sInf'
  sSup := sSup'
  sSup_le Ps := sSup'_le
  le_sSup Ps := le_sSup'
  sup P Q := sSup' {P, Q}
  le_sup_left P Q := le_sSup' P (by simp)
  le_sup_right P Q := le_sSup' Q (by simp)
  sup_le P Q R hPR hQR := sSup'_le R (by simp; tauto)
  -- inf P Q := sInf' {P, Q}
  -- inf_le_left P Q := sInf'_le P (by simp)
  -- inf_le_right P Q := sInf'_le Q (by simp)
  -- le_inf P Q R hPQ hPR := le_sInf' P (by simp; tauto)

-- not a Frame nor a Coframe

@[simp]
lemma mem_sSup_iff (S : Set (Partition α)) :
    a ∈ sSup S ↔ (∃ s ∈ disjParts (⋃ a ∈ S, a.parts), sSup s = a) := by
  change a ∈ sSup' _ ↔ _
  simp [sSup', ← mem_parts]

@[simp]
lemma mem_iSup_iff (P : ι → Partition α) :
    a ∈ ⨆ i, P i ↔ (∃ s ∈ disjParts (⋃ i, (P i).parts), sSup s = a) := by
  change a ∈ sSup' _ ↔ _
  simp [sSup', ← mem_parts]

@[simp]
lemma mem_sup_iff (P Q : Partition α) :
    a ∈ P ⊔ Q ↔ (∃ x ∈ disjParts (P.parts ∪ Q.parts), sSup x = a) := by
  change a ∈ sSup' _ ↔ _
  simp [sSup', ← mem_parts]

@[simp]
lemma mem_sInf_iff (Ps : Set (Partition α)) :
    a ∈ sInf Ps ↔ (∃ f : Ps → α, (∀ (P : Ps), f P ∈ P.val) ∧ iInf f = a) ∧ a ≠ ⊥ := by
  change a ∈ sInf' _ ↔ _
  simp [sInf', ← mem_parts]

@[simp]
lemma mem_iInf_iff (P : ι → Partition α) :
    a ∈ ⨅ i, P i ↔ (∃ f : ι → α, (∀ i, f i ∈ P i) ∧ iInf f = a) ∧ a ≠ ⊥ := by
  change a ∈ sInf _ ↔ _
  simp only [mem_sInf_iff, Subtype.forall, mem_range, forall_exists_index, ne_eq,
    and_congr_left_iff]
  refine fun habot => ⟨?_, ?_⟩ <;> rintro ⟨f, hf, rfl⟩
  · use fun i => f ⟨P i, by use i⟩, fun i ↦ hf (P i) i rfl,
      rangeFactorization_surjective.iInf_comp f
  · use fun ⟨p, hp⟩ => f hp.choose, fun p i => ?_, ?_
    · rintro rfl
      generalize_proofs h
      simpa [mem_parts, h.choose_spec] using hf h.choose
    change sInf _ = sInf _
    congr
    ext a
    simp only [mem_range, Subtype.exists]
    constructor
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      generalize_proofs h
      use h.choose
    rintro ⟨j, rfl⟩
    use P j, (by use j)
    generalize_proofs h
    refine (P j).eq_of_not_disjoint (by simpa [h.choose_spec] using hf h.choose) (hf j) ?_
    rw [disjoint_iff]
    exact ne_bot_of_le_ne_bot habot <| le_inf (iInf_le f _) (iInf_le f _)

end Sup

variable [Order.Frame α] {s t u : α} {S T : Set α} {P Q : Partition α}

def mk' (S : Set α) : Partition α := ⨆ s ∈ S, Partition.indiscrete' s

lemma mk'_agree (hS : S.PairwiseDisjoint id) : S.Pairwise (Agree on indiscrete') := by
  rintro x hx y hy hxy
  rw [agree_on_indiscrete'_iff]
  right
  exact hS hx hy hxy

lemma IsPartition.mk'_agree (hS : IsPartition S) : S.Pairwise (Agree on indiscrete') := by
  obtain ⟨P, hP⟩ := hS
  exact hP ▸ Partition.mk'_agree P.indep.pairwiseDisjoint

-- @[simp]
-- lemma mk'_parts_bot_not_mem (hS : S.PairwiseDisjoint id) (hSbot : ⊥ ∉ S) :
-- (mk' S).parts = S := by
--   rw [mk', biSup_parts_of_agree (mk'_agree hS)]
--   ext s
--   have : s ∈ S → s ≠ ∅ := (ne_of_mem_of_not_mem · hSbot)
--   simpa

-- @[simp]
-- lemma mk'_parts (hS : S.PairwiseDisjoint id) : (mk' S).parts = S \ {⊥} := by
--   rw [mk', biSup_parts_of_agree (mk'_agree hS)]
--   ext s
--   simp [and_comm]

-- lemma IsPartition.mk'_parts (hS : IsPartition S) : (mk' S).parts = S := by
--   obtain ⟨P, hP⟩ := hS
--   exact hP ▸ mk'_parts_bot_not_mem P.indep.pairwiseDisjoint P.bot_not_mem

-- lemma mk'_parts_iff : (mk' S).parts = S ↔ IsPartition S :=
--   ⟨fun hS ↦ ⟨mk' S, hS⟩, IsPartition.mk'_parts⟩

-- @[simp]
-- lemma mem_mk'_iff (hS : S.PairwiseDisjoint id) : s ∈ mk' S ↔ s ≠ ⊥ ∧ s ∈ S := by
--   rw [← mem_parts, mk'_parts hS]
--   simp [and_comm]

-- @[simp↓]
-- lemma IsPartition.mem_mk'_iff (hS : IsPartition S) : s ∈ mk' S ↔ s ∈ S := by
--   rw [← mem_parts, hS.mk'_parts]

-- lemma mk'_exists_subset_of_mem (hs : s ∈ S) (hs' : s.Nonempty) : ∃ t ∈ mk' S, s ⊆ t := by
--   suffices indiscrete' s ≤ mk' S by exact this s (by simp [hs'.ne_empty])
--   exact le_biSup _ hs

-- lemma mk'_exists_unique_subset_of_mem (hs : s ∈ S) (hs' : s.Nonempty) : ∃! t ∈ mk' S, s ⊆ t := by
--   obtain ⟨t, ht, hst⟩ := mk'_exists_subset_of_mem hs hs'
--   obtain ⟨a, has⟩ := hs'
--   exact ⟨t, ⟨ht, hst⟩, fun u ⟨hu, hsu⟩ => eq_of_mem_of_mem hu ht (hsu has) (hst has)⟩

-- lemma mk'_exists_unique_not_disjoint_of_mem (hs : s ∈ S) (hs' : s.Nonempty) :
--     ∃! t ∈ mk' S, ¬ Disjoint s t := by
--   simp_rw [not_disjoint_iff]
--   obtain ⟨t, ⟨ht'S, hst⟩, heqt⟩ := mk'_exists_unique_subset_of_mem hs hs'
--   exact ⟨t, ⟨ht'S, ⟨hs'.some, hs'.some_mem, hst hs'.some_mem⟩⟩,
--     fun w ⟨hw'S, a, has, haw⟩ => eq_of_mem_of_mem hw'S ht'S haw (hst has)⟩

-- @[simp]
-- lemma mk'_supp : (mk' S).supp = ⋃₀ S := by
--   ext x
--   simp [mk']

lemma indiscrete'_le_mk' (has : s ∈ S) : Partition.indiscrete' s ≤ mk' S :=
  le_biSup indiscrete' has

lemma mk'_mono (hS : S ⊆ T) : mk' S ≤ mk' T :=
  biSup_mono hS

-- lemma exists_subset_parts_iff_nonempty_and_eq_or_disjoint :
--     IsPartition S ↔ ∅ ∉ S ∧ S.PairwiseDisjoint id :=
--   ⟨fun hS ↦ ⟨fun a ↦ hS.bot_not_mem a, hS.pairwiseDisjoint⟩,
--     fun ⟨hS, hSdj⟩ => ⟨ofPairwiseDisjoint hSdj, by simp [hS]⟩⟩

-- lemma exists_parts_eq_pair_iff_nonempty_and_eq_or_disjoint {a b  : Set α} :
--     IsPartition {a, b} ↔ a.Nonempty ∧ b.Nonempty ∧ (a = b ∨ Disjoint a b) := by
--   rw [exists_subset_parts_iff_nonempty_and_eq_or_disjoint, pairwiseDisjoint_pair_iff,
--← and_assoc]
--   exact and_congr_left <| by simp [eq_comm, nonempty_iff_ne_empty]

-- lemma mk'_foo_mem (hs : s ∈ S) (hs' : s.Nonempty) : foo (mk' S) s ∈ mk' S :=
--   foo_mem_of_le (le_biSup _ hs) <| by simp [hs'.ne_empty]

-- @[simp]
-- lemma mk'_foo_mem_iff (hs : s ∈ S) : foo (mk' S) s ∈ mk' S ↔ s.Nonempty := by
--   refine ⟨fun h => ?_, mk'_foo_mem hs⟩
--   by_contra! heq
--   subst s
--   rw [foo_empty] at h
--   exact (mk' S).bot_not_mem h

-- lemma subset_mk'_foo (hs : s ∈ S) (hs' : s.Nonempty) : s ⊆ foo (mk' S) s :=
--   subset_foo_of_le (le_biSup _ hs) <| by simp [hs'.ne_empty]

-- lemma eq_mk'_foo_of_mem (hs : s ∈ S) (ht : t ∈ mk' S) (hst : ¬ Disjoint s t) :
--     foo (mk' S) s = t := by
--   have hs' : s.Nonempty := left_nonempty_of_not_disjoint hst
--   obtain ⟨u, hu, hsu⟩ := mk'_exists_unique_not_disjoint_of_mem hs hs'
--   obtain rfl := hsu t ⟨ht, hst⟩
--   refine hsu (foo (mk' S) s) ⟨mk'_foo_mem hs hs', ?_⟩
--   exact not_disjoint_iff.mpr ⟨hs'.some, hs'.some_mem, subset_mk'_foo hs hs' hs'.some_mem⟩

-- lemma mk'_foo_eq_of_not_disjoint (hs : s ∈ S) (ht : t ∈ S) (hdisj : ¬ Disjoint s t) :
--     foo (mk' S) s = foo (mk' S) t := by
--   have htne : t.Nonempty := right_nonempty_of_not_disjoint hdisj
--   apply eq_mk'_foo_of_mem hs <| mk'_foo_mem ht htne
--   contrapose! hdisj
--   exact hdisj.mono_right <| subset_mk'_foo ht htne

-- @[simp]
-- lemma mk'_singleton (s : Set α) : mk' {s} = Partition.indiscrete' s :=
--   ext fun x => by aesop

-- @[simp]
-- lemma mk'_insert (s : Set α) (S : Set (Set α)) :
--     mk' (insert s S) = mk' S ⊔ Partition.indiscrete' s := by
--   ext x y
--   rw [mk', mk', iSup_insert, sup_comm]

-- lemma foo_mk'_surjOn : SurjOn (foo (mk' S)) S (mk' S).parts := by
--   intro s hs
--   obtain ⟨a, has⟩ := (mk' S).nonempty_of_mem hs
--   obtain ⟨t, htS, hst⟩ := by simpa using le_supp_of_mem hs has
--   use t, htS, eq_mk'_foo_of_mem htS hs (not_disjoint_iff.mpr (by use a))

-- lemma foo_mk'_injOn_iff : S.InjOn (foo (mk' S)) ↔ S.EqOn (foo (mk' S)) id := by
--   refine ⟨fun h s hsS => ?_, fun h s hsS t htS heq => by rwa [h hsS, h htS] at heq⟩
--   apply subset_antisymm ?_
--   · refine self_subset_foo_iff.mpr <| mk'_supp ▸ ?_
--     exact subset_sUnion_of_subset S s subset_rfl hsS
--   by_contra! hsu
--   obtain ⟨a, hafx, hax⟩ := not_subset_iff_exists_mem_notMem.mp hsu; clear hsu
--   obtain (rfl | hsnem) := eq_empty_or_nonempty s
--   · simp at hafx
--   have hsmem := mk'_foo_mem hsS hsnem
--   obtain ⟨t, htS, hzt⟩ := by simpa using le_supp_of_mem hsmem hafx
--   obtain rfl := h hsS htS (eq_mk'_foo_of_mem htS hsmem <| not_disjoint_iff.mpr (by use a)).symm
--   exact hax hzt

-- lemma mk'_pair_nontrivial_iff :
--     (mk' {s, t}).parts.Nontrivial ↔ (mk' {s, t}).parts = {s, t} ∧ s ≠ t := by
--   refine ⟨fun ⟨x, hx, y, hy, hne⟩ => ?_, fun h => h.1.symm ▸ nontrivial_pair h.2⟩
--   obtain ⟨u, huS, rfl⟩ := foo_mk'_surjOn hx
--   obtain ⟨v, hvS, rfl⟩ := foo_mk'_surjOn hy
--   obtain (rfl | rfl) := (by simpa using huS) <;> obtain (rfl | rfl) := by simpa using hvS
--   on_goal 4 => simp at hne
--   on_goal 1 => simp at hne
--   all_goals
--   · rw [mem_parts, mk'_foo_mem_iff (by simp)] at hx hy
--     have hdisj := not_imp_comm.mp (mk'_foo_eq_of_not_disjoint huS hvS) hne
--     refine ⟨(mk'_parts_bot_not_mem (pairwiseDisjoint_pair (by simp [onFun,hdisj, disjoint_comm]))
--       ?_), ?_⟩ <;> simp [hdisj.ne hx.ne_empty, ne_comm, hx.ne_empty.symm, hy.ne_empty.symm]
