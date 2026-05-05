import Mathlib.Data.Set.Lattice
import Matroid.ForMathlib.Set
import Mathlib.Data.Set.Card
import Matroid.ForMathlib.Topology.ENat
-- import Mathlib.Order.Partition.Basic

variable {α ι : Type*} {s t x y : Set α} {P Q P' : Set α → Prop} {T : Set (Set α)}

open Set

namespace Set

section General

/-- `T.IsCover x P` means that `T` is a collection of sets with union `x`,
each satisfying property `P`.-/
@[mk_iff]
structure IsCover (T : Set (Set α)) (x : Set α) (P : Set α → Prop) : Prop where
  sUnion_eq : ⋃₀ T = x
  prop : ∀ ⦃y⦄, y ∈ T → P y

lemma IsCover.subset (h : T.IsCover x P) (hy : y ∈ T) : y ⊆ x := by
  grw [← h.sUnion_eq, ← subset_sUnion_of_mem hy]

lemma IsCover.biUnion_eq (h : T.IsCover x P) : ⋃ y ∈ T, y = x := by
  rw [← sUnion_eq_biUnion, h.sUnion_eq]

lemma IsCover.nonempty (h : T.IsCover x P) (hx : x.Nonempty) : T.Nonempty := by
  rw [nonempty_iff_empty_ne]
  rintro rfl
  simp [isCover_iff, eq_comm] at h
  simp_all only [Set.not_nonempty_empty]

@[simp]
lemma isCover_true_iff : T.IsCover x (fun _ ↦ True) ↔ ⋃₀ T = x := by
  simp [isCover_iff]

lemma isCover_iff_isCover_subset : T.IsCover x P ↔ T.IsCover x (fun A ↦ P A ∧ A ⊆ x) := by
  grind [isCover_iff]

lemma isCover_iUnion {y : ι → Set α} {S : ι → Set (Set α)} (h : ∀ i, (S i).IsCover (y i) P) :
    (⋃ i, S i).IsCover (⋃ i, y i) P := by
  refine ⟨by grw [sUnion_iUnion, iUnion_congr fun i ↦ (h i).sUnion_eq], ?_⟩
  simp only [mem_iUnion, forall_exists_index]
  exact fun x i h' ↦ (h i).prop h'

lemma isCover_biUnion {y : ι → Set α} {S : ι → Set (Set α)} {I : Set ι}
    (h : ∀ i ∈ I, (S i).IsCover (y i) P) : (⋃ i ∈ I, S i).IsCover (⋃ i ∈ I, y i) P := by
  convert isCover_iUnion (ι := I) (y := fun i ↦ y i) (S := fun i ↦ S i) (by simpa) <;> simp

/-- The covers of each element of a cover define a cover.
In this case we use typesets to give the cover of covers-/
lemma IsCover.biUnion' {x : Set α} (hcover : T.IsCover x P)
    (f : T → Set (Set α)) (hfun : ∀ x, (f x).IsCover x.1 Q) :
    (⋃ i : T, f i).IsCover x Q := by
  convert isCover_iUnion hfun
  rw [← hcover.biUnion_eq]
  simp

lemma IsCover.mono_prop (h : T.IsCover y P) (hPQ : ∀ x ∈ T, P x → Q x) : T.IsCover y Q :=
  ⟨h.sUnion_eq, fun F hF ↦ hPQ F hF (h.prop hF)⟩

lemma IsCover.mono_prop' (h : T.IsCover y P) (hPQ : ∀ x ⊆ y, P x → Q x) : T.IsCover y Q :=
  h.mono_prop fun x hx hPx ↦ hPQ x (h.subset hx) hPx

lemma isCover_congr (hPQ : ∀ x ∈ T, P x ↔ Q x) : T.IsCover y P ↔ T.IsCover y Q :=
  ⟨fun h ↦ h.mono_prop fun x hx ↦ (hPQ x hx).1, fun h ↦ h.mono_prop fun x hx ↦ (hPQ x hx).2⟩

lemma isCover_congr' (hPQ : ∀ x ⊆ y, P x ↔ Q x) : T.IsCover y P ↔ T.IsCover y Q :=
  ⟨fun h ↦ h.mono_prop' fun x hx ↦ (hPQ x hx).1, fun h ↦ h.mono_prop' fun x hx ↦ (hPQ x hx).2⟩

@[simp]
lemma isCover_empty_iff (P : Set α → Prop) : IsCover ∅ y P ↔ y = ∅ := by
  simp [isCover_iff, eq_comm]

lemma IsCover.image {β : Type*} {Q : Set β → Prop} (hT : T.IsCover x P) (f : Set α → Set β)
    (hPQ : ∀ y ⊆ x, P y → Q (f y)) : (f '' T).IsCover (⋃ y ∈ T, f y) Q :=
  ⟨by simp, by
    simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact fun y hy ↦ hPQ y (hT.subset hy) <| hT.prop hy⟩

lemma IsCover.image_union (h : T.IsCover y P) (hxN : y.Nonempty)
    (hPQ : ∀ z ⊆ y, P z → Q (z ∪ x)) : ((· ∪ x) '' T).IsCover (y ∪ x) Q := by
  convert h.image _ hPQ
  rw [← biUnion_distrib_union, ← sUnion_eq_biUnion, h.sUnion_eq]
  exact h.nonempty hxN

lemma IsCover.image_inter (h : T.IsCover x P) (hx : y ⊆ x) (hPQ : ∀ z ⊆ x, P z → Q (z ∩ y)) :
    ((· ∩ y) '' T).IsCover y Q := by
  convert h.image _ hPQ
  rw [← iUnion₂_inter, ← sUnion_eq_biUnion, h.sUnion_eq, inter_eq_self_of_subset_right hx]

lemma IsCover.image_inter_antitone (h : T.IsCover x P) (hP : Antitone P) (hx : y ⊆ x) :
    ((· ∩ y) '' T).IsCover y P :=
  h.image_inter hx fun _ _ ↦ hP inter_subset_left

lemma isCover_sUnion (T : Set (Set α)) (P : Set α → Prop) (hF : ∀ F ∈ T, P F) :
    T.IsCover (⋃₀ T) P :=
  ⟨rfl, hF⟩

lemma IsCover.union {S T : Set (Set α)} (hS : S.IsCover x P) (hT : T.IsCover y P) :
    (S ∪ T).IsCover (x ∪ y) P := by
  grind [isCover_iff]

@[simp]
lemma singleton_isCover_iff : ({y} : Set (Set α)).IsCover x P ↔ y = x ∧ P x := by
  simp +contextual [isCover_iff]

lemma IsCover.nontrivial (hT : T.IsCover x P) (hx : ¬ P x) (hne : x.Nonempty) : T.Nontrivial := by
  by_contra! hcon
  obtain rfl | ⟨y, rfl⟩ := hcon.eq_empty_or_singleton
  · simpa using (hT.nonempty hne)
  simp [hx] at hT

lemma IsCover.nontrivial_of_prop_empty (hT : T.IsCover x P) (hx : ¬ P x) (he : P ∅) :
    T.Nontrivial :=
  hT.nontrivial hx <| nonempty_iff_ne_empty.2 fun h ↦ hx <| h ▸ he

lemma IsCover.exists_mem (hT : T.IsCover x P) {a : α} (hax : a ∈ x) : ∃ s ∈ T, a ∈ s := by
  simpa [← hT.sUnion_eq] using hax

end General

section Number

variable {β : Type*} [AddCommMonoid β] [CompleteLattice β] [TopologicalSpace β] {f : Set α → β}

noncomputable def weightedCoverNumber (x : Set α) (f : Set α → β)
    (P : Set α → Prop := fun _ ↦ True) :=
  ⨅ (T : Set (Set α)) (_ : T.IsCover x P), ∑' (y : T), f y.1

lemma IsCover.weightedCoverNumber_le (h : T.IsCover x P) :
    x.weightedCoverNumber f P ≤ ∑' y : T, f y.1 :=
  iInf₂_le T h

lemma weightedCoverNumber_sUnion_le (f : Set α → β) (T : Set (Set α)) :
    (⋃₀ T).weightedCoverNumber f ≤ ∑' y : T, f y :=
  IsCover.weightedCoverNumber_le ⟨rfl, by simp⟩

lemma weightedCoverNumber_mono {f g : Set α → ℕ∞} (x : Set α) (P : Set α → Prop)
    (hfg : ∀ y ⊆ x, f y ≤ g y) :
    x.weightedCoverNumber f P ≤ x.weightedCoverNumber g P :=
  iInf₂_mono fun _T hT ↦ ENat.tsum_le_tsum <| fun z ↦ hfg _ <| hT.subset z.2

lemma weightedCoverNumber_subset {f : Set α → ℕ∞} (hf : Monotone f) (hxy : x ⊆ y)
    (hP : ∀ z ⊆ y, P z → Q (z ∩ x)) : x.weightedCoverNumber f Q ≤ y.weightedCoverNumber f P := by
  simp only [weightedCoverNumber, le_iInf_iff]
  refine fun T hT ↦ iInf₂_le_of_le _ (hT.image_inter hxy hP) ?_
  grw [ENat.tsum_image_le_tsum_comp, ENat.tsum_le_tsum fun x ↦ _]
  exact Subtype.forall.2 fun z hz ↦ hf inter_subset_left

lemma weightedCoverNumber_subset_of_antitone {f : Set α → ℕ∞} (hf : Monotone f) (hP : Antitone P)
    (hxy : x ⊆ y) : x.weightedCoverNumber f P ≤ y.weightedCoverNumber f P :=
  weightedCoverNumber_subset hf hxy fun _ _ ↦ hP inter_subset_left

lemma weightedCoverNumber_subset_of_monotone {f : Set α → ℕ∞} (hf : Monotone f) (hxy : x ⊆ y) :
    x.weightedCoverNumber f ≤ y.weightedCoverNumber f :=
  weightedCoverNumber_subset_of_antitone hf antitone_const hxy

-- lemma exi

-- lemma exists_partition_weightedCoverNumber {f : Set α → ℕ∞} (hf : Monotone f) (x : Set α) :
--     ∃ (T : Partition x), ⋃₀ T = s ∧ x.weightedCoverNumber f = ∑' x : T, f x := by
--   _

/-- This is the size of the smallest cover of `x` in which each set satisfies `P`. -/
noncomputable def coverNumber (x : Set α) (P : Set α → Prop) : ℕ∞ :=
  ⨅ (T : Set (Set α)) (_ : T.IsCover x P), T.encard

lemma IsCover.coverNumber_le {T : Set (Set α)} (h : T.IsCover x P) :
    x.coverNumber P ≤ T.encard := by
  simp only [coverNumber ]
  exact biInf_le encard h

lemma encard_eq_coverNumber_of_exists (hn : ∃ (T : Set (Set α)), T.IsCover x P) :
    ∃ T, IsCover T x P ∧ T.encard = x.coverNumber P := by
  obtain ⟨T, hT, hT_eq⟩ := ENat.exists_eq_iInf₂
    (f := fun (T : Set (Set α)) (hT : T.IsCover x P) ↦ T.encard) _ hn.choose_spec
  exact ⟨T, hT, hT_eq⟩

lemma exists_cover (x : Set α) (P : Set α → Prop) (hP : ∀ ⦃a⦄, a ∈ x → P {a}) :
    ∃ T, IsCover T x P ∧ T.encard = x.coverNumber P :=
  encard_eq_coverNumber_of_exists ⟨singleton '' x, by simp, by simpa⟩

lemma coverNumber_eq_top_or_exists_cover (x : Set α) (P : Set α → Prop) :
    x.coverNumber P = ⊤ ∨ ∃ T, IsCover T x P ∧ T.encard = x.coverNumber P := by
  obtain hex | hnot := exists_or_forall_not (fun T ↦ IsCover T x P)
  · exact .inr <| encard_eq_coverNumber_of_exists hex
  left
  simp only [coverNumber, iInf_eq_top, encard_eq_top_iff]
  exact fun T ht ↦ (hnot T ht).elim

lemma coverNumber_eq_weightedCoverNumber (x : Set α) (P : Set α → Prop) [DecidablePred P] :
    x.coverNumber P = x.weightedCoverNumber (fun z ↦ if P z then 1 else ⊤) := by
  refine (le_iInf₂ (fun T hT ↦ ?_)).antisymm <| le_iInf₂ fun T hT ↦ ?_
  · rw [← hT.sUnion_eq, ENat.tsum_ite, one_mul]
    obtain he | hne := {x : T | ¬ P x}.eq_empty_or_nonempty
    · replace he : ∀ x ∈ T, P x := by simpa [Set.ext_iff] using he
      grw [IsCover.coverNumber_le (T := T) ⟨rfl, by simpa using he⟩]
      simp [he]
    grw [ENat.top_mul (by simpa using hne.ne_empty), add_top, ← le_top]
  grw [iInf₂_le (i := T) (by simpa using hT.sUnion_eq),
    tsum_congr (g := 1) (by simpa using hT.prop)]
  simp

lemma one_le_coverNumber (hx : x.Nonempty) (P : Set α → Prop) : 1 ≤ x.coverNumber P := by
  simp [coverNumber, ← not_lt, ENat.lt_one_iff_eq_zero, hx.ne_empty]

lemma coverNumber_le_of_imp (hPQ : ∀ y ⊆ x, P y → Q y) : x.coverNumber Q ≤ x.coverNumber P := by
  obtain hnot | ⟨T, hT, hTP⟩ := coverNumber_eq_top_or_exists_cover x P
  · simp [hnot]
  grw [(hT.mono_prop' hPQ).coverNumber_le, hTP]

lemma coverNumber_congr (hPQ : ∀ y ⊆ x, (P y ↔ Q y)) : x.coverNumber P = x.coverNumber Q :=
  (coverNumber_le_of_imp (by grind)).antisymm <| coverNumber_le_of_imp <| by grind

lemma coverNumber_subset {P : Set α → Prop} (hxy : x ⊆ y) (hP : ∀ z ⊆ y, P z → Q (z ∩ x)) :
    x.coverNumber Q ≤ y.coverNumber P := by
  obtain htop | ⟨T, hT, hTcard⟩ := y.coverNumber_eq_top_or_exists_cover P
  · simp [htop]
  grw [(hT.image_inter hxy hP).coverNumber_le, encard_image_le, hTcard]

lemma coverNumber_subset_of_antitone (hP : Antitone P) (hyx : y ⊆ x) :
    y.coverNumber P ≤ x.coverNumber P :=
  coverNumber_subset hyx fun _ _ ↦ hP inter_subset_left

lemma coverNumber_le_of_forall_exists (hPQ : ∀ x ⊆ y, P x → ∃ z ⊆ y, x ⊆ z ∧ Q z) :
    y.coverNumber Q ≤ y.coverNumber P := by
  obtain hnot | ⟨T, hT, hTP⟩ := y.coverNumber_eq_top_or_exists_cover P
  · simp [hnot]
  choose! f hf using hPQ
  grw [← hTP, ← encard_image_le f, IsCover.coverNumber_le (T := f '' T) (P := Q)]
  convert hT.image f fun x hxy hx ↦ (hf x hxy hx).2.2
  refine subset_antisymm ?_ <| iUnion₂_subset fun x hx ↦ (hf _ (hT.subset hx) (hT.prop hx)).1
  grw [← hT.biUnion_eq]
  exact (iUnion₂_mono (fun x hx ↦ (hf _ (hT.subset hx) (hT.prop hx)).2.1))

lemma coverNumber_le_prop (hPQ : ∀ x ⊆ y, P x → Q x) : y.coverNumber Q ≤ y.coverNumber P :=
  coverNumber_le_of_forall_exists fun x hx hxP ↦ ⟨x, hx, rfl.subset, hPQ x hx hxP⟩

lemma coverNumber_iUnion_le_tsum {ι : Type*} (y : ι → Set α) (P : Set α → Prop) :
    (⋃ i, y i).coverNumber P ≤ ∑' i, (y i).coverNumber P := by
  obtain (h0 | h1) := exists_or_forall_not (fun i ↦ coverNumber (y i) P = ⊤)
  · simp [ENat.tsum_eq_top_of_eq_top h0]
  have hex := fun (i : ι) ↦ (y i).coverNumber_eq_top_or_exists_cover P
  simp_rw [or_iff_right (h1 _)] at hex
  choose! S hS using hex
  grw [(isCover_iUnion (fun i ↦ (hS i).1)).coverNumber_le, ENat.encard_iUnion_le_tsum_encard,
    tsum_congr (fun i ↦ (hS i).2)]

/--
Given a cover we can bound the cover number with the cover number of each element of the cover.
See IsCover.biUnion'
-/
lemma coverNumber_le_tsum_coverNumber {P' : Set α → Prop} (hcover : T.IsCover y P) :
    y.coverNumber P' ≤ ∑' x : T, (x.1).coverNumber P' := by
  obtain (h0 | h1) := exists_or_forall_not (fun x : T ↦ coverNumber x P' = ⊤)
  · simp [ENat.tsum_eq_top_of_eq_top h0]
  have hf : ∀ x : T, ∃ xT : Set (Set α), xT.IsCover (x.1) P' ∧
    xT.encard = (x.1).coverNumber P' := by
    intro x
    obtain (h | ⟨xT, hxres, hencard⟩) := x.1.coverNumber_eq_top_or_exists_cover P'
    · simp [h1 _ h]
    exact ⟨xT, hxres, hencard⟩
  choose f hfunco hfunca using hf
  have hcover := IsCover.biUnion' hcover f hfunco
  grw [hcover.coverNumber_le, ENat.encard_iUnion_le_tsum_encard, tsum_congr hfunca]

lemma coverNumber_le_bound {P' : Set α → Prop} {k : ℕ∞}
    (hcover : T.IsCover y P)
    (hflat : ∀ F, P F → F.coverNumber P' ≤ k) :
    y.coverNumber P' ≤ (T.encard) * k := by
  grw [coverNumber_le_tsum_coverNumber hcover, ENat.tsum_le_tsum (g := fun _ ↦ k),
    ENat.tsum_subtype_const, mul_comm]
  intro F
  simp [hflat _ <| hcover.prop F.2 ]
  --exact hP'

lemma isCover_image_singleton (hP : ∀ e ∈ x, P {e}) : (singleton '' x).IsCover x P  := by
  rw [isCover_iff, sUnion_image, biUnion_of_singleton, and_iff_right rfl]
  simpa

lemma isCover_singleton_le (hP : ∀ e ∈ x, P {e}) : x.coverNumber P ≤ x.encard := by
  grw [(isCover_image_singleton hP).coverNumber_le, encard_image_le singleton x ]

lemma coverNumber_eq_zero_iff (P : Set α → Prop) : x.coverNumber P = 0 ↔ IsCover ∅ x P := by
  simp [coverNumber]

lemma coverNumber_le_coverNumber {P Q : Set α → Prop} {x : Set α} {y : Set α} (f : Set α → Set α )
    (hcov : ∀ T, T.IsCover x P → (f '' T).IsCover y Q) : y.coverNumber Q ≤ x.coverNumber P := by
  obtain ht | ⟨T, hT, hTe ⟩ := coverNumber_eq_top_or_exists_cover x P
  · rw [ht]
    simp only [le_top]
  grw [←hTe, (hcov T hT).coverNumber_le, encard_image_le]

lemma coverNumber_le_coverNumber_union {P Q : Set α → Prop} {x : Set α} {y : Set α}
    (hx : x.Nonempty) (hP : ∀ z, P z → Q (z ∪ y)) : (x ∪ y).coverNumber Q ≤ x.coverNumber P :=
  coverNumber_le_coverNumber (· ∪ y) (fun ?_ hT ↦ (hT.image_union hx (fun z _ ↦ hP z)))

lemma coverNumber_union_le : (x ∪ y).coverNumber P ≤ x.coverNumber P + y.coverNumber P := by
  obtain ht | ⟨T, hT, hTe ⟩ := coverNumber_eq_top_or_exists_cover x P
  · simp [ht]
  obtain ht | ⟨T', hT', hT'e ⟩ := coverNumber_eq_top_or_exists_cover y P
  · simp [ht]
  grw [←hTe, ←hT'e, (hT.union hT').coverNumber_le, ← encard_union_le]

end Number
