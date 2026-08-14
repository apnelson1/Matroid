module

public import Mathlib.Data.Set.Lattice.Image

@[expose] public section

variable {α ι : Type*}

open Function symmDiff
namespace Set

lemma preimage_singleton {α β : Type*} (f : α → β) (y : β) : f ⁻¹' {y} = {x | f x = y} := rfl

lemma iUnion_eq_single_of_forall_subset {ι : Sort*} {s : ι → Set α} {a : ι}
    (hi : ∀ i ≠ a, s i ⊆ s a) : ⋃ i, s i = s a := by
  refine (subset_iUnion ..).antisymm' <| iUnion_subset fun i ↦ ?_
  obtain rfl | hne := eq_or_ne i a
  · rfl
  exact hi i hne

lemma iUnion_eq_single {ι : Sort*} (s : ι → Set α) {a : ι} (hi : ∀ i ≠ a, s i = ∅) :
    ⋃ i, s i = s a :=
  iUnion_eq_single_of_forall_subset fun i hia ↦ by grw [hi i hia, empty_subset]

lemma iUnion_inter_right_inter_eq_of_pairwise_disjoint {s t : ι → Set α}
    (h : Pairwise (Disjoint on s)) {j : ι} : (⋃ i, (s i ∩ t i)) ∩ s j = s j ∩ t j := by
  rw [iUnion_inter, iUnion_eq_single (a := j), inter_right_comm, inter_self, inter_comm]
  intro i hij
  rw [inter_right_comm, (h hij).inter_eq, empty_inter]

lemma iUnion_inter_left_inter_eq_of_pairwise_disjoint {s t : ι → Set α}
    (h : Pairwise (Disjoint on s)) {j : ι} : (⋃ i, (t i ∩ s i)) ∩ s j = t j ∩ s j := by
  rw [iUnion_congr (fun _ ↦ inter_comm ..), iUnion_inter_right_inter_eq_of_pairwise_disjoint h,

    inter_comm]
lemma biUnion_eq_biUnion_nonempty (s : ι → Set α) {u : Set ι} :
    ⋃ i ∈ u, s i = ⋃ i ∈ {i ∈ u | (s i).Nonempty}, s i := by
  refine subset_antisymm (iUnion₂_subset fun i hiu ↦ ?_) <| biUnion_mono (by simp) <| by simp
  obtain he | hne := (s i).eq_empty_or_nonempty
  · simp [he]
  exact subset_biUnion_of_mem <| by grind

lemma sInter_subset_sUnion {s : Set (Set α)} (hs : s.Nonempty) : ⋂₀ s ⊆ ⋃₀ s :=
  (sInter_subset_of_mem hs.some_mem).trans (subset_sUnion_of_mem hs.some_mem)

lemma inter_distrib_biInter (s : ι → Set α) {u : Set ι} (hu : u.Nonempty) (t : Set α) :
    t ∩ ⋂ i ∈ u, s i = ⋂ i ∈ u, t ∩ s i := by
  exact Eq.symm (inter_biInter hu (fun i ↦ s i) t)
  -- have := hu.coe_sort
  -- rw [biInter_eq_iInter, inter_iInter, biInter_eq_iInter]

lemma biInter_distrib_inter (s : ι → Set α) {u : Set ι} (hu : u.Nonempty) (t : Set α) :
    (⋂ i ∈ u, s i) ∩ t = ⋂ i ∈ u, s i ∩ t := by
  simp_rw [inter_comm, inter_distrib_biInter _ hu]

lemma union_distrib_biUnion (s : ι → Set α) {u : Set ι} (hu : u.Nonempty) (t : Set α) :
    t ∪ ⋃ i ∈ u, s i = ⋃ i ∈ u, t ∪ s i := by
  have := hu.coe_sort
  rw [biUnion_eq_iUnion, union_iUnion, biUnion_eq_iUnion]

lemma biUnion_distrib_union (s : ι → Set α) {u : Set ι} (hu : u.Nonempty) (t : Set α) :
    (⋃ i ∈ u, s i) ∪ t = ⋃ i ∈ u, s i ∪ t := by
  simp_rw [union_comm, union_distrib_biUnion _ hu]

lemma inter_distrib_sInter {s : Set (Set α)} (hs : s.Nonempty) (t : Set α) :
    t ∩ ⋂₀ s = ⋂ x ∈ s, (t ∩ x) := by
  rw [sInter_eq_biInter, inter_distrib_biInter _ hs]

lemma sInter_distrib_inter {s : Set (Set α)} (hs : s.Nonempty) (t : Set α) :
    ⋂₀ s ∩ t = ⋂ x ∈ s, x ∩ t := by
  simp_rw [inter_comm _ t, inter_distrib_sInter hs]

lemma union_distrib_sUnion {s : Set (Set α)} (hs : s.Nonempty) (t : Set α) :
    t ∪ ⋃₀ s = ⋃ x ∈ s, (t ∪ x) := by
  rw [sUnion_eq_biUnion, union_distrib_biUnion _ hs]

lemma sUnion_distrib_union {s : Set (Set α)} (hs : s.Nonempty) (t : Set α) :
    ⋃₀ s ∪ t = ⋃ x ∈ s, (x ∪ t) := by
  rw [sUnion_eq_biUnion, biUnion_distrib_union _ hs]

lemma sdiff_eq_sdiff_inter_of_subset {s t : Set α} (h : s ⊆ t) (r : Set α) :
    s \ r = s \ (r ∩ t) := by
  rw [sdiff_inter, sdiff_eq_empty.2 h, union_empty]

lemma sdiff_union_eq_union_of_subset (s : Set α) {t r : Set α} (h : t ⊆ r) :
    (s \ t) ∪ r = s ∪ r := by
  ext x; simp only [mem_union, mem_sdiff]; tauto

lemma sdiff_eq_sdiff_iff_inter_eq_inter {s t r : Set α} : s \ t = s \ r ↔ (t ∩ s = r ∩ s) := by
  rw [← sdiff_inter_self_eq_sdiff, ← sdiff_inter_self_eq_sdiff (t := r)]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  rw [← sdiff_sdiff_cancel_left inter_subset_right, h, sdiff_sdiff_cancel_left inter_subset_right]

@[simp] lemma sdiff_inter_sdiff_right {s t r : Set α} : (t \ s) ∩ (r \ s) = (t ∩ r) \ s :=
  (sdiff_inter_distrib_right s t r).symm

@[simp]
lemma iInter_sdiff_distrib {ι α : Type*} [Nonempty ι] {G : ι → Set α} {X : Set α} :
    (⋂ i, G i) \ X = ⋂ i, (G i) \ X := by
  ext x
  simp +contextual only [mem_sdiff, mem_iInter, iff_def, not_false_eq_true, and_self, implies_true,
    true_and]
  exact fun a ↦ notMem_of_mem_sdiff (a <| Classical.arbitrary ι)

@[simp]
lemma biInter_sdiff_distrib {ι α : Type*} {s : Set ι} (hs : s.Nonempty) {G : ι → Set α}
    {X : Set α} : (⋂ i ∈ s, G i) \ X = ⋂ i ∈ s, G i \ X := by
  ext x
  simp +contextual only [mem_sdiff, mem_iInter, iff_def, not_false_eq_true, and_self, implies_true,
    true_and]
  exact fun h ↦ (h _ hs.some_mem).2

@[simp]
lemma sInter_sdiff_distrib {α : Type*} {s : Set (Set α)} (hs : s.Nonempty) {X : Set α} :
    ⋂₀ s \ X = ⋂₀ ((· \ X) '' s) := by
  ext x
  simp +contextual only [mem_sdiff, mem_sInter, sInter_image, mem_iInter, iff_def,
    not_false_eq_true, and_self, implies_true, true_and]
  exact fun h ↦ (h _ hs.some_mem).2

lemma insert_inter_insert_eq {A : Set α} {b c : α} (hne : b ≠ c):
    (insert b A) ∩ (insert c A) = A := by
  aesop

lemma insert_union_insert_eq {A : Set α} {b c : α} :
    (insert b A) ∪ (insert c A) = insert c (insert b A) := by
  rw [insert_eq, insert_eq, ← union_union_distrib_right, @union_comm _ {b} _,
    union_assoc, ← insert_eq, ← insert_eq]

lemma notMem_or_exists_eq_insert_notMem (s : Set α) (x : α) :
    x ∉ s ∨ ∃ s₀, x ∉ s₀ ∧ s = insert x s₀ :=
  imp_iff_not_or.1 <| fun h ↦ ⟨s \ {x}, by simp, by simp [insert_eq_of_mem h]⟩

lemma biInter_diff_singleton_eq_diff (s : Set α) {t : Set α} (ht : t.Nonempty) :
    ⋂ (i ∈ t), s \ {i} = s \ t := by
  simp only [Set.ext_iff, mem_iInter, mem_sdiff, mem_singleton_iff]
  exact fun x ↦ ⟨fun h ↦ ⟨(h _ ht.some_mem).1, fun hxt ↦ (h x hxt).2 rfl⟩,
    fun h y hyt ↦ ⟨h.1, fun hxy ↦ h.2 <| hxy.symm ▸ hyt⟩⟩

lemma subset_sdiff_singleton_iff {s t : Set α} {x : α} : s ⊆ t \ {x} ↔ (s ⊆ t ∧ x ∉ s) := by
  rw [subset_sdiff, disjoint_singleton_right]

@[deprecated LE.le.sdiff_ssubset_of_nonempty (since := "2026-07-21")]
lemma sdiff_ssubset {s t : Set α} (hst : s ⊆ t) (hs : s.Nonempty) : t \ s ⊂ t :=
  hst.sdiff_ssubset_of_nonempty hs

theorem image_preimage_image {β : Type*} {s : Set α} {f : α → β} : f '' (f ⁻¹' (f '' s)) = f '' s :=
  subset_antisymm (by simp) (image_mono (subset_preimage_image _ _))

lemma ssubset_sdiff_iff {s t r : Set α} : s ⊂ t \ r ↔ s ⊆ t ∧ Disjoint s r ∧ ¬ (t ⊆ s ∪ r) := by
  rw [ssubset_iff_subset_not_subset, sdiff_subset_iff, subset_sdiff, union_comm, and_assoc]

lemma sdiff_ssubset_sdiff {s t r : Set α} (hst : s ⊂ t) (hstr : ¬ (t ⊆ s ∪ r)) : s \ r ⊂ t \ r := by
  rwa [ssubset_sdiff_iff, and_iff_right disjoint_sdiff_left, sdiff_union_self, sdiff_subset_iff,
    and_iff_right (hst.subset.trans subset_union_right)]

lemma sdiff_ssubset_sdiff_right {s t r : Set α} (htr : t ⊆ r) (hst : s ⊂ t) :
    r \ t ⊂ r \ s := by
  grw [ssubset_sdiff_iff, and_iff_right sdiff_subset,
    and_iff_right (disjoint_sdiff_left.mono_right hst.subset)]
  exact fun hss ↦ hst.not_subset <| by grind

lemma sdiff_ssubset_sdiff_right' {s t r : Set α} (hstr : s ∩ r ⊂ t ∩ r) : r \ t ⊂ r \ s := by
  rw [← sdiff_inter_self_eq_sdiff, ← sdiff_inter_self_eq_sdiff (t := s)]
  exact sdiff_ssubset_sdiff_right inter_subset_right hstr

lemma sdiff_ssubset_sdiff_iff (A B C : Set α) : A \ B ⊂ A \ C ↔ A ∩ C ⊂ A ∩ B := by
  rw [ssubset_iff_exists, ssubset_iff_exists]
  refine ⟨fun ⟨hle, x, ⟨hxA, hxC⟩, hxB⟩ => ⟨?_, ?_⟩, fun ⟨hle, x, hxB, hxC⟩ => ⟨?_, ?_⟩⟩
  · rintro a ⟨haA, haC⟩
    simp only [mem_inter_iff, haA, true_and]
    by_contra! haB
    exact hle ⟨haA, haB⟩ |>.2 haC
  · simp only [mem_sdiff, hxA, true_and, not_not] at hxB
    use x, ⟨hxA, hxB⟩, by simp [hxC]
  · rintro a ⟨haA, haB⟩
    use haA, fun haC ↦ haB (hle ⟨haA, haC⟩).2
  use x
  simp only [mem_inter_iff, not_and] at hxC
  simp [hxB.1, hxB.2, hxC]

lemma union_sdiff_eq_sdiff {A B C : Set α} (hBC : B ⊆ C) : (A ∪ B) \ C = A \ C := by
  ext x
  simp only [mem_sdiff, mem_union, and_congr_left_iff, or_iff_left_iff_imp]
  exact fun a a_1 ↦ (a (hBC a_1)).elim

@[simp]
lemma insert_eq_singleton_iff {x y : α} {s : Set α} :
    insert x s = {y} ↔ x = y ∧ ∀ a ∈ s, a = y := by
  simp +contextual [Set.ext_iff, iff_def]

-- theorem exists_pairwiseDisjoint_iUnion_eq (s : ι → Set α) :
--     ∃ t : ι → Set α, Pairwise (Disjoint on t) ∧ ⋃ i, t i = ⋃ i, s i ∧ ∀ i, t i ⊆ s i:= by
--   choose f hf using show ∀ x ∈ ⋃ i, s i, ∃ i, x ∈ s i by simp
--   use fun i ↦ {x ∈ s i | ∃ (h : x ∈ s i), f x (mem_iUnion_of_mem i h) = i}
--   refine ⟨fun i j hij ↦ Set.disjoint_left.2 ?_,
      -- subset_antisymm (iUnion_mono <| fun _ _ h ↦ h.1) ?_,
--     fun i ↦ by simp only [sep_subset]⟩
--   · simp only [mem_ofPred_eq, not_and, not_exists, and_imp, forall_exists_index]
--     exact fun a _ hfa hfi _ hfj haj ↦ hij <| by rw [← hfi, haj]
--   · simp only [iUnion_subset_iff]
--     exact fun i x hxi ↦ mem_iUnion.2 ⟨f x (mem_iUnion_of_mem i hxi), by simp [hf x _]⟩

lemma disjoint_iff_forall_notMem (A B : Set α) : Disjoint A B ↔ ∀ ⦃x⦄, x ∈ A → x ∉ B := by grind

lemma sdiff_symmDiff_sdiff (A B C : Set α) : (A \ B) ∆ (A \ C) = A ∩ (B ∆ C) := by grind

lemma symmDiff_sdiff_distrib (A B C : Set α) : (A ∆ B) \ C = (A \ C) ∆ (B \ C) := by grind

lemma disjoint_sdiff_iff (A B C : Set α) : Disjoint (A \ B) C ↔ A ∩ C ⊆ B := by
  rw [disjoint_iff_inter_eq_empty, ← inter_sdiff_right_comm]
  exact sdiff_eq_empty

lemma sdiff_symmDiff (A B : Set α) : (A \ B) ∆ A = A ∩ B := by
  ext x
  simp [symmDiff_def]

lemma symmDiff_union_left (A B C : Set α) : (A ∪ B) ∆ (A ∪ C) = (B ∆ C) \ A := by
  ext x
  simp only [symmDiff_def, sup_eq_union, mem_union, mem_sdiff]
  tauto

lemma union_diff_diff (A B : Set α) : (A ∪ B) \ (A \ B) = B := by
  ext x
  simp only [mem_sdiff, mem_union]
  tauto

variable {s t r : Set α}

lemma iUnion_bool {s : Bool → Set α} : ⋃ i, s i = s true ∪ s false :=
  Set.ext <| by simp [or_comm]

lemma iInter_bool {s : Bool → Set α} : ⋂ i, s i = s true ∩ s false :=
  Set.ext <| by simp [and_comm]

@[simp] lemma pair_nontrivial_iff {x y : α} : ({x,y} : Set α).Nontrivial ↔ x ≠ y :=
  ⟨by rintro h rfl; simp at h, nontrivial_pair⟩

lemma pairwise_on_bool' {α : Type*} {r : α → α → Prop} {f : Bool → α} (b : Bool) :
    Pairwise (r on f) ↔ r (f b) (f !b) ∧ r (f !b) (f b) := by
  simp_rw [Pairwise, b.forall_bool']
  simp

lemma pairwise_disjoint_on_bool' {α : Type*} {f : Bool → Set α} :
    Pairwise (Disjoint on f) ↔ Disjoint (f true) (f false) := by
  rw [pairwise_on_bool' true, Bool.not_true, disjoint_comm, and_self]

lemma pairwise_disjoint_on_bool'' {α : Type*} {f : Bool → Set α} (b : Bool) :
    Pairwise (Disjoint on f) ↔ Disjoint (f b) (f !b) := by
  rw [pairwise_on_bool', disjoint_comm, and_self]

lemma iUnion_bool' {α : Type*} (f : Bool → Set α) (b : Bool) : ⋃ i, f i = f b ∪ f !b := by
  cases b <;> simp [iUnion_bool, union_comm]

lemma iInter_bool' {α : Type*} (f : Bool → Set α) (b : Bool) : ⋂ i, f i = f b ∩ f !b := by
  cases b <;> simp [iInter_bool, inter_comm]

lemma sdiff_singleton_sdiff_eq (s t : Set α) (x : α) : (s \ {x}) \ t = s \ (insert x t) := by
  rw [sdiff_sdiff, singleton_union]

lemma exists_partition_of_subset_iUnion {s : Set α} {t : ι → Set α} (hst : s ⊆ ⋃ i, t i) :
    ∃ (r : ι → Set α), Pairwise (Disjoint on r) ∧ ⋃ i, r i = s ∧ (∀ i, r i ⊆ t i) := by
  obtain hι | hι := isEmpty_or_nonempty ι; simp_all
  have h (a) (ha : a ∈ s) : ∃ i, a ∈ t i := by simpa using hst ha
  choose! f hf using h
  refine ⟨fun i ↦ f ⁻¹' {i} ∩ s, by simp +contextual [Pairwise, disjoint_left], ?_, ?_⟩
  · rw [← iUnion_inter, inter_eq_right, ← preimage_iUnion, iUnion_singleton_eq_range]
    simp
  rintro i e ⟨rfl, h⟩
  exact hf _ h

lemma iUnion_sdiff_iUnion {ι α : Type*} {s t : ι → Set α} (hts : ∀ i, t i ⊆ s i)
    (hdj : Pairwise (Disjoint on s)) : ⋃ i, s i \ t i = (⋃ i, s i) \ ⋃ i, t i := by
  refine subset_antisymm (subset_sdiff.2 ⟨iUnion_mono fun i ↦ sdiff_subset, ?_⟩) ?_
  · simp only [disjoint_iUnion_right, disjoint_iUnion_left]
    intro i j
    obtain rfl | hne := eq_or_ne i j
    · exact disjoint_sdiff_left
    exact (hdj hne.symm).mono sdiff_subset (hts i)
  rw [iUnion_sdiff]
  exact iUnion_mono fun i ↦ sdiff_subset_sdiff_right <| subset_iUnion ..

@[simp]
lemma forall_mem_const' {α : Type*} {p : Prop} {s : Set α} (hs : s.Nonempty) :
    (∀ x ∈ s, p) ↔ p := ⟨fun h ↦ h _ hs.some_mem, fun hp _ _ ↦ hp⟩

@[simp]
lemma forall_mem_and {α : Type*} {p q : α → Prop} {s : Set α} :
    (∀ x ∈ s, p x ∧ q x) ↔ (∀ x ∈ s, p x) ∧ (∀ x ∈ s, q x) :=
  ⟨fun h ↦ ⟨fun x hx ↦ (h x hx).1, fun x hx ↦ (h x hx).2⟩,
    fun ⟨hp, hq⟩ x hx ↦ ⟨hp x hx, hq x hx⟩⟩

lemma biUnion_congr {α ι : Type*} {p : Set ι} {s t : ι → Set α}
    (h : ∀ i ∈ p, s i = t i) : ⋃ i ∈ p, s i = ⋃ i ∈ p, t i :=
  iUnion₂_congr h

lemma biInter_congr {α ι : Type*} {p : Set ι} {s t : ι → Set α}
    (h : ∀ i ∈ p, s i = t i) : ⋂ i ∈ p, s i = ⋂ i ∈ p, t i :=
  iInter₂_congr h
