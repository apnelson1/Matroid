import Mathlib.Data.Set.Lattice.Image

variable {α ι : Type*}

open Function
namespace Set

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

lemma diff_eq_diff_inter_of_subset {s t : Set α} (h : s ⊆ t) (r : Set α) :
    s \ r = s \ (r ∩ t) := by
  rw [diff_inter, diff_eq_empty.2 h, union_empty]

lemma diff_union_eq_union_of_subset (s : Set α) {t r : Set α} (h : t ⊆ r) :
    (s \ t) ∪ r = s ∪ r := by
  ext x; simp only [mem_union, mem_diff]; tauto

lemma diff_eq_diff_iff_inter_eq_inter {s t r : Set α} : s \ t = s \ r ↔ (t ∩ s = r ∩ s) := by
  rw [← diff_inter_self_eq_diff, ← diff_inter_self_eq_diff (t := r)]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  rw [← diff_diff_cancel_left inter_subset_right, h, diff_diff_cancel_left inter_subset_right]

@[simp] lemma diff_inter_diff_right {s t r : Set α} : (t \ s) ∩ (r \ s) = (t ∩ r) \ s := by
  simp only [diff_eq, inter_assoc, inter_comm sᶜ, inter_self]

@[simp]
lemma iInter_diff_distrib {ι α : Type*} [Nonempty ι] {G : ι → Set α} {X : Set α} :
    (⋂ i, G i) \ X = ⋂ i, (G i) \ X := by
  ext x
  simp +contextual only [mem_diff, mem_iInter, iff_def, not_false_eq_true, and_self, implies_true,
    true_and]
  exact fun a ↦ notMem_of_mem_diff (a <| Classical.arbitrary ι)

@[simp]
lemma biInter_diff_distrib {ι α : Type*} {s : Set ι} (hs : s.Nonempty) {G : ι → Set α}
    {X : Set α} : (⋂ i ∈ s, G i) \ X = ⋂ i ∈ s, G i \ X := by
  ext x
  simp +contextual only [mem_diff, mem_iInter, iff_def, not_false_eq_true, and_self, implies_true,
    true_and]
  exact fun h ↦ (h _ hs.some_mem).2

@[simp]
lemma sInter_diff_distrib {α : Type*} {s : Set (Set α)} (hs : s.Nonempty) {X : Set α} :
    ⋂₀ s \ X = ⋂₀ ((· \ X) '' s) := by
  ext x
  simp +contextual only [mem_diff, mem_sInter, sInter_image, mem_iInter, iff_def, not_false_eq_true,
    and_self, implies_true, true_and]
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
  simp only [Set.ext_iff, mem_iInter, mem_diff, mem_singleton_iff]
  exact fun x ↦ ⟨fun h ↦ ⟨(h _ ht.some_mem).1, fun hxt ↦ (h x hxt).2 rfl⟩,
    fun h y hyt ↦ ⟨h.1, fun hxy ↦ h.2 <| hxy.symm ▸ hyt⟩⟩

lemma subset_diff_singleton_iff {s t : Set α} {x : α} : s ⊆ t \ {x} ↔ (s ⊆ t ∧ x ∉ s) := by
  rw [subset_diff, disjoint_singleton_right]

lemma diff_ssubset {s t : Set α} (hst : s ⊆ t) (hs : s.Nonempty) : t \ s ⊂ t := by
  refine diff_subset.ssubset_of_ne fun h_eq ↦ ?_
  rw [sdiff_eq_left, disjoint_iff_inter_eq_empty, inter_eq_self_of_subset_right hst] at h_eq
  simp [h_eq] at hs

theorem image_preimage_image {β : Type*} {s : Set α} {f : α → β} : f '' (f ⁻¹' (f '' s)) = f '' s :=
  subset_antisymm (by simp) (image_subset f (subset_preimage_image _ _))

-- theorem exists_pairwiseDisjoint_iUnion_eq (s : ι → Set α) :
--     ∃ t : ι → Set α, Pairwise (Disjoint on t) ∧ ⋃ i, t i = ⋃ i, s i ∧ ∀ i, t i ⊆ s i:= by
--   choose f hf using show ∀ x ∈ ⋃ i, s i, ∃ i, x ∈ s i by simp
--   use fun i ↦ {x ∈ s i | ∃ (h : x ∈ s i), f x (mem_iUnion_of_mem i h) = i}
--   refine ⟨fun i j hij ↦ Set.disjoint_left.2 ?_,
      -- subset_antisymm (iUnion_mono <| fun _ _ h ↦ h.1) ?_,
--     fun i ↦ by simp only [sep_subset]⟩
--   · simp only [mem_setOf_eq, not_and, not_exists, and_imp, forall_exists_index]
--     exact fun a _ hfa hfi _ hfj haj ↦ hij <| by rw [← hfi, haj]
--   · simp only [iUnion_subset_iff]
--     exact fun i x hxi ↦ mem_iUnion.2 ⟨f x (mem_iUnion_of_mem i hxi), by simp [hf x _]⟩


variable {s t r : Set α}

@[simp] lemma iUnion_bool {s : Bool → Set α} : ⋃ i, s i = s true ∪ s false :=
  Set.ext <| by simp [or_comm]

@[simp] lemma iInter_bool {s : Bool → Set α} : ⋂ i, s i = s true ∩ s false :=
  Set.ext <| by simp [and_comm]


@[simp] lemma pair_nontrivial_iff {x y : α} : ({x,y} : Set α).Nontrivial ↔ x ≠ y :=
  ⟨by rintro h rfl; simp at h, nontrivial_pair⟩

lemma diff_singleton_diff_eq (s t : Set α) (x : α) : (s \ {x}) \ t = s \ (insert x t) := by
  rw [diff_diff, singleton_union]

lemma Subsingleton.elim {x y} {s : Set α} (hs : s.Subsingleton) (hxs : x ∈ s) (hys : y ∈ s) :
    x = y := by
  obtain rfl | ⟨a, rfl⟩ := hs.eq_empty_or_singleton <;> simp_all

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


lemma iUnion_diff_iUnion {ι α : Type*} {s t : ι → Set α} (hts : ∀ i, t i ⊆ s i)
    (hdj : Pairwise (Disjoint on s)) : ⋃ i, s i \ t i = (⋃ i, s i) \ ⋃ i, t i := by
  refine subset_antisymm (subset_diff.2 ⟨iUnion_mono fun i ↦ diff_subset, ?_⟩) ?_
  · simp only [disjoint_iUnion_right, disjoint_iUnion_left]
    intro i j
    obtain rfl | hne := eq_or_ne i j
    · exact disjoint_sdiff_left
    exact (hdj hne.symm).mono diff_subset (hts i)
  rw [iUnion_diff]
  exact iUnion_mono fun i ↦ diff_subset_diff_right <| subset_iUnion ..
