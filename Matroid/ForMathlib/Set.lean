import Mathlib.Data.Set.Lattice

variable {α ι : Type*}
namespace Set

lemma iInter_subset_iUnion [Nonempty ι] (s : ι → Set α) : ⋂ i, s i ⊆ ⋃ i, s i :=
  (iInter_subset s (Classical.arbitrary ι)).trans (subset_iUnion s (Classical.arbitrary ι))

lemma sInter_subset_sUnion {s : Set (Set α)} (hs : s.Nonempty) : ⋂₀ s ⊆ ⋃₀ s :=
  (sInter_subset_of_mem hs.some_mem).trans (subset_sUnion_of_mem hs.some_mem)

lemma biInter_subset_biUnion (s : ι → Set α) {u : Set ι} (hu : u.Nonempty) :
    ⋂ i ∈ u, s i ⊆ ⋃ i ∈ u, s i :=
  (biInter_subset_of_mem hu.choose_spec).trans (subset_biUnion_of_mem hu.choose_spec)

lemma inter_distrib_biInter (s : ι → Set α) {u : Set ι} (hu : u.Nonempty) (t : Set α) :
    t ∩ ⋂ i ∈ u, s i = ⋂ i ∈ u, t ∩ s i := by
  have := hu.coe_sort
  rw [biInter_eq_iInter, inter_iInter, biInter_eq_iInter]

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
  refine' ⟨fun h ↦ _, fun h ↦ by rw [h]⟩
  rw [← diff_diff_cancel_left inter_subset_right, h, diff_diff_cancel_left inter_subset_right]

@[simp] lemma diff_inter_diff_right {s t r : Set α} : (t \ s) ∩ (r \ s) = (t ∩ r) \ s := by
  simp only [diff_eq, inter_assoc, inter_comm sᶜ, inter_self]

lemma inter_diff_right_comm {s t r : Set α} : (s ∩ t) \ r = (s \ r) ∩ t := by
  simp_rw [diff_eq, inter_right_comm]

lemma pair_diff_left {x y : α} (hne : x ≠ y) : ({x, y} : Set α) \ {x} = {y} := by
  rw [insert_diff_of_mem _ (by exact rfl : x ∈ {x}), diff_singleton_eq_self (by simpa)]

lemma pair_diff_right {x y : α} (hne : x ≠ y) : ({x, y} : Set α) \ {y} = {x} := by
  rw [pair_comm, pair_diff_left hne.symm]

@[simp] lemma pair_subset_iff {x y : α} {s : Set α} : {x,y} ⊆ s ↔ x ∈ s ∧ y ∈ s := by
  rw [insert_subset_iff, singleton_subset_iff]

lemma pair_subset {x y : α} {s : Set α} (hx : x ∈ s) (hy : y ∈ s) : {x,y} ⊆ s :=
  pair_subset_iff.2 ⟨hx,hy⟩

lemma subset_insert_iff {s t : Set α} {x : α} :
    s ⊆ insert x t ↔ s ⊆ t ∨ (x ∈ s ∧ s \ {x} ⊆ t) := by
  rw [← diff_singleton_subset_iff]
  obtain (hx | hx) := em (x ∈ s)
  · rw [and_iff_right hx]
    exact ⟨fun h ↦ Or.inr h, fun h ↦ h.elim (fun hst ↦ diff_subset.trans hst) id⟩
  rw [diff_singleton_eq_self hx]
  tauto

lemma subset_pair_iff {x y : α} {s : Set α} : s ⊆ {x,y} ↔ ∀ a ∈ s, a = x ∨ a = y := by
  simp [subset_def]

lemma subset_pair_iff_eq {x y : α} {s : Set α} :
    s ⊆ {x,y} ↔ s = ∅ ∨ s = {x} ∨ s = {y} ∨ s = {x,y} := by
  refine ⟨?_, by rintro (rfl | rfl | rfl | rfl) <;> simp⟩
  rw [subset_insert_iff, subset_singleton_iff_eq, subset_singleton_iff_eq,
    ← subset_empty_iff (s := s \ {x}), diff_subset_iff, union_empty, subset_singleton_iff_eq]
  have h : x ∈ s ∧ ({y} = s \ {x}) → s = {x,y} := fun ⟨h1, h2⟩ ↦ by simp [h1, h2]
  tauto



  -- rw [subset_insert_iff, subset_singleton_iff_eq, or_assoc, subset_singleton_iff_eq,
  --   diff_eq_empty, subset_singleton_iff_eq, subset_antisymm_iff (a := s \ {x})] at h
  -- simp [subset_antisymm_iff]


  -- by_cases hx : x ∈ s
  -- · by_cases hy : y ∈ s
  --   · simp [subset_antisymm_iff (a := s)]
  -- simp_rw [subset_antisymm_iff (a := s), pair_subset_iff, singleton_subset_iff]

  -- rw [subset_insert_iff, subset_singleton_iff_eq, subset_antisymm_iff (a := s) (b := {x,y}),
  --   diff_subset_iff, subset_antisymm_iff (a := s), singleton_union, ]
  -- obtain (rfl | hne) := eq_or_ne x y
  -- · simp only [mem_singleton_iff, insert_eq_of_mem, subset_singleton_iff_eq, or_self]
  -- rw [pair_comm, subset_insert_iff, subset_singleton_iff_eq, subset_singleton_iff_eq, diff_eq_empty,
  --   subset_singleton_iff_eq, or_assoc, and_or_left, and_or_left]
  -- convert Iff.rfl; aesop
  -- refine ⟨fun h ↦ by rw [h, and_iff_right (.inl rfl), pair_diff_left hne.symm], fun h ↦ ?_⟩
  -- rw [subset_antisymm_iff, diff_subset_iff, singleton_union, subset_diff, singleton_subset_iff] at h
  -- exact h.2.1.antisymm (pair_subset h.1 h.2.2.1)

lemma Nonempty.subset_pair_iff_eq {x y : α} {s : Set α} (hs : s.Nonempty) :
    s ⊆ {x,y} ↔ s = {x} ∨ s = {y} ∨ s = {x,y} := by
  rw [Set.subset_pair_iff_eq, or_iff_right]; exact hs.ne_empty

lemma inter_insert_eq {A : Set α} {b c : α} (hne : b ≠ c):
    (insert b A) ∩ (insert c A) = A := by
  rw [insert_eq, insert_eq, ← inter_union_distrib_right, Disjoint.inter_eq _, empty_union]
  rwa [disjoint_singleton]

lemma union_insert_eq {A : Set α} {b c : α} :
    (insert b A) ∪ (insert c A) = insert c (insert b A) := by
  rw [insert_eq, insert_eq, ← union_union_distrib_right, @union_comm _ {b} _,
    union_assoc, ← insert_eq, ← insert_eq]

lemma not_mem_or_exists_eq_insert_not_mem (s : Set α) (x : α) :
    x ∉ s ∨ ∃ s₀, x ∉ s₀ ∧ s = insert x s₀ :=
  imp_iff_not_or.1 <| fun h ↦ ⟨s \ {x}, by simp, by simp [insert_eq_of_mem h]⟩

lemma biInter_diff_singleton_eq_diff (s : Set α) {t : Set α} (ht : t.Nonempty) :
    ⋂ (i ∈ t), s \ {i} = s \ t := by
  simp only [ext_iff, mem_iInter, mem_diff, mem_singleton_iff]
  exact fun x ↦ ⟨fun h ↦ ⟨(h _ ht.some_mem).1, fun hxt ↦ (h x hxt).2 rfl⟩,
    fun h y hyt ↦ ⟨h.1, fun hxy ↦ h.2 <| hxy.symm ▸ hyt⟩⟩

lemma subset_diff_singleton_iff {s t : Set α} {x : α} : s ⊆ t \ {x} ↔ (s ⊆ t ∧ x ∉ s) := by
  rw [subset_diff, disjoint_singleton_right]

lemma diff_ssubset {s t : Set α} (hst : s ⊆ t) (hs : s.Nonempty) : t \ s ⊂ t := by
  refine diff_subset.ssubset_of_ne fun h_eq ↦ ?_
  rw [sdiff_eq_left, disjoint_iff_inter_eq_empty, inter_eq_self_of_subset_right hst] at h_eq
  simp [h_eq] at hs
