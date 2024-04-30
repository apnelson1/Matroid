import Mathlib.Data.Set.Lattice

variable {α ι : Type*}
namespace Set

theorem iInter_subset_iUnion [Nonempty ι] (s : ι → Set α) : ⋂ i, s i ⊆ ⋃ i, s i :=
  (iInter_subset s (Classical.arbitrary ι)).trans (subset_iUnion s (Classical.arbitrary ι))

theorem sInter_subset_sUnion {s : Set (Set α)} (hs : s.Nonempty) : ⋂₀ s ⊆ ⋃₀ s :=
  (sInter_subset_of_mem hs.some_mem).trans (subset_sUnion_of_mem hs.some_mem)

theorem biInter_subset_biUnion (s : ι → Set α) {u : Set ι} (hu : u.Nonempty) :
    ⋂ i ∈ u, s i ⊆ ⋃ i ∈ u, s i :=
  (biInter_subset_of_mem hu.choose_spec).trans (subset_biUnion_of_mem hu.choose_spec)

theorem inter_distrib_biInter (s : ι → Set α) {u : Set ι} (hu : u.Nonempty) (t : Set α) :
    t ∩ ⋂ i ∈ u, s i = ⋂ i ∈ u, t ∩ s i := by
  have := hu.coe_sort
  rw [biInter_eq_iInter, inter_iInter, biInter_eq_iInter]

theorem biInter_distrib_inter (s : ι → Set α) {u : Set ι} (hu : u.Nonempty) (t : Set α) :
    (⋂ i ∈ u, s i) ∩ t = ⋂ i ∈ u, s i ∩ t := by
  simp_rw [inter_comm, inter_distrib_biInter _ hu]

theorem union_distrib_biUnion (s : ι → Set α) {u : Set ι} (hu : u.Nonempty) (t : Set α) :
    t ∪ ⋃ i ∈ u, s i = ⋃ i ∈ u, t ∪ s i := by
  have := hu.coe_sort
  rw [biUnion_eq_iUnion, union_iUnion, biUnion_eq_iUnion]

theorem biUnion_distrib_union (s : ι → Set α) {u : Set ι} (hu : u.Nonempty) (t : Set α) :
    (⋃ i ∈ u, s i) ∪ t = ⋃ i ∈ u, s i ∪ t := by
  simp_rw [union_comm, union_distrib_biUnion _ hu]

theorem inter_distrib_sInter {s : Set (Set α)} (hs : s.Nonempty) (t : Set α) :
    t ∩ ⋂₀ s = ⋂ x ∈ s, (t ∩ x) := by
  rw [sInter_eq_biInter, inter_distrib_biInter _ hs]

theorem sInter_distrib_inter {s : Set (Set α)} (hs : s.Nonempty) (t : Set α) :
    ⋂₀ s ∩ t = ⋂ x ∈ s, x ∩ t := by
  simp_rw [inter_comm _ t, inter_distrib_sInter hs]

theorem union_distrib_sUnion {s : Set (Set α)} (hs : s.Nonempty) (t : Set α) :
    t ∪ ⋃₀ s = ⋃ x ∈ s, (t ∪ x) := by
  rw [sUnion_eq_biUnion, union_distrib_biUnion _ hs]

theorem sUnion_distrib_union {s : Set (Set α)} (hs : s.Nonempty) (t : Set α) :
    ⋃₀ s ∪ t = ⋃ x ∈ s, (x ∪ t) := by
  rw [sUnion_eq_biUnion, biUnion_distrib_union _ hs]

theorem diff_eq_diff_inter_of_subset {s t : Set α} (h : s ⊆ t) (r : Set α) :
    s \ r = s \ (r ∩ t) := by
  rw [diff_inter, diff_eq_empty.2 h, union_empty]

theorem diff_union_eq_union_of_subset (s : Set α) {t r : Set α} (h : t ⊆ r) :
    (s \ t) ∪ r = s ∪ r := by
  ext x; simp only [mem_union, mem_diff]; tauto


theorem diff_eq_diff_iff_inter_eq_inter {s t r : Set α} : s \ t = s \ r ↔ (t ∩ s = r ∩ s) := by
  rw [← diff_inter_self_eq_diff, ← diff_inter_self_eq_diff (t := r)]
  refine' ⟨fun h ↦ _, fun h ↦ by rw [h]⟩
  rw [← diff_diff_cancel_left (inter_subset_right t s), h,
    diff_diff_cancel_left (inter_subset_right r s)]

@[simp] theorem diff_inter_diff_right {s t r : Set α} : (t \ s) ∩ (r \ s) = (t ∩ r) \ s := by
  simp only [diff_eq, inter_assoc, inter_comm sᶜ, inter_self]

theorem inter_diff_right_comm {s t r : Set α} : (s ∩ t) \ r = (s \ r) ∩ t := by
  simp_rw [diff_eq, inter_right_comm]

theorem pair_diff_left {x y : α} (hne : x ≠ y) : ({x, y} : Set α) \ {x} = {y} := by
  rw [insert_diff_of_mem _ (by exact rfl : x ∈ {x}), diff_singleton_eq_self (by simpa)]

theorem pair_diff_right {x y : α} (hne : x ≠ y) : ({x, y} : Set α) \ {y} = {x} := by
  rw [pair_comm, pair_diff_left hne.symm]

@[simp] theorem pair_subset_iff {x y : α} {s : Set α} : {x,y} ⊆ s ↔ x ∈ s ∧ y ∈ s := by
  rw [insert_subset_iff, singleton_subset_iff]

theorem pair_subset {x y : α} {s : Set α} (hx : x ∈ s) (hy : y ∈ s) : {x,y} ⊆ s :=
  pair_subset_iff.2 ⟨hx,hy⟩

theorem subset_insert_iff {s t : Set α} {x : α} :
    s ⊆ insert x t ↔ s ⊆ t ∨ (x ∈ s ∧ s \ {x} ⊆ t) := by
  rw [← diff_singleton_subset_iff]
  obtain (hx | hx) := em (x ∈ s)
  · rw [and_iff_right hx]
    exact ⟨fun h ↦ Or.inr h, fun h ↦ h.elim (fun hst ↦ (diff_subset _ _).trans hst) id⟩
  rw [diff_singleton_eq_self hx]
  tauto

theorem Nonempty.subset_pair_iff {x y : α} {s : Set α} (hs : s.Nonempty) :
    s ⊆ {x,y} ↔ s = {x} ∨ s = {y} ∨ s = {x,y} := by
  obtain (rfl | hne) := eq_or_ne x y
  · rw [pair_eq_singleton, hs.subset_singleton_iff]; simp
  rw [subset_insert_iff, subset_singleton_iff_eq, subset_singleton_iff_eq, diff_eq_empty,
    iff_false_intro hs.ne_empty, false_or, and_or_left, ← singleton_subset_iff,
    ← subset_antisymm_iff, eq_comm (b := s), ← or_assoc, or_comm (a := s = _), or_assoc]
  convert Iff.rfl using 3
  rw [Iff.comm, subset_antisymm_iff, diff_subset_iff, subset_diff, disjoint_singleton,
    and_iff_left hne.symm, ← and_assoc, and_comm, singleton_union, ← and_assoc, ← union_subset_iff,
    singleton_union, pair_comm, ← subset_antisymm_iff, eq_comm]

theorem inter_insert_eq {A : Set α} {b c : α} (hne : b ≠ c):
    (insert b A) ∩ (insert c A) = A := by
  rw [insert_eq, insert_eq, ← inter_union_distrib_right, Disjoint.inter_eq _, empty_union]
  rwa [disjoint_singleton]

theorem union_insert_eq {A : Set α} {b c : α} :
    (insert b A) ∪ (insert c A) = insert c (insert b A) := by
  rw [insert_eq, insert_eq, ← union_union_distrib_right, @union_comm _ {b} _,
    union_assoc, ← insert_eq, ← insert_eq]
