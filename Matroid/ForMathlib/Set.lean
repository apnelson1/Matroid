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
