import Mathlib.Data.Set.Lattice

namespace Set

theorem sInter_subset_sUnion {α : Type*} (S : Set (Set α)) (hS : S.Nonempty) : ⋂₀ S ⊆ ⋃₀ S :=
  (sInter_subset_of_mem hS.some_mem).trans (subset_sUnion_of_mem hS.some_mem)

theorem inter_distrib_sInter_left {α : Type*} {s : Set (Set α)} (hs : s.Nonempty) (t : Set α) :
    t ∩ ⋂₀ s = ⋂ x ∈ s, (t ∩ x) := by
  ext a
  simp only [mem_inter_iff, mem_sInter, mem_iInter]
  exact ⟨fun h i hi ↦ ⟨h.1, h.2 _ hi⟩, fun h ↦ ⟨(h _ hs.choose_spec).1, fun i hi ↦ (h i hi).2⟩⟩

theorem inter_distrib_sInter_right {α : Type*} {s : Set (Set α)} (hs : s.Nonempty) (t : Set α) :
    (⋂₀ s) ∩ t = ⋂ x ∈ s, (x ∩ t) := by
  simp_rw [inter_comm _ t, inter_distrib_sInter_left hs]
