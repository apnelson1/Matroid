import Mathlib.Data.Set.Lattice

namespace Set

theorem sInter_subset_sUnion {α : Type*} (S : Set (Set α)) (hS : S.Nonempty) : ⋂₀ S ⊆ ⋃₀ S :=
  (sInter_subset_of_mem hS.some_mem).trans (subset_sUnion_of_mem hS.some_mem)
