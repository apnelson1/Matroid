module

public import Mathlib.Combinatorics.Matroid.Loop

@[expose] public section

attribute [grind ←] Matroid.closure_subset_ground
open Set

namespace Matroid

lemma union_subset_ground {α : Type*} {M : Matroid α} {X Y : Set α}
    (hX : X ⊆ M.E) (hY : Y ⊆ M.E) : X ∪ Y ⊆ M.E := Set.union_subset hX hY

lemma iUnion_subset_ground {κ : Sort*} {α : Type*} {M : Matroid α} {X : κ → Set α} :
    (⋃ k, X k) ⊆ M.E ↔ ∀ k, X k ⊆ M.E := Set.iUnion_subset_iff

grind_pattern union_subset_ground => X ∪ Y ⊆ M.E where
  guard ¬ (X ∪ Y ⊆ M.E)
grind_pattern iUnion_subset_ground => (⋃ k, X k) ⊆ M.E

end Matroid

attribute [grind →] Matroid.IsBase.subset_ground Matroid.Indep.subset_ground
  Matroid.Dep.subset_ground Matroid.IsBasis.subset_ground
  Matroid.IsFlat.subset_ground Matroid.Spanning.subset_ground
  Matroid.IsLoop.mem_ground Matroid.IsNonloop.mem_ground Matroid.IsColoop.mem_ground

attribute [grind =] Matroid.dual_ground Matroid.loopyOn_ground Matroid.freeOn_ground
  Matroid.uniqueBaseOn_ground Matroid.restrict_ground_eq Matroid.comap_ground_eq
  Matroid.comapOn_ground_eq

grind_pattern Matroid.closure_subset_ground => M.closure X, M.E
grind_pattern Matroid.loops_subset_ground => M.loops, M.E
grind_pattern Matroid.coloops_subset_ground => M.coloops, M.E

grind_pattern Matroid.IsCircuit.subset_ground => M.IsCircuit C, M.E
