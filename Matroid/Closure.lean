import Mathlib.Combinatorics.Matroid.Closure

variable {α : Type*} {M : Matroid α}

open Set

namespace Matroid

lemma Spanning.rankFinite_of_finite {S : Set α} (hS : M.Spanning S) (hSfin : S.Finite) :
    M.RankFinite := by
  obtain ⟨B, hB⟩ := hS.exists_isBase_subset
  refine hB.1.rankFinite_of_finite <| hSfin.subset hB.2

lemma IsRestriction.closure_subset_closure {M N : Matroid α} (h : M ≤r N) (X : Set α) :
    M.closure X ⊆ N.closure X := by
  obtain ⟨R, h', rfl⟩ := h.exists_eq_restrict
  grw [← closure_inter_ground, restrict_closure_eq _, inter_subset_left]
  · exact closure_mono _ inter_subset_left
  exact inter_subset_right
