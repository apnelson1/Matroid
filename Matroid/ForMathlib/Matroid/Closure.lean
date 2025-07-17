import Mathlib.Data.Matroid.Closure

namespace Matroid

variable {α : Type*} {M : Set α}

lemma closure_eq_ground (M : Matroid α) {X : Set α} (hX : M.E ⊆ X) : M.closure X = M.E := by
  rw [← closure_inter_ground, Set.inter_eq_self_of_subset_right hX, closure_ground]

@[simp]
lemma closure_ground_union_left (M : Matroid α) {X : Set α} : M.closure (M.E ∪ X) = M.E := by
  rw [M.closure_eq_ground Set.subset_union_left]

@[simp]
lemma closure_ground_union_right (M : Matroid α) {X : Set α} : M.closure (X ∪ M.E) = M.E := by
  rw [M.closure_eq_ground Set.subset_union_right]

-- lemma closure_iUnion_closure_eq_closure_iUnion'

-- lemma closure_iUnion_congr' {α : Type*} {ι : Sort*} {κ : ι → Sort*} (M : Matroid α)
--     {X Y : (i : ι) → κ i → Set α}
--     (hXY : ∀ i (j : κ i), M.closure (X i j) = M.closure (Y i j)) :
--     M.closure (⋃ i, ⋃ j, X i j) = M.closure (⋃ i, ⋃ j, Y i j) :=
--   M.closure_iUnion_congr _ _ fun i ↦ M.closure_iUnion_congr _ _ fun j ↦ hXY i j

-- lemma closure_iUnion₂_congr {α : Type*} {ι : Sort*} {κ : ι → Sort*} (M : Matroid α)
--     {X Y : (i : ι) → κ i → Set α}
--     (hXY : ∀ i (j : κ i), M.closure (X i j) = M.closure (Y i j)) :
--     M.closure (⋃ i, ⋃ j, X i j) = M.closure (⋃ i, ⋃ j, Y i j) := by
--   rw [← closure_iUnion_closure_eq_closure_iUnion]
  -- M.closure_iUnion_congr _ _ fun i ↦ M.closure_iUnion_congr _ _ fun j ↦ hXY i j
