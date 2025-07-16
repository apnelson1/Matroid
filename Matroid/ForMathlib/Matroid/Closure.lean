import Mathlib.Data.Matroid.Closure

namespace Matroid

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
