import Matroid.Connectivity.Higher

open Set

namespace Matroid

section separation

variable {α : Type*} {M : Matroid α} {j k : ℕ∞} {a b e f : α} {A B X Y : Set α}

abbrev ThreeConnected (M : Matroid α) := M.IsTutteConnected 3

abbrev InternallyThreeConnected (M : Matroid α) := M.IsInternallyConnected 3

theorem bixby (M : Matroid α) (hM : M.IsTutteConnected 3) (he : e ∈ M.E) :
    (M ／ {e}).IsInternallyConnected 3 ∨ (M ＼ {e}).IsInternallyConnected 3 := by
  sorry
  -- (WLOG `e ∈ M.E`.)
