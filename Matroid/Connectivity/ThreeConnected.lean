import Matroid.Connectivity.Separation

open Set

namespace Matroid

section separation

variable {α : Type*} {M : Matroid α} {j k : ℕ∞} {a b e f : α} {A B X Y : Set α}



theorem bixby (M : Matroid α) (hM : M.TutteConnected 3) (he : e ∈ M.E) :
    (M ／ {e}).InternallyConnected 3 ∨ (M ＼ {e}).InternallyConnected 3 := by
  -- (WLOG `e ∈ M.E`.)
