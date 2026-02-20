import Matroid.Connectivity.Separation.Tutte

variable {α : Type*} {M : Matroid α} {N : Bool → Matroid α} {e f : α} {X C D : Set α}
  {i j b c : Bool} {k : ℕ∞}

open Set Matroid.Separation Bool



namespace Matroid
