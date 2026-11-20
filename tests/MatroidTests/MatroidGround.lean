module

public import Matroid.Connectivity.Separation.Basic

open Matroid Set
open scoped symmDiff

variable {α ι : Type*} {M : Matroid α} {X Y Z : Set α}

example (hX : M.Indep X) (hY : M.IsBase Y) : X ∪ Y ⊆ M.E := by
  grind

example {F : ι → Set α} (hF : ∀ i, M.Indep (F i)) : (⋃ i, F i) ⊆ M.E := by
  grind

example (h : M.Skew X Y) : Y ⊆ M.E := by
  grind

example (h : M.Skew X Y) (hZX : Z ⊆ X) : Z ⊆ M.E := by
  grind

example (P : M.Separation) (i : Bool) (hX : X ⊆ P i) :
    P.toggle X i = P i ∆ X :=
  P.toggle_apply X (i := i)
