import Mathlib.Tactic
import Mathlib.Data.Set.Finite.Basic
import Matroid.Graph.Connected.Basic
import Matroid.Graph.Independent
import Matroid.Graph.Tree
import Matroid.ForMathlib.Minimal
import Matroid.Graph.Walk.Index
import Matroid.ForMathlib.Tactic.ENatToNat

import Matroid.Exercises.HamiltonianCycle.NeBot
import Matroid.Exercises.HamiltonianCycle.Degree
import Matroid.Exercises.HamiltonianCycle.Walk

open Set

namespace Graph

variable {α β ι : Type*} {x y z u v : α} {e f : β} {G H : Graph α β}
variable {S A : Set α}

lemma IsIndependent.mono (hS : G.IsIndependent S) (hle : A ⊆ S) : G.IsIndependent A :=
  ⟨hle.trans hS.subset_vxSet, hS.pairwise_nonadj.mono hle⟩

lemma IsMaxIndependent.isIndependent (hS : G.IsMaxIndependent S) : G.IsIndependent S :=
  hS.1
