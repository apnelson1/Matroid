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

lemma IsIndependent.subset (hS : G.IsIndependent S) : S ⊆ V(G) := hS.1

lemma IsMaxIndependent.isIndependent (hS : G.IsMaxIndependent S) : G.IsIndependent S :=
  hS.1

lemma IsMaxIndependent.subset (hS : G.IsMaxIndependent S) : S ⊆ V(G) := hS.isIndependent.subset

lemma IsMaxIndependent.encard_eq_zero_iff_vertexSet_empty (hS : G.IsMaxIndependent S) :
    S.encard = 0 ↔ V(G) = ∅ := by
  refine ⟨?_, ?_⟩
  · intro hyp
    by_contra! hcon
    obtain ⟨x, hx⟩ := hcon
    rw [← isIndependent_singleton] at hx
    have := hS.2 _ hx
    simp_all
  rw [encard_eq_zero]
  by_contra! hcon
  rw [←not_nonempty_iff_eq_empty] at hcon
  obtain ⟨x, hx⟩ := hcon.2
  exact hcon.1 ⟨x, hS.subset hx⟩
