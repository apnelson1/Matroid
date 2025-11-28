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

lemma IsMinSepSet.isSepSet (hS : G.IsMinSepSet S) : G.IsSepSet S := hS.toIsSepSet

lemma IsSepSet.eq_empty (hS : G.IsSepSet S) (h : S = ∅) : ¬ G.Connected := by
  have := hS.not_connected
  simp_all only [vertexDelete_empty, not_false_eq_true]

lemma IsSepSet.encard_eq_zero (hS : G.IsSepSet S) (h : S.encard = 0) : ¬ G.Connected := by
  refine hS.eq_empty ?_
  simp_all only [Set.encard_eq_zero]

lemma IsMinSepSet.encard_eq_zero_iff (hS : G.IsMinSepSet S) : S.encard = 0 ↔ ¬ G.Connected := by
  refine ⟨fun h ↦ hS.isSepSet.encard_eq_zero h, ?_⟩
  by_contra! hcon
  obtain ⟨hG, hS_encard⟩ := hcon
  replace hS_encard : 0 < S.encard := by enat_to_nat!; omega
  have empty_isSepSet : G.IsSepSet ∅ := by
    refine ⟨?_, ?_⟩ <;> simp_all
  have := hS.minimal ∅ empty_isSepSet
  simp only [encard_empty] at this
  enat_to_nat!; omega

lemma IsMinSepSet.eq_empty_iff (hS : G.IsMinSepSet S) : S = ∅ ↔ ¬ G.Connected := by
  rw [←Set.encard_eq_zero]
  exact hS.encard_eq_zero_iff

lemma IsMinSepSet.encard_pos_iff (hS : G.IsMinSepSet S) : 0 < S.encard ↔ G.Connected := by
  rw [Set.encard_pos, ←not_iff_not, Set.not_nonempty_iff_eq_empty, ←Set.encard_eq_zero]
  exact hS.encard_eq_zero_iff
