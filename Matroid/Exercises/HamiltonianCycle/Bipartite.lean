import Matroid.Graph.Independent
import Matroid.ForMathlib.Minimal
import Matroid.ForMathlib.Tactic.ENatToNat
import Matroid.Graph.Bipartite

import Matroid.Exercises.HamiltonianCycle.Degree
import Matroid.Exercises.HamiltonianCycle.Walk

open Set

namespace Graph

variable {α β ι : Type*} {x y z u v : α} {e f : β} {G H : Graph α β}
variable {X S A : Set α} {F : Set β}

variable {B : G.Bipartition}

lemma Bipartition.Same.not_adj (h : B.Same x y) : ¬ G.Adj x y := by
  wlog hx : x ∈ B.left generalizing B x y with aux
  · rw [notMem_left_iff] at hx
    rw [←B.symm_same] at h
    swap
    · exact h.left_mem
    exact aux h hx
  intro hadj
  refine h.not_opp ?_
  exact B.opp_of_adj hadj

lemma Bipartition.same_of_mem_left_of_mem_left
    (hx : x ∈ B.left) (hy : y ∈ B.left) : B.Same x y :=
  ⟨B.left_subset hx, B.left_subset hy, by tauto⟩

lemma Bipartition.same_of_mem_right_of_mem_right
    (hx : x ∈ B.right) (hy : y ∈ B.right) : B.Same x y := by
  rw [←B.symm_same]
  refine ⟨B.right_subset hx, B.right_subset hy, by tauto⟩

lemma Bipartition.opp_of_mem_left_of_mem_right
    (hx : x ∈ B.left) (hy : y ∈ B.right) : B.Opp x y :=
  ⟨B.left_subset hx, B.right_subset hy, by tauto⟩

lemma Bipartition.opp_of_mem_right_of_mem_left
    (hx : x ∈ B.right) (hy : y ∈ B.left) : B.Opp x y := by
  rw [←B.symm_opp]
  exact ⟨B.right_subset hx, B.left_subset hy, by tauto⟩

lemma Bipartition.left_pairwise_not_adj (B : G.Bipartition) :
    B.left.Pairwise fun x y ↦ ¬ G.Adj x y := by
  intro x hx y hy hne
  refine Bipartition.Same.not_adj (B := B) ?_
  exact B.same_of_mem_left_of_mem_left hx hy

lemma Bipartition.right_pairwise_not_adj (B : G.Bipartition) :
    B.right.Pairwise fun x y ↦ ¬ G.Adj x y := by
  intro x hx y hy hne
  refine Bipartition.Same.not_adj (B := B) ?_
  exact B.same_of_mem_right_of_mem_right hx hy

lemma Bipartition.left_isIndependent (B : G.Bipartition) : G.IsIndependent B.left :=
  ⟨B.left_subset, B.left_pairwise_not_adj⟩

lemma Bipartition.right_isIndependent (B : G.Bipartition) : G.IsIndependent B.right :=
  ⟨B.right_subset, B.right_pairwise_not_adj⟩

lemma Bipartition.subset_left_isIndependent (h : S ⊆ B.left) : G.IsIndependent S :=
  B.left_isIndependent.mono h

lemma Bipartition.subset_right_isIndependent (h : S ⊆ B.right) : G.IsIndependent S :=
  B.right_isIndependent.mono h

lemma Bipartition.isMaxIndependent_encard_ge (B : G.Bipartition) (hS : G.IsMaxIndependent S) :
    V(G).encard ≤ 2 * S.encard := by
  rw [←B.union_eq, Set.encard_union_eq B.disjoint]
  wlog hle : B.left.encard ≤ B.right.encard generalizing B with aux
  · simp only [not_le] at hle
    specialize aux B.symm hle.le
    simp only [symm_left, symm_right, add_comm] at aux
    assumption
  obtain (h|h) := Classical.em (S.encard = ⊤)
  · simp_all
  suffices : B.right.encard ≤ S.encard
  · enat_to_nat! <;> omega
  exact hS.2 _ B.right_isIndependent
