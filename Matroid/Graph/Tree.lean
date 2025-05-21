import Matroid.Graphic
import Matroid.Graph.Distance

variable {α β : Type*} {G H T : Graph α β} {u v x y z : α} {e e' f g : β} {X : Set α} {F : Set β}
{P C Q : WList α β}
open Set WList

namespace Graph

@[mk_iff]
structure IsTree (T : Graph α β) : Prop where
  isForest : T.IsForest
  connected : T.Connected

/-- If `G` is connected, then a maximally acylic subgraph of `G` is connected.
The correct statement is that any two vertices connected in the big graph are
connected in the small one.
TODO : Write the proof completely in terms of `IsAcyclicSet`
-/
lemma Connected.isTree_of_maximal_isAcyclicSet (hG : G.Connected) (hF : Maximal G.IsAcyclicSet F) :
    (G ↾ F).IsTree := by
  rw [show G.IsAcyclicSet = fun X ↦ X ⊆ E(G) ∧ (G ↾ X).IsForest by
    ext; exact isAcyclicSet_iff] at hF
  refine ⟨hF.prop.2, by_contra fun hcon ↦ ?_⟩
  obtain ⟨S, e, x, y, heF, hx, hy, hxy⟩ := hG.exists_of_edgeRestrict_not_connected hcon
  have hne : x ≠ y := S.disjoint.ne_of_mem hx hy
  have hx' : x ∉ S.right := S.disjoint.not_mem_of_mem_left hx
  have hy' : y ∉ S.left := S.disjoint.not_mem_of_mem_right hy
  have hFac : (G ↾ F).IsForest := hF.prop.2
  have h_left : (G ↾ F)[S.left].IsForest := hFac.mono (induce_le S.left_subset)
  have h_right : (G ↾ F)[S.right].IsForest := hFac.mono (induce_le S.right_subset)
  have h_left' := h_left.union_isForest_of_subsingleton_inter (singleEdge_isForest hne e) ?_; swap
  · rw [induce_vertexSet, singleEdge_vertexSet, pair_comm, inter_insert_of_not_mem hy']
    exact Subsingleton.inter_singleton
  have h' := h_left'.union_isForest_of_subsingleton_inter h_right ?_; swap
  · simp only [union_vertexSet, induce_vertexSet, singleEdge_vertexSet, union_insert,
      union_singleton]
    rw [insert_inter_of_not_mem hx', insert_inter_of_mem hy, S.disjoint.inter_eq]
    simp
  have hins : insert e F ⊆ E(G) := insert_subset hxy.edge_mem hF.prop.1
  refine heF <| hF.mem_of_prop_insert ⟨hins, h'.mono ?_⟩
  rw [(Compatible.of_disjoint_edgeSet (by simp [heF])).union_comm (G := (G ↾ F)[S.left]),
    Graph.union_assoc, ← S.eq_union]
  refine le_of_le_le_subset_subset (G := G) (by simp) (union_le (by simpa) (by simp)) (by simp) ?_
  simp [inter_eq_self_of_subset_left hins, inter_eq_self_of_subset_left hF.prop.1]

/-- Every connected graph has a spanning tree -/
lemma Connected.exists_isTree_spanningSubgraph (hG : G.Connected) : ∃ T, T.IsTree ∧ T ≤s G := by
  obtain ⟨B, hB⟩ := G.cycleMatroid.exists_isBase
  refine ⟨G ↾ B, ?_, by simp⟩
  rw [Matroid.isBase_iff_maximal_indep, cycleMatroid_indep] at hB
  exact hG.isTree_of_maximal_isAcyclicSet hB
