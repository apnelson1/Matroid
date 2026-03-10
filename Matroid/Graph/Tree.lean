import Matroid.Graph.AcyclicSet
import Matroid.Graphic

variable {α β : Type*} {G H T : Graph α β} {u v x y z : α} {e e' f g : β} {X : Set α} {F : Set β}
{P C Q : WList α β}
open Set WList

namespace Graph

/-- If `G` is connected, then a maximally acylic subgraph of `G` is connected.
The correct statement is that any two vertices connected in the big graph are
connected in the small one. -/
lemma Connected.isTree_of_maximal_isAcyclicSet (hG : G.Connected) (hF : Maximal G.IsAcyclicSet F) :
    (G ↾ F).IsTree where
  isForest := by
    rw [show G.IsAcyclicSet = fun X ↦ X ⊆ E(G) ∧ (G ↾ X).IsForest by
      ext; exact isAcyclicSet_iff] at hF
    exact hF.prop.2
  connected := by
    refine connected_iff.mpr ⟨hG.nonempty, fun x y hx hy ↦ ?_⟩
    rw [IsMaximalAcyclicSet.connBetween_iff hF]
    exact hG.pre x y hx hy

-- lemma Connected.isBase_cycleMatroid_iff (hG : G.Connected) {T} :
--     G.cycleMatroid.IsBase T ↔ (G ↾ T).IsTree := by
--   rw [Matroid.isBase_iff_maximal_indep, cycleMatroid_indep]
--   refine ⟨fun h ↦ hG.isTree_of_maximal_isAcyclicSet h, fun h ↦ ?_⟩

  -- have := h.

/-- Every connected graph has a spanning tree -/
lemma Connected.exists_isTree_spanningSubgraph (hG : G.Connected) : ∃ T, T.IsTree ∧ T ≤s G := by
  obtain ⟨B, hB⟩ := G.cycleMatroid.exists_isBase
  refine ⟨G ↾ B, ?_, by simp⟩
  rw [Matroid.isBase_iff_maximal_indep, cycleMatroid_indep] at hB
  exact hG.isTree_of_maximal_isAcyclicSet hB

lemma Connected.encard_vertexSet_le (hG : G.Connected) : V(G).encard ≤ E(G).encard + 1 := by
  obtain ⟨T, hT, hTG⟩ := hG.exists_isTree_spanningSubgraph
  grw [← hTG.vertexSet_eq, hT.encard_vertexSet, hTG.le]

lemma Connected.ncard_vertexSet_le [G.Finite] (hG : G.Connected) : V(G).ncard ≤ E(G).ncard + 1 := by
  rw [← ENat.coe_le_coe, Nat.cast_add, G.vertexSet_finite.cast_ncard_eq,
    G.edgeSet_finite.cast_ncard_eq]
  exact hG.encard_vertexSet_le
