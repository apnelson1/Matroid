import Matroid.Graph.Planarity.Realization.Basic
import Matroid.Graph.Planarity.GraphContinuum.Basic
import Matroid.Graph.Planarity.Topology.Circuit
import Matroid.Graph.Forest
import Matroid.Graph.Planarity.CycleList.Basic
import Matroid.Graph.Minor.Conn


variable {α β E : Type*} [MetricSpace E] {G C : Graph α β} {S T : Set α} {u v : α}

open Set Function TopologicalSpace Topology Relation UniformSpace Sum Path
open scoped unitInterval

namespace Graph

lemma K5_lemma (hCG : C ≤ G) (hC : IsCycle C) (hu : u ∈ V(G)) (hv : v ∈ V(G)) (huv : u ≠ v)
    (hadj : G.Adj u v) (h : 3 ≤ (V(C) ∩ N(G, u) ∩ N(G, v)).encard) : CompleteGraph 5 ≤m G := by
  sorry

lemma K33_lemma (hCG : C ≤ G) (hC : IsCycle C) (hu : u ∈ V(G)) (hv : v ∈ V(G)) (huv : u ≠ v)
    (hadj : G.Adj u v) (h : sorry) : CompleteBipartiteGraph 3 3 ≤m G := by
  sorry

-- theorem K33_not_planar (f : (CompleteBipartiteGraph 3 3).Realization → E)
--     (hf : Topology.IsEmbedding f) : ∃ C : Set E, IsCircuit C ∧ C ⊆ range f ∧ IsConnected Cᶜ := by
--   sorry
