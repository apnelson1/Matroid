import Matroid.Graph.Planarity.Realization.Basic
import Matroid.Graph.Planarity.GraphContinuum.Basic
import Matroid.Graph.Planarity.Topology.Circuit
import Matroid.Graph.Forest


variable {α β E : Type*} [MetricSpace E] {G : Graph α β} {S T : Set α}

open Set Function TopologicalSpace Topology Relation UniformSpace Sum Path
open scoped unitInterval

namespace Graph

theorem K33_not_planar (f : (CompleteBipartiteGraph 3 3).Realization → E)
    (hf : Topology.IsEmbedding f) : ∃ C : Set E, IsCircuit C ∧ C ⊆ range f ∧ IsConnected Cᶜ := by
  sorry
