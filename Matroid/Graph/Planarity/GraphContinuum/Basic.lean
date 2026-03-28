import Matroid.Graph.Planarity.GraphContinuum.Realization
import Matroid.Graph.Planarity.Topology.ConnPartition

variable {α β : Type*} {G : Graph α β} {S T : Set α}

open Set Function TopologicalSpace Topology Relation UniformSpace Sum Path WList
open scoped unitInterval

/-!
# Basic properties of graph continua
-/

class GraphContinuum (α : Type*) extends EMetricSpace α, CompactSpace α where
  verts : Set α
  graphLike : ∀ T ∈ ComponentPartition verts, T ≃ₜ (Set.Ioo 0 1 : Set ℝ)

namespace GraphContinuum

variable [GraphContinuum α]

scoped notation "V(" α ")" => GraphContinuum.verts (α := α)

def edges (α) [GraphContinuum α] : Partition (Set α) := ComponentPartition V(α)

scoped notation "E(" α ")" => GraphContinuum.edges (α := α)

def homeo_Ioo (hT : T ∈ E(α)) : T ≃ₜ (Set.Ioo 0 1 : Set ℝ) := graphLike T hT


