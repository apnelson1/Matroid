import Matroid.Graph.Planarity.GraphContinuum.Realization
import Matroid.Graph.Planarity.GraphContinuum.Basic


variable {α β E : Type*} {G : Graph α β} {S T : Set α}

open Set Function TopologicalSpace Topology Relation UniformSpace Sum Path
open scoped unitInterval

namespace Graph

theorem K33_not_planar (f : (CompleteBipartiteGraph 3 3).Realization → E)
    (hf : Topology.IsEmbedding f) : 
