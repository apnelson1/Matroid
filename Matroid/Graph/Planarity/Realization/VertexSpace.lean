module

public import Matroid.Graph.Finite
public import Mathlib.Topology.UniformSpace.Basic

/-!
# The discrete `0`-skeleton of a graph

Both realization models — the whole-edge quotient in `Realization.Basic` and the incidence
(half-edge) quotient in `Realization.Presentation` — glue their cells onto the same discrete
vertex space.  The instances live here so that neither development has to import the other.

**Do not fold this back into `Realization.Basic`.**  The incidence model is being grown to parity
in order to replace the whole-edge one, and this file is what keeps the two decoupled: it is meant
to survive when `Realization.Basic` is deleted.  Merging it back would silently re-couple them.
-/

public section

open Set Function

namespace Graph

variable {α β : Type*} {G : Graph α β}

/-- Discrete uniformity (hence discrete topology) on vertices. -/
instance (G : Graph α β) : UniformSpace V(G) := ⊥

instance : DiscreteTopology V(G) where
  eq_bot := rfl

instance instFiniteVertex [G.Finite] : Finite V(G) := G.vertexSet_finite
instance instFiniteEdge [G.EdgeFinite] : Finite E(G) := G.edgeSet_finite

end Graph
