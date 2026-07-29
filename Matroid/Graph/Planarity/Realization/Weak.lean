import Matroid.Graph.Planarity.Realization.Basic

/-!
# The weak realization of a graph

`Graph.Realization G` is the point-set quotient used to construct a graph realization.  This file
gives that quotient topology an explicit, tagged carrier, `Graph.Realization.Weak G`.  Keeping the
tag separate from the point-set quotient lets the weak topology coexist with the unit-edge metric
topology defined in `Realization.Metric`.
-/

open Function TopologicalSpace Topology
open scoped unitInterval

namespace Graph.Realization

variable {α β : Type*} (G : Graph α β)

/-- The quotient (or weak CW) topology on the point-set realization. -/
noncomputable abbrev quotientTopology : TopologicalSpace G.Realization :=
  TopologicalSpace.coinduced
    (Quotient.mk' (s := G.glueRel) : G.PreRealization → G.Realization)
    (inferInstance : TopologicalSpace G.PreRealization)

lemma quotientTopology_eq :
    quotientTopology G = (inferInstance : TopologicalSpace G.Realization) := by
  rfl

/--
The realization of `G` with its weak CW topology.

This is a type tag in the style of `OrderDual`: it is definitionally the point-set realization,
while typeclass inference can attach the weak topology to the tagged head.
-/
def Weak := G.Realization

noncomputable instance : TopologicalSpace (Weak G) := quotientTopology G

namespace Weak

/-- Reinterpret a point-set realization as a weak realization. -/
@[match_pattern, implicit_reducible]
def ofRealization : G.Realization ≃ Weak G := Equiv.refl _

/-- Forget the weak topology tag. -/
@[match_pattern, implicit_reducible]
def toRealization : Weak G ≃ G.Realization := Equiv.refl _

/-- The weak realization is homeomorphic to the underlying quotient with its quotient topology. -/
noncomputable def homeomorph : Weak G ≃ₜ G.Realization where
  toEquiv := toRealization G
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

end Weak

/-- The quotient map from the pre-realization to the weak realization. -/
def preToWeak (x : G.PreRealization) : Weak G :=
  Quotient.mk' (s := G.glueRel) x

/-- The pre-realization projection is a quotient map onto the weak realization. -/
theorem preToWeak_isQuotientMap : IsQuotientMap (preToWeak G) :=
  isQuotientMap_quotient_mk'

namespace Weak

/-- Include a graph vertex in the weak realization. -/
def vertexMk (v : V(G)) : Weak G :=
  G.vertexMk v

/-- Parametrize an edge in the weak realization. -/
noncomputable def edgePath (e : E(G))  :=
  G.edgePath e

@[simp]
lemma toRealization_vertexMk (v : V(G)) :
    toRealization G (vertexMk G v) = G.vertexMk v := rfl

@[simp]
lemma toRealization_edgePath (e : E(G)) (t : I) :
    toRealization G (edgePath G e t) = G.edgePath e t := rfl

end Weak

end Graph.Realization
