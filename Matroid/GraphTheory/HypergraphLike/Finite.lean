module

public import Matroid.GraphTheory.HypergraphLike.Basic
public import Mathlib.Data.Set.Finite.Basic

/-!
# Finite hypergraph-like objects

Finiteness concerns the vertices, incidences, and edges of the object, independently of its
ambient label types. Repeated incidences and edges with no incidences are counted separately.
-/

@[expose] public section

namespace HypergraphLike

variable {V ι E Gr : Type*} {G : Gr} [HypergraphLike V ι E G]

/-- A hypergraph-like object is finite when its vertex, incidence, and edge sets are finite. -/
protected class Finite (G : Gr) [HypergraphLike V ι E G] : Prop where
  vertexSet_finite : V(G).Finite
  incidenceSet_finite : I(G).Finite
  edgeSet_finite : E(G).Finite

instance [HypergraphLike.Finite G] : _root_.Finite V(G) := Finite.vertexSet_finite

instance [HypergraphLike.Finite G] : _root_.Finite I(G) := Finite.incidenceSet_finite

instance [HypergraphLike.Finite G] : _root_.Finite E(G) := Finite.edgeSet_finite

end HypergraphLike
