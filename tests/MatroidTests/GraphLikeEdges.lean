module

import Matroid.GraphLike.Basic
import Matroid.Graph.Basic
import MatroidTests.ConnectedComponentSets

/-! # Raw geometric-edge consumers

Ordinary edge lemmas use point sets and membership hypotheses. A subtype is used below only
for the equivalence with construction components. The two graph notations coexist.
-/

open Set
open scoped GraphLike Graph

variable {X V E : Type*} [TopologicalSpace X] (G H : GraphLike X) (J : Graph V E)
  {e f : Set X} {x y : X}

example : (E(G) : Set (Set X)) = G.edgeSet := rfl
example : V(G) = G.vertexSet := rfl
example : E(J) = J.edgeSet := rfl
example : V(J) = J.vertexSet := rfl

example (he : e ∈ E(G)) : e ⊆ G.carrier := G.edge_subset he

example (he : e ∈ E(G)) (hf : f ∈ E(G)) (hne : e ≠ f) : e ∩ f ⊆ V(G) :=
  G.edge_inter_subset_vertexSet he hf hne

example (he : e ∈ E(G)) : IsCompact e := G.edge_isCompact he

example (he : e ∈ E(G)) : IsConnected (e \ V(G)) := G.edgeInterior_isConnected he

example (he : e ∈ E(G)) (hb : G.edgeBoundary e = {x, y}) : IsPrimitiveLink e x y :=
  G.edge_isPrimitiveLink he hb

example (h : G.IsLink e x y) : e ∈ E(G) ∧ x ∈ V(G) ∧ y ∈ V(G) ∧ x ∈ e ∧ y ∈ e :=
  ⟨h.edge_mem, h.left_mem, h.right_mem, h.isPrimitiveLink.left_mem, h.isPrimitiveLink.right_mem⟩

-- A point set can be an edge of two spaces without any edge-index transport.
example (hG : e ∈ E(G)) (hH : e ∈ E(H)) : e ⊆ G.carrier ∩ H.carrier :=
  subset_inter (G.edge_subset hG) (H.edge_subset hH)

example [G.Finite] : E(G).Finite := GraphLike.Finite.edgeSet_finite

example : G.carrier = V(G) ∪ ⋃₀ E(G) := G.carrier_eq_vertexSet_union_sUnion_edges

-- Subtypes are appropriate here: this is an equivalence of actual edge collections.
example (c : ConnectedComponents ↥(G.carrier \ V(G))) :
    (G.componentEdgeEquiv c).1 = G.carrier ∩ closure (Subtype.val '' c.toSet) :=
  G.componentEdgeEquiv_coe c

example (e : E(G)) :
    G.carrier ∩ closure (Subtype.val '' (G.componentEdgeEquiv.symm e).toSet) = e.1 :=
  G.componentEdgeEquiv_symm_range e

/-- info: 'GraphLike.edge_isPrimitiveLink' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GraphLike.edge_isPrimitiveLink
/-- info: 'GraphLike.componentEdgeEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GraphLike.componentEdgeEquiv
