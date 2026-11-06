/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Matroid.GraphTheory.IncidenceHypergraph.Basic
public import Matroid.GraphTheory.HypergraphLike.Hierarchy.GraphLike
public import Matroid.GraphTheory.HypergraphLike.Hierarchy.Directed

/-!
# Incidence graphs

This file defines multigraphs by extending `IncidenceHypergraph` with a pairing of the two
incidences of each edge. The two incidences remain distinct for a loop.

The `HypergraphLike` instance inherits the incidence maps, support sets, links, adjacency, and
incidence counts from the underlying hypergraph. Its scoped notation `V(G)`, `I(G)`, and `E(G)`
denotes the active vertex, incidence, and edge sets.
-/

@[expose] public section

open Set HypergraphLike

/-- An incidence based multigraph with two paired incidences for every edge. -/
structure Pseudograph (V I E : Type*) extends IncidenceHypergraph V I E where
  /-- Every edge has an incidence associated with it. -/
  edgeMap_range : range edgeMap' = edgeSet
  /-- The other incidence of the same edge. -/
  other' : incidenceSet → incidenceSet
  /-- The two incidences of an edge are distinct, including for a loop. -/
  other'_ne : ∀ i, other' i ≠ i
  /-- The other incidence is associated with the same edge. -/
  edgeMap'_other' : ∀ i, edgeMap' (other' i) = edgeMap' i
  /-- Every incidence of an edge is one of its two paired incidences. -/
  edgeMap'_eq : ∀ i j, edgeMap' i = edgeMap' j → j = i ∨ j = other' i

initialize_simps_projections Pseudograph
  (as_prefix vertexSet, as_prefix incidenceSet, as_prefix edgeSet)

variable {V I E : Type*} {G H : Pseudograph V I E} {i j : I}

namespace Pseudograph

instance : HypergraphLike V I E G where
  verts := G.vertexSet
  edges := G.edgeSet
  incs := G.incidenceSet
  edgeMap' i := ⟨G.edgeMap' i, G.edgeMap'_mem i⟩
  attach' i := ⟨G.attach' i, G.attach'_mem i⟩
  IsSource i := i ∈ G.incidenceSet
  IsTarget i := i ∈ G.incidenceSet
  mem_incs_iff i := by simp

instance : Undirected G where
  isSource_iff i := by simp [IsSource, IsTarget]

instance : GraphLike G where
  other' := G.other'
  edgeMap'_other' i := Subtype.ext <| G.edgeMap'_other' i
  other'_ne := G.other'_ne
  edgeMap'_eq i j hij := G.edgeMap'_eq i j (congrArg Subtype.val hij)
  exists_isSource_of_mem_edgeSet' e he := by
    obtain ⟨i, rfl⟩ := G.edgeMap_range.symm ▸ show e ∈ G.edgeSet from he
    use i, rfl, isSource_of_mem_incs <| Subtype.coe_prop i
  exists_isTarget_of_mem_edgeSet' e he := by
    obtain ⟨i, rfl⟩ := G.edgeMap_range.symm ▸ show e ∈ G.edgeSet from he
    use i, rfl, isTarget_of_mem_incs <| Subtype.coe_prop i

/-- Two pseudographs are equal if their active sets and incidence maps agree. -/
@[ext]
lemma ext (hV : V(G) = V(H)) (hI : I(G) = I(H)) (hE : E(G) = E(H))
    (hEdge : ∀ (i) (hiG : i ∈ I(G)) (hiH : i ∈ I(H)), G.edgeMap' ⟨i, hiG⟩ = H.edgeMap' ⟨i, hiH⟩)
    (hAttach : ∀ (i) (hiG : i ∈ I(G)) (hiH : i ∈ I(H)),
    G.attach' ⟨i, hiG⟩ = H.attach' ⟨i, hiH⟩) : G = H := by
  cases G with | mk G hG Gother hnG heG huG =>
  cases H with | mk H hH Hother hnH heH huH =>
  obtain rfl : G = H := IncidenceHypergraph.ext hV hI hE hEdge hAttach
  obtain rfl : Gother = Hother :=
    funext fun i ↦ ((huG i (Hother i) (heH i).symm).resolve_left (hnH i)).symm
  rfl

end Pseudograph
