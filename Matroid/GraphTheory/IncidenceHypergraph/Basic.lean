/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Data.ENat.Basic
public import Matroid.GraphTheory.HypergraphLike.Degree
public import Matroid.GraphTheory.HypergraphLike.Hierarchy.Directed

/-!
# Incidence hypergraphs

This file defines hypergraphs with ambient vertex, incidence, and edge types. Each active
incidence has an associated edge and an attached vertex. The underlying data is a span of sets
`V(G) ← I(G) → E(G)`, as in the span definition of a hypergraph described by
[nLab](https://ncatlab.org/nlab/show/hypergraph).

`IncidenceHypergraph` permits repeated incidences, isolated vertices, and edges with no incidences.
Its `HypergraphLike` instance marks every active incidence as both a source and a target. The
incidence maps, support sets, links, adjacency, degree, order, uniformity, and regularity come from
that interface. Its scoped notation `V(G)`, `I(G)`, and `E(G)` denotes the active sets.

The operation `IncidenceHypergraph.dual` exchanges vertices and edges while preserving incidence
labels.
-/

@[expose] public section

variable {V I E : Type*}

open Set Function HypergraphLike

/-- An incidence hypergraph on ambient vertex, incidence, and edge types `ν`, `ι`, and `ε`. -/
structure IncidenceHypergraph (V I E : Type*) where
  /-- The vertices present in the hypergraph. -/
  vertexSet : Set V
  /-- The incidences present in the hypergraph. -/
  incidenceSet : Set I
  /-- The edges present in the hypergraph. -/
  edgeSet : Set E
  /-- The edge associated with an active incidence. -/
  edgeMap' : incidenceSet → E
  /-- Every incidence is associated with an edge of the hypergraph. -/
  edgeMap'_mem : ∀ i, edgeMap' i ∈ edgeSet
  /-- The vertex attached to an active incidence. -/
  attach' : incidenceSet → V
  /-- Every incidence is attached to a vertex of the hypergraph. -/
  attach'_mem : ∀ i, attach' i ∈ vertexSet

initialize_simps_projections IncidenceHypergraph
  (as_prefix vertexSet, as_prefix incidenceSet, as_prefix edgeSet)

namespace IncidenceHypergraph

instance {G : IncidenceHypergraph V I E} : HypergraphLike V I E G where
  verts := G.vertexSet
  edges := G.edgeSet
  incs := G.incidenceSet
  edgeMap' i := ⟨G.edgeMap' i, G.edgeMap'_mem i⟩
  attach' i := ⟨G.attach' i, G.attach'_mem i⟩
  IsSource i := i ∈ G.incidenceSet
  IsTarget i := i ∈ G.incidenceSet
  mem_incs_iff i := by simp

instance {G : IncidenceHypergraph V I E} : Undirected G where
  isSource_iff i := by simp [IsSource, IsTarget]

variable {G H : IncidenceHypergraph V I E} {e : E} {v : V} {k : ℕ∞}

/-- Two incidence hypergraphs are equal if their active sets and incidence maps agree. -/
@[ext]
protected lemma ext {G H : IncidenceHypergraph V I E} (hV : V(G) = V(H)) (hI : I(G) = I(H))
    (hE : E(G) = E(H)) (hEdge : ∀ (i : I) (hiG : i ∈ I(G)) (hiH : i ∈ I(H)),
    G.edgeMap' ⟨i, hiG⟩ = H.edgeMap' ⟨i, hiH⟩) (hAttach : ∀ (i : I) (hiG : i ∈ I(G))
    (hiH : i ∈ I(H)), G.attach' ⟨i, hiG⟩ = H.attach' ⟨i, hiH⟩) : G = H := by
  cases G
  cases H
  cases hI
  simp_all [verts, incs, edges, funext_iff]

/-! ### Duality -/

/-- The incidence dual, obtained by exchanging vertices and edges while preserving incidences. -/
@[simps vertexSet incidenceSet edgeSet]
def dual (G : IncidenceHypergraph V I E) : IncidenceHypergraph E I V where
  vertexSet := E(G)
  incidenceSet := I(G)
  edgeSet := V(G)
  edgeMap' := G.attach'
  edgeMap'_mem := G.attach'_mem
  attach' := G.edgeMap'
  attach'_mem := G.edgeMap'_mem

@[simp]
lemma edgeMap_dual [Nonempty V] (G : IncidenceHypergraph V I E) (i : I) :
    edgeMap G.dual i = attach G i := rfl

@[simp]
lemma attach_dual [Nonempty E] (G : IncidenceHypergraph V I E) (i : I) :
    attach G.dual i = edgeMap G i := rfl

@[simp]
lemma dual_dual (G : IncidenceHypergraph V I E) : G.dual.dual = G := rfl

@[simp]
lemma mem_incVerts_dual : e ∈ incVerts G.dual v ↔ v ∈ incVerts G e := mem_incEdges (G := G)

lemma dual_bijective : Bijective (dual : IncidenceHypergraph V I E → _) :=
  ⟨LeftInverse.injective dual_dual, RightInverse.surjective dual_dual⟩

@[simp]
lemma dual_inj : G.dual = H.dual ↔ G = H := dual_bijective.injective.eq_iff

@[simp]
lemma degree_dual (G : IncidenceHypergraph V I E) (e : E) : degree G.dual e = order G e := rfl

@[simp]
lemma order_dual (G : IncidenceHypergraph V I E) (v : V) : order G.dual v = degree G v := rfl

@[simp]
lemma isUniform_dual : IsUniform G.dual k ↔ IsRegular G k := Iff.rfl

@[simp]
lemma isRegular_dual : IsRegular G.dual k ↔ IsUniform G k := Iff.rfl

variable {W J F : Type*}

def comap (f : J → I) (G : IncidenceHypergraph V I E) : IncidenceHypergraph V J E where
  vertexSet := V(G)
  incidenceSet := f ⁻¹' I(G)
  edgeSet := E(G)
  edgeMap' j := G.edgeMap' ⟨f j, j.prop⟩
  edgeMap'_mem j := G.edgeMap'_mem ⟨f j, j.prop⟩
  attach' j := G.attach' ⟨f j, j.prop⟩
  attach'_mem j := G.attach'_mem ⟨f j, j.prop⟩

def vertexMap (f : V → W) (G : IncidenceHypergraph V I E) : IncidenceHypergraph W I E where
  vertexSet := f '' V(G)
  incidenceSet := I(G)
  edgeSet := E(G)
  edgeMap' i := G.edgeMap' ⟨i, i.prop⟩
  edgeMap'_mem i := G.edgeMap'_mem ⟨i, i.prop⟩
  attach' i := f (G.attach' i)
  attach'_mem i := mem_image_of_mem f <| G.attach'_mem ⟨i, i.prop⟩

def edgeMap (f : E → F) (G : IncidenceHypergraph V I E) : IncidenceHypergraph V I F where
  vertexSet := V(G)
  incidenceSet := I(G)
  edgeSet := f '' E(G)
  edgeMap' i := f (G.edgeMap' i)
  edgeMap'_mem i := mem_image_of_mem f <| G.edgeMap'_mem i
  attach' i := G.attach' i
  attach'_mem i := G.attach'_mem i

end IncidenceHypergraph
