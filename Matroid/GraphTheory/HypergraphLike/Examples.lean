import Matroid.GraphTheory.HypergraphLike.Basic
import Matroid.GraphTheory.GraphTopology.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Order.Cover

universe u v

open Set Function

/-- Prop is a digraph using the implication relation. -/
instance : HypergraphLike Prop ((Prop × Prop) × Bool) (Prop × Prop) Prop where
  verts := univ
  edges := {e | e.1 → e.2}
  incs := {i | cond i.2 (i.1.1 → i.1.2) (i.1.2 → i.1.1)}
  edgeMap' i := ⟨cond i.1.2 i.1.1 i.1.1.swap, by grind⟩
  attach' i := ⟨i.1.1.1, mem_univ _⟩
  IsSource i := i.2 ∧ (i.1.1 → i.1.2)
  IsTarget i := ¬i.2 ∧ (i.1.2 → i.1.1)
  mem_incs_iff i := by grind

/-- The Hasse digraph of a lattice, with edges directed from a vertex to one covering it. -/
instance Lattice.hypergraphLike {α : Type*} (L : Lattice α) :
    HypergraphLike α ((α × α) × Bool) (α × α) L := by
  letI := L
  exact {
    verts := univ
    edges := {e | e.1 ⋖ e.2}
    incs := {i | i.1.1 ⋖ i.1.2}
    edgeMap' i := ⟨i.1.1, i.2⟩
    attach' i := ⟨cond i.1.2 i.1.1.1 i.1.1.2, mem_univ _⟩
    IsSource i := i.2 ∧ i.1.1 ⋖ i.1.2
    IsTarget i := ¬i.2 ∧ i.1.1 ⋖ i.1.2
    mem_incs_iff := by grind }

/-- The Cayley digraph for a group and a chosen element. Edge `x` runs from `x` to `x * p.2`.
The chosen element need not generate the whole group. -/
instance Group.cayleyHypergraphLike {α : Type*} (p : Group α × α) :
    HypergraphLike α (α × Bool) α p := by
  letI := p.1
  exact {
    verts := univ
    edges := univ
    incs := univ
    edgeMap' i := ⟨i.1.1, mem_univ _⟩
    attach' i := ⟨cond i.1.2 i.1.1 (i.1.1 * p.2), mem_univ _⟩
    IsSource i := i.2
    IsTarget i := ¬i.2
    mem_incs_iff := by simp }

/-- A quiver as a directed multigraph, retaining each arrow as a separate edge. -/
instance Quiver.hypergraphLike {V : Type u} (Q : Quiver.{v} V) :
    HypergraphLike V ((Σ x y : V, Q.Hom x y) × Bool) (Σ x y : V, Q.Hom x y) Q where
  verts := univ
  edges := univ
  incs := univ
  edgeMap' i := ⟨i.1.1, mem_univ _⟩
  attach' i := ⟨cond i.1.2 i.1.1.1 i.1.1.2.1, mem_univ _⟩
  IsSource i := i.2
  IsTarget i := ¬i.2
  mem_incs_iff := by simp

/-- A graph-like space as an undirected graph with its geometric edges.
An incidence records an edge and a boundary vertex. The extra Boolean tag distinguishes
the two incidences of a loop; only `false` is used for non-loop incidences. -/
instance GraphLike.hypergraphLike {X : Type*} [TopologicalSpace X] (G : GraphLike X) :
    HypergraphLike X (Set X × X × Bool) (Set X) G where
  verts := G.vertexSet
  edges := G.edgeSet
  incs := {i | i.1 ∈ G.edgeSet ∧ i.2.1 ∈ G.edgeBoundary i.1 ∧
    (i.2.2 = true → G.edgeBoundary i.1 = {i.2.1})}
  edgeMap' i := ⟨i.1.1, i.2.1⟩
  attach' i := ⟨i.1.2.1, i.2.2.1.2⟩
  IsSource i := i.1 ∈ G.edgeSet ∧ i.2.1 ∈ G.edgeBoundary i.1 ∧
    (i.2.2 = true → G.edgeBoundary i.1 = {i.2.1})
  IsTarget i := i.1 ∈ G.edgeSet ∧ i.2.1 ∈ G.edgeBoundary i.1 ∧
    (i.2.2 = true → G.edgeBoundary i.1 = {i.2.1})
  mem_incs_iff := by simp
