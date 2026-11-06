import Matroid.GraphTheory.HypergraphLike.Basic
import Matroid.GraphTheory.GraphTopology.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Order.Cover
import Mathlib.GroupTheory.Generators

open Set Function

/-- Prop is a digraph using the implication relation. -/
instance : HypergraphLike Prop ((Prop × Prop) × Bool) (Prop × Prop) Prop where
  verts := univ
  edges := {e | e.1 → e.2}
  incs := {i | i.1.1 → i.1.2}
  edgeMap' i := ⟨i.1.1, i.2⟩
  attach' i := ⟨cond i.1.2 i.1.1.2 i.1.1.1, mem_univ _⟩
  IsSource i := !i.2 ∧ (i.1.1 → i.1.2)
  IsTarget i := i.2 ∧ (i.1.1 → i.1.2)
  mem_incs_iff i := by grind

/-- The Hasse digraph of a lattice, with edges directed from a vertex to one covering it. -/
instance Lattice.hypergraphLike (α : Type*) [Lattice α] :
    HypergraphLike α ((α × α) × Bool) (α × α) α where
  verts := univ
  edges := {e | e.1 ⋖ e.2}
  incs := {i | i.1.1 ⋖ i.1.2}
  edgeMap' i := ⟨i.1.1, i.2⟩
  attach' i := ⟨cond i.1.2 i.1.1.2 i.1.1.1, mem_univ _⟩
  IsSource i := !i.2 ∧ i.1.1 ⋖ i.1.2
  IsTarget i := i.2 ∧ i.1.1 ⋖ i.1.2
  mem_incs_iff := by grind

/-- The Cayley digraph for a group and a chosen generating set -/
@[instance_reducible]
def Group.hypergraphLike {α ι : Type*} [Group α] (p : Group.Generators α ι) :
    HypergraphLike α ((α × ι) × Bool) (α × ι) α where
  verts := univ
  edges := univ
  incs := univ
  edgeMap' i := ⟨i.val.fst, mem_univ _⟩
  attach' i := ⟨cond i.val.snd (i.val.fst.fst * p.val i.val.fst.snd) i.val.fst.fst, mem_univ _⟩
  IsSource i := !i.2
  IsTarget i := i.2
  mem_incs_iff := by simp

/-- A quiver as a directed multigraph, retaining each arrow as a separate edge. -/
instance Quiver.hypergraphLike (V : Type*) [Quiver V] :
    HypergraphLike V ((Σ x y : V, Hom x y) × Bool) (Σ x y : V, Hom x y) V where
  verts := univ
  edges := univ
  incs := univ
  edgeMap' i := ⟨i.1.1, mem_univ _⟩
  attach' i := ⟨cond i.1.2 i.1.1.2.1 i.1.1.1, mem_univ _⟩
  IsSource i := !i.2
  IsTarget i := i.2
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
