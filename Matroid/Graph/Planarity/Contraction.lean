module

public import Matroid.Graph.Planarity.FaceCycle

/-!
# Contraction and vertex splitting in a polygonal plane drawing

This file connects the face-cycle API to the 3-connected Kuratowski induction. Its theorems find
facial cycles after deleting or contracting a vertex and use two arcs of such a cycle to split the
contracted vertex. The construction works with `PLDrawing`; the final conclusion is `G.Planar`.
-/

open Set

-- Mathlib's `Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n)` is `scoped`. Without this
-- `open`, the two general theorems below cannot be instantiated at `EuclideanSpace ℝ (Fin 2)`,
-- which is what `planar_of_contract_of_facial_cycle_two_paths` needs of them.
open scoped EuclideanSpace

namespace Graph

public noncomputable section

variable {α β : Type*} {G H C : Graph α β} {e : β} {u v : α} {P₁ P₂ : WList α β}

namespace PLDrawing

section Plane

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (Module.finrank ℝ V = 2)]

/-- In a polygonal drawing of a finite 3-connected graph, deleting a vertex produces a face whose
frontier is a cycle containing every neighbor of the deleted vertex. -/
theorem exists_facial_cycle_of_delete_vertex [H.Finite] [H.Simple] (hH : H.ConnGE 3)
    (D : PLDrawing H V) (u : V(H)) :
    ∃ (C : Graph α β) (hC : C ≤ H - {u.1}),
      C.IsCycle ∧
      (D.toDrawing.restrict deleteVerts_le).IsFacialSubgraph hC ∧
      N(H, u.1) ⊆ V(C) := by
  /-
  Apply `D.exists_isCycle_frontier_faceSet_eq` to the face exposed by deleting `u`.
  The remaining work is the local incidence statement saying every edge incident with `u`
  approaches that exposed face, hence every neighbor lies on its frontier cycle.

  If that incidence statement can be formulated without 3-connectivity or without a graph, extract
  it before finishing this theorem.
  -/
  sorry

/-- The facial cycle around the contracted vertex, expressed back in the original graph. -/
theorem exists_facial_cycle_of_contract [G.Finite] [G.Simple]
    (he : G.IsLink e u v) (huv : u ≠ v) (hcontract : (G /(e, he)).ConnGE 3)
    (D : PLDrawing (G /(e, he)) V) :
    ∃ (C : Graph α β) (hCG : C ≤ G) (hCcontract : C ≤ (G /(e, he)) - {u}),
      C.IsCycle ∧
      (D.toDrawing.restrict deleteVerts_le).IsFacialSubgraph hCcontract ∧
      u ∉ V(C) ∧ v ∉ V(C) ∧
      N(G, u) \ {v} ⊆ V(C) ∧ N(G, v) \ {u} ⊆ V(C) := by
  /-
  First apply `exists_facial_cycle_of_delete_vertex hcontract D` at the contracted vertex.
  Then isolate the carrier/subgraph bookkeeping translating the deleted contracted graph back to
  the original graph with `u,v` removed.

  Do not mix that bookkeeping into the topological face-cycle proof.
  -/
  sorry

end Plane

/-- The local vertex-splitting step used in the 3-connected case of Kuratowski's theorem.

If the neighbors destined for `u` and `v` occupy the two appropriate arcs of the exposed facial
cycle, split the contracted vertex inside that face and obtain a drawing of `G`.

Unlike the two statements above, this one is pinned to `EuclideanSpace ℝ (Fin 2)`: its conclusion
is `G.Planar`,
which is stated about that model, and reading it off a drawing in some other plane would need a
transport-along-an-isometry lemma that nothing else in the development wants. -/
theorem planar_of_contract_of_facial_cycle_two_paths [G.Finite] [G.Simple]
    (he : G.IsLink e u v) (huv : u ≠ v)
    (D : PLDrawing (G /(e, he)) (EuclideanSpace ℝ (Fin 2)))
    (hCG : C ≤ G) (hCcontract : C ≤ (G /(e, he)) - {u}) (hcycle : C.IsCycle)
    (hfacial : (D.toDrawing.restrict deleteVerts_le).IsFacialSubgraph hCcontract)
    (hu_neighbors : N(G, u) \ {v} ⊆ V(C))
    (hv_neighbors : N(G, v) \ {u} ⊆ V(C))
    (hP₁ : C.IsPath P₁) (hP₂ : C.IsPath P₂)
    (huP₁ : ∀ x ∈ P₁.vertex.tail.dropLast, ¬ G.Adj u x)
    (hvP₂ : ∀ x ∈ P₂.vertex.tail.dropLast, ¬ G.Adj v x)
    (hP₁P₂ : C.IsCyclicWalk (P₁ ++ P₂)) :
    G.Planar := by
  /-
  This is genuine remaining geometric work, not bookkeeping.

  Recommended decomposition:
  1. choose the face witnessing `hfacial`;
  2. build two disjoint small routing trees/arcs inside that open face, one serving the `u`-side
     attachment vertices and one the `v`-side attachment vertices;
  3. place the new vertices `u,v` and the edge `e` inside the face;
  4. splice the old incident edge paths to the two new vertices;
  5. verify the `Drawing.ofVertexAndEdgePaths` obligations;
  6. conclude `G.Planar`.

  Keep all polygonal/metric routing lemmas private unless their statements shed the graph-specific
  data.  Any such shedding is a signal to move them to `ForMathlib`.
  -/
  sorry

end PLDrawing

end

end Graph
