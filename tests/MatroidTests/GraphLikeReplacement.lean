import Matroid.Graph.Topology.Draft

open Set Metric symmDiff
open scoped GraphLike

-- Draft uses Lean's legacy module format, so this check is built separately from the test root.
-- Run `lake build MatroidTests.GraphLikeReplacement`.
example {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (G : GraphLike V) [G.Finite] (ε : Set V → ℝ) (hε : ∀ e ∈ E(G), 0 < ε e) :
    ∃ (H : GraphLike V) (q : ↥E(G) ≃ ↥E(H)), H.vertexSet = G.vertexSet ∧
      (∀ e ∈ E(H), IsSegmentFigure e) ∧
      ∀ e, H.edgeBoundary (q e).1 = G.edgeBoundary e.1 ∧
        (q e).1 ⊆ thickening (ε e.1) e.1 := by
  obtain ⟨H, q, hV, hP, hq⟩ := G.exists_polygonalization
    (fun e ↦ thickening (ε e) e) (fun _ _ ↦ isOpen_thickening)
    (fun e he ↦ self_subset_thickening (hε e he) _)
  exact ⟨H, q, hV, H.isPolygonal_iff_isSegmentFigure.mp hP, hq⟩

-- Coincident endpoints remain coincident; loops are not silently excluded.
example {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (G : GraphLike V) [G.Finite] {e : Set V} (he : e ∈ E(G)) {x : V}
    (hb : G.edgeBoundary e = {x, x}) (ε : ℝ) :
    (G.polygonalize ε).edgeBoundary (G.polygonalizeEdgeEquiv ε ⟨e, he⟩).1 = {x, x} := by
  rw [G.polygonalizeEdgeEquiv_boundary]
  exact hb

-- A raw edge and its membership proof suffice for geometry.
example {X : Type*} [TopologicalSpace X] (G : GraphLike X)
    {e : Set X} (he : e ∈ E(G)) : (G.edgeInterior e).Infinite :=
  G.edgeInterior_infinite he

-- Subdivision requires finitely many edges, not finitely many vertices or ambient Hausdorffness.
example {X : Type*} [TopologicalSpace X] (G : GraphLike X) (hE : E(G).Finite) :
    ∃ H : GraphLike X, G.finer H ∧ (H.vertexSet ∆ G.vertexSet).Finite ∧ E(H).Finite ∧
      ∀ e ∈ E(H), ∃ (x y : H.vertexSet) (P : Path x.1 y.1),
        Function.Injective P ∧ range P = e ∧ H.edgeBoundary e = {x.1, y.1} :=
  G.exists_finer_with_injective_edges hE

-- Carrier transfer remains valid without any finiteness hypothesis on either edge set.
example {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [ContinuousSMul ℝ X] [ContinuousAdd X] {G H : GraphLike X}
    (hG : G.IsPolygonal) (hH : H.carrier ⊆ G.carrier)
    (hfinite : ∀ e ∈ E(H), (e ∩ G.vertexSet).Finite) : H.IsPolygonal :=
  hG.of_carrier_subset hH hfinite

-- Isolated vertices are retained by the finite-refinement operation.
example {X : Type*} [TopologicalSpace X] (G : GraphLike X) [G.Finite]
    (Z : Set X) (hZ : Z.Finite) (hGZ : G.vertexSet ⊆ Z) (hZG : Z ⊆ G.carrier)
    {x : X} (hx : x ∈ G.vertexSet) :
    x ∈ (G.refineVertices Z hZ hGZ hZG).vertexSet := by
  rw [G.refineVertices_vertexSet]
  exact hGZ hx

example {X : Type*} [TopologicalSpace X] :
    (⊥ : GraphLike X).carrier = ∅ ∧ (⊥ : GraphLike X).vertexSet = ∅ := ⟨rfl, rfl⟩

example {X : Type*} [TopologicalSpace X] (G : GraphLike X) [G.Finite]
    (hE : E(G).Nonempty) (H : G.FiniteRefinement) : ∃ K : G.FiniteRefinement, H < K := by
  let : Fact E(G).Nonempty := ⟨hE⟩
  exact exists_gt H

/-- info: 'GraphLike.exists_polygonalization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GraphLike.exists_polygonalization

/-- info: 'GraphLike.exists_finer_with_injective_edges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GraphLike.exists_finer_with_injective_edges

/-- info: 'GraphLike.IsPolygonal.of_carrier_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GraphLike.IsPolygonal.of_carrier_subset

/-- info: 'GraphLike.refineVertices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GraphLike.refineVertices
