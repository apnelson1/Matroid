module

public import Matroid.GraphTheory.GraphTopology.Polygonal
public import Matroid.MiniTauCeti.JCT.Geometry.SegmentFigure.Basic

/-! # Straight-line graph-like spaces

Straight edges, geometric recognition, and preservation under refinement.
-/

@[expose] public section

open Set Function Set.Notation

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X] {G H : GraphLike X}
  {e f : Set X} {x y : X}

namespace GraphLike

/-- Every edge is the straight segment between its boundary vertices. -/
def IsStraightLine (G : GraphLike X) : Prop :=
  ∀ ⦃e : Set X⦄, e ∈ E(G) → ∀ ⦃x y : X⦄, G.edgeBoundary e = {x, y} → e = segment ℝ x y

namespace IsStraightLine

/-- Straight-line edges have distinct endpoints. -/
theorem endpoints_ne (hG : G.IsStraightLine) (he : e ∈ E(G)) (h : G.edgeBoundary e = {x, y}) :
    x ≠ y := by
  intro hxy
  obtain ⟨z, hz⟩ := G.edgeInterior_nonempty he
  have hzS := G.edgeInterior_subset_edge e hz
  rw [hG he h, hxy, segment_same] at hzS
  have hzB : z ∈ G.edgeBoundary e := by simpa [h, hxy] using hzS
  exact hz.2 hzB.2

/-- The interior of a straight-line edge is the open segment between its endpoints. -/
theorem interior_eq_openSegment (hG : G.IsStraightLine) (he : e ∈ E(G))
    (h : G.edgeBoundary e = {x, y}) : G.edgeInterior e = openSegment ℝ x y := by
  have hd : G.edgeInterior e = e \ G.edgeBoundary e := by
    simp only [edgeInterior, edgeBoundary]; ext z; simp
  rw [hd, h, hG he h, segment_sdiff_pair (hG.endpoints_ne he h)]

/-- A straight-line edge is determined by its endpoint pair. -/
theorem edge_eq_of_boundary_eq (hG : G.IsStraightLine) (he : e ∈ E(G)) (hf : f ∈ E(G))
    (h : G.edgeBoundary e = G.edgeBoundary f) : e = f := by
  obtain ⟨x, _, y, _, hb, _⟩ := G.boundary_isPair he
  exact (hG he hb).trans (hG hf (h.symm.trans hb)).symm

/-- Straight-line edges are convex. -/
theorem convex_range (hG : G.IsStraightLine) (he : e ∈ E(G)) : Convex ℝ e := by
  obtain ⟨x, _, y, _, h, _⟩ := G.boundary_isPair he
  rw [hG he h]
  exact convex_segment x y

/-- A straight edge contains no vertices other than its endpoints. -/
theorem segment_inter_vertexSet (hG : G.IsStraightLine) (he : e ∈ E(G))
    (h : G.edgeBoundary e = {x, y}) : segment ℝ x y ∩ V(G) = {x, y} := by
  rwa [← hG he h]

/-- The open segment of a straight edge avoids all vertices. -/
theorem openSegment_disjoint_vertexSet (hG : G.IsStraightLine) (he : e ∈ E(G))
    (h : G.edgeBoundary e = {x, y}) : Disjoint (openSegment ℝ x y) V(G) := by
  rw [← hG.interior_eq_openSegment he h]
  exact disjoint_sdiff_left

/-- For straight-line spaces, finite vertices imply finite edges. -/
theorem finite_iff (hG : G.IsStraightLine) : G.Finite ↔ V(G).Finite := by
  refine ⟨fun h ↦ h.vertexSet_finite, fun hV ↦ ⟨hV, ?_⟩⟩
  exact hV.finite_subsets.of_injOn (fun e he ↦ G.edgeBoundary_subset_vertexSet e)
    (fun e he f hf h ↦ hG.edge_eq_of_boundary_eq he hf h)

/-- A finite straight-line carrier is a finite union of segments, including isolated vertices. -/
theorem isSegmentFigure_carrier (hG : G.IsStraightLine) [G.Finite] : IsSegmentFigure G.carrier := by
  rw [G.carrier_eq_vertexSet_union_sUnion_edges, sUnion_eq_biUnion]
  refine (IsSegmentFigure.of_finite Finite.vertexSet_finite).union
    (IsSegmentFigure.biUnion Finite.edgeSet_finite fun e he ↦ ?_)
  obtain ⟨x, _, y, _, h, _⟩ := G.boundary_isPair he
  rw [hG he h]
  exact isSegmentFigure_segment x y

/-- Straight edges are segment figures. -/
theorem isPolygonal (hG : G.IsStraightLine) : G.IsPolygonal := by
  intro e he
  obtain ⟨x, _, y, _, hb, _⟩ := G.boundary_isPair he
  rw [hG he hb]
  exact isSegmentFigure_segment x y

section TopologicalVectorSpace

variable [ContinuousAdd X] [ContinuousSMul ℝ X]

/-- A nondegenerate contained segment with only its endpoints as vertices is an edge. -/
theorem exists_edge_iff (hG : G.IsStraightLine) :
    (∃ e ∈ E(G), G.edgeBoundary e = {x, y}) ↔
      x ≠ y ∧ segment ℝ x y ⊆ G.carrier ∧ segment ℝ x y ∩ V(G) = {x, y} := by
  refine ⟨fun ⟨e, he, hb⟩ ↦ ⟨hG.endpoints_ne he hb, hG he hb ▸ G.edge_subset he,
    hG.segment_inter_vertexSet he hb⟩, fun ⟨hxy, hsub, hv⟩ ↦ ?_⟩
  have hopen : openSegment ℝ x y ⊆ G.carrier \ V(G) := by
    refine fun z hz ↦ ⟨hsub <| openSegment_subset_segment ℝ x y hz, fun hzV ↦ ?_⟩
    obtain rfl | rfl := hv.subset ⟨openSegment_subset_segment ℝ x y hz, hzV⟩
    · exact ne_of_mem_openSegment_left hxy hz rfl
    exact ne_of_mem_openSegment_right hxy hz rfl
  obtain ⟨e, he, _, hb⟩ :=
    G.exists_edge_of_isConnected_of_mem_closure ⟨⟨midpoint ℝ x y, midpoint_mem_openSegment x y⟩,
      (convex_openSegment x y).isPreconnected⟩ hopen hxy
      (hv.symm.subset (by simp)).right (hv.symm.subset (by simp)).right
      (segment_subset_closure_openSegment <| left_mem_segment ..) <|
      segment_subset_closure_openSegment <| right_mem_segment ..
  exact ⟨e, he, hb⟩

/-- Adding vertices without changing the carrier preserves straightness. -/
theorem of_finer (hG : G.IsStraightLine) (hGH : G.finer H) : H.IsStraightLine := by
  intro e he x y h
  obtain ⟨f, ⟨hf, -, hef⟩, -⟩ := finer.existsUnique_edge G hGH he
  obtain ⟨a, -, b, -, hab, -⟩ := G.boundary_isPair hf
  have hseg : segment ℝ a b ⊆ G.carrier := hG hf hab ▸ G.edge_subset hf
  let : T2Space ↥(segment ℝ a b) := (Topology.IsEmbedding.inclusion hseg).t2Space
  refine (H.edge_isPrimitiveLink he h).eq_segment_of_subset (a := a) (b := b) ?_
  rw [← hG hf hab]
  exact hef

end TopologicalVectorSpace

end GraphLike.IsStraightLine
