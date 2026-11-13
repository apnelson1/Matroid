module

public import Matroid.GraphTheory.GraphTopology.StraightLine
public import Matroid.GraphTheory.GraphTopology.Assembly
public import Matroid.MiniTauCeti.JCT.Analysis.Convex.SegmentCutting

/-! # Segment figures as finite straight-line graph-like spaces

Cut a finite segment family at its intersection endpoints and prescribed points, then assemble
its nondegenerate pieces into geometric edges. Marked points supply the vertices directly.
-/

@[expose] public section

open Set Function Set.Notation
open scoped GraphLike

section SegmentFigure

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [ContinuousAdd X] [ContinuousSMul ℝ X]

namespace GraphLike

variable (S : Set X) (E : Set (X × X)) (F : Set X) [T2Space S]
  (hE : E.Finite) (hF : F.Finite)
  (hS : S = ⋃ e ∈ E, segment ℝ e.1 e.2) (hFS : F ⊆ S)

include hE hF hS hFS in
private theorem segment_decomposition :
    IsLinkDecomposition S (segmentPartitionVertices E F) (segmentPartitionPieces E F) := by
  refine IsLinkDecomposition.ofFinite (finite_segmentPartitionVertices hE hF)
    (finite_segmentPartitionPieces hE (hF.subset inter_subset_left)) ?_ ?_ ?_
  · rw [segmentPartition_union hE hF, ← hS, union_eq_right.mpr hFS]
  · intro d hd
    obtain ⟨a, -, b, -, hab, rfl, hv⟩ := segmentPartitionPieces_eq_segment hd
    exact ⟨a, b, isPrimitiveLink_segment hab, hv⟩
  · intro d hd f hf hdf
    exact disjoint_left.mpr fun x hx hy ↦
      hx.2 (segmentPartitionPieces_pairwise E F hd hf hdf ⟨hx.1, hy.1⟩)

/-- Cut a supplied finite segment cover at intersections and prescribed vertices.
The carrier is the supplied set, and the geometric edges are the partition pieces. -/
noncomputable def ofSegments : GraphLike X :=
  (by exact segment_decomposition S E F hE hF hS hFS :
    IsLinkDecomposition S (segmentPartitionVertices E F) (segmentPartitionPieces E F)).toGraphLike

@[simp] theorem ofSegments_carrier : (ofSegments S E F hE hF hS hFS).carrier = S := rfl

@[simp] theorem ofSegments_vertexSet :
    V(ofSegments S E F hE hF hS hFS) = segmentPartitionVertices E F := rfl

@[simp] theorem ofSegments_edgeSet :
    E(ofSegments S E F hE hF hS hFS) = segmentPartitionPieces E F :=
  by exact (segment_decomposition S E F hE hF hS hFS).toGraphLike_edgeSet

instance ofSegments_finite : (ofSegments S E F hE hF hS hFS).Finite :=
  by
    exact (segment_decomposition S E F hE hF hS hFS).toGraphLike_finite
      (finite_segmentPartitionVertices hE hF)
      (finite_segmentPartitionPieces hE (hF.subset inter_subset_left))

theorem ofSegments_isStraightLine : (ofSegments S E F hE hF hS hFS).IsStraightLine := by
  intro d hd x y hb
  rw [ofSegments_edgeSet] at hd
  obtain ⟨a, -, b, -, -, hd, hv⟩ := segmentPartitionPieces_eq_segment hd
  change d ∩ segmentPartitionVertices E F = {x, y} at hb
  rw [hd]
  rcases pair_eq_pair_iff.mp (hv.symm.trans hb) with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · rw [hx, hy]
  · rw [hx, hy, segment_symm]

/-- Every subfamily of the supplied segments is preserved as vertices and whole edges. -/
theorem ofSegments_cover {E' : Set (X × X)} (hE' : E' ⊆ E) :
    (⋃ e ∈ E', segment ℝ e.1 e.2) =
      ((⋃ e ∈ E', segment ℝ e.1 e.2) ∩ V(ofSegments S E F hE hF hS hFS)) ∪
        ⋃ d ∈ {d ∈ E(ofSegments S E F hE hF hS hFS) |
          d ⊆ ⋃ e ∈ E', segment ℝ e.1 e.2}, d := by
  simpa only [ofSegments_vertexSet, ofSegments_edgeSet] using
    segmentPartition_cover_biUnion hE hF hE'

end GraphLike

variable {S F : Set X}

/-- A finite family of figures has a common straight-line presentation preserving each figure
as vertices and whole edges, including any prescribed finite set of vertices. -/
theorem IsSegmentFigure.exists_common_straightLineGraphLike
    {ι : Type*} [Finite ι] {S : ι → Set X} [T2Space ↥(⋃ i, S i)]
    (hS : ∀ i, IsSegmentFigure (S i))
    (hF : F.Finite) (hFS : F ⊆ ⋃ i, S i) :
    ∃ G : GraphLike X, G.Finite ∧ G.IsStraightLine ∧ G.carrier = ⋃ i, S i ∧
      F ⊆ G.vertexSet ∧
      ∀ i, S i = (S i ∩ G.vertexSet) ∪ ⋃ e ∈ {e ∈ E(G) | e ⊆ S i}, e := by
  classical
  choose E hE heq using hS
  have hUnion : (⋃ i, S i) = ⋃ e ∈ ⋃ i, E i, segment ℝ e.1 e.2 := by
    simp_rw [heq, biUnion_iUnion]
  let G := GraphLike.ofSegments (⋃ i, S i) (⋃ i, E i) F
    (finite_iUnion hE) hF hUnion hFS
  refine ⟨G, inferInstance, GraphLike.ofSegments_isStraightLine .., rfl,
    subset_segmentPartitionVertices _ _, fun i ↦ ?_⟩
  simpa only [← heq i] using
    GraphLike.ofSegments_cover (⋃ i, S i) (⋃ i, E i) F
      (finite_iUnion hE) hF hUnion hFS (subset_iUnion E i)

/-- A segment figure has a finite straight-line presentation containing prescribed vertices. -/
theorem IsSegmentFigure.exists_straightLineGraphLike [T2Space S] (hS : IsSegmentFigure S)
    (hF : F.Finite) (hFS : F ⊆ S) :
    ∃ G : GraphLike X, G.Finite ∧ G.IsStraightLine ∧ G.carrier = S ∧
      F ⊆ G.vertexSet := by
  obtain ⟨E, hE, hcover⟩ := hS
  exact ⟨GraphLike.ofSegments S E F hE hF hcover hFS, inferInstance,
    GraphLike.ofSegments_isStraightLine .., rfl, subset_segmentPartitionVertices _ _⟩

/-- Segment figures are precisely the carriers of finite straight-line graph-like spaces. -/
theorem isSegmentFigure_iff_exists_straightLineGraphLike [T2Space S] :
    IsSegmentFigure S ↔
      ∃ G : GraphLike X, G.Finite ∧ G.IsStraightLine ∧ G.carrier = S := by
  constructor
  · intro hS
    obtain ⟨G, hfin, hstraight, hcarrier, _⟩ :=
      hS.exists_straightLineGraphLike finite_empty (empty_subset S)
    exact ⟨G, hfin, hstraight, hcarrier⟩
  rintro ⟨G, hfin, hstraight, rfl⟩
  let := hfin
  exact hstraight.isSegmentFigure_carrier

end SegmentFigure

