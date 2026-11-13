module

public import Matroid.GraphTheory.GraphTopology.PolygonalStar
public import Matroid.GraphTheory.GraphTopology.Polygonal
public import Matroid.GraphTheory.GraphTopology.Restriction
public import Matroid.MiniTauCeti.JCT.Geometry.StarComponents
public import Matroid.MiniTauCeti.JCT.Geometry.SegmentFigure.Accessibility

/-! # Faces along polygonal edges

A face `F ∈ F(G)` whose frontier contains one interior point of a polygonal edge contains the
whole edge in its frontier. Consequently the frontier of a face of a polygonal graphlike is the
carrier of a whole-edge restriction, and each polygonal edge has one or two bounding faces.

## Main statements

* `edge_subset_frontier_of_mem` : whole-edge containment for a supplied face. Only the given edge
  needs to be polygonal.
* `coe_restrict_frontier`, `coe_restrict_frontier_of_isClosed` : the frontier of a face is made
  of whole edges and vertices.
* `isBoundaryEdge_iff`, `boundingFaces_eq`, `boundingFaces_nonempty`,
  `encard_boundingFaces_le_two` : incidence between polygonal edges and faces.
* `exists_segment_sdiff_subset_of_mem_frontier` : straight access from the frontier into a face.

The face results are stated in a real inner-product plane, where the sector calculations of
`StarComponents` are available. Straight access holds in any real normed space.
-/

@[expose] public section

open Function Set Topology Metric

namespace GraphLike

section Normed

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {G : GraphLike X} {F : Set X}

/-- A point of a segment-figure carrier on the frontier of a face enters that face along a
straight segment. -/
theorem exists_segment_sdiff_subset_of_mem_frontier (hpoly : IsSegmentFigure G.carrier)
    {p : X} (hp : p ∈ G.carrier) (hF : F ∈ F(G)) (hpF : p ∈ frontier F) :
    ∃ y : X, y ≠ p ∧ segment ℝ p y \ {p} ⊆ F := by
  obtain ⟨w, hw⟩ := nonempty_of_mem_faceSet hF
  rw [eq_connectedComponentIn_of_mem_faceSet hF hw] at hpF ⊢
  exact hpoly.exists_segment_sdiff_subset_connectedComponentIn_compl hp hpF

end Normed

section Plane

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [Fact (Module.finrank ℝ X = 2)] {G : GraphLike X} {e F : Set X} {p q : X}

/-- A face whose frontier contains an interior point of a polygonal edge contains the whole
edge, including its endpoints, in its frontier. Only this edge needs to be polygonal; the
graphlike may be infinite. -/
theorem edge_subset_frontier_of_mem (he : e ∈ E(G)) (hpoly : IsSegmentFigure e)
    (hF : F ∈ F(G)) (hp : p ∈ G.edgeInterior e) (hpF : p ∈ frontier F) :
    e ⊆ frontier F := by
  obtain ⟨w, hw⟩ := nonempty_of_mem_faceSet hF
  have hFeq := eq_connectedComponentIn_of_mem_faceSet hF hw
  let U : Set (G.edgeInterior e) := Subtype.val ⁻¹' frontier F
  have hUclosed : IsClosed U := isClosed_frontier.preimage continuous_subtype_val
  have hUopen : IsOpen U := by
    rw [isOpen_iff_forall_mem_open]
    intro z hz
    change z.1 ∈ frontier F at hz
    obtain ⟨r, hr, Y, hY, hcard, _, hstar⟩ := G.exists_radius_edgeInterior he hpoly z.2
    have hYne : Y.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨C, hC, hCF⟩ := exists_sector_subset_connectedComponentIn_compl
      hYne hstar (mem_ball_self hr) (hFeq ▸ hz)
    have hCF' : C ⊆ F := hFeq ▸ hCF
    refine ⟨Subtype.val ⁻¹' ball z.1 r, ?_,
      isOpen_ball.preimage continuous_subtype_val, mem_ball_self hr⟩
    intro q hq
    have hqG : q.1 ∈ G.carrier := G.edge_subset he q.2.1
    refine ⟨closure_mono hCF'
      (ball_inter_subset_closure_sector_of_card_eq_two hr hY hcard hstar hC ⟨hq, hqG⟩), ?_⟩
    exact fun h ↦ subset_compl_of_mem_faceSet hF (interior_subset h) hqG
  let : ConnectedSpace (G.edgeInterior e) :=
    isConnected_iff_connectedSpace.mp (G.edgeInterior_isConnected he)
  have hU : U = univ := IsClopen.eq_univ ⟨hUclosed, hUopen⟩ ⟨⟨p, hp⟩, hpF⟩
  have hsub : G.edgeInterior e ⊆ frontier F := by
    intro q hq
    exact (show (⟨q, hq⟩ : G.edgeInterior e) ∈ U from hU ▸ mem_univ _)
  exact (G.edge_subset_closure_edgeInterior he).trans (closure_minimal hsub isClosed_frontier)

/-- The frontier of a face of a polygonal graphlike meets the carrier in the carrier of a
whole-edge restriction: every edge meeting the frontier in an interior point lies in it. -/
theorem coe_restrict_frontier (hG : G.IsPolygonal) (hF : F ∈ F(G)) :
    (G.restrict (frontier F) : Set X) = frontier F ∩ G.carrier := by
  refine subset_antisymm (subset_inter (G.restrict_subset _) (G.restrict_subset_self _)) ?_
  rintro x ⟨hxF, hxG⟩
  by_cases hxV : x ∈ V(G)
  · rw [coe_restrict]
    exact Or.inl ⟨hxF, hxV⟩
  · obtain ⟨e, he, hxe⟩ := G.exists_edge_of_mem ⟨hxG, hxV⟩
    exact edge_subset_restrict he (edge_subset_frontier_of_mem he (hG he) hF hxe hxF) hxe.1

/-- For a closed carrier, the frontier of a face of a polygonal graphlike is exactly the carrier
of its whole-edge restriction. -/
theorem coe_restrict_frontier_of_isClosed (hG : G.IsPolygonal) (hF : F ∈ F(G))
    (hc : IsClosed G.carrier) :
    (G.restrict (frontier F) : Set X) = frontier F := by
  rw [coe_restrict_frontier hG hF, inter_eq_left.mpr (frontier_subset_carrier_of_mem_faceSet hF hc)]

/-- For a polygonal edge, a face is incident exactly when it contains the whole edge in its
frontier. -/
theorem isBoundaryEdge_iff (he : e ∈ E(G)) (hpoly : IsSegmentFigure e) :
    G.IsBoundaryEdge e F ↔ F ∈ F(G) ∧ e ⊆ frontier F := by
  constructor
  · rintro ⟨hF, _, p, hp, hpF⟩
    exact ⟨hF, edge_subset_frontier_of_mem he hpoly hF hp hpF⟩
  · rintro ⟨hF, hsub⟩
    obtain ⟨p, hp⟩ := G.edgeInterior_nonempty he
    exact ⟨hF, he, p, hp, hsub hp.1⟩

/-- The bounding faces are the same at all interior points of a polygonal edge. -/
theorem boundingFaces_eq (he : e ∈ E(G)) (hpoly : IsSegmentFigure e)
    (hp : p ∈ G.edgeInterior e) (hq : q ∈ G.edgeInterior e) :
    G.boundingFaces p = G.boundingFaces q := by
  ext F
  exact ⟨fun ⟨hF, hpF⟩ ↦ ⟨hF, edge_subset_frontier_of_mem he hpoly hF hp hpF hq.1⟩,
    fun ⟨hF, hqF⟩ ↦ ⟨hF, edge_subset_frontier_of_mem he hpoly hF hq hqF hp.1⟩⟩

omit [Fact (Module.finrank ℝ X = 2)] in
/-- A sector of a star of the carrier avoids the carrier. -/
private lemma sector_subset_compl_carrier {r : ℝ} {Y : Finset X} {C : Set X} (hYne : Y.Nonempty)
    (hstar : closedBall p r ∩ G.carrier = {p} ∪ ⋃ y ∈ Y, segment ℝ p y)
    (hC : C ∈ sectors p r Y) : C ⊆ G.carrierᶜ := by
  intro z hz hzG
  have hzD := subset_diskMinusRadii_of_mem_sectors hC hz
  have hzstar := hstar ▸ (show z ∈ closedBall p r ∩ G.carrier from
    ⟨ball_subset_closedBall hzD.1, hzG⟩)
  apply hzD.2
  rcases hzstar with rfl | hrad
  · obtain ⟨y, hy⟩ := hYne
    exact mem_iUnion₂.mpr ⟨y, hy, left_mem_segment ℝ _ y⟩
  · exact hrad

/-- An interior point of a polygonal edge has a bounding face. -/
theorem boundingFaces_nonempty (he : e ∈ E(G)) (hpoly : IsSegmentFigure e)
    (hp : p ∈ G.edgeInterior e) : (G.boundingFaces p).Nonempty := by
  obtain ⟨r, hr, Y, hY, hcard, _, hstar⟩ := G.exists_radius_edgeInterior he hpoly hp
  have hYne : Y.Nonempty := Finset.card_pos.mp (by omega)
  have hn : (sectors p r Y).ncard = 2 := by rw [ncard_sectors hr hYne hY, hcard]
  obtain ⟨C, hC⟩ := Set.nonempty_of_ncard_ne_zero (by omega : (sectors p r Y).ncard ≠ 0)
  have hconn := isConnected_of_mem_sectors hC
  have hCS := sector_subset_compl_carrier hYne hstar hC
  obtain ⟨x, hx⟩ := hconn.nonempty
  have hCF : C ⊆ G.faceAt x := hconn.isPreconnected.subset_connectedComponentIn hx hCS
  have hF : G.faceAt x ∈ F(G) := mem_faceSet_of_mem_faceAt (hCS hx)
  refine ⟨G.faceAt x, hF, closure_mono hCF (mem_closure_of_mem_sectors hr hYne hY hC), ?_⟩
  exact fun h ↦ subset_compl_of_mem_faceSet hF (interior_subset h) (G.edge_subset he hp.1)

/-- An interior point of a polygonal edge has at most two bounding faces: each bounding face
contains one of the two sectors of a local star. Both sectors may lie in the same face. -/
theorem encard_boundingFaces_le_two (he : e ∈ E(G)) (hpoly : IsSegmentFigure e)
    (hp : p ∈ G.edgeInterior e) : (G.boundingFaces p).encard ≤ 2 := by
  classical
  obtain ⟨r, hr, Y, hY, hcard, _, hstar⟩ := G.exists_radius_edgeInterior he hpoly hp
  have hYne : Y.Nonempty := Finset.card_pos.mp (by omega)
  have hn : (sectors p r Y).ncard = 2 := by rw [ncard_sectors hr hYne hY, hcard]
  have hfin : (sectors p r Y).Finite := finite_of_ncard_ne_zero (by omega)
  let g : Set X → Set X := fun C ↦ G.faceAt (if h : C.Nonempty then h.some else p)
  have hsub : G.boundingFaces p ⊆ g '' sectors p r Y := by
    rintro F ⟨hF, hpF⟩
    obtain ⟨w, hw⟩ := nonempty_of_mem_faceSet hF
    have hFeq := eq_connectedComponentIn_of_mem_faceSet hF hw
    obtain ⟨C, hC, hCF⟩ := exists_sector_subset_connectedComponentIn_compl
      hYne hstar (mem_ball_self hr) (hFeq ▸ hpF)
    have hCne := (isConnected_of_mem_sectors hC).nonempty
    refine ⟨C, hC, ?_⟩
    simp only [g, dite_eq_left hCne]
    exact (eq_connectedComponentIn_of_mem_faceSet hF (hFeq ▸ hCF hCne.some_mem)).symm
  calc (G.boundingFaces p).encard ≤ (g '' sectors p r Y).encard := encard_le_encard hsub
    _ ≤ (sectors p r Y).encard := encard_image_le _ _
    _ = 2 := by rw [← hfin.cast_ncard_eq, hn]; rfl

/-- The finite cardinal form of `encard_boundingFaces_le_two`. -/
theorem ncard_boundingFaces_le_two (he : e ∈ E(G)) (hpoly : IsSegmentFigure e)
    (hp : p ∈ G.edgeInterior e) : (G.boundingFaces p).ncard ≤ 2 :=
  (encard_le_coe_iff_finite_ncard_le.mp (encard_boundingFaces_le_two he hpoly hp)).2

/-- Some face contains a whole polygonal edge, including its endpoints, in its frontier. -/
theorem exists_mem_faceSet_edge_subset_frontier (he : e ∈ E(G)) (hpoly : IsSegmentFigure e) :
    ∃ F ∈ F(G), e ⊆ frontier F := by
  obtain ⟨p, hp⟩ := G.edgeInterior_nonempty he
  obtain ⟨F, hF, hpF⟩ := boundingFaces_nonempty he hpoly hp
  exact ⟨F, hF, edge_subset_frontier_of_mem he hpoly hF hp hpF⟩

end Plane

end GraphLike
