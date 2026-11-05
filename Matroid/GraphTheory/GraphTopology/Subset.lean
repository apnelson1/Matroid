module

public import Matroid.GraphLike.RestrictionGeometry
public import Matroid.ForMathlib.Analysis.Convex.Segment
public import Matroid.ForMathlib.Geometry.SegmentFigure.Topology

/-! # Subsets and differences of straight-line graph-like spaces

Connected-subset inheritance uses edge remainders and interval topology. Finite-support
differences use the general support law; the right selection need not be finite.
-/

@[expose] public section

open Set Topology unitInterval Topology.IsInducing

namespace GraphLike

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X] {G : GraphLike X}

/-- Relative closure of a difference of supports of a straight-line space is a figure.
Only the selections on the left must be finite. -/
theorem isSegmentFigure_relativeClosure_sdiff (hG : G.IsStraightLine)
    (A C : Set X) (B D : Set (Set X)) (hA : A.Finite) (hB : B.Finite) :
    IsSegmentFigure (G.carrier ∩ closure (G.support A B \ G.support C D)) := by
  rw [G.closure_support_sdiff A C B D hA hB]
  exact hG.isSegmentFigure_support _ _ hA.sdiff hB.sdiff

/-- In a Hausdorff ambient space the finite left support is closed, so the ambient
closure is the same as the relative closure. -/
theorem isSegmentFigure_closure_sdiff [T2Space X] (hG : G.IsStraightLine)
    (A C : Set X) (B D : Set (Set X)) (hA : A.Finite) (hB : B.Finite) :
    IsSegmentFigure (closure (G.support A B \ G.support C D)) := by
  have hc : IsCompact (G.support A B) :=
    (hA.inter_of_left _).isCompact.union
      ((hB.inter_of_left _).isCompact_sUnion fun e he ↦ G.edge_isCompact he.2)
  have hsub : closure (G.support A B \ G.support C D) ⊆ G.carrier :=
    (closure_minimal sdiff_subset hc.isClosed).trans (G.support_subset A B)
  simpa only [inter_eq_right.mpr hsub] using
    isSegmentFigure_relativeClosure_sdiff hG A C B D hA hB

variable [ContinuousAdd X] [ContinuousSMul ℝ X]

private theorem isSegmentFigure_image_segment_of_isCompact_ordConnected {T : Set I}
    (hc : IsCompact T) (ho : OrdConnected T) (a b : X) :
    IsSegmentFigure <| Path.segment a b '' T := by
  obtain rfl | hne := T.eq_empty_or_nonempty
  · simp
  obtain ⟨s, t, hst, rfl⟩ := IsEmbedding.id.exists_eq_image_Icc_of_isConnected_isCompact
    (by simp : T ⊆ range id) ⟨hne, ho.isPreconnected⟩ hc
  simp only [image_id, Path.segment_apply]
  rw [← image_image, image_subtype_val_Icc,
    ← segment_eq_Icc (show (s : ℝ) ≤ t from hst), image_segment]
  exact isSegmentFigure_segment ..

/-- A relatively closed preconnected subset of a finite straight-line carrier is a figure.
The subset may cut edges partway; it need not be a whole-edge restriction. -/
theorem isSegmentFigure_of_isClosed_isPreconnected [G.Finite] (hG : G.IsStraightLine)
    {C : Set X} (hCS : C ⊆ G.carrier)
    (hc : IsClosed (Subtype.val ⁻¹' C : Set G.carrier)) (hconn : IsPreconnected C) :
    IsSegmentFigure C := by
  obtain rfl | hne := C.eq_empty_or_nonempty
  · exact isSegmentFigure_empty
  let : CompactSpace G.carrier := isCompact_iff_compactSpace.mp G.isCompact
  have hCc : IsCompact C := by
    simpa only [Subtype.image_preimage_coe, inter_eq_right.mpr hCS] using
      hc.isCompact.image continuous_subtype_val
  have hCeq : C = (C ∩ V(G)) ∪ ⋃ e ∈ E(G), C ∩ e := by
    rw [← inter_iUnion₂, ← sUnion_eq_biUnion, ← inter_union_distrib_left,
      ← G.carrier_eq_vertexSet_union_sUnion_edges, inter_eq_left.mpr hCS]
  rw [hCeq]
  refine IsSegmentFigure.union
    (IsSegmentFigure.of_finite <| GraphLike.Finite.vertexSet_finite.subset inter_subset_right)
    (IsSegmentFigure.biUnion Finite.edgeSet_finite fun e he ↦ ?_)
  obtain ⟨a, _, b, _, hb, _⟩ := G.boundary_isPair he
  have heq := hG he hb
  have hsegS : segment ℝ a b ⊆ G.carrier := heq ▸ G.edge_subset he
  let : T2Space ↥(segment ℝ a b) := (IsEmbedding.inclusion hsegS).t2Space
  rw [heq]
  by_cases hCe : C ⊆ segment ℝ a b
  · rw [inter_eq_left.mpr hCe]
    obtain ⟨x, y, he⟩ := hCc.exists_eq_segment_of_isConnected_of_subset_segment ⟨hne, hconn⟩ hCe
    rw [he]
    exact isSegmentFigure_segment x y
  have hab := hG.endpoints_ne he hb
  let f : I → G.carrier := fun t ↦
    ⟨Path.segment a b t, hsegS <| Path.range_segment a b ▸ mem_range_self t⟩
  have hf : Continuous f := (Path.segment a b).continuous.subtype_mk _
  have hrange : range f = Subtype.val ⁻¹' segment ℝ a b := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact Path.range_segment a b ▸ mem_range_self t
    intro hx
    obtain ⟨t, ht⟩ := (Path.range_segment a b).symm ▸ hx
    exact ⟨t, Subtype.ext ht⟩
  let K := G.carrier \ G.edgeInterior e
  have hattach : range f ∩ Subtype.val ⁻¹' K ⊆ {f ⊥, f ⊤} := by
    intro x hx
    have hxseg : x.val ∈ segment ℝ a b := by
      have hxrange := hx.left
      rwa [hrange] at hxrange
    have hxends : x.val ∈ G.edgeBoundary e :=
      G.edge_inter_remainder he ▸ ⟨heq.symm ▸ hxseg, hx.right⟩
    rw [hb] at hxends
    change x = f (0 : I) ∨ x = f (1 : I)
    simpa only [mem_insert_iff, mem_singleton_iff, Subtype.ext_iff,
      f, Path.source, Path.target] using hxends
  have hcover : C ⊆ segment ℝ a b ∪ K := by
    rw [← heq, G.edge_union_remainder he]
    exact hCS
  have hgap : (f ⁻¹' Subtype.val ⁻¹' C)ᶜ.OrdConnected := by
    refine hf.ordConnected_compl_preimage_of_isPreconnected
      (fun s t h ↦ Path.segment_injective_of_ne hab <| congrArg Subtype.val h)
      (G.edge_isClosed_remainder he) hattach ?_ (fun _ hx ↦ hrange ▸ hcover hx) ?_
    · rw [← subtypeVal.isPreconnected_image]
      simpa only [Subtype.image_preimage_coe, inter_eq_right.mpr hCS] using hconn
    rw [hrange]
    exact fun h ↦ hCe (fun x hx ↦ h (show (⟨x, hCS hx⟩ : G.carrier) ∈
      Subtype.val ⁻¹' C from hx))
  let L : LowerSet I := (upperClosure (f ⁻¹' Subtype.val ⁻¹' C)ᶜ).compl
  let R : UpperSet I := (lowerClosure (f ⁻¹' Subtype.val ⁻¹' C)ᶜ).compl
  have hLR : (L : Set I) ∪ R = f ⁻¹' Subtype.val ⁻¹' C := by
    simpa only [compl_compl] using hgap.compl_upperClosure_union_compl_lowerClosure
  have hcompact := (hc.preimage hf).isCompact
  have him : Path.segment a b '' (f ⁻¹' Subtype.val ⁻¹' C) = C ∩ segment ℝ a b := by
    change Path.segment a b '' Path.segment a b ⁻¹' C = _
    rw [image_preimage_eq_inter_range, Path.range_segment]
  simpa only [← image_union, hLR, him] using
    (isSegmentFigure_image_segment_of_isCompact_ordConnected (T := (L : Set I))
      hcompact.compl_upperClosure_compl L.lower.ordConnected a b).union <|
    isSegmentFigure_image_segment_of_isCompact_ordConnected (T := (R : Set I))
      hcompact.compl_lowerClosure_compl R.upper.ordConnected a b

end GraphLike
