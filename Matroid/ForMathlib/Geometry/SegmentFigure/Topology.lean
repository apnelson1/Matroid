module

public import Matroid.ForMathlib.Geometry.SegmentFigure.Basic
public import Matroid.ForMathlib.Geometry.SegmentFigure.Cardinality
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Topology of segment figures

Segment figures are compact. Their connected components are unions of generating segments,
so are themselves segment figures. In a Hausdorff ambient space a finite disjoint union of
closed intervals maps onto the figure by a quotient map, giving local connectedness and
finitely many connected components.
-/

@[expose] public section

open Set Topology

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul ℝ V] {S : Set V}

namespace IsSegmentFigure

theorem isCompact (hS : IsSegmentFigure S) : IsCompact S :=
  hS.induction_on isCompact_empty fun a b _ _ ih ↦ (isCompact_segment a b).union ih

theorem isClosed [T2Space V] (hS : IsSegmentFigure S) : IsClosed S :=
  hS.isCompact.isClosed

/-- A component consists of all generating segments that meet it. -/
theorem connectedComponentIn (hS : IsSegmentFigure S) (x : V) :
    IsSegmentFigure (connectedComponentIn S x) := by
  obtain ⟨E, hE, hS⟩ := hS
  have hsub (e) (he : e ∈ E) : segment ℝ e.fst e.snd ⊆ S := hS ▸ fun y hy ↦ mem_biUnion he hy
  let F := {e ∈ E | (segment ℝ e.fst e.snd ∩ _root_.connectedComponentIn S x).Nonempty}
  refine ⟨F, hE.subset (sep_subset _ _), subset_antisymm (fun y hy ↦ ?_) (fun y hy ↦ ?_)⟩
  · have hyS := connectedComponentIn_subset S x hy
    rw [hS, mem_iUnion₂] at hyS
    obtain ⟨e, he, hye⟩ := hyS
    exact mem_biUnion ⟨he, y, hye, hy⟩ hye
  obtain ⟨e, ⟨he, z, hze, hzx⟩, hye⟩ := mem_iUnion₂.mp hy
  rw [connectedComponentIn_eq hzx]
  exact (convex_segment e.fst e.snd).isPreconnected.subset_connectedComponentIn hze (hsub e he) hye

/-- There are finitely many distinct components, including the empty value outside the figure. -/
theorem finite_range_connectedComponentIn (hS : IsSegmentFigure S) :
    (range (_root_.connectedComponentIn S)).Finite := by
  obtain ⟨E, hE, heq⟩ := hS
  refine ((hE.image (fun e ↦ _root_.connectedComponentIn S e.fst)).insert ∅).subset ?_
  rintro C ⟨x, rfl⟩
  by_cases hx : x ∈ S
  · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp <| heq ▸ hx
    refine Or.inr ⟨e, he, (connectedComponentIn_eq ?_).symm⟩
    exact (convex_segment e.fst e.snd).isPreconnected.subset_connectedComponentIn hxe
      (fun y hy ↦ heq ▸ mem_biUnion he hy) (left_mem_segment ℝ e.fst e.snd)
  exact Or.inl (connectedComponentIn_eq_empty hx)

/-- Local path connectedness follows from a finite interval presentation. No local convexity
of the ambient space is needed. -/
theorem locallyPathConnectedSpace [T2Space V] (hS : IsSegmentFigure S) :
    LocallyPathConnectedSpace S := by
  obtain ⟨E, hE, hS⟩ := hS
  let := hE.to_subtype
  let : LocallyPathConnectedSpace (Icc (0 : ℝ) 1) := (convex_Icc 0 1).locallyPathConnectedSpace
  let f : (Σ _ : E, Icc (0 : ℝ) 1) → S := fun ⟨e, t⟩ ↦
    ⟨AffineMap.lineMap e.1.1 e.1.2 (t : ℝ), hS ▸ mem_biUnion e.2
      ((segment_eq_image_lineMap ℝ e.1.1 e.1.2) ▸ mem_image_of_mem _ t.2)⟩
  have hf : Continuous f := continuous_sigma fun e ↦
    (AffineMap.lineMap_continuous.comp continuous_subtype_val).subtype_mk _
  refine (IsQuotientMap.of_surjective_continuous (fun ⟨x, hx⟩ ↦ ?_) hf).locallyPathConnectedSpace
  obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp <| hS ▸ hx
  obtain ⟨t, ht, rfl⟩ := segment_eq_image_lineMap ℝ e.fst e.snd ▸ hxe
  exact ⟨⟨⟨e, he⟩, ⟨t, ht⟩⟩, rfl⟩

theorem locallyConnectedSpace [T2Space V] (hS : IsSegmentFigure S) : LocallyConnectedSpace S := by
  let := hS.locallyPathConnectedSpace
  infer_instance

theorem finite_connectedComponents (hS : IsSegmentFigure S) : Finite (ConnectedComponents S) := by
  choose r hr using ConnectedComponents.surjective_coe (α := S)
  let := hS.finite_range_connectedComponentIn.to_subtype
  let f : ConnectedComponents S → range (_root_.connectedComponentIn S) := fun q ↦
    ⟨Subtype.val '' connectedComponent (r q), (r q).val, connectedComponentIn_eq_image (r q).prop⟩
  refine Finite.of_injective f fun q q' h ↦ ?_
  have heq : connectedComponent (r q) = connectedComponent (r q') :=
    Subtype.val_injective.image_injective (congrArg Subtype.val h)
  exact (hr q).symm.trans ((ConnectedComponents.coe_eq_coe.mpr heq).trans (hr q'))

theorem isTotallyDisconnected_iff_finite [T1Space V] (hS : IsSegmentFigure S) :
    IsTotallyDisconnected S ↔ S.Finite := by
  refine ⟨fun h ↦ hS.finite_iff.mpr fun a b hab ↦ h _ hab (convex_segment a b).isPreconnected
    (left_mem_segment ℝ a b) <| right_mem_segment ℝ a b, fun h ↦ ?_⟩
  let := h.to_subtype
  exact totallyDisconnectedSpace_subtype_iff.mp inferInstance

end IsSegmentFigure

theorem IsSegmentFigure.isBounded {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {T : Set W} (hT : IsSegmentFigure T) : Bornology.IsBounded T :=
  hT.isCompact.isBounded

end
