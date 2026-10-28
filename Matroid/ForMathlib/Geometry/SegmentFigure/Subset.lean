module

public import Matroid.GraphLike.Subset
public import Matroid.ForMathlib.Geometry.SegmentFigure.Real
public import Matroid.ForMathlib.Analysis.Convex.Segment

/-!
# Closed subsets of segment figures

Relatively closed preconnected subsets of a Hausdorff figure are figures. More generally,
a subset is a figure exactly when it is relatively closed and has finitely many connected
components. The ambient vector space need not be Hausdorff.

The proof uses a finite straight-line graph-like presentation and its edge remainders,
then applies the order-topological gap theorem. A component may meet one edge in two
separated pieces.
-/

@[expose] public section

open Set Topology unitInterval Topology.IsInducing

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [ContinuousAdd V]
  [ContinuousSMul ℝ V] {S C : Set V}

local instance : IsTopologicalAddGroup V where
  continuous_neg := by simpa only [neg_one_smul] using (continuous_const_smul (-1 : ℝ) :
    Continuous fun x : V ↦ (-1 : ℝ) • x)

namespace IsSegmentFigure

/-- A compact preconnected subset of a Hausdorff segment is a figure. In the nonempty
case the underlying result gives a single segment, not merely a finite union. -/
theorem of_isCompact_isPreconnected_subset_segment {a b : V} [T2Space ↥(segment ℝ a b)]
    (hc : IsCompact C) (hconn : IsPreconnected C) (hsub : C ⊆ segment ℝ a b) :
    IsSegmentFigure C := by
  obtain rfl | hne := C.eq_empty_or_nonempty
  · exact isSegmentFigure_empty
  obtain ⟨x, y, rfl⟩ := hc.exists_eq_segment_of_isConnected_of_subset_segment ⟨hne, hconn⟩ hsub
  exact isSegmentFigure_segment x y

section

variable [T2Space S]

/-- Relatively closed preconnected subsets of a Hausdorff figure are figures.
Only the figure, not the ambient vector space, must be Hausdorff. The empty set is allowed. -/
theorem of_isClosed_preimage_isPreconnected (hS : IsSegmentFigure S) (hCS : C ⊆ S)
    (hc : IsClosed (Subtype.val ⁻¹' C : Set S)) (hconn : IsPreconnected C) : IsSegmentFigure C := by
  obtain ⟨G, hfin, hstraight, rfl, _⟩ :=
    hS.exists_straightLineGraphLike finite_empty <| empty_subset S
  let := hfin
  exact GraphLike.isSegmentFigure_of_isClosed_isPreconnected hstraight hCS hc hconn

/-- Ambient closedness implies the relative closedness needed by the subset theorem. -/
theorem of_isClosed_isPreconnected (hS : IsSegmentFigure S) (hCS : C ⊆ S) (hc : IsClosed C)
    (hconn : IsPreconnected C) : IsSegmentFigure C :=
  hS.of_isClosed_preimage_isPreconnected hCS (hc.preimage continuous_subtype_val) hconn

open ConnectedComponents in
/-- A subset of a Hausdorff figure is a figure exactly when it is relatively closed and
has finitely many connected components. -/
theorem iff_isClosed_preimage_finite_connectedComponents (hS : IsSegmentFigure S) (hCS : C ⊆ S) :
    IsSegmentFigure C ↔ IsClosed (Subtype.val ⁻¹' C : Set S) ∧ Finite (ConnectedComponents C) := by
  refine ⟨fun h ↦ ⟨(subtypeVal.isCompact_preimage' h.isCompact
    (⟨⟨·, hCS ·⟩, rfl⟩)).isClosed, h.finite_connectedComponents⟩, fun ⟨hc, _⟩ ↦ ?_⟩
  let F (q : ConnectedComponents C) : Set C := mk ⁻¹' {q}
  have heq : C = ⋃ q, Subtype.val '' F q := by
    ext x
    simp only [mem_iUnion, mem_image, F, mem_preimage, mem_singleton_iff]
    exact ⟨fun hx ↦ ⟨mk ⟨x, hx⟩, ⟨x, hx⟩, rfl, rfl⟩, fun ⟨_, y, _, hy⟩ ↦ hy ▸ y.prop⟩
  refine heq ▸ iUnion fun q ↦ ?_
  obtain ⟨x, rfl⟩ := surjective_coe q
  change IsSegmentFigure (Subtype.val '' mk ⁻¹' {mk x})
  rw [connectedComponents_preimage_singleton]
  refine hS.of_isClosed_preimage_isPreconnected (fun y ⟨z, _, hz⟩ ↦ hz ▸ hCS z.prop) ?_ <|
    isPreconnected_connectedComponent.image _ continuous_subtype_val.continuousOn
  have hinc : IsClosedEmbedding <| inclusion hCS := by
    refine ⟨IsEmbedding.inclusion hCS, ?_⟩
    convert hc using 1
    ext z
    simp [range_inclusion]
  convert hinc.isClosedMap _ (isClosed_connectedComponent (x := x)) using 1
  ext z
  simp only [mem_preimage, mem_image, inclusion, Subtype.ext_iff]

end

/-- In a Hausdorff ambient space the relative characterization is equivalently stated
using ambient closedness. -/
theorem iff_isClosed_finite_connectedComponents [T2Space V] (hS : IsSegmentFigure S) (hCS : C ⊆ S) :
    IsSegmentFigure C ↔ IsClosed C ∧ Finite (ConnectedComponents C) :=
  ⟨fun h ↦ ⟨h.isClosed, h.finite_connectedComponents⟩,
    fun ⟨hc, hfin⟩ ↦ (hS.iff_isClosed_preimage_finite_connectedComponents hCS).mpr
      ⟨hc.preimage continuous_subtype_val, hfin⟩⟩

end IsSegmentFigure

end
