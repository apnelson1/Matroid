module

public import Matroid.GraphTheory.GraphTopology.Basic
public import Matroid.MiniTauCeti.JCT.Geometry.SegmentFigure.Basic

/-! # Polygonal graph-like spaces -/

@[expose] public section

open Set

namespace GraphLike

variable {X : Type*} [TopologicalSpace X]

variable [AddCommGroup X] [Module ℝ X] {G : GraphLike X}

/-- Every geometric edge is a finite union of straight segments. -/
def IsPolygonal (G : GraphLike X) : Prop :=
  ∀ {e : Set X}, e ∈ E(G) → IsSegmentFigure e

/-- A finite polygonal graphlike has a segment-figure carrier, including isolated vertices. -/
theorem IsPolygonal.isSegmentFigure_carrier (hG : G.IsPolygonal) [G.Finite] :
    IsSegmentFigure G.carrier := by
  rw [G.carrier_eq_vertexSet_union_sUnion_edges, sUnion_eq_biUnion]
  exact (IsSegmentFigure.of_finite Finite.vertexSet_finite).union
    (IsSegmentFigure.biUnion Finite.edgeSet_finite fun _ he ↦ hG he)

end GraphLike
