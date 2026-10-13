module

public import Matroid.ForMathlib.Geometry.PolygonalPath.Basic
public import Matroid.ForMathlib.Geometry.SegmentFigure

/-!
# Polygonal paths as segment figures

This file is the bridge from polygonal paths to the representation-independent segment-figure
theory.
-/

@[expose] public section

open Set

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The set traced by a polygonal path is a segment figure. -/
@[grind .]
theorem PolygonalPath.isSegmentFigure_toSet {x y : V} (P : PolygonalPath x y) :
    IsSegmentFigure P.toSet := by
  refine ⟨{y}, {s | s ∈ P.edges}, finite_singleton _, P.edges.finite_toSet, ?_⟩
  rw [PolygonalPath.toSet_eq_insert_biUnion]
  rfl

end
