module

public import Matroid.ForMathlib.Geometry.Polygon.Basic
public import Matroid.ForMathlib.Geometry.SegmentFigure

/-!
# Polygon boundaries as segment figures

This file is the bridge from polygons to the representation-independent segment-figure theory.
-/

@[expose] public section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The boundary of a polygon is a segment figure. -/
@[grind .]
theorem Polygon.isSegmentFigure_boundary {n : ℕ} (p : Polygon V n) :
    IsSegmentFigure (p.boundary ℝ) := by
  rw [Polygon.boundary_eq_iUnion_segment]
  exact IsSegmentFigure.iUnion fun i ↦ isSegmentFigure_segment _ _

end
