module

public import Matroid.MiniTauCeti.JCT.Geometry.Polygon.PolygonalPath
public import Matroid.MiniTauCeti.JCT.Topology.Circuit.Parametrization

/-!
# Polygonal paths and polygons as circuits

Simple closed polygonal paths and simple polygons have circuit images.
-/

@[expose] public section

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace PolygonalPath

variable {x : E} {P : PolygonalPath x x}

/-- A simple closed polygonal path is a circuit. -/
theorem IsSimpleLoop.isCircuit (h : P.IsSimpleLoop) : IsCircuit P.toSet :=
  P.toSet_eq_range_toPath ▸ Path.IsSimpleLoop.isCircuit h

end PolygonalPath

namespace Polygon

variable {n : ℕ} {p : Polygon E n}

/-- The boundary of a simple polygon is a circuit. -/
theorem IsSimple.isCircuit (h : p.IsSimple ℝ) : IsCircuit (p.boundary ℝ) := by
  let := h.neZero
  exact toSet_toPolygonalPath p 0 ▸ ((isSimple_iff_isSimpleLoop p 0).mp h).isCircuit

end Polygon
