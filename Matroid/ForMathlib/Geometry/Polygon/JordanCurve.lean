module

public import Matroid.ForMathlib.Geometry.Polygon.PolygonalPath
public import Matroid.ForMathlib.Topology.JordanCurve

/-!
# The polygonal Jordan curve theorem

A simple closed polygonal path is a Jordan curve, so everything in
`Matroid.ForMathlib.Topology.JordanCurve` applies to it. This file is that bridge, together with the
restatements of the two sides of a polygon in the plane and on the sphere.

The path bridge uses the path parametrization to build `IsJordanCurve`; the polygon bridge converts
the cyclic boundary to a closed polygonal path. The side statements then follow from the Jordan
curve theorem.

## Main statements

* `PolygonalPath.IsSimpleLoop.isJordanCurve`, `Polygon.IsSimple.isJordanCurve` : the bridges.
* `PolygonalPath.IsSimpleLoop.exists_sides`, `PolygonalPath.IsSimpleLoop.exists_sides_onePoint`.
-/

@[expose] public section

open Set Function Topology Bornology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]

namespace PolygonalPath

variable {x : E} {P : PolygonalPath x x}

omit [Fact (Module.finrank ℝ E = 2)] in
/-- A simple closed polygonal path is a Jordan curve. -/
theorem IsSimpleLoop.isJordanCurve (h : P.IsSimpleLoop) : IsJordanCurve P.toSet :=
  ⟨x, P.toPath, h, P.toSet_eq_range_toPath.symm⟩

/-- The Jordan curve theorem for a polygon, plane form. -/
theorem IsSimpleLoop.exists_sides (h : P.IsSimpleLoop) :
    ∃ U V : Set E,
      IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ Disjoint U V ∧ U ∪ V = P.toSetᶜ ∧
      IsBounded U ∧ ¬ IsBounded V ∧ frontier U = P.toSet ∧ frontier V = P.toSet :=
  h.isJordanCurve.exists_sides

/-- The Jordan curve theorem for a polygon, sphere form. On `OnePoint E` the two sides are
interchangeable. -/
theorem IsSimpleLoop.exists_sides_onePoint (h : P.IsSimpleLoop) :
    ∃ U V : Set (OnePoint E),
      IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ Disjoint U V ∧
      U ∪ V = ((↑) '' P.toSet)ᶜ ∧ OnePoint.infty ∈ V ∧
      frontier U = (↑) '' P.toSet ∧ frontier V = (↑) '' P.toSet :=
  h.isJordanCurve.exists_sides_onePoint

end PolygonalPath

namespace Polygon

variable {n : ℕ} {p : Polygon E n}

omit [Fact (Module.finrank ℝ E = 2)] in
/-- The boundary of a simple polygon is a Jordan curve. -/
theorem IsSimple.isJordanCurve (h : p.IsSimple ℝ) (i : Fin n) : IsJordanCurve (p.boundary ℝ) := by
  sorry

end Polygon
