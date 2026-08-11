module

public import Matroid.ForMathlib.Geometry.Polygon.PolygonalPath
public import Matroid.ForMathlib.Topology.JordanCurve

/-!
# The polygonal Jordan curve theorem

A simple closed polygonal path is a Jordan curve, so everything in
`Matroid.ForMathlib.Topology.JordanCurve` applies to it. This file is that bridge, together with the
restatements the plane-topology development actually calls: the two sides of a polygon, in the plane
and on the sphere.

Only the polygonal case of the Jordan curve theorem is used anywhere in the Kuratowski development,
and unlike the general case it is elementary: the complement of a polygon is separated by the parity
of the number of crossings of a generic ray. So the statements here are targets to be proved, not
assumptions to be lived with, even though for now they inherit their `sorry` from
`IsJordanCurve.exists_sides`.

Both entry points are provided, since both presentations occur: `PolygonalPath.IsSimpleLoop` when
the curve arrives with a base point — the common case, since a cycle in a graph is traversed from
one of its vertices — and `Polygon.IsSimple` when it does not.

## Main statements

* `PolygonalPath.IsSimpleLoop.isJordanCurve`, `Polygon.IsSimple.isJordanCurve` : the bridges.
* `PolygonalPath.IsSimpleLoop.exists_sides`, `PolygonalPath.IsSimpleLoop.exists_sides_onePoint`.
-/

@[expose] public section

open Set Function Topology Bornology

namespace PolygonalPath

variable {x : EuclideanSpace ℝ (Fin 2)} {P : PolygonalPath x x}

/-- A simple closed polygonal path is a Jordan curve. -/
theorem IsSimpleLoop.isJordanCurve (h : P.IsSimpleLoop) : IsJordanCurve P.toSet :=
  ⟨x, P.toPath, h, P.toSet_eq_range_toPath.symm⟩

/-- The Jordan curve theorem for a polygon, plane form. -/
theorem IsSimpleLoop.exists_sides (h : P.IsSimpleLoop) :
    ∃ U V : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ Disjoint U V ∧ U ∪ V = P.toSetᶜ ∧
      IsBounded U ∧ ¬ IsBounded V ∧ frontier U = P.toSet ∧ frontier V = P.toSet :=
  h.isJordanCurve.exists_sides

/-- The Jordan curve theorem for a polygon, sphere form. This is the one the face arguments use:
on `OnePoint ℝ²` the two sides are interchangeable, so no argument has to name the unbounded one. -/
theorem IsSimpleLoop.exists_sides_onePoint (h : P.IsSimpleLoop) :
    ∃ U V : Set (OnePoint (EuclideanSpace ℝ (Fin 2))),
      IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ Disjoint U V ∧
      U ∪ V = ((↑) '' P.toSet)ᶜ ∧ OnePoint.infty ∈ V ∧
      frontier U = (↑) '' P.toSet ∧ frontier V = (↑) '' P.toSet :=
  h.isJordanCurve.exists_sides_onePoint

end PolygonalPath

namespace Polygon

variable {n : ℕ} {p : Polygon (EuclideanSpace ℝ (Fin 2)) n}

/-- The boundary of a simple polygon is a Jordan curve. The index `i` is not decoration: the empty
polygon is simple and its boundary is empty, so a base point has to be available. -/
theorem IsSimple.isJordanCurve (h : p.IsSimple ℝ) (i : Fin n) : IsJordanCurve (p.boundary ℝ) := by
  sorry

end Polygon
