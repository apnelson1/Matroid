module

public import Matroid.GraphLike.Basic
public import Matroid.ForMathlib.Geometry.PolygonalPath.PrimitivePath

/-! # Polygonal graph-like spaces -/

@[expose] public section

open Set

namespace GraphLike

variable {X : Type*} [TopologicalSpace X]

def IsPolygonal [AddCommGroup X] [Module ℝ X] [ContinuousSMul ℝ X] [ContinuousAdd X]
    (T : GraphLike X) : Prop :=
  ∀ {e : Set X}, e ∈ T.edgeSet → ∀ {x y : X}, T.edgeBoundary e = {x, y} →
    ∃ P : PolygonalPath x y, P.toPath.IsPrimitive ∧ P.toSet = e

end GraphLike
