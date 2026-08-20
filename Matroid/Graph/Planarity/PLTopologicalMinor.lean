module

public import Matroid.Graph.Planarity.PLDrawing
public import Matroid.Graph.Planarity.TopologicalMinor

@[expose] public section

/-! # Polygonal drawings and subdivisions -/

namespace Graph

noncomputable section

variable {α β γ δ : Type*} {G : Graph α β} {H : Graph γ δ}
  {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [ContinuousSMul ℝ V] [ContinuousAdd V]

namespace Drawing.IsPL

/-- Subdividing the cells of a polygonal drawing preserves polygonality. This uses the
combinatorial subdivision witness, not merely an arbitrary homeomorphism of realizations. -/
theorem subdivide {D : Drawing H V} (hD : D.IsPL) (S : H.IsoSubdivision G) :
    (D.subdivide S).IsPL := by
  sorry

/-- Suppressing subdivision vertices in a polygonal drawing preserves polygonality. -/
theorem suppress {D : Drawing G V} (hD : D.IsPL) (S : H.IsoSubdivision G) :
    (D.suppress S).IsPL := by
  sorry

end Drawing.IsPL

namespace PLDrawing

/-- Subdivide a bundled polygonal drawing without changing its support. -/
noncomputable def subdivide (D : PLDrawing H V) (S : H.IsoSubdivision G) : PLDrawing G V := by
  sorry

@[simp]
theorem subdivide_toDrawing (D : PLDrawing H V) (S : H.IsoSubdivision G) :
    (D.subdivide S).toDrawing = D.toDrawing.subdivide S := by
  sorry

end PLDrawing


end


end Graph
