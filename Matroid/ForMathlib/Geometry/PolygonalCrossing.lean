module

public import Matroid.ForMathlib.Geometry.CircuitCrossing
public import Matroid.ForMathlib.Geometry.SegmentFigure.Affine
public import Matroid.ForMathlib.Topology.PrimitiveLink

/-! # Ray-crossing parity of polygonal primitive loops

Transversality supplies finite fibers, while the circuit bridge supplies boundary evenness.
Compactness supplies the separate closedness premise for complement local constancy.
-/

@[expose] public section

attribute [local instance] Complex.finrank_real_complex_fact

open Set Complex

namespace IsPrimitiveLink

/-- A polygonal primitive loop has locally constant crossing parity in a transverse direction. -/
theorem isLocallyConstant_rayCrossings_parity {S : Set ℂ} {a v : ℂ}
    (hL : IsPrimitiveLink S a a) (hS : IsSegmentFigure S)
    (htrans : ∀ x y, x ≠ y → segment ℝ x y ⊆ S →
      Complex.orientation.areaForm v x ≠ Complex.orientation.areaForm v y) :
    IsLocallyConstant (fun z : ↥Sᶜ ↦ (Complex.rayCrossings S z.1 v).ncard % 2) := by
  apply Complex.orientation.isLocallyConstant_rayCrossings_parity
    (isPrimitiveLink_iff_isCircuit.mp hL).1 hL.isCompact.isClosed
  intro z _
  apply ((hS.finite_fibers_iff (Complex.orientation.areaForm v).toAffineMap).mpr htrans
    (Complex.orientation.areaForm v z)).subset
  rintro p ⟨hp, t, _, rfl⟩
  refine ⟨hp, ?_⟩
  change Complex.orientation.areaForm v (z + t • v) = Complex.orientation.areaForm v z
  simp only [map_add, map_smul, Orientation.areaForm_apply_self, smul_zero, add_zero]

end IsPrimitiveLink
