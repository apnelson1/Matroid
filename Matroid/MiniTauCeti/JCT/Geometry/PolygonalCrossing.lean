module

public import Matroid.MiniTauCeti.JCT.Geometry.RayCrossingParity
public import Matroid.MiniTauCeti.JCT.Topology.Path.Crossing
public import Matroid.MiniTauCeti.JCT.Geometry.SegmentFigure.Affine
public import Matroid.MiniTauCeti.JCT.Topology.PrimitiveLink

/-! # Ray-crossing parity of polygonal primitive loops

Transversality supplies finite fibers, while supplied-path parity gives boundary evenness.
Compactness supplies the separate closedness premise for complement local constancy.
-/

@[expose] public section

attribute [local instance] Complex.finrank_real_complex_fact

open Set Complex

namespace Path.IsSimpleLoop

/-- A polygonal primitive loop has locally constant crossing parity in a transverse direction. -/
theorem isLocallyConstant_rayCrossings_parity {a v : ℂ} {P : Path a a}
    (hP : P.IsSimpleLoop) (hS : IsSegmentFigure (range P))
    (htrans : ∀ x y, x ≠ y → segment ℝ x y ⊆ (range P) →
      Complex.orientation.areaForm v x ≠ Complex.orientation.areaForm v y) :
    IsLocallyConstant (fun z : ↥(range P)ᶜ ↦ (Complex.rayCrossings (range P) z.1 v).ncard % 2) := by
  apply Complex.orientation.isLocallyConstant_rayCrossings_parity_of_even_boundaryCrossings
    (fun _ hU ↦ hP.even_ncard_boundaryCrossings hU) (isCompact_range P.continuous).isClosed
  intro z _
  apply ((hS.finite_fibers_iff (Complex.orientation.areaForm v).toAffineMap).mpr htrans
    (Complex.orientation.areaForm v z)).subset
  rintro p ⟨hp, t, _, rfl⟩
  refine ⟨hp, ?_⟩
  change Complex.orientation.areaForm v (z + t • v) = Complex.orientation.areaForm v z
  simp only [map_add, map_smul, Orientation.areaForm_apply_self, smul_zero, add_zero]

end Path.IsSimpleLoop
