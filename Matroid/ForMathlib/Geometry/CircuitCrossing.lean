module

public import Matroid.ForMathlib.Geometry.RayCrossingParity
public import Matroid.ForMathlib.Topology.Circuit.Crossing

/-! # Circuit applications of ray-crossing parity

Circuit boundary evenness supplies the generic geometric parity law.
Closedness remains an independent premise of complement local constancy.
-/

@[expose] public section

open Set Module

namespace Orientation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (finrank ℝ E = 2)]

/-- Circuit ray-crossing parity agrees across a disjoint segment when its two forward
carrier sections are finite. -/
theorem rayCrossings_ncard_mod_two_eq_of_finite_ray_intersections
    (o : Orientation ℝ E (Fin 2)) {S : Set E} {v x y : E} (hC : IsCircuit S)
    (hx : (S ∩ {p | ∃ t : ℝ, 0 ≤ t ∧ p = x + t • v}).Finite)
    (hy : (S ∩ {p | ∃ t : ℝ, 0 ≤ t ∧ p = y + t • v}).Finite)
    (hbase : segment ℝ x y ∩ S = ∅) :
    (o.rayCrossings S x v).ncard % 2 = (o.rayCrossings S y v).ncard % 2 :=
  o.rayCrossings_ncard_mod_two_eq_of_even_boundaryCrossings
    (fun _ hU ↦ hC.even_ncard_boundaryCrossings hU) hx hy hbase

/-- A closed circuit with finite forward sections has locally constant ray-crossing parity
on its complement. -/
theorem isLocallyConstant_rayCrossings_parity (o : Orientation ℝ E (Fin 2))
    {S : Set E} {v : E} (hC : IsCircuit S) (hclosed : IsClosed S)
    (hfin : ∀ z ∉ S, (S ∩ {p | ∃ t : ℝ, 0 ≤ t ∧ p = z + t • v}).Finite) :
    IsLocallyConstant (fun z : ↥Sᶜ ↦ (o.rayCrossings S z.1 v).ncard % 2) :=
  o.isLocallyConstant_rayCrossings_parity_of_even_boundaryCrossings
    (fun _ hU ↦ hC.even_ncard_boundaryCrossings hU) hclosed hfin

end Orientation
