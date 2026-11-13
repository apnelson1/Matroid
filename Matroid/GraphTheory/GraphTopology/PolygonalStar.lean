module

public import Matroid.GraphTheory.GraphTopology.Basic
public import Matroid.MiniTauCeti.JCT.Geometry.PrimitiveLink

/-! # Local stars in polygonal edges -/

@[expose] public section

open Set Metric Topology

namespace GraphLike

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- At an interior point of a polygonal edge, the carrier meets a sufficiently small ball in
exactly two radii. Only this edge needs to be polygonal, and the graphlike may be infinite. -/
theorem exists_radius_edgeInterior (G : GraphLike X) {e : Set X} (he : e ∈ E(G))
    (hpoly : IsSegmentFigure e) {p : X} (hp : p ∈ G.edgeInterior e) :
    ∃ ρ > 0, ∃ Y : Finset X, ↑Y ⊆ sphere p ρ ∧ Y.card = 2 ∧ ↑Y ⊆ e ∧
      closedBall p ρ ∩ G.carrier = {p} ∪ ⋃ y ∈ Y, segment ℝ p y := by
  obtain ⟨a, _, b, _, hb, hlink⟩ := G.boundary_isPair he
  have hends : p ∉ ({a, b} : Set X) := fun h ↦ hp.2 (hb.symm ▸ h).2
  obtain ⟨δ, hδ, hlocal⟩ := Metric.mem_nhds_iff.mp (G.carrier_eventuallyEq_edge he hp)
  obtain ⟨ρ, hρ, hρδ, Y, hcard, hY, hstar⟩ :=
    hlink.exists_local_star_two_le hpoly hp.1 (Or.inr hends) (half_pos hδ)
  have heq : closedBall p ρ ∩ G.carrier = closedBall p ρ ∩ e := by
    ext x
    by_cases hx : x ∈ closedBall p ρ
    · have hxδ : x ∈ ball p δ :=
        mem_ball.mpr ((mem_closedBall.mp hx).trans_lt (hρδ.trans_lt (half_lt_self hδ)))
      simp only [mem_inter_iff, hx, true_and]
      exact Iff.of_eq (hlocal hxδ)
    · simp [hx]
  refine ⟨ρ, hρ, Y, hY, hcard, ?_, heq.trans hstar⟩
  intro y hy
  have hyS : y ∈ {p} ∪ ⋃ y ∈ Y, segment ℝ p y :=
    Or.inr (mem_iUnion₂.mpr ⟨y, hy, right_mem_segment ℝ p y⟩)
  exact (hstar.symm ▸ hyS).2

end GraphLike
