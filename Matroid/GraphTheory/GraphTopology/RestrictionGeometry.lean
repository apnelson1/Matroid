module

public import Matroid.GraphTheory.GraphTopology.StraightLine
public import Matroid.GraphTheory.GraphTopology.Restriction
public import Matroid.GraphTheory.GraphTopology.SegmentFigure

/-! # Geometry of whole-edge restrictions

Restrictions preserve edge geometry without finiteness assumptions. Finite restrictions
of a straight-line space are segment figures, even when the original space is infinite.
Common finite presentations realize their figures as actual restrictions.
-/

@[expose] public section

open Set Function
open scoped GraphLike

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X] {G : GraphLike X}
  {A : Set X}

namespace GraphLike

/-- Whole-edge restriction preserves straightness. -/
theorem restrict_isStraightLine (hG : G.IsStraightLine) (A : Set X) :
    (G.restrict A).IsStraightLine := by
  intro e he x y h
  rw [G.restrict_edgeSet A] at he
  rw [G.restrict_edgeBoundary he.2] at h
  exact hG he.1 h

/-- A finite restriction of a possibly infinite straight-line space is a segment figure. -/
theorem IsStraightLine.isSegmentFigure_restrict (hG : G.IsStraightLine)
    (hV : (A ∩ V(G)).Finite) (hE : {e ∈ E(G) | e ⊆ A}.Finite) :
    IsSegmentFigure (G.restrict A : Set X) := by
  let : (G.restrict A).Finite := (G.restrict_finite_iff A).mpr ⟨hV, hE⟩
  exact (restrict_isStraightLine hG A).isSegmentFigure_carrier

/-- Whole-edge restriction preserves polygonality, including loop edges. -/
theorem restrict_isPolygonal (hG : G.IsPolygonal) (A : Set X) : (G.restrict A).IsPolygonal := by
  intro e he
  rw [G.restrict_edgeSet A] at he
  exact hG he.1

end GraphLike

variable [ContinuousAdd X] [ContinuousSMul ℝ X]

/-- Every figure in a finite family is an actual restriction of a common straight-line
presentation. Any prescribed finite set of points in the union remains a set of vertices. -/
theorem IsSegmentFigure.exists_common_straightLineGraphLike_restrictions {ι : Type*} [Finite ι]
    {S : ι → Set X} [T2Space ↥(⋃ i, S i)] (hS : ∀ i, IsSegmentFigure (S i)) (hA : A.Finite)
    (hAS : A ⊆ ⋃ i, S i) : ∃ G : GraphLike X, G.Finite ∧ G.IsStraightLine ∧ G.carrier = ⋃ i, S i ∧
      A ⊆ G.vertexSet ∧ ∀ i, (G.restrict (S i) : Set X) = S i := by
  obtain ⟨G, hfin, hstraight, hcarrier, hvertices, hcover⟩ :=
    IsSegmentFigure.exists_common_straightLineGraphLike hS hA hAS
  refine ⟨G, hfin, hstraight, hcarrier, hvertices, fun i ↦ ?_⟩
  simpa only [GraphLike.coe_restrict, sUnion_eq_biUnion] using (hcover i).symm
