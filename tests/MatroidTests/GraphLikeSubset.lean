module

public import Matroid.GraphTheory.GraphTopology.Subset
public import Matroid.ForMathlib.Geometry.SegmentFigure.Clipping

/-! # Relative closure consumers for graph-like supports -/

open Set
open scoped GraphLike

section GraphLike

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  {G : GraphLike X} (hG : G.IsStraightLine)

-- There is no finiteness assumption on G or on the deleted selection.
-- There are no continuity assumptions on the vector operations or ambient separation.
example (A C : Set X) (B D : Set (Set X)) (hA : A.Finite) (hB : B.Finite) :
    IsSegmentFigure (G.carrier ∩ closure (G.support A B \ G.support C D)) :=
  GraphLike.isSegmentFigure_relativeClosure_sdiff hG A C B D hA hB

-- Deleting every vertex leaves the retained edge interior; closure restores its range.
example (e : Set X) (he : e ∈ E(G)) :
    IsSegmentFigure (G.carrier ∩ closure (G.support ∅ {e} \ G.support univ ∅)) ∧
      G.carrier ∩ closure (G.support ∅ {e} \ G.support univ ∅) = e := by
  refine ⟨GraphLike.isSegmentFigure_relativeClosure_sdiff hG ∅ univ {e} ∅
    finite_empty (finite_singleton e), ?_⟩
  rw [G.closure_support_sdiff ∅ univ {e} ∅ finite_empty (finite_singleton e)]
  simp [GraphLike.support, inter_eq_left.mpr (singleton_subset_iff.mpr he)]

example [T2Space X] (A C : Set X) (B D : Set (Set X))
    (hA : A.Finite) (hB : B.Finite) :
    IsSegmentFigure (closure (G.support A B \ G.support C D)) :=
  GraphLike.isSegmentFigure_closure_sdiff hG A C B D hA hB

end GraphLike

section Figures

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] {S T : Set V}

-- Only the left carrier is assumed Hausdorff, not V, T, or their union.
example [T2Space S] (hS : IsSegmentFigure S) (hT : IsSegmentFigure T) :
    IsSegmentFigure (S ∩ closure (S \ T)) := hS.relativeClosure_sdiff hT

end Figures

/-- info: 'GraphLike.isSegmentFigure_relativeClosure_sdiff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GraphLike.isSegmentFigure_relativeClosure_sdiff

/-- info: 'GraphLike.isSegmentFigure_closure_sdiff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GraphLike.isSegmentFigure_closure_sdiff

/-- info: 'IsSegmentFigure.relativeClosure_sdiff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IsSegmentFigure.relativeClosure_sdiff

/-- info: 'IsSegmentFigure.closure_sdiff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IsSegmentFigure.closure_sdiff
