module

public import Matroid.GraphLike.StraightLine
public import Matroid.GraphLike.Restriction
public import Matroid.GraphLike.Presentation

/-! # Geometry of whole-edge restrictions

Restrictions preserve edge geometry without finiteness assumptions. Finite selections
in a straight-line space are segment figures, even when the original space is infinite.
Common finite presentations realize their figures as actual restrictions.
-/

@[expose] public section

open Set Function
open scoped GraphLike

namespace GraphLike

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
variable {G : GraphLike X}

/-- Whole-edge restriction preserves straightness. -/
theorem restrict_isStraightLine (hG : G.IsStraightLine)
    (A : Set X) (B : Set (Set X)) : (G.restrict A B).IsStraightLine := by
  intro e he x y h
  have hm : e ∈ B ∩ E(G) := (G.restrict_edgeSet A B) ▸ he
  rw [G.restrict_edgeBoundary A B hm.2 hm.1] at h
  exact hG hm.2 h

/-- A finite support in a possibly infinite straight-line space is a segment figure. -/
theorem IsStraightLine.isSegmentFigure_support (hG : G.IsStraightLine)
    (A : Set X) (B : Set (Set X)) (hA : A.Finite) (hB : B.Finite) :
    IsSegmentFigure (G.support A B) := by
  let : (G.restrict A B).Finite :=
    (G.restrict_finite_iff A B).mpr ⟨hA.inter_of_left _, hB.inter_of_left _⟩
  exact (restrict_isStraightLine hG A B).isSegmentFigure_carrier

variable [ContinuousAdd X] [ContinuousSMul ℝ X]

/-- Whole-edge restriction preserves polygonality, including loop edges. -/
theorem restrict_isPolygonal (hG : G.IsPolygonal)
    (A : Set X) (B : Set (Set X)) : (G.restrict A B).IsPolygonal := by
  intro e he x y h
  have hm : e ∈ B ∩ E(G) := (G.restrict_edgeSet A B) ▸ he
  rw [G.restrict_edgeBoundary A B hm.2 hm.1] at h
  exact hG hm.2 h

end GraphLike

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [ContinuousAdd X] [ContinuousSMul ℝ X]

/-- Every figure in a finite family is an actual restriction of a common straight-line
presentation. Any prescribed finite set of points in the union remains a set of vertices. -/
theorem IsSegmentFigure.exists_common_straightLineGraphLike_restrictions
    {ι : Type*} [Finite ι] {S : ι → Set X} [T2Space ↥(⋃ i, S i)]
    (hS : ∀ i, IsSegmentFigure (S i)) {F : Set X}
    (hF : F.Finite) (hFS : F ⊆ ⋃ i, S i) :
    ∃ G : GraphLike X, G.Finite ∧ G.IsStraightLine ∧ G.carrier = ⋃ i, S i ∧
      F ⊆ G.vertexSet ∧
      ∀ i, (G.restrict (S i) {e | e ⊆ S i}).carrier = S i := by
  obtain ⟨G, hfin, hstraight, hcarrier, hvertices, hcover⟩ :=
    IsSegmentFigure.exists_common_straightLineGraphLike hS hF hFS
  refine ⟨G, hfin, hstraight, hcarrier, hvertices, fun i ↦ ?_⟩
  refine Eq.trans ?_ (hcover i).symm
  change G.support (S i) {e | e ⊆ S i} = _
  ext x
  simp only [GraphLike.support, mem_union, mem_inter_iff, mem_sUnion, mem_iUnion,
    mem_ofPred_eq]
  constructor
  · rintro (hx | ⟨e, ⟨hs, he⟩, hx⟩)
    · exact Or.inl hx
    · exact Or.inr ⟨e, ⟨he, hs⟩, hx⟩
  · rintro (hx | ⟨e, ⟨he, hs⟩, hx⟩)
    · exact Or.inl hx
    · exact Or.inr ⟨e, ⟨hs, he⟩, hx⟩
