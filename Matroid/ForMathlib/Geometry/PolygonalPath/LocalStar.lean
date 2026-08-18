module

public import Matroid.ForMathlib.Geometry.SegmentFigure

/-!
# Local structure of a simple polygonal arc

At a point of a simple polygonal path other than its endpoints, the path has exactly two local
germs. This is a fact about simple polygonal arcs in a real normed space, independent of dimension.

The theorem allows the radius to be bounded by any prescribed positive scale, so the local star can
be combined with other radius bounds.
-/

open Set Metric

namespace PolygonalPath

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {x y q : V} {P : PolygonalPath x y}

/-- A nonendpoint point of a simple polygonal path has, at every sufficiently small requested
scale, a neighborhood consisting of exactly two radial segments, expressed by the star equation. -/
theorem IsSimple.exists_local_star_two (hP : P.IsSimple) (hqP : q ∈ P.toSet) (hqx : q ≠ x)
    (hqy : q ≠ y) {ε : ℝ} (hε : 0 < ε) : ∃ ρ, 0 < ρ ∧ ρ ≤ ε ∧ ∃ Y : Finset V, Y.card = 2 ∧
    (Y : Set V) ⊆ sphere q ρ ∧ closedBall q ρ ∩ P.toSet = {q} ∪ ⋃ z ∈ Y, segment ℝ q z := by
  /-
  Proof decomposition intended for implementation:

  1. Subdivide `P` at `q`.  `toSet_subdivide` and `isSimple_subdivide_iff` let the rest of the
     argument work with a path having `q` as a vertex without changing the represented arc.
  2. Use `IsSimple.breakAt` at `q`.  The two resulting simple subpaths meet exactly in `{q}`.
     Because `q ≠ x,y`, both subpaths are nontrivial.
  3. Reverse the left subpath, so both pieces start at `q`.  Apply
     `exists_ball_inter_subset_firstSegment` to each and choose a common radius below both bounds
     and below `ε`.
  4. Apply `P.isSegmentFigure_toSet.exists_radius`, then `exists_radius_of_le`, to obtain the star
     equation at that common scale.
  5. Prove `2 ≤ Y.card` with `le_card_radii_of_pairwise`, using the two broken subpaths as the two
     pieces.  Their global intersection is already `{q}`, so unlike the theta-endpoint argument no
     artificial localization is needed here.
  6. Prove `Y.card ≤ 2` with `card_radii_le_of_cover`; the two first-segment bounds from step 3 are
     exactly its `hUz`.
  7. Antisymmetry gives `Y.card = 2`.

  If implementation exposes a useful theorem about a nontrivial simple path having
  `firstTip ≠ source`, that theorem belongs in `PolygonalPath.Basic`, not as a private helper here.
  -/
  sorry

end PolygonalPath
