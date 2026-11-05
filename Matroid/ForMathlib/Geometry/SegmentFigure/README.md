# Segment figures

`IsSegmentFigure S` means that `S` is a finite union of closed real segments.
Degenerate segments include isolated points; the empty family represents the empty set.
The predicate concerns the set and does not choose a presentation or parametrization.

Import the chapter needed by the consumer. The former `Geometry.SegmentFigure` import has
been replaced by this folder.

| Module | Public content |
| --- | --- |
| [Basic](Basic.lean) | Definition, generators, finite unions, intersections, induction, affine images, finite subsets with the same convex hull |
| [Affine](Affine.lean) | Affine sections, injective affine preimages, finite fibers, image reflection, finite-dimensional span |
| [Cardinality](Cardinality.lean) | Finite/countable characterization and nondegenerate contained segments |
| [Topology](Topology.lean) | Compactness, closedness, boundedness, components, local path connectedness, total disconnectedness |
| [Real](Real.lean) | Finite unions of bounded closed intervals; connected figures are intervals |
| [Maximal](Maximal.lean) | Canonical maximal segments, finite coverage, extension, isolated points, affine transport |
| [Shape](Shape.lean) | Convex figures are empty or single segments; connected collinear figures are segments |
| [Clipping](Clipping.lean) | Closed convex sections, closure of convex clipping, closure of differences |
| [Subset](Subset.lean) | Relatively closed preconnected subsets of Hausdorff figures; the relative closedness and finite-components characterization |
| [Star](Star.lean) | Metric local stars and intrinsic radius counts, moved from the former file |
| [Transverse](Transverse.lean) | Transverse planar directions and finite coordinate fibers |
| [RayCrossing](RayCrossing.lean) | Boundary crossings restricted to rays, finiteness, and ray avoidance |

## Assumptions

The definition, finite operations, affine operations, cardinality, maximal-segment
normal form, and convex characterization require only an additive commutative group with a
real module structure. Affine images need neither continuity nor injectivity. Affine preimages
require injectivity.

Compactness and component results use continuous vector operations. Ambient closedness,
local path connectedness, and clipping use a Hausdorff ambient topology. Subset inheritance
requires only that the containing figure be Hausdorff, with closedness relative to that figure.
Finiteness of the component set does not require Hausdorffness. Total disconnectedness is
equivalent to finiteness already under the T₁ assumption. Boundedness and metric stars have
their normed-space assumptions only on the relevant declarations.

## Two different finite descriptions

**Straight-line presentation** produces a finite `GraphLike` with the figure as its carrier.
[GraphLike/Presentation](../../../GraphLike/Presentation.lean) owns
`exists_straightLineGraphLike` and `exists_common_straightLineGraphLike`. The latter preserves
each input figure as vertices and whole edges, including prescribed points as vertices.
Edges are nondegenerate; isolated points remain vertices. These presentations require
continuous vector operations and a Hausdorff carrier, not a Hausdorff ambient space.

**Maximal segments** are defined intrinsically by `maximalSegments S`. They cover `S`, and
every segment contained in `S` extends to one of them. They need not form a subdivision:
the two maximal segments of a cross meet at their interiors. Singleton maximal segments
are precisely isolated points. Injective affine maps transport this family exactly.

## Subsets and clipping

For `C ⊆ S` with `IsSegmentFigure S` and `T2Space S`,
`IsSegmentFigure.iff_isClosed_preimage_finite_connectedComponents` proves

```lean
IsSegmentFigure C ↔
  IsClosed (Subtype.val ⁻¹' C : Set S) ∧ Finite (ConnectedComponents C)
```

The preconnected case is `of_isClosed_preimage_isPreconnected`, including the empty subset.
Neither theorem requires ambient Hausdorffness. `of_isClosed_isPreconnected` retains the
ambient-closed calling form; `iff_isClosed_finite_connectedComponents` retains the
ambient-closed characterization when the ambient space is Hausdorff.

The proof is owned by [GraphLike/Subset](../../../GraphLike/Subset.lean); this chapter supplies
the straight-line presentation. It uses compact edge parametrizations and the edge-remainder
facts in `GraphLike.edge`. The interval attachment theorem in
[Topology/Order](../../Topology/Order.lean) is purely topological: a preconnected set reaching
the remainder of an attached interval has an order-connected parameter gap. A separate
ordered-space theorem gives at most two compact order-connected pieces. When the entire
subset lies in one segment, [Segment](../../Analysis/Convex/Segment.lean)
identifies a nonempty compact connected subset with a single segment.

For convex `C`, `inter_convex` requires closedness, while `closure_inter_convex` does not.
For two figures, `relativeClosure_sdiff` requires only a Hausdorff left carrier and proves
that `S ∩ closure (S \ T)` is a figure. It uses common whole-edge restrictions and
`GraphLike.closure_support_sdiff`, whose right-hand selection need not be finite.
The ambient `closure_sdiff` follows by closedness of `S` and restores endpoints that deletion
may remove. An injective
affine line section is a real figure by `preimage`, and its interval presentation follows
from `isSegmentFigure_iff_finite_iUnion_Icc`.

Arbitrary subsets and infinite intersections need not be figures. Neither convex hulls,
products, nor Minkowski sums preserve figures: they can fill triangles or squares. An empty
intersection family gives the whole ambient space, so `iInter` requires a nonempty index type;
`inter_biInter` permits an empty family by intersecting inside a supplied figure.

## Crossings and ray avoidance

Planar directions use Mathlib's `Complex.orientation.areaForm v p`, not a separate coordinate
definition. `Transverse.lean` contains direction selection and its planar consequences only.
Modules using the area form enable the existing `Complex.finrank_real_complex_fact` locally.

The underlying affine facts are independent of the complex plane. Exact line criteria live in
[AffineMap](../../LinearAlgebra/AffineSpace/AffineMap.lean); segment criteria and finite-cover
fibres live in [SegmentCover](../../Analysis/Convex/SegmentCover.lean). Both imports exclude
topology and figures. The intrinsic `IsSegmentFigure.finite_fibers_iff` and finite exceptional
values live in [Affine](Affine.lean). Apply the equivalence to `(o.areaForm v).toAffineMap`
to obtain finite fibres from transversality. The direction classification also covers finite
carriers, rank-one spaces, and infinite-dimensional modules.

The crossing definition is `boundaryCrossings`, owned by
[Topology/Crossing](../../Topology/Crossing.lean). The generic
[ray module](../RayCrossing.lean) defines `Orientation.rayCrossings` as the intersection of the
forward ray with the half-plane crossing set. `Complex.rayCrossings` is its canonical complex
specialization. The intersection counts points independently of segment presentations and
includes the initial point when it is a crossing. Same-side touches are not counted; the zero
direction has no crossings.

`Orientation.mem_boundaryCrossings_halfPlane_iff` gives the two strict-side closure conditions.
`Orientation.mem_rayCrossings_iff` bases the supporting half-plane at a point on the ray.
[Generic parity](../RayCrossingParity.lean) uses the supplied boundary-evenness law and finite
forward carrier sections. It imports neither circuits nor figures. The
[circuit bridge](../CircuitCrossing.lean) supplies evenness; local constancy separately requires
closedness. Both carrier and region may vary in the shared crossing-germ theorem.

The endpoint approach theorem belongs to [Segment](../../Analysis/Convex/Segment.lean):
`AffineMap.mem_closure_lt_of_openSegment_subset` uses containment of an open segment, over a
densely ordered ring with continuous scalar multiplication and constant translations.
Continuity of the functional and Hausdorffness are unnecessary. Crossing-specific consequences
belong in [AffineCrossing](../AffineCrossing.lean).

[Figure ray intervals](RayCrossing.lean) characterize singleton-ray intervals by infinitude of
the area-coordinate image. An infinite figure supplies a transverse direction and such an
interval. A caller chooses an interior parameter to obtain a single exterior origin.

`Complex.exists_ray_avoiding_of_bddAbove` uses an upper bound on the longitudinal coordinate
`(p / v).re`. The generic [bounded-set theory](../../Analysis/LocallyConvex/Bounded.lean) supplies
an avoiding ray in every prescribed direction from Von Neumann boundedness. Compact callers
use `hcompact.isVonNBounded ℝ`; empty-crossing callers use
`Orientation.exists_rayCrossings_eq_empty hcompact.isBounded`. Whole-ray avoidance also excludes
touches and overlap.

## Verification

[SegmentFigure regression consumers](../../../../tests/MatroidTests/SegmentFigure.lean)
exercise algebraic ambient spaces, reversed/degenerate figures, common straight-line presentations,
intrinsic subsets, and clipping followed by deletion. They also check that the main presentation,
maximal-segment, and subset theorems use only Lean's standard logical axioms.
[Subset regressions](../../../../tests/MatroidTests/SegmentFigureSubset.lean) additionally
exercise carrier-relative hypotheses, the finite straight-line consumer, empty and singleton
cases, a connected subset with a disconnected segment intersection, and the finite-component
reverse implication. Both test modules are imported by the `lake test` root.
