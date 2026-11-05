# Graph-like spaces

This folder owns geometric carriers with a vertex set and primitive-link edges,
independently of an abstract graph representation.

`V(G) : Set X` and `E(G) : Set (Set X)` follow the `Graph` convention. Ordinary edge
statements use `e : Set X` with `he : e ∈ E(G)`; the edge is the point set itself.
`G.edgeInterior e = e \ V(G)` and `G.edgeBoundary e = e ∩ V(G)` are graph-relative,
not ambient interior and frontier. Use `↥E(G)` only when a map or equivalence needs a type
of actual edges. Construction proofs use `ConnectedComponents ↥(S \ Z)` directly, including
before a graph-like space has been constructed. The general-topology operation
`ConnectedComponents.toSet` extracts a component's point set in its own space. Its image under
subtype inclusion is a set in the ambient space; intersecting its closure with the carrier
produces an edge. There is no separate graph-specific component type or component geometry API.

| File | API |
| --- | --- |
| [Defs](Defs.lean) | `GraphLike`, vertex and geometric edge sets, graph-relative interiors/boundaries, incidence, finiteness, refinement, and faces |
| [Basic](Basic.lean) | Edge and carrier laws, relatively closed edge remainders, compactness, and containment of connected sets in edges |
| [Assembly](Assembly.lean) | Assembly from primitive links, its edge equivalence and equations, and finite sufficient conditions |
| [Polygonal](Polygonal.lean) | Polygonality of edges |
| [StraightLine](StraightLine.lean) | Straightness, geometric incidence, finiteness, and refinement preservation |
| [Presentation](Presentation.lean) | Finite straight-line presentations of segment figures, prescribed vertices, and common presentations |
| [Restriction](Restriction.lean) | Whole-edge restriction, support calculus, edge correspondences, and relative closure of finite-support differences |
| [Map](Map.lean) | Transport by a carrier-local embedding, edge image laws, identity and composition |
| [MapRestriction](MapRestriction.lean) | Transport commutes with support and restriction |
| [RestrictionGeometry](RestrictionGeometry.lean) | Geometry of restrictions and actual restrictions of common presentations |
| [MapGeometry](MapGeometry.lean) | Affine preservation of straightness and polygonality |
| [Subset](Subset.lean) | Relatively closed connected subsets and finite-support differences |

`GraphLike.ofLinks` constructs a graph-like space from indexed primitive links. It requires
relatively open link interiors and a relatively closed, totally separated vertex set, with
Hausdorffness only on the assembled carrier. Neither the vertex set nor the index type must
be finite. Its edge set is exactly the range of the supplied family. Membership, interior,
and boundary laws apply directly to each supplied point set. `ofLinksEdgeEquiv` is available
when an indexed correspondence is needed; its value at an index is that index's supplied set.

`ofFiniteLinks` derives those topological hypotheses from finite vertices and a finite link
family, and supplies a `GraphLike.Finite` instance. Both constructors retain vertices outside
all links. `ofLinks_finite_iff` characterizes finiteness by the vertex set and index type.
Assembly returns the object directly, not an existential package.

`GraphLike.IsStraightLine` says that an edge equals the segment between its boundary
vertices. It retains no orientation or parametrization. Its edges have distinct endpoints,
and an endpoint pair determines at most one edge. The predicate does not require finiteness.

For a finite straight-line space, the carrier is a segment figure. Conversely, every segment
figure with a Hausdorff carrier in a real topological vector space has a finite straight-line presentation,
including any prescribed finite subset among its vertices. The common-presentation theorem
preserves each input figure as vertices and whole edges. Its vertex term retains isolated points.

The construction is owned by [Presentation](Presentation.lean), using the algebraic
[segment-cutting lemmas](../ForMathlib/Analysis/Convex/SegmentCutting.lean).
[Subset](Subset.lean) owns the connected-subset argument using edge remainders. The
[segment-figure wrapper](../ForMathlib/Geometry/SegmentFigure/Subset.lean) supplies a finite
straight-line presentation. [Closure of differences](../ForMathlib/Geometry/SegmentFigure/Clipping.lean)
uses common restrictions and the general support-difference law. Neither consumer reconstructs
a second segment-family representation.

Restriction retains selected edges and their endpoints without finiteness assumptions.
Transport requires an embedding only on the carrier. Restriction retains the selected point
sets, and transport takes their images, preserving loops and parallel edges.

The association with an abstract graph stays in
[`Graph/Topology/Defs.lean`](../Graph/Topology/Defs.lean).
The [straight-line drawing bridge](../Graph/Topology/StraightLine.lean) uses
`D.toGraphLike.IsStraightLine` directly. Importing this folder does not introduce the legacy
carrier/vertex inclusion order from `Graph/Topology/Draft.lean`; the meaning and notation
of a more general relation remain open.

[Core regression consumers](../../tests/MatroidTests/StraightLine.lean) run under `lake test`.
The raw-edge, assembly, restriction, map, compatibility, and subset tests run under `lake test`.
Assembly tests construct a loop, parallel arcs, isolated vertices, and an infinite family of loops.
The [drawing operation regressions](../../tests/MatroidTests/GraphLikeDrawingOperations.lean)
and [straight-line drawing regression](../../tests/MatroidTests/StraightLineDrawing.lean) are
built separately because the existing graph drawing files use Lean's legacy module format.
`Drawing.restrict` and `Drawing.postcomp` now reuse the graph-like constructions.
