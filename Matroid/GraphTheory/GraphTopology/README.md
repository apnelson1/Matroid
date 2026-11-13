# Graph-like spaces

This folder owns geometric carriers with a vertex set and primitive-link edges,
independently of an abstract graph representation.

`V(G) : Set X` and `E(G) : Set (Set X)` follow the `Graph` convention. Ordinary edge
statements use `e : Set X` with `he : e ∈ E(G)`; the edge is the point set itself.
`G.edgeInterior e = e \ V(G)` and `G.edgeBoundary e = e ∩ V(G)` are graph-relative,
not ambient interior and frontier. Use `↥E(G)` only when a map or equivalence needs a type
of actual edges. Both the graph-like axioms and edge construction use ambient component
sets `connectedComponentIn (S \ Z) x` for points `x ∈ S \ Z`. Their closures relative to
`S` are the edges; no component quotient or separately stored edge family is needed.
Construction proofs identify these component sets with supplied link interiors or retained
edge interiors using connectedness and maximality.

| File | API |
| --- | --- |
| [Defs](Defs.lean) | `GraphLike`, vertex and geometric edge sets, graph-relative interiors/boundaries, incidence, finiteness, refinement, and faces |
| [Basic](Basic.lean) | Edge and carrier laws, relatively closed edge remainders, compactness, and containment of connected sets in edges |
| [Assembly](Assembly.lean) | Primitive-link decomposition, edge recognition, finite sufficient conditions, and label correspondence |
| [Polygonal](Polygonal.lean) | Polygonality of edges |
| [StraightLine](StraightLine.lean) | Straightness, geometric incidence, finiteness, and refinement preservation |
| [SegmentFigure](SegmentFigure.lean) | Finite straight-line presentations of segment figures, prescribed vertices, and common presentations |
| [Restriction](Restriction.lean) | Maximal-contained whole-edge restriction, intersection laws, finiteness, and relative closure of differences |
| [Map](Map.lean) | Transport by a carrier-local embedding, edge image laws, identity and composition |
| [MapRestriction](MapRestriction.lean) | Transport commutes with restriction |
| [RestrictionGeometry](RestrictionGeometry.lean) | Geometry of restrictions and actual restrictions of common presentations |
| [MapGeometry](MapGeometry.lean) | Affine preservation of straightness and polygonality |
| [Subset](Subset.lean) | Relatively closed connected subsets and differences with a finite left restriction |

`GraphLike.IsLinkDecomposition S Z D` certifies a primitive-link cover of a supplied carrier
`S` with vertices `Z` and pieces `D`. It requires total separation of the vertices and
relative openness of the punctured pieces. Closedness of the vertices and disjointness
of distinct interiors follow. Only `S` must be Hausdorff; infinite families, loops,
parallel edges and isolated vertices are allowed.

`h.toGraphLike` stores `S` and `Z` directly, and `h.toGraphLike_edgeSet` proves its edge set
is `D`. `GraphLike.edgeSet_eq` recognizes the same pieces in a graph that already exists.
`IsLinkDecomposition.ofFinite` discharges the topology from finite vertices, finite pieces,
and disjoint interiors. `ofFiniteIndexed` applies this to a finite family's range.
An injective family `L` gives a separate label correspondence through `G.edgeEquivOfRange`;
its value at an index has underlying set `L i`. No parametrizations or labels are stored
in the graph-like space.

`GraphLike.IsStraightLine` says that an edge equals the segment between its boundary
vertices. It retains no orientation or parametrization. Its edges have distinct endpoints,
and an endpoint pair determines at most one edge. The predicate does not require finiteness.

For a finite straight-line space, the carrier is a segment figure. Conversely, every segment
figure with a Hausdorff carrier in a real topological vector space has a finite straight-line presentation,
including any prescribed finite subset among its vertices. The common-presentation theorem
preserves each input figure as vertices and whole edges. Its vertex term retains isolated points.

`GraphLike.ofSegments` takes a supplied segment witness and prescribed marks. Its vertices
and edges are the partition vertices and pieces, and every input subfamily is preserved as
vertices and whole edges. The construction is owned by [SegmentFigure](SegmentFigure.lean), using the algebraic
[segment-cutting lemmas](../../MiniTauCeti/JCT/Analysis/Convex/SegmentCutting.lean).
[Subset](Subset.lean) owns the connected-subset argument using edge remainders. The
[segment-figure wrapper](../../MiniTauCeti/JCT/Geometry/SegmentFigure/Subset.lean) supplies a finite
straight-line presentation. [Closure of differences](../../MiniTauCeti/JCT/Geometry/SegmentFigure/Clipping.lean)
uses common restrictions and the general closure-of-differences law. Neither consumer reconstructs
a second segment-family representation.

`G.restrict A` is the greatest whole-edge restriction contained in `A`: its vertices are
`A ∩ V(G)` and its edges are `{e ∈ E(G) | e ⊆ A}`. No finiteness assumption is needed.
Graph-like spaces coerce to their carriers as sets, so carrier laws use `(G.restrict A : Set X)`.
Transport requires an embedding only on the carrier and commutes with restriction to
`f '' (A ∩ G)`. Retaining whole edges and taking their images preserves loops and parallel edges.

The association with an abstract graph stays in
[`Graph/Topology/Drawing/Defs.lean`](../Graph/Topology/Drawing/Defs.lean).
The [straight-line drawing bridge](../Graph/Topology/StraightLine.lean) uses
`D.toGraphLike.IsStraightLine` directly for `Graph.Drawing G X`.
`Drawing.restrict` and `Drawing.postcomp` reuse the graph-like constructions.

Approximation, polygonal faces, and duality use the segment-figure polygonality interface.
The regression consumers are retained in [tests/MatroidTests](../../../tests/MatroidTests).
