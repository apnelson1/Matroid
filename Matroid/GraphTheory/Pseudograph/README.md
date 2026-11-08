# Pseudographs

[Basic.lean](Basic.lean) defines `Pseudograph` on ambient vertex, incidence, and edge types.
Only incidences in `I(P)` belong to the graph. Each edge has two paired incidences, including loops.

| API | Location |
| --- | --- |
| Forget incidence labels | [toGraph.lean](toGraph.lean) |
| Incidence fibres and orientations | [Shared incidence and orientation API](../HypergraphLike/Orientation.lean) |
| Coarse graph-link characterization | [Incidence.lean](Incidence.lean) |
| Shared morphisms and embeddings fixing vertex and edge labels | [Hom.lean](Hom.lean) |
| Incidence relabelling and the coarse-graph quotient | [Quotient.lean](Quotient.lean) |
| Chosen presentations of graphs and lifts of graph embeddings | [OfGraph.lean](OfGraph.lean) |
| Orientation endpoints in the coarse graph | [Incidence.lean](Incidence.lean) |
| Shared half-edge realization and path API | [Shared realization core](../HypergraphLike/Topology/Realization/Basic.lean) |
| Shared separation results | [Separation](../HypergraphLike/Topology/Realization/Separation.lean) |
| Open-edge homeomorphisms and topological path components | [Open edges](../HypergraphLike/Topology/Realization/EdgeInterior.lean) |
| Induced continuous maps, closed embeddings, and homeomorphisms | [Shared realization morphisms](../HypergraphLike/Topology/Realization/Hom.lean) |
| Compactness under `HypergraphLike.Finite` | [Shared finite realizations](../HypergraphLike/Topology/Realization/Finite.lean) |
| Graph connectedness bridges, CW structure, metric, and drawing maps | [Topology/Realization](Topology/Realization) |

The realization has one half-interval for each member of `I(P)` and retains isolated vertices.
Unused ambient incidence labels contribute no points. Incidence relabelling compares `I(P)`
and `I(Q)`; it places no requirement on their unused ambient labels.

The morphisms are `HypergraphLike.Hom`, `HypergraphLike.Emb`, and `HypergraphLike.Iso`.
Incidence relabellings use `Pseudograph.Equiv.toIso` and the shared realization maps directly.
Finiteness assumptions use `HypergraphLike.Finite P`, which means that `V(P)`, `I(P)`, and `E(P)`
are finite; the ambient label types may be infinite.
Pairing preservation is proved in the
[shared graph morphism API](../HypergraphLike/Graph/Hom.lean).
A plain `HypergraphLike.IncHom` can collapse the two incidences of an edge and does not supply
this guarantee. `Pseudograph.Embedding` fixes vertex and edge labels while allowing incidence
relabelling; `HypergraphLike.IsSubgraph` also preserves the incidence labels.

The quotient topology and unit-edge metric topology remain separate.
The identity from the quotient topology to the metric topology is continuous.
Graph drawing bridges live in [Graph/Topology/Realization](../Graph/Topology/Realization).
