# Jordan curve theorem and supporting mathematics

This is our existing development, relocated from `Matroid/ForMathlib` and supplemented by the
work committed in the `planar-duality` checkout. It has not been replaced by Tau Ceti's proof.

| Subject | Entry point |
| --- | --- |
| Full Jordan separation for compact intrinsic circuits in real normed planes | [Geometry/Jordan.lean](Geometry/Jordan.lean) |
| Polygonal separation, independent of full JCT | [Geometry/PolygonalJordan.lean](Geometry/PolygonalJordan.lean) |
| Geometric K₃,₃ obstruction | [Geometry/K33.lean](Geometry/K33.lean) |
| Intrinsic circuits and their ordinary-circle classification | [Topology/Circuit/Basic.lean](Topology/Circuit/Basic.lean), [Topology/Circuit/CompactParametrization.lean](Topology/Circuit/CompactParametrization.lean) |
| Primitive links and their crossings | [Topology/PrimitiveLink.lean](Topology/PrimitiveLink.lean), [Topology/PrimitiveLink/Crossing.lean](Topology/PrimitiveLink/Crossing.lean) |
| Polygonal constructions and approximation | [Geometry/PolygonalPath](Geometry/PolygonalPath) |
| Segment figures | [Geometry/SegmentFigure/README.md](Geometry/SegmentFigure/README.md) |

Import individual modules as `Matroid.MiniTauCeti.JCT.Geometry.Jordan`, for example.
`Matroid.lean` imports all the supporting modules directly; there is no separate
`Matroid.MiniTauCeti.JCT` aggregate module. Declaration namespaces such as `IsCircuit`,
`Path`, and `PolygonalPath` are unchanged.

The full proof uses polygonal separation and approximation to establish the K₃,₃ obstruction.
A connected circuit complement or three complementary components would produce that forbidden
configuration. This route is distinct from Tau Ceti's JCT and Schoenflies development.

Graph-specific consumers remain in
[`Matroid/GraphTheory/Graph/Topology`](../../GraphTheory/Graph/Topology/README.md).
Unfinished mathematics remains in [`Unfinished`](../../../Unfinished/README.md).
The Janiszewski and later duality foundations in separate T3 checkouts have not yet been imported.

[Verification commands and their limits](Verification.md) describe the build commands, registered regressions,
and limits of the remaining checks.
