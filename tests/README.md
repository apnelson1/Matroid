# tests/

Regression tests, kept out of the source tree.

A `grind`/`simp` tag that never fires produces no error, no warning and no failing proof — it just
costs a match attempt forever. The only way to learn that a tag works is an `example` that closes
only if it does. Those examples used to sit at the bottom of the mathematical file they tested,
where they are noise: a reader of `RadialPoint.lean` did not ask for a test suite, and a test that
has to justify its presence in a mathematical file gets deleted the next time someone tidies.
That is what happened to `Path.lean`'s block.

## Layout

`MatroidTests` is a `lean_lib` with `srcDir = "tests"`. It is **not** in `defaultTargets`; it is
the package's `testDriver`, so it builds under `lake test` and not under `lake build`.

```
tests/MatroidTests.lean            -- root, imports the regression suite
tests/MatroidTests/ConstructionPolygonal.lean -- polygonal construction consumers
tests/MatroidTests/ConstructionSubdivision.lean -- segment partition consumers
tests/MatroidTests/ConstructionTopology.lean -- path and circle construction consumers
tests/MatroidTests/GrindTags.lean  -- one section per source module under test
tests/MatroidTests/Hom.lean        -- graph homomorphism consumers
tests/MatroidTests/IRw.lean        -- all transport and registration regressions
tests/MatroidTests/Immersion.lean  -- immersion routes and composition
tests/MatroidTests/JordanCurve.lean -- circuit region consumers and proof-integrity check
tests/MatroidTests/JordanPrerequisites.lean -- independent foundations and their proof integrity
tests/MatroidTests/PrimitivePath.lean -- primitive-path chart consumers
tests/MatroidTests/OrderInterval.lean -- interval parametrization and path splitting
tests/MatroidTests/OrderCompletion.lean -- dense-order extension and completion
tests/MatroidTests/JCTGenerality.lean -- generalized JCT prerequisite consumers
tests/MatroidTests/OnePointTransport.lean -- explicit one-point set transport
tests/MatroidTests/PolygonalPath.lean -- polygonal path regressions
```

Add a module here, `public import` it from `tests/MatroidTests.lean`, and `lake test` covers it.

`MatroidTests/TopologicalMinor.lean` retains older standalone regression tests; it is not
currently imported by the test root or covered by `lake test`.

`MatroidTests/GraphLikeReplacement.lean` and `GraphLikeDrawingOperations.lean` retain historical
imports from the earlier graph-topology layout. They are outside the registered test root and
need migration before their checks can run against the current drawing API.

`ConnectedComponentSets` is included in `lake test` and checks connected component sets on
connected and disconnected spaces and a nonclosed subspace.

`GraphLikeSubset` is included in `lake test` and covers geometric subset operations.
`StraightLineDrawing` remains a separate drawing consumer outside the registered test root.

The split exists so that a silent `lake build` means the mathematical library is clean while
caller-facing tactic and tag behavior remains covered by `lake test`.

Run `lake test` explicitly after changing production modules or their consumers: the regression
library is not a default build target. The [CI workflow](../.github/workflows/build.yml)
runs `lake build` followed by `lake test` on pushes and pull requests.

The JCT sources live under `Matroid/MiniTauCeti/JCT`, corresponding to the module prefix
`Matroid.MiniTauCeti.JCT`. Build commands, regression coverage, and verification limits are
described in [the verification guide](../Matroid/MiniTauCeti/JCT/Verification.md).

## Writing a test

Write the test for the shape a **caller** will actually have, not the lemma restated. Restating the
lemma tests almost nothing. The informative test is the one a step below it — and when *that* fails
it usually means the API is missing the consumer-facing form, not that the tag is wrong. Both
pointwise companions in `RadialPoint.lean` were found this way.

Record the negative results too. A lemma that `grind` cannot use even when passed as an explicit
hint is worth an entry, because otherwise the next person re-runs the experiment. `Path.lean`'s
producer case is the model.

The former IRw frontier probes are retained in `IRw.lean` now that all five original behaviors
are implemented.
