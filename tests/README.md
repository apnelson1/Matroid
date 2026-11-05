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
tests/MatroidTests/GrindTags.lean  -- one section per source module under test
tests/MatroidTests/Hom.lean        -- graph homomorphism consumers
tests/MatroidTests/IRw.lean        -- all transport and registration regressions
tests/MatroidTests/Immersion.lean  -- immersion routes and composition
tests/MatroidTests/JordanCurve.lean -- Jordan curve tag regressions
tests/MatroidTests/PolygonalPath.lean -- polygonal path regressions
```

Add a module here, `public import` it from `tests/MatroidTests.lean`, and `lake test` covers it.

`MatroidTests/TopologicalMinor.lean` retains older standalone regression tests; it is not
currently imported by the test root or covered by `lake test`.

`MatroidTests/GraphLikeReplacement.lean` checks the graphlike polygonalization interface and its
axioms. Its dependency `Graph.Topology.Draft` uses Lean's legacy module format and cannot be
imported by the module-format test root. Run `lake build MatroidTests.GraphLikeReplacement`
separately when changing that interface.

`MatroidTests/StraightLine.lean` checks the extracted `GraphLike` foundation, finite straight-line
presentations, geometric incidence, refinement, isolated vertices, crossings, and overlaps.
It is included in `lake test`. Its graph-facing companion uses the legacy drawing modules:
run `lake build MatroidTests.StraightLineDrawing` to check the drawing bridge and its axioms.

`GraphLikeEdges` checks the raw point-set edge API, `V(G)`/`E(G)` notation alongside `Graph`,
and incidence and topology lemmas without subtype edge wrappers. It runs under `lake test`.
It also imports `ConnectedComponentSets`, which tests the shared point-set operation on
connected and disconnected spaces and a nonclosed subspace, independently of graph data.

`GraphLikeAssembly` tests the explicit assembly constructors on a circle loop, parallel arcs,
isolated vertices, and countably many disjoint circles. It is included in `lake test` and
guards the constructors' axiom dependencies.

`GraphLikeRestriction`, `GraphLikeMap`, `GraphLikeOperations`, and `GraphLikeSubset` are
included in `lake test`. They cover whole-edge selection, finite-support differences,
carrier-local embedding transport, restriction/transport compatibility, and geometry.
Run `lake build MatroidTests.GraphLikeDrawingOperations MatroidTests.StraightLineDrawing`
for the legacy-format drawing adapters and their guarded axiom checks.

Editor-completion experiments and the obsolete `PresentationRevised` checks are preserved in
the Git-ignored [resources/TestArchive](../resources/TestArchive/). They are not part of the
regression suite.

The split exists so that a silent `lake build` means the mathematical library is clean while
caller-facing tactic and tag behavior remains covered by `lake test`.

**A test library outside the default build is a test library that stops running without anyone
noticing.** That risk is real and it is not handled by convention here: it is handled by
`.github/workflows/build.yml`, which runs `lake test` as a separate step after `lake build`. If you
move or rename this library, move that step with it, or the suite goes quiet.

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
