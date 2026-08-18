# tests/

Regression tests, kept out of the source tree.

A `grind`/`simp` tag that never fires produces no error, no warning and no failing proof — it just
costs a match attempt forever. The only way to learn that a tag works is an `example` that closes
only if it does. Those examples used to sit at the bottom of the mathematical file they tested,
where they are noise: a reader of `RadialPoint.lean` did not ask for a test suite, and a test that
has to justify its presence in a mathematical file gets deleted the next time someone tidies.
That is what happened to `Path.lean`'s block.

## Layout

`MatroidTests` is a `lean_lib` with `srcDir = "tests"`, and it is in `defaultTargets`. **That is
the point of the setup, not a detail**: a test library outside the default build is a test library
that stops running without anyone noticing, which is the same failure it exists to prevent.

```
tests/MatroidTests.lean            -- root, imports every test module
tests/MatroidTests/GrindTags.lean  -- one section per source module under test
```

Add a module here, `public import` it from `tests/MatroidTests.lean`, and `lake build` covers it.

## Writing a tag test

Write the test for the shape a **caller** will actually have, not the lemma restated. Restating the
lemma tests almost nothing. The informative test is the one a step below it — and when *that* fails
it usually means the API is missing the consumer-facing form, not that the tag is wrong. Both
pointwise companions in `RadialPoint.lean` were found this way.

Record the negative results too. A lemma that `grind` cannot use even when passed as an explicit
hint is worth an entry, because otherwise the next person re-runs the experiment. `Path.lean`'s
producer case is the model.

## What is not here

`Matroid/ForMathlib/Tactic/*` carry their own `example`s. Those are tactic tests — they exercise
the tactic being defined in the same file, and they belong with it. This directory is for tests of
*tags*, whose subject is the interaction between a lemma and the automation, and which therefore
belong to neither file individually.
