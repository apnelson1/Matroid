# tests/

Regression tests, kept out of the source tree.

A `grind`/`simp` tag that never fires produces no error, no warning and no failing proof — it just
costs a match attempt forever. The only way to learn that a tag works is an `example` that closes
only if it does. Those examples used to sit at the bottom of the mathematical file they tested,
where they are noise: a reader of `RadialPoint.lean` did not ask for a test suite, and a test that
has to justify its presence in a mathematical file gets deleted the next time someone tidies.
That is what happened to `Path.lean`'s block.

Instance resolution has the same shape. A `#synth` that succeeds by the wrong route, or a
combinator instance that silently stops being reachable, breaks no proof today — it just quietly
changes what the class means. `Iso.lean` pins the chosen instance term so that a change has to be
acknowledged.

## Layout

`MatroidTests` is a `lean_lib` with `srcDir = "tests"`. It is **not** in `defaultTargets`; it is
the package's `testDriver`, so it builds under `lake test` and not under `lake build`.

```
tests/MatroidTests.lean            -- root, imports every test module
tests/MatroidTests/GrindTags.lean  -- one section per source module under test
tests/MatroidTests/Iso.lean        -- instance-resolution pins for Matroid/Graph/Iso
```

Add a module here, `public import` it from `tests/MatroidTests.lean`, and `lake test` covers it.

The split exists so that a silent `lake build` means the mathematical library is clean. Tests here
report on success as well as failure — `Iso.lean`'s `#synth` checks print the instance they
resolved, by design — and forty lines of `info:` on every build is noise that trains you to stop
reading build output, which is worse than the noise itself.

**A test library outside the default build is a test library that stops running without anyone
noticing.** That risk is real and it is not handled by convention here: it is handled by
`.github/workflows/build.yml`, which runs `lake test` as a separate step after `lake build`. If you
move or rename this library, move that step with it, or the suite goes quiet.

## Writing a test

Write the test for the shape a **caller** will actually have, not the lemma restated. Restating the
lemma tests almost nothing. The informative test is the one a step below it — and when *that* fails
it usually means the API is missing the consumer-facing form, not that the tag is wrong. Both
pointwise companions in `RadialPoint.lean` were found this way.

For a resolution pin the equivalent is `#guard_msgs (whitespace := lax) in #synth C F`, which
fails both when synthesis fails and when it succeeds by a different route. Pin the term only where
it is stable: `set_option pp.explicit true` makes the structural pins readable, but on a goal
carrying a numeral it drags in forty lines of `OfNat` plumbing, and terms printing a `fun` binder
name or an unfolded body will churn on the next Mathlib bump. An unpinned `#synth` is still a real
test — it fails on synthesis failure — it just does not pin the route.

Record the negative results too. A lemma that `grind` cannot use even when passed as an explicit
hint is worth an entry, because otherwise the next person re-runs the experiment. `Path.lean`'s
producer case is the model.

## What is not here

`Matroid/ForMathlib/Tactic/*` carry their own `example`s. Those are tactic tests — they exercise
the tactic being defined in the same file, and they belong with it. This directory is for tests
whose subject is elaboration-level behaviour that belongs to no single source file: whether a
`grind` tag fires, and which instance the elaborator picks. Both are invisible to a normal
proof — they have no failing goal to point at — so they need a home where someone is looking.
