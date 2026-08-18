module

public import Matroid.ForMathlib.Geometry.PolygonalPath.Basic

/-!
# Regression tests: `PolygonalPath` tags

Each `example` fails if the tag named above it is removed. See `tests/README.md` for why these
live here and not at the bottom of `ForMathlib/Geometry/PolygonalPath/Basic.lean` — the earlier
convention did not survive: a `section RegressionTests` at the end of a mathematical file reads as
scratch work and gets tidied away by the next pass.
-/

open Set unitInterval

namespace PolygonalPath

variable {α : Type*} {a b c x y z : α}

section Combinatorics

variable (P : PolygonalPath x y)

-- `cons_internal`, `internal_concat`, `cons_internal_concat`, `drop_zero`, `drop_length`. All five
-- carry a `0 < P.length` side condition, so plain `simp` cannot fire them: it never looks at the
-- context. Measured — each of the five reports `simp made no progress` on its own statement with
-- the hypothesis present, and `cons_internal_concat` does not close even under `simp [*]`, because
-- `internal_concat` rewrites its left-hand side first. `grind` reads the context, so these are the
-- tags that make the three vertex-list identities usable.
example (h : 0 < P.length) : x :: P.internal = P.vertices.dropLast := by grind

example (h : 0 < P.length) : P.internal ++ [y] = P.vertices.tail := by grind

example (h : 0 < P.length) : x :: (P.internal ++ [y]) = P.vertices := by grind

-- These two are the caller's shape rather than the lemma restated: a length computed through
-- `drop`. The three above have no such form — the step below them is `List` membership, which
-- `grind` cannot reach because the relevant `List` lemmas are not tagged.
example (h : 0 < P.length) : (P.drop x 0).length = P.length := by grind

example (i : ℕ) (u : α) (hi : i < P.length) (hlt : 0 < i) : (P.drop u i).length < P.length := by
  grind

end Combinatorics

section Edges

variable {P : PolygonalPath x y}

-- `mem_reverse_edges`, the pointwise form of `reverse_edges`. The caller holds an edge, not the
-- list equation — four proofs in the file each re-derived this before it was named.
example {a b : α} (h : (a, b) ∈ P.edges) : (b, a) ∈ P.reverse.edges := by grind

-- `mem_edges_firstTip` / `mem_edges_lastTip`. The caller's shape is "this path has *some* edge at
-- this end", which is what the two superseded `exists_edge_*` lemmas used to state; with the tips
-- named, `grind` reaches it from the length hypothesis alone.
example (h : 0 < P.length) : ∃ u, (u, y) ∈ P.edges := by grind

example (h : 0 < P.length) : ∃ u, (x, u) ∈ P.edges := by grind

-- `edges_cast`: a cast path has the same edges. The caller holds a membership in the uncast path.
example {x' y' : α} (hx : x = x') (hy : y = y') {s : α × α} (hs : s ∈ P.edges) :
    s ∈ (P.cast hx hy).edges := by grind

-- `append_cast_right`: casting the right factor of an append agrees with casting the append.
example {p : α} (A : PolygonalPath x p) (B : PolygonalPath p y) (heq : y = x) :
    ((A.append B).cast rfl heq).edges = (A.append (B.cast rfl heq)).edges := by grind

end Edges

section SimpleEdge

variable [AddCommGroup α] [Module ℝ α]

-- `mem_toSet_cons_iff`, both directions. The forward one is the recursion step over `toSet`, which
-- existed as six inline copies — five here and one in `SimpleLoop.lean` — before it was named.
example {u v : α} {P : PolygonalPath v c} {a : α} (ha : a ∈ (cons u v P).toSet) (hau : a ≠ u)
    (hauv : a ∉ openSegment ℝ u v) : a ∈ P.toSet := by grind

example {u v : α} {P : PolygonalPath v c} {a : α} (ha : a ∈ P.toSet) :
    a ∈ (cons u v P).toSet := by grind

-- `eq_first_edge_of_mem_segment` / `eq_last_edge_of_mem_segment`: an endpoint of a simple path
-- lies on no segment but its own. The caller has two edges through the same endpoint and wants
-- them identified.
example {p : α} {B : PolygonalPath p y} (hB : B.IsSimple) {b : α} (hb : (p, b) ∈ B.edges)
    {s t : α × α} (hs : s ∈ B.edges) (ht : t ∈ B.edges) (hps : p ∈ segment ℝ s.1 s.2)
    (hpt : p ∈ segment ℝ t.1 t.2) : s = t := by grind

example {p : α} {A : PolygonalPath x p} (hA : A.IsSimple) {u : α} (ha : (u, p) ∈ A.edges)
    {s t : α × α} (hs : s ∈ A.edges) (ht : t ∈ A.edges) (hps : p ∈ segment ℝ s.1 s.2)
    (hpt : p ∈ segment ℝ t.1 t.2) : s = t := by grind

end SimpleEdge

-- There is no `section Path`. `IsSimple.toSet_breakAt_eq` is deliberately untagged: at
-- `grind.unusedLemmaThreshold 10` it activated 20 times and contributed nothing at
-- `Radial.lean:254`, which is the acceptance criterion in `Assimilation.md` §3 firing for the
-- first time. Its one consumer names it explicitly.

end PolygonalPath
