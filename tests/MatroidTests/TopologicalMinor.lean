module

public import Matroid.Graph.TopologicalMinor

/-!
# Regression tests: `Graph.TopologicalMinor` tags

Each `example` fails if the tag named above it is removed; both blocks were ablation checked as
groups. See `tests/README.md` for why these live here.

Two candidates were probed and rejected, recorded here so they are not re-proposed:

* `SubgraphReplacement.edge_mem_walk` (`M.edge i ∈ E(M.walk i)`) loses the normal-form race —
  `simp` rewrites `E(M.walk i)` to `(M.walk i).edge` before the rule can match, leaving
  `M.edge i ∈ (M.walk i).edge`. It would need restating in the `.edge` vocabulary to be tagged.
* `TopologicalMinor.vertexSet_mono` / `edgeSet_mono` cannot take `@[grind →]`: `TopologicalMinor`
  is a structure in `Type`, so the witness is data and there is no propositional antecedent to key
  on. Keying the conclusion instead would mean a bare `V(G) ⊆ V(H)`, which fires on every `⊆` goal.
* `TopologicalModel.vertexSet_normalized` / `edgeSet_normalized` were tagged `@[simp]` and
  **reverted**: they broke the two `simpa … using he` steps in
  `IsoSubdivision.exists_iso_subdivision`. Both are `rfl`, and both call sites already pass them
  to `simp` explicitly.
-/

open Set WList

namespace Graph

variable {α β γ δ ι : Type*} {G H : Graph α β} {v : α}

section Simp

-- `SubgraphReplacement.walk_first`, `walk_last`, `walk_nonempty`. The chosen route of a
-- replacement component runs between the component's two distinguished vertices and is nonempty.
variable (M : G.SubgraphReplacement ι) (i : ι)

example : (M.walk i).first = M.left i := by simp
example : (M.walk i).last = M.right i := by simp
example : (M.walk i).Nonempty := by simp

-- the shape a caller holds, rather than the lemma restated
example (w : α) (hw : M.left i = w) : (M.walk i).first = w := by simp_all

end Simp

section Grind

-- `TopologicalMinor.branchVerts_eq_prefix`, `_suffix`, `_union`. All three carry side conditions
-- relating `(h.map e).first` and `(h.map e).last` that live in the caller's hypotheses, so plain
-- `simp` can never discharge them. They also share a left-hand side, `h.branchVerts e v`; these
-- three examples together check that they do not shadow one another.
variable [DecidableEq α] [DecidableEq β] (h : G.TopologicalMinor H) (e : E(G))

example (hne : (h.map e).first ≠ (h.map e).last) :
    h.branchVerts e (h.map e).first = V((h.map e).prefixUntilEdgeLabel e.val) := by grind

example (hne : (h.map e).first ≠ (h.map e).last) :
    h.branchVerts e (h.map e).last = V((h.map e).suffixFromEdgeLabel e.val) := by grind

example (hloop : (h.map e).first = (h.map e).last) :
    h.branchVerts e (h.map e).first = V((h.map e).prefixUntilEdgeLabel e.val) ∪
      V((h.map e).suffixFromEdgeLabel e.val) := by grind

end Grind

end Graph
