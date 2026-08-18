import Matroid.Graph.Planarity.ThetaCurve
import Matroid.Graph.Connected.Ear

/-!
# Faces of a 2-connected polygonal drawing are bounded by cycles

`Status.md` §4.2. In a polygonal drawing of a finite loopless `2`-connected graph, every face has
a cycle of the graph as its frontier, and is a whole component of the complement of that cycle.

This is the theorem §5 and §6 run on: `Face.lean`'s three parked statements
(`exists_facial_cycle_of_delete_vertex`, `exists_facial_cycle_of_contract`,
`planar_of_contract_of_facial_cycle_two_paths`) are corollaries of it.

## The hypotheses are weaker than `Status.md` §4.2 states

`Status.md` asks for `G` finite, **simple**, `2 ≤ κ(G)`. The argument uses only **loopless**, which
is what `ConnGE.exists_isEar` and `ConnGE.ear_induction` were already corrected to after the same
discovery at §4.1. Nothing downstream pays: `Face.lean`'s consumers carry `[H.Simple]` anyway.

What looseness costs, and why it is the right trade: under `Loopless` the cycle `C` produced can be
a **digon** — two vertices joined by two parallel edges. That really is a `Graph.IsCycle` here
(`isCycle_iff_exists_isCyclicWalk_eq`, `Forest.lean:207`, and `IsCyclicWalk` admits a closed walk of
length `2`), and it really can bound a face, so the conclusion must admit it and does not claim
`3 ≤ V(C).encard`. A drawn digon is still a simple closed *curve*: its two cells are disjoint but
for their ends, so at least one of them bends and the traced polygon has at least three vertices.
Only the *base* cycle needs `3 ≤ V(C₀).encard`, and `ConnGE.exists_isCycle_le` supplies it.

## Proof of the main theorem, in the steps the statement is built to support

Write `D|H` for `D.restrict`, `|H|` for `(D|H).support` and `𝕊` for `OnePoint ℝ²`.

1. **Base cycle.** `ConnGE.exists_isCycle_le` (`Forest.lean`) gives `C₀ ≤ G` with `C₀.IsCycle` and
   `3 ≤ V(C₀).encard`.
2. **Induction.** `ConnGE.ear_induction` over `C₀ ≤ H ≤ G`, with motive
   `fun H ↦ ∀ hle : H ≤ G, ∀ F : (D|hle).onePoint.Face, <conclusion for F>`.
3. **Base case `H = C₀`.** `exists_isSimpleLoop_toSet_eq_support_of_isCyclicWalk` below traces
   `|C₀|` as a simple polygonal loop; `IsSimpleLoop.isJordanCurve` and
   `IsSimpleLoop.exists_sides_onePoint` (`Geometry/Polygon/JordanCurve.lean:39,51`) split `𝕊 ∖ |C₀|`
   into two open connected sets, each with frontier `|C₀|`. Both are faces by
   `Drawing.exists_faceSet_eq` (`Face.lean:162`), and they exhaust the complement, so the given `F`
   is one of them and its cycle is `C₀`.
4. **Step.** Attach an ear `P` to `H`, giving `H' := H ∪ P.toGraph` and `H' ≤ G` by
   `IsEar.union_le` (`Ear.lean:105`). The relative interior of `|P|` is connected and misses `|H|`,
   so it lies in a single face `F'` of `D|H`, and the two ends of `P` lie in `frontier F'`.
5. **Cut that face.** The induction hypothesis gives `frontier F' = |C|` for a cycle `C ≤ H`.
   The ends of `P` are vertex images on `|C|`, hence images of *vertices* of `C`
   (`Drawing.pathInterior_edgePath_disjoint_vertex` `Drawing.lean:157` says no open cell contains a
   vertex image, and `Drawing.vertex_injective` `Drawing.lean:129` identifies which vertex). They
   are distinct, so they split `C` into two paths `C₁, C₂`. Now
   `exists_two_regions_crosscut` (`ThetaCurve.lean:132`) with `J := |C|`, `F := F'`, `A := |P|`
   cuts `F'` into exactly two regions, with frontiers `|C₁ + P|` and `|C₂ + P|`. Its hypothesis
   that `A` meets `J` in exactly its two ends is
   `Drawing.support_restrict_inter_support_restrict_of_isEar` below — the one hypothesis of 3.10
   that has to come from the drawing axioms rather than from a caller.
6. **Every other face is untouched.** A face `F'' ≠ F'` of `D|H` misses `|H'|`, so it is still a
   face of `D|H'`; conversely `|H| ⊆ |H'|` puts every face of `D|H'` inside a face of `D|H`. So the
   faces of `D|H'` are the `F'' ≠ F'` together with the two pieces of `F' ∖ |P|`, and each has the
   required cycle — `C₁ + P` and `C₂ + P` are cycles by `IsCyclicWalk.toGraph_isCycle`
   (`Forest.lean:192`).
7. **Termination** is inside `ear_induction`, not here.

## Main statements

* `Graph.Drawing.support_restrict_inter_support_restrict_of_isEar` : an ear meets the rest of the
  drawing exactly at its two ends. Needs no polygonality.
* `Graph.PLDrawing.exists_polygonalPath_toSet_eq_support_of_isPath` : a polygonal drawing of a path
  traces a simple polygonal arc.
* `Graph.PLDrawing.exists_isSimpleLoop_toSet_eq_support_of_isCyclicWalk` : and of a cyclic walk, a
  simple polygonal loop.
* `Graph.PLDrawing.exists_polygon_isSimple_of_isCycle` : the `Polygon` form of the latter, which is
  what `exists_two_regions_crosscut` consumes.
* `Graph.PLDrawing.exists_isCycle_frontier_faceSet_eq` : **Theorem 4.2**.
* `Graph.PLDrawing.exists_isCycle_isFacialSubgraph` : 4.2 in the packaged form `Face.lean` uses.

## File placement

The three tracing lemmas are `PLDrawing`-level and the ear lemma is `Drawing`-level: none mentions
a face, JCT or the plane. They sit here because this file is their only consumer. By
`Decisions.md` D7 they move to `PLDrawing.lean` and `Drawing.lean` as soon as a second consumer
appears that does not want `ThetaCurve.lean`'s imports — §5 and §6 will both want them, and both
will already be importing this file.
-/

open Function Set Topology

namespace Graph

noncomputable section

universe u

variable {α β : Type*} {G H C : Graph α β} {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "𝕊" => OnePoint (EuclideanSpace ℝ (Fin 2))

namespace Drawing

section Ear

variable {X : Type*} [TopologicalSpace X]

/- **Route.** `⊇` is immediate: `hP.first_mem` and `hP.last_mem` put both ends in `V(H)`, and
`Drawing.vertex_mem_support` (`Drawing.lean:120`) puts their images in both supports.

`⊆` is where the drawing axioms are spent. Expand both sides with `Drawing.support_eq`
(`Drawing.lean:137`) — a support is the union of the closed cells and the vertex images — and take
a point `z` in both. Four cases, each closed by one lemma:

* `z` a vertex image on each side. `Drawing.vertex_injective` (`Drawing.lean:129`) makes it one
  vertex of `V(P.toGraph) ∩ V(H)`, which `hP.internal_disjoint` cuts down to `{P.first, P.last}`
  (`WList.mem_vertexSet_iff` splits a walk's vertices into its ends and `internalVertexSet`).
* `z` interior to a cell of `P` and a vertex image of `H`, or the mirror case:
  `Drawing.pathInterior_edgePath_disjoint_vertex` (`Drawing.lean:157`) — no open cell contains any
  vertex image — rules both out outright.
* `z` interior to a cell of each. `hP.edge_disjoint` makes the two edges distinct, so
  `Drawing.range_edgePath_inter` (`Drawing.lean:171`) confines `z` to the images of shared ends,
  which are vertex images, contradicting the previous case.

`Drawing.range_edgePath_restrict` (`Drawing.lean:416`) is what identifies a restricted cell with
the corresponding cell of `D` in each case, and `Drawing.restrict_vertex` (`Drawing.lean:397`) does
the same for vertex images. Nothing here is polygonal, finite, or planar. -/
/-- **An ear meets the rest of the drawing exactly at its two ends.**

This is the hypothesis `exists_two_regions_crosscut` (`Status.md` 3.10) calls `hAJ`, and the only
one of its hypotheses that the drawing axioms have to produce rather than a caller. It is stated
against `H` rather than against the facial cycle `C ≤ H` because that is the stronger statement and
the one whose proof is the drawing axioms; the `C` version follows by intersecting, since both ends
lie on `|C|`.

Costs nothing beyond `Drawing`: no polygonality, no finiteness, no plane. -/
theorem support_restrict_inter_support_restrict_of_isEar (D : Drawing G X) {P : WList α β}
    (hP : G.IsEar H P) (hle : H ≤ G) :
    (D.restrict hP.isPath.isWalk.toGraph_le).support ∩ (D.restrict hle).support =
      {D.vertex ⟨P.first, hP.isPath.isWalk.first_mem⟩,
        D.vertex ⟨P.last, hP.isPath.isWalk.last_mem⟩} := by
  sorry

end Ear

end Drawing

namespace PLDrawing

/-! ### Tracing a walk

A polygonal drawing assigns a polygonal path to each *edge*. Walking along a walk and concatenating
those paths gives a polygonal path whose image is the support of the drawing restricted to the
walk's graph. Both statements below are existence statements rather than definitions, for the same
reason `Drawing.IsPL` (`PLDrawing.lean:81`) is: the concatenation depends on an orientation choice
per edge — the walk traverses `e` from `edgeSource e` or from `edgeTarget e`, and `PolygonalPath`
is typed by its endpoints, so the two cases produce *different terms of different types*. That data
is not canonical (reversal and subdivision both change it), so it is quantified away here exactly
as `PLDrawing.lean` quantifies it away there. A `def` would have to fix the choice, and a `def`
with a `sorry` body is barred outright (`DesignPrinciples.md` §10).

No finiteness anywhere: a walk is finite by construction.
-/

/- **Route.** Induction on `W` with `WList.cons`. At `cons x e W'`, `PolygonalPath.append`
(`PolygonalPath/Basic.lean:342`) glues `D.cell ⟨e, _⟩` — reversed by `PolygonalPath.reverse`
(`:358`) when the walk traverses `e` against `edgeSource`/`edgeTarget` — onto the path for `W'`,
and `PolygonalPath.cast` retypes the shared endpoint.

*Simplicity* is `PolygonalPath.isSimple_append_iff` (`:701`); its two side conditions are exactly
what a graph path gives: `Drawing.range_edgePath_inter` (`Drawing.lean:171`) says two distinct
cells meet only in the images of shared ends, and `hW.nodup` says the walk revisits no vertex, so
consecutive cells meet only at the shared vertex image and non-consecutive ones not at all.

*The support equation* is `PolygonalPath.toSet_append` (`:556`) and `toSet_reverse` (`:564`)
against `Drawing.support_eq` (`Drawing.lean:137`), which expands a support as the union of the
cells and the vertex images; `PLDrawing.range_edgePath_restrictCell` (`PLDrawing.lean:107`)
identifies each restricted cell with the corresponding cell of `D`.

The obstruction that would otherwise send the prover back to first principles is the orientation
bookkeeping in the `cons` step. It is handled once, by `Drawing.restrict_vertex_edgeSource` /
`_edgeTarget` (`Drawing.lean:401,408`), which are what make `PLDrawing.restrictCell`
(`PLDrawing.lean:96`) typecheck without a reversal; the same two lemmas serve here. -/
/-- **A polygonal drawing of a path traces a simple polygonal arc**, from the image of the walk's
first vertex to the image of its last, whose image is exactly the support of the drawing restricted
to the walk. -/
theorem exists_polygonalPath_toSet_eq_support_of_isPath (D : PLDrawing G V) {W : WList α β}
    (hW : G.IsPath W) :
    ∃ A : PolygonalPath (D.toDrawing.vertex ⟨W.first, hW.isWalk.first_mem⟩)
        (D.toDrawing.vertex ⟨W.last, hW.isWalk.last_mem⟩),
      A.IsSimple ∧ A.toSet = (D.toDrawing.restrict hW.isWalk.toGraph_le).support := by
  sorry

/- **Route.** As above, but closing up: a cyclic walk is a closed trail with `W.tail.vertex.Nodup`,
so `PolygonalPath.isSimpleLoop_append_iff` (`SimpleLoop.lean:157`) applies to the split of `W` at
any interior vertex, its `hxy : x ≠ y` coming from `hW.nodup`. Loops of the graph are not a special
case to worry about *here* — a loop edge gives a one-edge cyclic walk whose cell is already an
embedded circle by `cell_isSimpleArcOrLoop` — but they are excluded by `[G.Loopless]` at every
consumer below. -/
/-- **A polygonal drawing of a cyclic walk traces a simple polygonal loop.** Digons and loop edges
are included: the cells of a drawing are disjoint but for their ends, so the traced loop is
embedded even when the walk has one or two edges. -/
theorem exists_isSimpleLoop_toSet_eq_support_of_isCyclicWalk (D : PLDrawing G V) {W : WList α β}
    (hW : G.IsCyclicWalk W) :
    ∃ A : PolygonalPath (D.toDrawing.vertex ⟨W.first, hW.isWalk.first_mem⟩)
        (D.toDrawing.vertex ⟨W.first, hW.isWalk.first_mem⟩),
      A.IsSimpleLoop ∧ A.toSet = (D.toDrawing.restrict hW.isWalk.toGraph_le).support := by
  sorry

/- **Route.** `isCycle_iff_exists_isCyclicWalk_eq` (`Forest.lean:207`) turns `hCcyc` into a cyclic
walk `W` with `W.toGraph = C`; `exists_isSimpleLoop_toSet_eq_support_of_isCyclicWalk` traces it;
`PolygonalPath.toPolygon` (`Polygon/PolygonalPath.lean:64`) is the polygon and
`boundary_toPolygon` (`:125`) the boundary equation — its `0 < P.length` side condition is
`IsSimpleLoop.length_pos` (`SimpleLoop.lean:82`). Simplicity transfers by
`Polygon.isSimple_iff_exists_isSimpleLoop` (`Polygon/PolygonalPath.lean:518`).

`Polygon.IsSimple` also carries `2 ≤ n` (`Polygon.IsSimple.two_le`, `Polygon/Basic.lean:349`), and
`n` here is `P.vertices.dropLast.length` — the number of *bends*, not of graph vertices. For a
digon `C` that is not automatic from `length_pos`; use `IsSimpleLoop.three_le_length`
(`SimpleLoop.lean:258`), which gives `3 ≤ P.length` for any simple loop and so covers the digon and
the loop edge at once. This is the step the module docstring argues informally ("at least one of
the two cells bends"); `three_le_length` is what discharges it, and it needs no case split.

The only real step is rewriting `(D.restrict hW.isWalk.toGraph_le).support` to
`(D.restrict hC).support` along `W.toGraph = C`; that is a `subst`, since `hC` and
`hW.isWalk.toGraph_le` are proofs of the same proposition once the graphs agree. -/
/-- The `Polygon` form of the previous lemma. This is the shape `exists_two_regions_crosscut`
(`Status.md` 3.10) and `Polygon.IsSimple.exists_arcs` consume, so callers cutting a face with a
crosscut want this one; callers reasoning about the curve itself want the `PolygonalPath` form. -/
theorem exists_polygon_isSimple_of_isCycle (D : PLDrawing G V) (hC : C ≤ G) (hCcyc : C.IsCycle) :
    ∃ (n : ℕ) (p : Polygon V n),
      p.IsSimple ℝ ∧ p.boundary ℝ = (D.toDrawing.restrict hC).support := by
  sorry

/-! ### Status.md 4.2 -/

/- **Route for `exists_isCycle_frontier_faceSet_eq`.**

The seven steps are in this file's module docstring; this names the API for each.

*Setting up.* Faces are taken on `𝕊` throughout: `Drawing.onePoint` (`Face.lean:213`) transports
the drawing, `Drawing.isClosed_support_onePoint` (`Face.lean:228`) supplies the `IsClosed` argument
that `Drawing.faceSet_isOpen` (`Face.lean:177`) and `Drawing.frontier_faceSet_subset_support`
(`Face.lean:185`) need, and `EuclideanSpace ℝ (Fin 2)` discharges its `[T2Space]` and
`[LocallyCompactSpace]`. `Drawing.support_onePoint` (`Face.lean:217`) moves support equations
across.

*Step 1.* `ConnGE.exists_isCycle_le` (`Forest.lean`) — note it returns `3 ≤ V(C₀).encard`, which
is precisely `ear_induction`'s `h3`, so do not reprove it.

*Step 2.* `ConnGE.ear_induction` (`Connected/Ear.lean`, and cited by name because that file is
being worked on). Signature at the time of writing:

    ConnGE.ear_induction [G.Finite] [G.Loopless] (hG : G.ConnGE 2) (hC₀ : C₀.IsCycle)
      (hC₀G : C₀ ≤ G) (h3 : 3 ≤ V(C₀).encard) {motive : Graph α β → Prop} (base : motive C₀)
      (step : ∀ ⦃H P⦄, C₀ ≤ H → H ≤ G → G.IsEar H P → motive H → motive (H ∪ P.toGraph)) :
      motive G

**Pass `motive` explicitly.** Its own docstring says why: `@[elab_as_elim]` infers the motive by
abstracting `G` out of the goal, and the motive wanted here is `fun H ↦ ∀ _ : H ≤ G, …`, in which
`G` occurs both as the abstracted variable and free in the binder's type. Abstraction cannot
produce that, and the resulting error is about elaboration, not about the mathematics.

*Step 3, base.* `exists_isSimpleLoop_toSet_eq_support_of_isCyclicWalk` above, then
`PolygonalPath.IsSimpleLoop.isJordanCurve` (`Geometry/Polygon/JordanCurve.lean:39`) and
`IsSimpleLoop.exists_sides_onePoint` (`:51`). Both sides are open, connected, disjoint from the
support and have frontier `|C₀|`, so `Drawing.exists_faceSet_eq` (`Face.lean:162`) makes each a
face; they cover the complement, so the given `F` is one of them.

`exists_sides_onePoint` is `sorry` — it is `Status.md` 3.2, and 3.2 is *not* covered by the §0
licence: §0 licenses `IsJordanCurve.exists_sides` alone and §3.1 derives the sphere form from it.
So this route depends on an open obligation that is somebody's work, not an assumption.

*Step 4.* The ear's relative interior misses `|H|` because its internal vertices are outside `V(H)`
(`IsEar.internal_disjoint`) and its edges outside `E(H)` (`IsEar.edge_disjoint`), and cells of a
drawing are pairwise disjoint off their ends — `Drawing.range_edgePath_inter` (`Drawing.lean:171`)
and `Drawing.pathInterior_edgePath_disjoint_vertex` (`Drawing.lean:157`). Connectedness of the
relative interior comes from the traced arc of
`exists_polygonalPath_toSet_eq_support_of_isPath` applied to `IsEar.isPath`. Landing it in one face
is `Drawing.faceSet_eq_connectedComponentIn` (`Face.lean:125`), which is hypothesis-free.

*Step 5.* `exists_two_regions_crosscut` (`ThetaCurve.lean:132`), fed by
`exists_polygon_isSimple_of_isCycle` above for its `p` and by
`exists_polygonalPath_toSet_eq_support_of_isPath` for its `A`. Its `hF` is stated with
`connectedComponentIn`, which is why this theorem's third conjunct is stated that way too — the
handoff is then a rewrite, not a construction. `Polygon.IsSimple.exists_arcs`
(`Polygon/PolygonalPath.lean:545`) supplies the two arcs of `|C|` if the caller needs them named.

That the two ends of `P` are images of *vertices of `C`* rather than merely points of `|C|` is the
one place the drawing axioms are used directly: `pathInterior_edgePath_disjoint_vertex` puts no
vertex image in an open cell, and `Drawing.vertex_injective` (`Drawing.lean:129`) then names the
vertex. `exists_two_regions_crosscut` is `sorry`, and so is `ConnGE.ear_induction`.

*Step 6.* `Drawing.restrict` is monotone in the subgraph, so `|H| ⊆ |H'|` follows from
`Drawing.support_eq` (`Drawing.lean:137`); `Drawing.exists_faceSet_eq` again recognises each
surviving face. `IsCyclicWalk.toGraph_isCycle` (`Forest.lean:192`) makes `C₁ + P` and `C₂ + P`
cycles, and `IsEar.union_le` (`Ear.lean:105`) puts them under `G`. -/
/-- **The face theorem** (`Status.md` 4.2). In a polygonal drawing of a finite loopless
`2`-connected graph, every face of the drawing on the sphere has a cycle of the graph as its
frontier, and *is* a connected component of the complement of that cycle.

The third conjunct is not implied by the second for a general set — it is what says the face is a
whole component of `𝕊 ∖ |C|` and not merely a set whose frontier happens to be `|C|`. It is stated
with `connectedComponentIn` rather than as "is a face of the restricted drawing" because that is
the form `exists_two_regions_crosscut` takes as a hypothesis, and §5 and §6 feed it straight in. -/
theorem exists_isCycle_frontier_faceSet_eq [G.Finite] [G.Loopless] (hG : G.ConnGE 2)
    (D : PLDrawing G ℝ²) (F : D.toDrawing.onePoint.Face) :
    ∃ (C : Graph α β) (hC : C ≤ G), C.IsCycle ∧
      frontier (D.toDrawing.onePoint.faceSet F) = (D.toDrawing.onePoint.restrict hC).support ∧
      ∀ ⦃q⦄, q ∈ D.toDrawing.onePoint.faceSet F →
        D.toDrawing.onePoint.faceSet F =
          connectedComponentIn ((D.toDrawing.onePoint.restrict hC).support)ᶜ q := by
  sorry

/- **Route.** `exists_isCycle_frontier_faceSet_eq`, then `⟨F, ‹_›⟩` for the existential in
`Drawing.IsFacialSubgraph` (`Face.lean:205`). One line once 4.2 lands; it exists so that
`Face.lean`'s consumers, stated against `IsFacialSubgraph`, do not each have to repackage. -/
/-- 4.2 in the packaged form `Face.lean`'s §5 and §6 statements are written against. Strictly
weaker than `exists_isCycle_frontier_faceSet_eq`, which names the face; use that one unless the
`IsFacialSubgraph` interface is what the caller already has. -/
theorem exists_isCycle_isFacialSubgraph [G.Finite] [G.Loopless] (hG : G.ConnGE 2)
    (D : PLDrawing G ℝ²) (F : D.toDrawing.onePoint.Face) :
    ∃ (C : Graph α β) (hC : C ≤ G), C.IsCycle ∧ D.toDrawing.onePoint.IsFacialSubgraph hC := by
  sorry

end PLDrawing

end

end Graph
