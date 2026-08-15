import Matroid.Graph.Planarity.Drawing
import Matroid.ForMathlib.Topology.OnePoint
import Matroid.ForMathlib.Topology.JordanCurve

/-!
# Faces of a drawing

A **face** of a drawing is a connected component of the complement of its support. The definition
needs nothing at all — no finiteness, no separation, no plane, no polygons — and neither do most of
its basic properties, so this file keeps them hypothesis-free and introduces assumptions one at a
time, at the statement that first needs them.

## What each fact costs

| fact | hypotheses |
|---|---|
| `Face`, `faceSet`, `faceAt`, nonempty, connected, disjoint from the support | none |
| `faceSet_eq_connectedComponentIn`, `exists_faceSet_eq` (recognising a face) | none |
| `faceSet_isOpen`, `frontier_faceSet_subset_support` | `IsClosed D.support`, `LocallyConnectedSpace X` |
| `isClosed_support` | `[G.Finite] [T2Space X]` |

In particular *recognising* a face — Status.md 3.4, the step used constantly in §§3–6 — is free:
`eq_connectedComponentIn_of_frontier_subset` needs no hypothesis on the ambient space whatsoever.
And the two facts that do cost something are stated against `IsClosed D.support` rather than against
`[G.Finite] [T2Space X]`, which is merely one sufficient condition for it; an infinite graph with
closed support has open faces just the same.

Nothing here is polygonal. The polygonal category is needed first for the *local* structure of a
drawing (Status.md 3.5–3.8, the star lemma), and the plane is needed first for *counting* faces via
the Jordan curve theorem. Neither enters at this level.

## The sphere

Faces of a plane drawing are taken in `𝕊 = OnePoint ℝ²`, purely to remove the exceptional unbounded
face; `Drawing.onePoint` is the transport. That `𝕊` is locally connected — needed for those faces to
be open, and asserted without comment in Status.md §0 — is not in Mathlib; see
`Matroid.ForMathlib.Topology.OnePoint`.

## Main definitions

* `Graph.Drawing.Face`, `Graph.Drawing.faceSet`, `Graph.Drawing.faceAt`
* `Graph.Drawing.IsFacialSubgraph`
* `Graph.Drawing.onePoint`

## Main statements

* `Graph.Drawing.exists_faceSet_eq` : an open connected set off the drawing whose frontier lies in
  the drawing is a face.
* `Graph.Drawing.faceSet_isOpen`, `Graph.Drawing.frontier_faceSet_subset_support`.
-/

open Function Set Topology

namespace Graph

noncomputable section

universe u v

variable {α β γ δ : Type*} {G H : Graph α β}
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {W : Set X}

namespace Drawing

/-! ### Faces, with no hypotheses -/

/-- The faces of a drawing are the connected components of its complement. -/
def Face (D : Drawing G X) : Type u := ConnectedComponents ↑(D.supportᶜ)

/-- The subset of the ambient space belonging to a face. -/
def faceSet (D : Drawing G X) (F : D.Face) : Set X :=
  Subtype.val '' ConnectedComponents.mk ⁻¹' {F}

/- **Proof route for this whole section** (formalisation helper). Everything down to
`frontier_faceSet_subset_support` is `ConnectedComponents` plumbing with no drawing content; the
only fact about `D` used anywhere is that `D.supportᶜ` is a set. All names below were checked
against this Mathlib pin.

The single bridge, used by nearly all of them:
`connectedComponentIn_eq_image (h : x ∈ F) :`
`  connectedComponentIn F x = (↑) '' connectedComponent ⟨x, h⟩`
(`Mathlib/Topology/Connected/Basic.lean:508`). `faceSet` is definitionally the left-hand image, so
this is the translation between `Face` and `connectedComponentIn` and should be proved once, as
`faceSet_eq_connectedComponentIn`, with the rest derived from it.

* `faceSet_nonempty` — `ConnectedComponents.surjective_coe`
  (`Mathlib/Topology/Connected/Clopen.lean:538`) gives `x` with `mk x = F`; then
  `⟨x.1, x, rfl, rfl⟩`.
* `faceSet_disjoint_support` — `x.2 : ↑x ∈ D.supportᶜ`; nothing else.
* `faceSet_eq_connectedComponentIn` — `ConnectedComponents.coe_eq_coe'` (`Clopen.lean:529`) turns
  `mk ⟨x,_⟩ = mk y` into membership of a `connectedComponent`, then the bridge above.
* `faceSet_isConnected` — `isConnected_connectedComponentIn_iff` (`Basic.lean:547`), via the
  previous lemma and `faceSet_nonempty`.
* `mem_faceSet_faceAt` — `mem_connectedComponentIn` (`Basic.lean:519`), or directly `⟨⟨x,hx⟩, …⟩`.
* `exists_faceSet_eq` — **do not reprove this.** `eq_connectedComponentIn_of_frontier_subset` in
  `Matroid/ForMathlib/Topology/JordanCurve.lean:69` is already proved and is exactly the statement;
  take any `a ∈ W`, apply it, and hand back `D.faceAt (hWD.notMem_of_mem_left ha)`.
* `faceSet_isOpen` — `IsOpen.connectedComponentIn`
  (`Mathlib/Topology/Connected/LocallyConnected.lean:70`), applied to `hD.isOpen_compl`.
* `frontier_faceSet_subset_support` — contrapositive, as the docstring says; needs `faceSet_isOpen`
  plus `connectedComponentIn_eq` (`Basic.lean:587`) to identify the two components.
* `support_onePoint` — `support` is `range D` and `onePoint` is `postcomp`, so this is
  `Set.range_comp`; `postcomp_apply` is the simp lemma.
* `isClosed_support_onePoint` — `D.support_isCompact` (`Drawing.lean:154`), `IsCompact.image` along
  `OnePoint.continuous_coe` (`Mathlib/Topology/Compactification/OnePoint/Basic.lean:267`), then
  `IsCompact.isClosed`; the `T2Space (OnePoint X)` instance fires from `[T2Space X]` and
  `[LocallyCompactSpace X]`, which is why those two hypotheses are on the statement.

If any of these turns out to need more than a few lines, that is structural feedback about `Face`
and comes back here rather than being worked around. -/

/-- Every face contains a point. -/
lemma faceSet_nonempty (D : Drawing G X) (F : D.Face) : (D.faceSet F).Nonempty := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe F
  exact ⟨x.1, x, rfl, rfl⟩

/-- A face is disjoint from the drawing. -/
lemma faceSet_disjoint_support (D : Drawing G X) (F : D.Face) :
    Disjoint (D.faceSet F) D.support := by
  refine disjoint_left.mpr ?_
  rintro _ ⟨⟨_, hx⟩, -, rfl⟩
  exact hx

/-- The face containing `x` is its connected component in the complement of the drawing. -/
lemma faceSet_eq_connectedComponentIn (D : Drawing G X) (F : D.Face) {x : X}
    (hx : x ∈ D.faceSet F) : D.faceSet F = connectedComponentIn D.supportᶜ x := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hF : F = ConnectedComponents.mk y := (mem_singleton_iff.mp hy).symm
  subst F
  change (↑) '' (ConnectedComponents.mk ⁻¹' {ConnectedComponents.mk y}) =
    connectedComponentIn D.supportᶜ ↑y
  rw [connectedComponentIn_eq_image y.2]
  congr 1
  ext w
  exact ConnectedComponents.coe_eq_coe'

/-- A face is connected. -/
lemma faceSet_isConnected (D : Drawing G X) (F : D.Face) : IsConnected (D.faceSet F) := by
  obtain ⟨x, hx⟩ := D.faceSet_nonempty F
  rw [D.faceSet_eq_connectedComponentIn F hx]
  exact isConnected_connectedComponentIn_iff.mpr <|
    (D.faceSet_disjoint_support F).notMem_of_mem_left hx

/-- The face containing a point off the drawing. -/
def faceAt (D : Drawing G X) {x : X} (hx : x ∉ D.support) : D.Face :=
  ConnectedComponents.mk ⟨x, hx⟩

lemma mem_faceSet_faceAt (D : Drawing G X) {x : X} (hx : x ∉ D.support) :
    x ∈ D.faceSet (D.faceAt hx) :=
  ⟨⟨x, hx⟩, rfl, rfl⟩

lemma faceSet_faceAt (D : Drawing G X) {x : X} (hx : x ∉ D.support) :
    D.faceSet (D.faceAt hx) = connectedComponentIn D.supportᶜ x :=
  D.faceSet_eq_connectedComponentIn _ (D.mem_faceSet_faceAt hx)

/-- **Recognising a face.** An open connected set off the drawing whose frontier lies in the drawing
is a face. Status.md 3.4, and the workhorse of §§3–6: every face produced by cutting one face with
an arc is identified this way.

This costs nothing — no finiteness, no separation axiom, no local connectedness — because
`eq_connectedComponentIn_of_frontier_subset` costs nothing. -/
lemma exists_faceSet_eq (D : Drawing G X) (hW : IsOpen W) (hWc : IsConnected W)
    (hWD : Disjoint W D.support) (hfr : frontier W ⊆ D.support) :
    ∃ F : D.Face, D.faceSet F = W := by
  obtain ⟨a, ha⟩ := hWc.nonempty
  refine ⟨D.faceAt (hWD.notMem_of_mem_left ha), ?_⟩
  rw [D.faceSet_faceAt]
  exact (eq_connectedComponentIn_of_frontier_subset hW hWc.isPreconnected hWD hfr ha).symm

/-! ### Openness, and what it costs

Two facts need the support to be closed and the space to be locally connected, and nothing else
does. `isClosed_support` below is one sufficient condition for the first, not a replacement for it.
-/

/-- Components of an open set in a locally connected space are open. -/
lemma faceSet_isOpen [LocallyConnectedSpace X] (D : Drawing G X) (hD : IsClosed D.support)
    (F : D.Face) : IsOpen (D.faceSet F) := by
  obtain ⟨x, hx⟩ := D.faceSet_nonempty F
  rw [D.faceSet_eq_connectedComponentIn F hx]
  exact hD.isOpen_compl.connectedComponentIn

/-- The frontier of a face lies in the drawing: a point of the frontier outside the support would
have its own face as an open neighbourhood, which would then meet and hence equal `F`. -/
lemma frontier_faceSet_subset_support [LocallyConnectedSpace X] (D : Drawing G X)
    (hD : IsClosed D.support) (F : D.Face) : frontier (D.faceSet F) ⊆ D.support := by
  intro x hxfr
  by_contra hxsup
  obtain ⟨a, ha⟩ := D.faceSet_nonempty F
  have hFeq := D.faceSet_eq_connectedComponentIn F ha
  have hUopen := D.faceSet_isOpen hD (D.faceAt hxsup)
  have hxU := D.mem_faceSet_faceAt hxsup
  obtain ⟨y, hyU, hyF⟩ :=
    (mem_closure_iff.mp (frontier_subset_closure hxfr)) _ hUopen hxU
  rw [D.faceSet_faceAt hxsup] at hyU
  rw [hFeq] at hyF
  have heq : connectedComponentIn D.supportᶜ x = connectedComponentIn D.supportᶜ a :=
    (connectedComponentIn_eq hyU).trans (connectedComponentIn_eq hyF).symm
  have hxF : x ∈ D.faceSet F := by
    rw [hFeq, ← heq]
    exact mem_connectedComponentIn hxsup
  exact ((D.faceSet_isOpen hD F).frontier_eq ▸ hxfr).2 hxF

/-- A subgraph is facial in `D` if its drawing is exactly the frontier of a face. -/
def IsFacialSubgraph (D : Drawing G X) (h : H ≤ G) : Prop :=
  ∃ F : D.Face, frontier (D.faceSet F) = (D.restrict h).support

/-! ### Transport to the sphere -/

/-- A drawing in `X` read as a drawing in `OnePoint X`. For `X := ℝ²` this is the passage to the
sphere `𝕊`, which exists only to remove the exceptional unbounded face: on `𝕊` no face is
distinguished, so no argument has to treat one of them separately. -/
def onePoint (D : Drawing G X) : Drawing G (OnePoint X) :=
  D.postcomp ⟨(↑), OnePoint.continuous_coe⟩ OnePoint.coe_injective

@[simp]
lemma support_onePoint (D : Drawing G X) : D.onePoint.support = (↑) '' D.support := by
  ext y
  simp only [support, onePoint, mem_range, mem_image, postcomp_apply]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨D x, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩

/-- On the sphere the support of a drawing of a finite graph is still closed, and now its complement
is an open subset of a compact space. -/
lemma isClosed_support_onePoint [G.Finite] [T2Space X] [LocallyCompactSpace X] (D : Drawing G X) :
    IsClosed D.onePoint.support := by
  rw [support_onePoint]
  exact (D.support_isCompact.image OnePoint.continuous_coe).isClosed

end Drawing

/-! ### Plane topology used in the 3-connected case

Parked here because they are the statements that mention faces. They are Status.md §5 and §6 and
belong in a file of their own once that development starts.

**Handoff to formalisation helper (blocks Status.md item 6 → 7).** The next dependency after θ
(Status.md §3.9–3.11, assumed) is **§4**:

* **4.1 Ear existence** — **done**, in `Matroid/Graph/Connected/Ear.lean`: `Graph.IsEar`,
  `Graph.ConnGE.exists_isEar`, and the eliminator `Graph.ConnGE.ear_induction` that 4.2 consumes
  (non-dependent motive; instantiate it as `motive H := ∀ hle : H ≤ G, <face statement about
  D.restrict hle>` and recover the `≤` its step needs from `Graph.IsEar.union_le`). It landed in
  `Connected/` rather than here because it is purely combinatorial — D7, dependency weight.
  Note that Status.md 4.1 was *false* as stated and has been corrected: the hypothesis is
  `V(H).Nontrivial`, not `V(H) ≠ ∅`. Free for 4.2, whose `H` always contains `C₀`.
* **4.2 Face theorem** — every face of a 2-connected *polygonal* drawing has frontier `|C|` for a
  cycle `C ≤ G`. Needs: induction over subgraphs `C₀ ≤ H ≤ G`, adding ears, identifying the ear's
  relative interior with a face of `D.restrict`, splitting that face via
  `exists_two_regions_crosscut` (3.10), and packaging `frontier F = (restrict hC).support` as
  `IsFacialSubgraph`. Remaining bridges, now that the combinatorial half is in place: cycle support
  ↔ simple polygon / Jordan loop on `𝕊`; induction carrier relating faces of `D|H` to faces of
  `D|H'`. (`H + P` as a subgraph of `G` is `Graph.IsEar.union_le`.)

The three theorems below are Status.md §5–§6 and are corollaries of 4.2 + 3.10 + pairing. Next
step: state 4.2 in a Planarity file of its own (D7), with proof routes naming the two bridges
above, then tactic can return. -/

namespace Drawing

variable {e : β} {u v : α} {C : Graph α β} {P₁ P₂ : WList α β}

/-- In a plane drawing of a finite 3-connected graph, deleting a vertex produces a face whose
frontier is a cycle containing every neighbor of the deleted vertex. -/
theorem exists_facial_cycle_of_delete_vertex [H.Finite] [H.Simple] (hH : H.ConnGE 3)
    (D : Drawing H (EuclideanSpace ℝ (Fin 2))) (u : V(H)) :
    ∃ (C : Graph α β) (hC : C ≤ H - {u.1}),
      C.IsCycle ∧ (D.restrict deleteVerts_le).IsFacialSubgraph hC ∧ N(H, u.1) ⊆ V(C) := by
  
  sorry

/-- The facial cycle around the contracted vertex, expressed back in the original graph.

This packages the carrier bookkeeping between `(G /(e, he)) - {u}` and `G - {u, v}`. In
particular, every neighbor of either endpoint other than the other endpoint lies on the cycle. -/
theorem exists_facial_cycle_of_contract [G.Finite] [G.Simple]
    (he : G.IsLink e u v) (huv : u ≠ v) (hcontract : (G /(e, he)).ConnGE 3)
    (D : Drawing (G /(e, he)) (EuclideanSpace ℝ (Fin 2))) :
    ∃ (C : Graph α β) (hCG : C ≤ G) (hCcontract : C ≤ (G /(e, he)) - {u}),
      C.IsCycle ∧ (D.restrict deleteVerts_le).IsFacialSubgraph hCcontract ∧
      u ∉ V(C) ∧ v ∉ V(C) ∧ N(G, u) \ {v} ⊆ V(C) ∧ N(G, v) \ {u} ⊆ V(C) := by
  sorry

/-- The local vertex-splitting step used in the 3-connected case of Kuratowski's theorem.

Suppose `e` joins `u` and `v`, the contraction of `e` has a plane drawing, and deleting the
contracted vertex exposes a facial cycle `C`. If `C` is the union of two paths such that the
interior of the first contains no neighbor of `u` and the interior of the second contains no
neighbor of `v`, then the contracted vertex can be split inside that face to obtain a drawing of
`G`.

The last five hypotheses deliberately have the same shape as the first conclusion of
`Graph.K33_K5_lemma`. -/
theorem planar_of_contract_of_facial_cycle_two_paths [G.Finite] [G.Simple]
    (he : G.IsLink e u v) (huv : u ≠ v)
    (D : Drawing (G /(e, he)) (EuclideanSpace ℝ (Fin 2)))
    (hCG : C ≤ G) (hCcontract : C ≤ (G /(e, he)) - {u}) (hcycle : C.IsCycle)
    (hfacial : (D.restrict deleteVerts_le).IsFacialSubgraph hCcontract)
    (hu_neighbors : N(G, u) \ {v} ⊆ V(C)) (hv_neighbors : N(G, v) \ {u} ⊆ V(C))
    (hP₁ : C.IsPath P₁) (hP₂ : C.IsPath P₂)
    (huP₁ : ∀ x ∈ P₁.vertex.tail.dropLast, ¬ G.Adj u x)
    (hvP₂ : ∀ x ∈ P₂.vertex.tail.dropLast, ¬ G.Adj v x)
    (hP₁P₂ : C.IsCyclicWalk (P₁ ++ P₂)) :
    G.Planar := by
  sorry

end Drawing

end

end Graph
