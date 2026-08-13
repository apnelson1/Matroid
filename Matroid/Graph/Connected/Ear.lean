module

public import Matroid.Graph.Forest
public import Matroid.Graph.Simple
public import Matroid.Graph.WList.TakeDrop.Pred
import all Mathlib.Combinatorics.Graph.Delete

@[expose] public section

/-!
# Ears and ear decompositions

An **ear** of a subgraph `H` inside `G` is a path of `G` with two *distinct* ends in `V(H)`, no
internal vertex in `V(H)`, and no edge in `E(H)`. Attaching one enlarges `H` inside `G` without
creating a cut vertex, which is what makes Whitney's ear induction work.

This file is `Status.md` §4.1 for the Kuratowski project, together with the ear decomposition that
§4.1 is the inductive step of.

## The loop disjunct

Existence is *not* unconditional: if `G` has a loop `e ∉ E(H)` at a vertex of `H`, that loop may be
the only way to leave `H`, and it is not an ear. Take `G` a triangle plus a loop at `a` and `H` the
triangle. So the general statement is a disjunction — an ear, or a loop — and `[G.Loopless]`
removes the second alternative.

Attaching a loop preserves `2`-connectivity, so nothing would break by admitting loops as
degenerate ears. Admitting *cycles* would: a cycle attached at a single vertex creates a cut vertex
(two triangles glued at a point are not `2`-connected), which is why `IsEar` requires
`first ≠ last` and why `V(H).Nontrivial` rather than `V(H).Nonempty` is the right hypothesis. Since
`ConnGE 2` forces `3 ≤ V(G).encard`, no caller is inconvenienced by this.

## What each fact costs

| fact | hypotheses |
|---|---|
| `IsEar` and its consumers | none |
| `exists_isEar_or_isLoopAt_of_connected` | `G.Connected`, `∀ x, (G - {x}).Connected` |
| `ConnGE.exists_isEar` | `G.ConnGE 2`, `[G.Loopless]` |
| `ConnGE.exists_isCycle_le` | `G.ConnGE 2` |
| `IsEarDecomposition.connGE_two` | none |
| `ConnGE.ear_induction`, `ConnGE.exists_isEarDecomposition` | `ConnGE 2`, `Finite`, `Loopless` |

Ear existence needs neither `[G.Finite]` nor `[G.Simple]`: walks are finite by construction, so
cutting one at the first vertex of `V(H)` costs nothing, and `ConnGE.deleteVerts` at a singleton
needs only that a singleton is finite. Nor does the base cycle. `[G.Finite]` enters exactly once —
it is what makes the ears terminate — and the converse half of Whitney needs no instance at all.

This corrects `Status.md` 4.1, which asserted `V(H) ≠ ∅` where `V(H).Nontrivial` is needed, and
claimed its hypothesis set was minimal.

## Main definitions

* `Graph.IsEar`
* `Graph.EarBuild` — attaching a list of ears, in order
* `Graph.IsEarDecomposition`

## Main statements

* `Graph.ConnGE.exists_isEar` — `Status.md` 4.1, corrected.
* `Graph.ConnGE.ear_induction` — the eliminator `Status.md` 4.2 consumes.
* `Graph.connGE_two_iff_exists_isEarDecomposition` — Whitney's theorem.
-/

variable {α β : Type*} {G H K C₀ : Graph α β} {u v x y : α} {e f : β} {P Q : WList α β}
  {Ps : List (WList α β)} {n : ℕ}

open Set WList

namespace Graph

/-! ### Ears -/

/-- `G.IsEar H P` means that `P` is an **ear** of `H` in `G`: a path of `G` whose two ends are
distinct vertices of `H`, with no internal vertex in `V(H)` and no edge in `E(H)`.

Nothing is assumed about how `H` sits inside `G`; `H ≤ G` is a hypothesis of the statements that
*produce* an ear, not part of being one. -/
structure IsEar (G H : Graph α β) (P : WList α β) : Prop where
  isPath : G.IsPath P
  first_ne_last : P.first ≠ P.last
  first_mem : P.first ∈ V(H)
  last_mem : P.last ∈ V(H)
  internal_disjoint : Disjoint P.internalVertexSet V(H)
  edge_disjoint : Disjoint E(P) E(H)

lemma IsEar.nonempty (h : G.IsEar H P) : P.Nonempty := by
  obtain ⟨x, rfl⟩ | hne := P.exists_eq_nil_or_nonempty
  · exact (h.first_ne_last rfl).elim
  · exact hne

lemma IsEar.edgeSet_nonempty (h : G.IsEar H P) : E(P).Nonempty :=
  h.nonempty.edgeSet_nonempty

/- Route: `IsWalk.toGraph_le` `Walk/Basic.lean:776` applied to `h.isPath.isWalk`. -/
lemma IsEar.toGraph_le (h : G.IsEar H P) : P.toGraph ≤ G :=
  h.isPath.isWalk.toGraph_le

/- Route: `Graph.left_le_union` `Subgraph/Defs.lean:471`. -/
lemma IsEar.le_union (_h : G.IsEar H P) : H ≤ H ∪ P.toGraph :=
  Graph.left_le_union ..

/- Route: `Graph.union_le` `Subgraph/Defs.lean:475` with `IsEar.toGraph_le`; compatibility of the
two subgraphs is `compatible_of_le_le` `Subgraph/Compatible.lean:66`. -/
lemma IsEar.union_le (h : G.IsEar H P) (hle : H ≤ G) : H ∪ P.toGraph ≤ G :=
  Graph.union_le hle h.toGraph_le

/-- Attaching an ear strictly grows the subgraph. This is what makes the ear induction terminate.

Route: `IsEar.le_union` for `≤`. For `≠`: `edgeSet_nonempty` gives `e ∈ E(P)`, `edge_disjoint` puts
`e ∉ E(H)`, and `toGraph_edgeSet` `Walk/Basic.lean:714` with `union_edgeSet` puts
`e ∈ E(H ∪ P.toGraph)`. -/
lemma IsEar.lt_union (h : G.IsEar H P) : H < H ∪ P.toGraph := by
  obtain ⟨e, he⟩ := h.edgeSet_nonempty
  refine lt_iff_le_and_ne.mpr ⟨h.le_union, fun heq ↦ ?_⟩
  apply_fun Graph.edgeSet at heq
  exact h.edge_disjoint.notMem_of_mem_left he <| Set.ext_iff.mp heq e |>.mpr (by grind)

/-! ### Existence: `Status.md` 4.1

The primitive form below uses `G.Connected` and `∀ x ∈ V(G), (G - {x}).Connected` and nothing else.
`ConnGE 2` is one sufficient condition for that pair, recorded separately. -/

/-- **Ear existence.** A proper subgraph `H` of `G` with at least two vertices has an ear, unless
`G` has a loop at a vertex of `H` outside `E(H)`.

`V(H).Nontrivial` cannot be weakened: with `G = K₃` and `H` a single vertex, both ends of a
prospective ear would have to be that vertex.

Route, following `Status.md` 4.1 with its gap repaired.
`Connected.exists_inc_notMem_of_lt` `Connected/Basic.lean:148` applied to `hlt : H < G`
(`lt_iff_le_and_ne`, from `hle` and `hne`) and `hV.nonempty` yields `e`, `x` with `G.Inc e x`,
`e ∉ E(H)`, `x ∈ V(H)`. This one lemma covers both branches of `Status.md`'s hand-rolled case
split on whether `V(H) = V(G)`.

Split `G.Inc e x` on loop versus nonloop (`Inc.isLoopAt_or_isNonloopAt`, `Basic.lean` near
`IsLoopAt.other_eq` :57):
* loop at `x`: the right disjunct, with `hx : x ∈ V(H)` and `e ∉ E(H)` already in hand.
* nonloop, so `G.IsLink e x u` with `u ≠ x`:
  * `u ∈ V(H)`: `IsLink.walk_isPath` `Walk/Path.lean:195` gives the one-edge ear.
    `internalVertexSet` `WList/TakeDrop/Index.lean:17` is `vertex.tail.dropLast`, empty here.
  * `u ∉ V(H)`: pick `y₀ ∈ V(H) \ {x}` from `hV`. **This is the step `Status.md` omits.**
    `hGx x` makes `G - {x}` connected, and `u, y₀ ∈ V(G - {x})`, so
    `ConnBetween.exists_isPath` `Connected/Vertex/Defs.lean:70` gives a path `Q` of `G - {x}`;
    `isPath_deleteVerts_iff` `Walk/Path.lean:242` reads off both `G.IsPath Q` and `x ∉ V(Q)`.
    Cut with `Q.prefixUntil (· ∈ V(H))` `WList/TakeDrop/Defs.lean:22`, then
    `prefixUntil_last_eq_of_prop` `WList/TakeDrop/Pred.lean:44` lands the far end in `V(H)` and
    `prefixUntil_vertex_dropLast_not_prop` `Pred.lean:144` keeps the internal vertices out of it.
    `cons x e` that prefix.
    `first_ne_last` holds because `x ∉ V(Q)`.
    `edge_disjoint`: an edge of `H` has both ends in `V(H)` (`hle`), but no two consecutive
    vertices of the prefix both lie in `V(H)`. -/
theorem exists_isEar_or_isLoopAt_of_connected (hG : G.Connected)
    (hGx : ∀ x ∈ V(G), (G - {x}).Connected) (hle : H ≤ G) (hV : V(H).Nontrivial) (hne : H ≠ G) :
    (∃ P, G.IsEar H P) ∨ ∃ e x, x ∈ V(H) ∧ G.IsLoopAt e x ∧ e ∉ E(H) := by
  obtain ⟨e, x, hex, heH, hxH⟩ := hG.exists_inc_notMem_of_lt (Std.lt_of_le_of_ne hle hne)
    hV.nonempty
  refine hex.isLoopAt_or_isNonloopAt.elim (Or.inr ⟨e, x, hxH, ·, heH⟩) fun ⟨u, hux, h⟩ ↦ Or.inl ?_
  obtain ⟨y₀, hy₀, hy₀x⟩ := hV.exists_ne x
  obtain ⟨Q, hQ, rfl, rfl⟩ := hGx x (hle.vertexSet_mono hxH) |>.connBetween (by grind : u ∈ _)
    (by grind : y₀ ∈ _) |>.exists_isPath
  simp only [isPath_deleteVerts_iff, disjoint_singleton_right, mem_vertexSet_iff] at hQ
  classical
  have hpre := Q.prefixUntil_isPrefix (· ∈ V(H))
  have hnotMem := mt (hpre.subset ·) hQ.2
  use cons x e (Q.prefixUntil (· ∈ V(H))), ?_, (ne_of_mem_of_not_mem last_mem hnotMem |>.symm), hxH,
    prefixUntil_prop_last ⟨_, last_mem, hy₀⟩, disjoint_internalVertexSet_cons_prefixUntil .., ?_
  · rw [cons_isPath_iff, prefixUntil_first]
    use h, hQ.1.prefix hpre, hnotMem
  by_cases hnt : (cons x e (Q.prefixUntil (· ∈ V(H)))).Nontrivial
  · exact hnt.disjoint_edgeSet_of_disjoint_internalVertexSet hle
      (cons_isWalk_iff.mpr ⟨(Q.prefixUntil_first (· ∈ V(H))) ▸ h, (hQ.1.prefix hpre).isWalk⟩)
      (disjoint_internalVertexSet_cons_prefixUntil Q (· ∈ V(H)) x e)
  have hnil : (Q.prefixUntil (· ∈ V(H))).Nil := by
    rwa [← WList.not_nonempty_iff, ← cons_nontrivial_iff]
  rw [hnil.eq_nil_first, cons_edgeSet, nil_edgeSet, insert_empty_eq]
  exact disjoint_singleton_left.mpr heH

/-- A `2`-connected graph has more than `n` vertices. This is the `le_card` field of `ConnGE`
`Connected/Defs.lean:43` with the `V(G).Subsingleton` alternative ruled out: a subsingleton graph is
`⊥` or a bouquet, and `connGE_bot` and `connGE_bouquet_iff` `Connected/Defs.lean` cap both at
`ConnGE 1`. -/
lemma ConnGE.lt_encard_vertexSet (hG : G.ConnGE n) (hn : 2 ≤ n) : n < V(G).encard := by
  refine hG.le_card.resolve_left fun h ↦ ?_
  obtain hempty | ⟨v, hv⟩ := h.eq_empty_or_singleton
  · obtain rfl := vertexSet_eq_empty_iff.mp hempty
    grind [connGE_bot]
  obtain heq := Graph.eq_bouquet_of_subsingleton (hv ▸ rfl : v ∈ _) h
  grind [connGE_bouquet_iff]

/- Route: `ConnGE.deleteVerts` `Connected/Defs.lean:751` at `X = {x}`, whose side condition
`(V(G) ∩ {x}).Finite` follows from `Set.Subsingleton.finite`; it yields `(G - {x}).ConnGE 1`, then
`connGE_one_iff` `Connected/Defs.lean:676`. -/
lemma ConnGE.deleteVert_connected (hG : G.ConnGE 2) (hx : x ∈ V(G)) : (G - {x}).Connected := by
  have := hG.deleteVerts (Subsingleton.inter_singleton.finite : (V(G) ∩ {x}).Finite)
  rw [inter_eq_right.mpr (singleton_subset_iff.mpr hx), encard_singleton] at this
  rw [← connGE_one_iff]
  norm_cast

/-- **`Status.md` 4.1, corrected.** A proper subgraph with at least two vertices of a loopless
`2`-connected graph has an ear.

No `[G.Finite]` and no `[G.Simple]`. -/
theorem ConnGE.exists_isEar [G.Loopless] (hG : G.ConnGE 2) (hle : H ≤ G) (hV : V(H).Nontrivial)
    (hne : H ≠ G) : ∃ P, G.IsEar H P :=
  exists_isEar_or_isLoopAt_of_connected (hG.connected (by omega))
    (fun _ ↦ hG.deleteVert_connected) hle hV hne |>.resolve_right <| by simp

/-- Same, without discharging the loop alternative. -/
theorem ConnGE.exists_isEar_or_isLoopAt (hG : G.ConnGE 2) (hle : H ≤ G) (hV : V(H).Nontrivial)
    (hne : H ≠ G) : (∃ P, G.IsEar H P) ∨ ∃ e x, x ∈ V(H) ∧ G.IsLoopAt e x ∧ e ∉ E(H) :=
  exists_isEar_or_isLoopAt_of_connected (hG.connected one_le_two)
    (fun _ hx ↦ hG.deleteVert_connected hx) hle hV hne

lemma neighbor_isSep (hx : x ∈ V(G)) (h : ∃ v ∈ V(G), ¬ G.Adj x v) : G.IsSep N(G, x) := by
  refine ⟨G.neighbor_subset x, ?_⟩
  sorry -- 1-menger. Should be trivial

/-! ### The base cycle -/

/-- Every vertex of a `2`-connected graph has two distinct neighbours, both different from itself.

`u ≠ x` and `v ≠ x` have to be stated, not inferred: `Adj` is `∃ e, G.IsLink e x y`
(Mathlib `Combinatorics/Graph/Basic.lean:316`), so a loop at `x` makes `G.Adj x x` true. Without
them `exists_isCycle_le` cannot place `u` and `v` in `V(G - {x})`.

This is also strictly what is wanted in place of `MinDegreeGE 2`, which would not serve: parallel
edges make the degree `2` without producing a second neighbour, and it is the second neighbour that
excludes a digon.

Route: if `x` had no neighbour outside `{x}` then `∅` is an `IsSep` `Connected/Defs.lean:370`, and
if `u` were its only one then `x` is isolated in `G - {u}`, which still has another vertex by
`ConnGE.lt_encard_vertexSet`, so `{u}` is an `IsSep` of `encard 1`. Either contradicts `hG.le_cut`.
Compare `EdgeConnGE.minDegreeGE` `Connected/Bond.lean:565`, the edge-connectivity analogue, which is
proved the same way. -/
lemma ConnGE.exists_two_adj (hG : G.ConnGE 2) (hx : x ∈ V(G)) :
    ∃ u v, u ≠ v ∧ u ≠ x ∧ v ≠ x ∧ G.Adj x u ∧ G.Adj x v := by
  obtain hh := hG.lt_encard_vertexSet le_rfl

  contrapose! hG
  have := G.neighbor_isSep hx
  sorry

/-- A `2`-connected graph has, through each of its vertices, a cycle on at least three vertices.

The bound on `V(C₀)` matters: `IsCycle` `Forest.lean:167` is `Minimal (¬ IsForest ·)`, which admits
loops and digons, and neither is `2`-connected — so a decomposition rooted at one would have no
converse. No finiteness instance is needed: the cycle is built, not extracted.

Route: `ConnGE.exists_two_adj` gives `e₁ : G.IsLink e₁ x u` and `e₂ : G.IsLink e₂ x v` with
`u ≠ v`, hence `e₁ ≠ e₂`, and with `u ≠ x`, `v ≠ x`, which is what places both in `V(G - {x})`.
`ConnGE.deleteVert_connected` and `ConnBetween.exists_isPath`
`Connected/Vertex/Defs.lean:70` give a path `Q` of `G - {x}` from `u` to `v`; `x ∉ V(Q)` by
`isPath_deleteVerts_iff` `Walk/Path.lean:242`. Then `(cons x e₁ Q).concat e₂ x` is closed with
`tail.vertex.Nodup` and length `> 2`, so `IsWalk.isCyclicWalk_of_closed_nodup` `Walk/Cycle.lean:58`
applies. Convert with `IsCyclicWalk.toGraph_isCycle` `Forest.lean:192` and
`IsWalk.toGraph_le` `Walk/Basic.lean:776`; `toGraph_vertexSet` `Walk/Basic.lean:710` gives the
`encard` bound from the three distinct vertices `x, u, v`.

`Connected.isCycle_of_regular` `Degree/Max.lean:97` is the model for the last two steps. -/
theorem ConnGE.exists_isCycle_le (hG : G.ConnGE 2) (hx : x ∈ V(G)) :
    ∃ C₀, C₀.IsCycle ∧ C₀ ≤ G ∧ x ∈ V(C₀) ∧ 3 ≤ V(C₀).encard := by
  
  sorry

/-! ### Ear induction

The eliminator `Status.md` 4.2 consumes. The motive is non-dependent: 4.2 instantiates it as
`motive H := ∀ hle : H ≤ G, <face statement about D.restrict hle>` and recovers the `≤` its step
needs from `IsEar.union_le`. -/

/-- **Ear induction.** A property that holds of a cycle in `G` and survives attaching an ear holds
of `G` itself.

Pass `motive` explicitly. `@[elab_as_elim]` will otherwise infer it by abstracting `G` out of the
goal, and §4.2's motive `fun H ↦ ∀ _ : H ≤ G, …` has `G` occurring both as the abstracted variable
and free in the binder's type, which abstraction cannot produce.

Route: strong induction on `(E(G) \ E(H)).encard`, over `H` with `C₀ ≤ H ≤ G`, as `Status.md` 4.2.
Given `H ≠ G`, `ConnGE.exists_isEar` applies: `V(H).Nontrivial` because `C₀ ≤ H` and
`3 ≤ V(C₀).encard`. `IsEar.lt_union` makes the measure drop, and `[G.Finite]` bounds it.
Termination endgame: when `E(H) = E(G)` also `V(H) = V(G)`, since a vertex of `G` outside `V(H)`
still carries an edge (`ConnGE.exists_isNonloopAt` `Connected/Basic.lean:633`) whose ends lie in
`V(H)` once that edge is in `E(H)`. -/
@[elab_as_elim]
theorem ConnGE.ear_induction [G.Finite] [G.Loopless] (hG : G.ConnGE 2) (hC₀ : C₀.IsCycle)
    (hC₀G : C₀ ≤ G) (h3 : 3 ≤ V(C₀).encard) {motive : Graph α β → Prop} (base : motive C₀)
    (step : ∀ ⦃H P⦄, C₀ ≤ H → H ≤ G → G.IsEar H P → motive H → motive (H ∪ P.toGraph)) :
    motive G := by
  sorry

/-! ### Ear decompositions -/

/-- `G.EarBuild H Ps K` means that attaching the ears of `Ps` to `H` in order, inside `G`,
produces `K`. -/
inductive EarBuild (G : Graph α β) : Graph α β → List (WList α β) → Graph α β → Prop
  -- Fresh binder names throughout: reusing the section variables `H`, `P`, `Ps`, `K` counts as
  -- overriding their binder kind, which constructors may not do. And `[]` cannot be written for
  -- the empty list here, because `A []` parses as the induce notation `G[X]`.
  | nil (A : Graph α β) : G.EarBuild A List.nil A
  | cons {A B : Graph α β} {R : WList α β} {Rs : List (WList α β)} (hR : G.IsEar A R)
      (h : G.EarBuild (A ∪ R.toGraph) Rs B) : G.EarBuild A (R :: Rs) B

/- Route: induction on the derivation; `IsEar.le_union` at each `cons`, `le_trans` to chain. -/
lemma EarBuild.le (h : G.EarBuild H Ps K) : H ≤ K := by
  sorry

/- Route: induction on the derivation; `IsEar.union_le` at each `cons` re-establishes `≤ G`. -/
lemma EarBuild.le_of_le (h : G.EarBuild H Ps K) (hle : H ≤ G) : K ≤ G := by
  sorry

/-- An **ear decomposition** of `G`: a cycle of `G` on at least three vertices, and a list of ears
attaching to it that exhausts `G`.

`three_le` is part of the definition rather than a hypothesis on the converse below, because a
`IsCycle` that is a loop or a digon is not what "ear decomposition" means anywhere. -/
structure IsEarDecomposition (G C₀ : Graph α β) (Ps : List (WList α β)) : Prop where
  isCycle : C₀.IsCycle
  three_le : 3 ≤ V(C₀).encard
  le : C₀ ≤ G
  earBuild : G.EarBuild C₀ Ps G

/-! ### Whitney's theorem -/

/-- A cycle on at least three vertices is `2`-connected.

Route: `IsCycle.exists_isCyclicWalk_eq` `Forest.lean:200` presents `C₀` as a cyclic walk, and
`IsCycle.exists_two_paths_of_ne` `Forest.lean:281` supplies the two arcs between any two of its
vertices, which is exactly what `le_cut` needs against a separator of `encard ≤ 1`. The `le_card`
field is `h3`. -/
lemma IsCycle.connGE_two (hC₀ : C₀.IsCycle) (h3 : 3 ≤ V(C₀).encard) : C₀.ConnGE 2 := by
  sorry

/-- **Attaching an ear preserves `2`-connectivity.** The inductive content of the converse half of
Whitney's theorem.

This is where `first_ne_last` is used, and it is exactly what fails for a cycle attached at one
vertex: two triangles glued at a point have a cut vertex.

Route: let `S` be a separator of `H ∪ P.toGraph` with `S.encard ≤ 1`. Since `P.first ≠ P.last`,
`S` misses one of them, say `P.first`. `H - S` is connected by `hH.le_cut`, and every internal
vertex of `P` reaches `P.first` along `P` avoiding `S` — or, if `S` meets `P`'s interior, along the
other side to `P.last`. Assemble with `ConnBetween.trans` `Connected/Vertex/Defs.lean:44`.
The `le_card` field is inherited from `hH` through `IsEar.le_union`. -/
theorem IsEar.connGE_two_union (hP : G.IsEar H P) (hle : H ≤ G) (hH : H.ConnGE 2) :
    (H ∪ P.toGraph).ConnGE 2 := by
  sorry

/-- **Whitney, converse half.** A graph with an ear decomposition is `2`-connected.

No finiteness and no looplessness: the ear list is finite by construction, and an ear is a path, so
no loop of `G` is ever reached — which is why the forward direction below needs `[G.Loopless]`.

Route: `IsCycle.connGE_two` for the base, then induction on the `EarBuild` derivation with
`IsEar.connGE_two_union` at each step, carrying `H ≤ G` along by `EarBuild.le_of_le`. -/
theorem IsEarDecomposition.connGE_two (h : G.IsEarDecomposition C₀ Ps) : G.ConnGE 2 := by
  sorry

/-- **Whitney, forward half.** Every finite loopless `2`-connected graph has an ear decomposition.

Route: `ConnGE.exists_isCycle_le` at any vertex (`ConnGE.lt_encard_vertexSet` supplies one) for
`C₀`, then the same measure as `ConnGE.ear_induction`, collecting the ears into a list instead of
consuming them; `ConnGE.exists_isEar` supplies each.
Obstruction: the eliminator discards its ears, so this cannot be routed through it — the recursion
has to be written out. -/
theorem ConnGE.exists_isEarDecomposition [G.Finite] [G.Loopless] (hG : G.ConnGE 2) :
    ∃ C₀ Ps, G.IsEarDecomposition C₀ Ps := by
  sorry

/-- **Whitney's theorem.** For a finite loopless graph, `2`-connectivity is exactly the existence of
an ear decomposition. -/
theorem connGE_two_iff_exists_isEarDecomposition [G.Finite] [G.Loopless] :
    G.ConnGE 2 ↔ ∃ C₀ Ps, G.IsEarDecomposition C₀ Ps :=
  ⟨fun hG ↦ hG.exists_isEarDecomposition, fun ⟨_, _, h⟩ ↦ h.connGE_two⟩

end Graph

end
