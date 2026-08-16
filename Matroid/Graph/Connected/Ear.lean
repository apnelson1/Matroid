module

public import Matroid.Graph.Forest
public import Matroid.Graph.Connected.Menger
public import Matroid.Graph.WList.TakeDrop.Pred
public import Matroid.Graph.Degree.Defs
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
    (by grind [ConnBetween.mono] : y₀ ∈ _) |>.exists_isPath
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

lemma neighbor_isSep (hx : x ∈ V(G)) (h : ∃ v ∈ V(G), v ≠ x ∧ ¬ G.Adj x v) :
    G.IsSep (N(G, x) \ {x}) := by
  obtain ⟨v, hv, hne, hna⟩ := h
  refine ⟨sdiff_subset.trans (G.neighbor_subset x), fun hconn ↦ hne ?_⟩
  suffices ∀ {y}, Relation.ReflTransGen (G - (N(G, x) \ {x})).Adj x y → y = x from
    this (connBetween_iff_reflTransGen_adj.mp
    (hconn.connBetween (x := x) (y := v) (by simp [hx]) (by simp [hv, hna]))).2
  intro y hy
  induction hy with
  | refl => rfl
  | tail _ hadj ih =>
    rw [ih, deleteVerts_adj_iff] at hadj
    obtain ⟨hAdj, -, hc⟩ := hadj
    simp only [mem_sdiff, mem_singleton_iff, not_and, not_not] at hc
    exact hc hAdj

/-! ### The base cycle -/

/-- A `2`-connected graph has, through each of its vertices, a cycle on at least three vertices.

The bound on `V(C₀)` matters: `IsCycle` `Forest.lean:167` is `Minimal (¬ IsForest ·)`, which admits
loops and digons, and neither is `2`-connected — so a decomposition rooted at one would have no
converse. No finiteness instance is needed: the cycle is built, not extracted.

Route: Since `G` is `2`-connected, there are at least 3 vertices. Let `x` and `y` be distinct
vertices in `V(G)`. Take some `G'` that satisfies `G'.IsSimpleficationOf G`, via
`exists_isSimpleficationOf_of_le` with `⊥` graph. `G'` is also `2`-connected, (
`connectivity_simplify`) so there are two internally disjoint paths from `x` to `y` in `G'`.
Then, appending the reverse of the second path to the first path, we get a tour and
`IsTour.dedup_tail_isCyclicWalk` gives a cycle that contains `x`. -/
theorem ConnGE.exists_isCycle_le (hG : G.ConnGE 2) (hx : x ∈ V(G)) :
    ∃ C₀, C₀.IsCycle ∧ C₀ ≤ G ∧ x ∈ V(C₀) ∧ 3 ≤ V(C₀).encard := by
  have : (⊥ : Graph α β).Simple := by rw [← noEdge_empty]; infer_instance
  obtain ⟨G', -, hsimp⟩ := exists_isSimpleficationOf_of_le (G := ⊥) (H := G) bot_le
  have hG' : G'.ConnGE 2 := (connGE_iff_le_connectivity 2).2 <|
    connectivity_simplify hsimp ▸ (connGE_iff_le_connectivity 2).1 hG
  have hx' : x ∈ V(G') := hsimp.isSpanningSubgraph.vertexSet_eq ▸ hx
  have hN : 2 ≤ (N(G', x) \ {x}).encard := by
    by_contra hlt
    have hle1 : (N(G', x) \ {x}).encard ≤ 1 := by
      rw [not_le] at hlt
      enat_to_nat!
      omega
    have hSle : ({x} ∪ (N(G', x) \ {x})).encard ≤ 2 := by
      refine (encard_union_le _ _).trans ?_
      rw [encard_singleton, add_comm]
      exact (add_le_add_left hle1 1).trans_eq (by norm_num)
    obtain ⟨y, hyV, hyS⟩ := diff_nonempty_of_encard_lt_encard <|
      hSle.trans_lt (hG'.lt_encard_vertexSet le_rfl)
    have hyx : y ≠ x := fun h ↦ hyS (by simp [h])
    exact hlt <| hG'.le_cut <| G'.neighbor_isSep hx'
      ⟨y, hyV, hyx, fun hadj ↦ hyS (Or.inr ⟨hadj, hyx⟩)⟩
  obtain ⟨u, hu, v, hv, huv⟩ := (one_lt_encard_iff_nontrivial.1
    (lt_of_lt_of_le (by simp : (1 : ℕ∞) < 2) hN))
  simp only [mem_sdiff, mem_singleton_iff] at hu hv
  obtain ⟨e1, he1⟩ := show G'.Adj x u from hu.1
  obtain ⟨e2, he2⟩ := show G'.Adj x v from hv.1
  have huV : u ∈ V(G' - ({x} : Set α)) := by
    simp [vertexSet_deleteVerts, he1.right_mem, hu.2]
  have hvV : v ∈ V(G' - ({x} : Set α)) := by
    simp [vertexSet_deleteVerts, he2.right_mem, hv.2]
  obtain ⟨Q, hQ, rfl, rfl⟩ := (hG'.deleteVert_connected hx').connBetween huV hvV |>.exists_isPath
  simp only [isPath_deleteVerts_iff, disjoint_singleton_right, mem_vertexSet_iff] at hQ
  have hP : G'.IsPath (cons x e1 Q) := cons_isPath_iff.2 ⟨he1, hQ.1, hQ.2⟩
  have hC : G'.IsCyclicWalk ((cons x e1 Q).concat e2 x) :=
    hP.concat_isCyclicWalk he2.symm <| by
      simp only [cons_edge, List.mem_cons, not_or]
      exact ⟨fun h ↦ huv (he1.right_unique (h ▸ he2)),
        fun he ↦ hQ.2 <| hQ.1.isWalk.vertex_mem_of_edge_mem he he2.inc_left⟩
  refine ⟨_, hC.toGraph_isCycle, hC.isWalk.toGraph_le.trans hsimp.le, ?_, ?_⟩
  · simp [toGraph_vertexSet]
  rw [toGraph_vertexSet, concat_vertexSet_eq, cons_vertexSet,
    insert_eq_of_mem (mem_insert _ _)]
  have hxuv : x ∉ ({Q.first, Q.last} : Set α) := by
    intro hxQ
    simp only [mem_insert_iff, mem_singleton_iff] at hxQ
    exact hxQ.elim (hu.2 ∘ Eq.symm) (hv.2 ∘ Eq.symm)
  have hcard : ({x, Q.first, Q.last} : Set α).encard = 3 := by
    rw [encard_insert_of_notMem hxuv, encard_pair huv]
    norm_num
  rw [← hcard]
  have hf : Q.first ∈ insert x V(Q) :=
    mem_insert_of_mem _ (mem_vertexSet_iff.2 (first_mem (w := Q)))
  have hl : Q.last ∈ insert x V(Q) :=
    mem_insert_of_mem _ (mem_vertexSet_iff.2 (last_mem (w := Q)))
  exact encard_le_encard <|
    insert_subset (mem_insert _ _) (insert_subset hf (singleton_subset_iff.2 hl))

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
theorem ConnGE.ear_induction [G.Finite] [G.Loopless] (hG : G.ConnGE 2) (hC₀G : C₀ ≤ G)
    (h3 : 3 ≤ V(C₀).encard) {motive : Graph α β → Prop} (base : motive C₀)
    (step : ∀ ⦃H P⦄, C₀ ≤ H → H ≤ G → G.IsEar H P → motive H → motive (H ∪ P.toGraph)) :
    motive G := by
  suffices ∀ n (H : Graph α β), (E(G) \ E(H)).ncard = n → C₀ ≤ H → H ≤ G → motive H → motive G from
    this _ C₀ rfl le_rfl hC₀G base
  intro n
  induction n using Nat.strong_induction_on with | h n ih => _
  rintro H rfl hC₀H hHG hH
  obtain rfl | hHne := eq_or_ne H G
  · exact hH
  have hV : V(H).Nontrivial := by
    have hnt : V(C₀).Nontrivial := one_lt_encard_iff_nontrivial.1 <|
      (by norm_num : (1 : ℕ∞) < 3).trans_le h3
    obtain ⟨x, hx, y, hy, hxy⟩ := hnt
    exact ⟨x, vertexSet_mono hC₀H hx, y, vertexSet_mono hC₀H hy, hxy⟩
  obtain ⟨P, hP⟩ := hG.exists_isEar hHG hV hHne
  refine ih (E(G) \ E(H ∪ P.toGraph)).ncard
    (ncard_lt_ncard ?_ (G.edgeSet_finite.subset sdiff_subset)) (H ∪ P.toGraph) rfl
    (hC₀H.trans hP.le_union) (hP.union_le hHG) (step hC₀H hHG hP hH)
  have hss : E(G) \ E(H ∪ P.toGraph) ⊆ E(G) \ E(H) := by
    intro e
    simp only [edgeSet_union, toGraph_edgeSet, mem_sdiff, mem_union, not_or, and_imp]
    exact fun heG heH _ ↦ ⟨heG, heH⟩
  obtain ⟨e, heP⟩ := hP.edgeSet_nonempty
  have heP' : e ∈ E(P.toGraph) := by simpa [toGraph_edgeSet] using heP
  refine hss.ssubset_of_not_subset fun hsub ↦ ?_
  have := hsub ⟨edgeSet_mono hP.toGraph_le heP', hP.edge_disjoint.notMem_of_mem_left heP⟩
  simp [edgeSet_union] at this
  exact this.2.2 heP

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
  induction h with
  | nil => exact le_rfl
  | cons hR _ ih => exact hR.le_union.trans ih

/- Route: induction on the derivation; `IsEar.union_le` at each `cons` re-establishes `≤ G`. -/
lemma EarBuild.le_of_le (h : G.EarBuild H Ps K) (hle : H ≤ G) : K ≤ G := by
  induction h with
  | nil => exact hle
  | cons hR _ ih => exact ih (hR.union_le hle)

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
lemma IsCycle.connGE_two (hC₀ : C₀.IsCycle) (h3 : 3 ≤ V(C₀).encard) : C₀.ConnGE 2 where
  le_card := Or.inr <| (by norm_num : (2 : ℕ∞) < 3).trans_le h3
  le_cut C hC := by
    by_contra hlt
    have hle1 : C.encard ≤ 1 := by
      contrapose! hlt
      convert Order.add_one_le_of_lt hlt
      · rfl
      · norm_num
    obtain rfl | ⟨x, rfl⟩ := encard_le_one_iff_eq.1 hle1
    · exact empty_isSep_iff.mp hC hC₀.connected
    obtain ⟨W, hW, rfl⟩ := hC₀.exists_isCyclicWalk_eq
    have hx : x ∈ W := by simpa [mem_vertexSet_iff] using hC.subset_vx (mem_singleton x)
    have hnt : W.Nontrivial := hW.nontrivial_iff_vertexSet_nontrivial.2 <|
      one_lt_encard_iff_nontrivial.1 <| (by norm_num : (1 : ℕ∞) < 3).trans_le (by simpa using h3)
    obtain ⟨P, hP, hPeq⟩ := hW.exists_isPath_toGraph_eq_delete_vertex hnt hx
    exact hC.not_connected <| hPeq ▸ hP.isWalk.toGraph_connected

lemma IsCycle.three_le_encard_of_simple [G.Simple] (hG : G.IsCycle) : 3 ≤ V(G).encard := by
  obtain ⟨x, hx⟩ := hG.nonempty
  have h := eDegree_le_encard hx
  rw [hG.regular_two hx] at h
  exact le_trans (by norm_num : (3 : ℕ∞) ≤ 2 + 1) h

lemma ConnGE.not_isForest (hG : G.ConnGE 2) : ¬ G.IsForest := by
  obtain ⟨x, hx⟩ := (hG.connected one_le_two).nonempty
  obtain ⟨C, hC, hle, -, -⟩ := hG.exists_isCycle_le hx
  exact not_isForest_iff_exists_isCycle.2 ⟨C, hC, hle⟩

lemma isCycle_iff_minimal_connGE_two [G.Simple] : G.IsCycle ↔ Minimal (·.ConnGE 2) G := by
  constructor
  · intro hG
    refine ⟨hG.connGE_two hG.three_le_encard_of_simple, ?_⟩
    exact fun H hH hle ↦ hG.le_of_le hH.not_isForest hle
  · intro hG
    refine ⟨hG.prop.not_isForest, ?_⟩
    intro H hH hle
    obtain ⟨C, hC, hCle⟩ := not_isForest_iff_exists_isCycle.1 hH
    have : C.Simple := ‹G.Simple›.mono (hCle.trans hle)
    exact (hG.le_of_le (hC.connGE_two hC.three_le_encard_of_simple) (hCle.trans hle)).trans hCle

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
    (H ∪ P.toGraph).ConnGE 2 where
  le_card := Or.inr <| (hH.lt_encard_vertexSet le_rfl).trans_le <|
    encard_le_encard (vertexSet_mono hP.le_union)
  le_cut S hS := by
    by_contra hlt
    have hle1 : S.encard ≤ 1 := by
      contrapose! hlt
      convert Order.add_one_le_of_lt hlt
      · rfl
      · norm_num
    obtain rfl | ⟨s, rfl⟩ := encard_le_one_iff_eq.1 hle1
    · exact empty_isSep_iff.mp hS <|
        (compatible_of_le_le hle hP.toGraph_le).union_connected_of_nonempty_inter
          (hH.connected one_le_two) hP.isPath.isWalk.toGraph_connected
          ⟨P.first, hP.first_mem, by simp [toGraph_vertexSet]⟩
    refine hS.not_connected ?_
    classical
    have hHconn : (H - ({s} : Set α)).Connected := by
      by_cases hsH : s ∈ V(H)
      · exact hH.deleteVert_connected hsH
      · rw [(deleteVerts_eq_self_iff _ _).mpr (by simpa [disjoint_singleton_right])]
        exact hH.connected one_le_two
    have ht : ∃ t ∈ ({P.first, P.last} : Set α), t ≠ s := by
      by_contra! h
      exact hP.first_ne_last <| (h _ (by simp)).trans (h _ (by simp)).symm
    obtain ⟨t, htends, hts⟩ := ht
    have htH : t ∈ V(H) := by
      simp only [mem_insert_iff, mem_singleton_iff] at htends
      obtain rfl | rfl := htends <;> simp [hP.first_mem, hP.last_mem]
    have htHS : t ∈ V(H - ({s} : Set α)) := by simp [htH, hts]
    have hHS_le : H - ({s} : Set α) ≤ (H ∪ P.toGraph) - ({s} : Set α) :=
      deleteVerts_mono_left hP.le_union _
    have hcompat : H.Compatible P.toGraph := compatible_of_le_le hle hP.toGraph_le
    have walk_sub {Q : WList α β} (hQ : G.IsPath Q) (hEQ : E(Q) ⊆ E(P))
        (hfirst : Q.first ∈ V(P)) (hdj : s ∉ V(Q)) :
        ((H ∪ P.toGraph) - ({s} : Set α)).ConnBetween Q.first Q.last := by
      have hU : (H ∪ P.toGraph).IsWalk Q :=
        hQ.isWalk.isWalk_le (hP.union_le hle)
          (hEQ.trans <| by
            rw [← toGraph_edgeSet]
            exact edgeSet_mono hcompat.right_le_union)
          (by simp [vertexSet_union, toGraph_vertexSet, hfirst])
      exact (isWalk_deleteVerts_iff.2 ⟨hU, disjoint_singleton_right.2 hdj⟩).connBetween_first_last
    have hP_to_t (x : α) (hxP : x ∈ P) (hxs : x ≠ s) :
        ((H ∪ P.toGraph) - ({s} : Set α)).ConnBetween x t := by
      have hxV : x ∈ V(P) := mem_vertexSet_iff.2 hxP
      have hinter : V(P.prefixUntilVertex x) ∩ V(P.suffixFromVertex x) =
          {(P.prefixUntilVertex x).last} :=
        ((prefixUntilVertex_append_suffixFromVertex P x).symm ▸
            hP.isPath).inter_eq_singleton_of_append
          (by rw [prefixUntilVertex_last hxP, suffixFromVertex_first hxP])
      rw [prefixUntilVertex_last hxP] at hinter
      have hpre : G.IsPath (P.prefixUntilVertex x) :=
        hP.isPath.prefix (prefixUntilVertex_isPrefix P x)
      have hsuf : G.IsPath (P.suffixFromVertex x) :=
        hP.isPath.suffix (suffixFromVertex_isSuffix P x)
      have hEpre : E(P.prefixUntilVertex x) ⊆ E(P) :=
        (prefixUntilVertex_isPrefix P x).edge_subset
      have hEsuf : E(P.suffixFromVertex x) ⊆ E(P) :=
        (suffixFromVertex_isSuffix P x).edge_subset
      have hfirst_pre : (P.prefixUntilVertex x).first ∈ V(P) := by
        simp [prefixUntilVertex_first]
      have hfirst_suf : (P.suffixFromVertex x).first ∈ V(P) := by
        simpa [suffixFromVertex_first hxP] using hxV
      have hHS (a b : α) (ha : a ∈ V(H - ({s} : Set α))) (hb : b ∈ V(H - ({s} : Set α))) :
          ((H ∪ P.toGraph) - ({s} : Set α)).ConnBetween a b :=
        (hHconn.connBetween ha hb).mono hHS_le
      have htends' : t = P.first ∨ t = P.last := by simpa using htends
      obtain rfl | rfl := htends'
      · by_cases hspre : s ∈ V(P.prefixUntilVertex x)
        · have hssuf : s ∉ V(P.suffixFromVertex x) := fun hs ↦ hxs <|
            (eq_of_mem_singleton (hinter ▸ ⟨hspre, hs⟩)).symm
          have hlasts : P.last ≠ s := by
            intro h
            exact hssuf <| mem_vertexSet_iff.2 <|
              h ▸ suffixFromVertex_last P x ▸ WList.last_mem
          have hxlast := walk_sub hsuf hEsuf hfirst_suf hssuf
          rw [suffixFromVertex_first hxP, suffixFromVertex_last] at hxlast
          exact hxlast.trans (hHS P.last P.first (by simp [hP.last_mem, hlasts])
            (by simp [hP.first_mem, hts]))
        · have hxfirst := walk_sub hpre hEpre hfirst_pre hspre
          rw [prefixUntilVertex_first, prefixUntilVertex_last hxP] at hxfirst
          exact hxfirst.symm
      · -- `t = P.last`
        by_cases hssuf : s ∈ V(P.suffixFromVertex x)
        · have hspre : s ∉ V(P.prefixUntilVertex x) := fun hs ↦ hxs <|
            (eq_of_mem_singleton (hinter ▸ ⟨hs, hssuf⟩)).symm
          have hfirsts : P.first ≠ s := by
            intro h
            exact hspre <| mem_vertexSet_iff.2 <|
              h ▸ prefixUntilVertex_first P x ▸ WList.first_mem
          have hxfirst := walk_sub hpre hEpre hfirst_pre hspre
          rw [prefixUntilVertex_first, prefixUntilVertex_last hxP] at hxfirst
          exact hxfirst.symm.trans
            (hHS P.first P.last (by simp [hP.first_mem, hfirsts]) (by simp [hP.last_mem, hts]))
        · have hxlast := walk_sub hsuf hEsuf hfirst_suf hssuf
          rw [suffixFromVertex_first hxP, suffixFromVertex_last] at hxlast
          exact hxlast
    refine connected_iff.2 ⟨⟨t, ?_⟩, fun u v hu hv ↦ ?_⟩
    · simp [vertexSet_deleteVerts, vertexSet_union, htH, hts]
    simp only [vertexSet_deleteVerts, vertexSet_union, mem_sdiff, mem_union,
      mem_singleton_iff] at hu hv
    have hto_t {w : α} (hw : w ∈ V(H) ∨ w ∈ V(P.toGraph)) (hws : w ≠ s) :
        ((H ∪ P.toGraph) - ({s} : Set α)).ConnBetween w t := by
      obtain hw | hw := hw
      · exact (hHconn.connBetween (by simp [hw, hws]) htHS).mono hHS_le
      · exact hP_to_t w (by simpa [toGraph_vertexSet, mem_vertexSet_iff] using hw) hws
    exact (hto_t hu.1 hu.2).trans (hto_t hv.1 hv.2).symm

/-- **Whitney, converse half.** A graph with an ear decomposition is `2`-connected.

No finiteness and no looplessness: the ear list is finite by construction, and an ear is a path, so
no loop of `G` is ever reached — which is why the forward direction below needs `[G.Loopless]`.

Route: `IsCycle.connGE_two` for the base, then induction on the `EarBuild` derivation with
`IsEar.connGE_two_union` at each step, carrying `H ≤ G` along by `EarBuild.le_of_le`. -/
theorem IsEarDecomposition.connGE_two (h : G.IsEarDecomposition C₀ Ps) : G.ConnGE 2 := by
  refine EarBuild.rec (motive := fun (A : Graph α β) _ B _ ↦ A ≤ G → A.ConnGE 2 → B.ConnGE 2)
    (fun _ _ hA ↦ hA) (fun hR _ ih hle hA ↦
      ih (hR.union_le hle) (hR.connGE_two_union hle hA))
    h.earBuild h.le (h.isCycle.connGE_two h.three_le)

/-- **Whitney, forward half.** Every finite loopless `2`-connected graph has an ear decomposition.

Route: `ConnGE.exists_isCycle_le` at any vertex (`ConnGE.lt_encard_vertexSet` supplies one) for
`C₀`, then the same measure as `ConnGE.ear_induction`, collecting the ears into a list instead of
consuming them; `ConnGE.exists_isEar` supplies each.
Obstruction: the eliminator discards its ears, so this cannot be routed through it — the recursion
has to be written out. -/
theorem ConnGE.exists_isEarDecomposition [G.Finite] [G.Loopless] (hG : G.ConnGE 2) :
    ∃ C₀ Ps, G.IsEarDecomposition C₀ Ps := by
  obtain ⟨x, hx⟩ := (hG.connected one_le_two).nonempty
  obtain ⟨C₀, hC₀, hC₀G, -, h3⟩ := hG.exists_isCycle_le hx
  suffices ∀ n (H : Graph α β), (E(G) \ E(H)).ncard = n →
      C₀ ≤ H → H ≤ G → ∃ Ps, G.EarBuild H Ps G by
    obtain ⟨Ps, hPs⟩ := this _ C₀ rfl le_rfl hC₀G
    exact ⟨C₀, Ps, hC₀, h3, hC₀G, hPs⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro H hn hC₀H hHG
    by_cases hHeq : H = G
    · rw [hHeq]
      exact ⟨List.nil, EarBuild.nil G⟩
    have hV : V(H).Nontrivial := by
      have hnt : V(C₀).Nontrivial := one_lt_encard_iff_nontrivial.1 <|
        (by norm_num : (1 : ℕ∞) < 3).trans_le h3
      obtain ⟨x, hx, y, hy, hxy⟩ := hnt
      exact ⟨x, vertexSet_mono hC₀H hx, y, vertexSet_mono hC₀H hy, hxy⟩
    obtain ⟨P, hP⟩ := hG.exists_isEar hHG hV hHeq
    refine (ih (E(G) \ E(H ∪ P.toGraph)).ncard ?_ (H ∪ P.toGraph) rfl
      (hC₀H.trans hP.le_union) (hP.union_le hHG)).elim fun Ps hPs ↦
        ⟨P :: Ps, EarBuild.cons hP hPs⟩
    rw [← hn]
    refine ncard_lt_ncard ?_ (G.edgeSet_finite.subset sdiff_subset)
    have hss : E(G) \ E(H ∪ P.toGraph) ⊆ E(G) \ E(H) := by
      intro e
      simp only [edgeSet_union, toGraph_edgeSet, mem_sdiff, mem_union, not_or, and_imp]
      exact fun heG heH _ ↦ ⟨heG, heH⟩
    obtain ⟨e, heP⟩ := hP.edgeSet_nonempty
    have heP' : e ∈ E(P.toGraph) := by simpa [toGraph_edgeSet] using heP
    exact hss.ssubset_of_not_subset fun hsub ↦ by
      have := hsub ⟨edgeSet_mono hP.toGraph_le heP', hP.edge_disjoint.notMem_of_mem_left heP⟩
      simp [edgeSet_union] at this
      exact this.2.2 heP

/-- **Whitney's theorem.** For a finite loopless graph, `2`-connectivity is exactly the existence of
an ear decomposition. -/
theorem connGE_two_iff_exists_isEarDecomposition [G.Finite] [G.Loopless] :
    G.ConnGE 2 ↔ ∃ C₀ Ps, G.IsEarDecomposition C₀ Ps :=
  ⟨fun hG ↦ hG.exists_isEarDecomposition, fun ⟨_, _, h⟩ ↦ h.connGE_two⟩

end Graph

end
