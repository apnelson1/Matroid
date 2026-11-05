module

public import Matroid.Graph.Forest
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
  exact hne

lemma IsEar.edgeSet_nonempty (h : G.IsEar H P) : E(P).Nonempty := h.nonempty.edgeSet_nonempty

lemma IsEar.toGraph_le (h : G.IsEar H P) : P.toGraph ≤ G := h.isPath.isWalk.toGraph_le

lemma IsEar.le_union (_h : G.IsEar H P) : H ≤ H ∪ P.toGraph := Graph.left_le_union ..

lemma IsEar.toGraph_le_union (h : G.IsEar H P) : P.toGraph ≤ H ∪ P.toGraph :=
  (Compatible.of_disjoint_edgeSet <| by simpa using h.edge_disjoint.symm).right_le_union

lemma IsEar.union_le (h : G.IsEar H P) (hle : H ≤ G) : H ∪ P.toGraph ≤ G :=
  Graph.union_le hle h.toGraph_le

/-- Attaching an ear strictly grows the subgraph. This is what makes the ear induction terminate. -/
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
prospective ear would have to be that vertex. -/
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
  obtain hnt | hnil := em (cons x e (Q.prefixUntil (· ∈ V(H)))).Nontrivial
  · exact hnt.disjoint_edgeSet_of_disjoint_internalVertexSet hle
      (cons_isWalk_iff.mpr ⟨(Q.prefixUntil_first (· ∈ V(H))) ▸ h, (hQ.1.prefix hpre).isWalk⟩)
      (disjoint_internalVertexSet_cons_prefixUntil Q (· ∈ V(H)) x e)
  rw [cons_nontrivial_iff, WList.not_nonempty_iff] at hnil
  rw [hnil.eq_nil_first, cons_edgeSet, nil_edgeSet, insert_empty_eq]
  exact disjoint_singleton_left.mpr heH

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

/-! ### Ear induction

The eliminator `Status.md` 4.2 consumes. The motive is non-dependent: 4.2 instantiates it as
`motive H := ∀ hle : H ≤ G, <face statement about D.restrict hle>` and recovers the `≤` its step
needs from `IsEar.union_le`. -/

/-- **Ear induction.** A property that holds of a cycle in `G` and survives attaching an ear holds
of `G` itself.

Pass `motive` explicitly. `@[elab_as_elim]` will otherwise infer it by abstracting `G` out of the
goal, and §4.2's motive `fun H ↦ ∀ _ : H ≤ G, …` has `G` occurring both as the abstracted variable
and free in the binder's type, which abstraction cannot produce. -/
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
    obtain ⟨x, hx, y, hy, hxy⟩ : V(C₀).Nontrivial := one_lt_encard_iff_nontrivial.1 <|
      (by norm_num : (1 : ℕ∞) < 3).trans_le h3
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
  simp only [edgeSet_union, toGraph_edgeSet, mem_sdiff, mem_union, mem_edgeSet_iff, not_or] at this
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

lemma EarBuild.le (h : G.EarBuild H Ps K) : H ≤ K := by
  induction h with
  | nil => exact le_rfl
  | cons hR _ ih => exact hR.le_union.trans ih

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

/-- **Attaching an ear preserves `2`-connectivity.** The inductive content of the converse half of
Whitney's theorem.

This is where `first_ne_last` is used, and it is exactly what fails for a cycle attached at one
vertex: two triangles glued at a point have a cut vertex. -/
theorem IsEar.connGE_two_union (hP : G.IsEar H P) (hle : H ≤ G) (hH : H.ConnGE 2) :
    (H ∪ P.toGraph).ConnGE 2 where
  le_card := Or.inr <| (hH.lt_encard_vertexSet le_rfl).trans_le <|
    encard_le_encard (vertexSet_mono hP.le_union)
  le_cut S hS := by
    by_contra! hlt
    replace hlt : S.encard ≤ 1 := by eomega
    obtain rfl | ⟨s, rfl⟩ := encard_le_one_iff_eq.1 hlt
    · exact empty_isSep_iff.mp hS <| compatible_of_le_le hle hP.toGraph_le
        |>.union_connected_of_nonempty_inter (hH.connected one_le_two)
        hP.isPath.isWalk.toGraph_connected ⟨P.first, hP.first_mem, by simp [toGraph_vertexSet]⟩
    have hHconn : (H - ({s} : Set α)).Connected := by
      obtain hsH | hsH := em (s ∈ V(H))
      · exact hH.deleteVert_connected hsH
      rw [(deleteVerts_eq_self_iff ..).mpr (by simpa [disjoint_singleton_right])]
      exact hH.connected one_le_two
    obtain ⟨t, htends, hts⟩ : ∃ t ∈ ({P.first, P.last} : Set α), t ≠ s := by
      by_contra! h
      exact hP.first_ne_last <| (h _ (by simp)).trans (h _ (by simp)).symm
    have hPfH : P.first ∈ V(H) := by simp [hP.first_mem]
    have hPlH : P.last ∈ V(H) := by simp [hP.last_mem]
    have ht : ∀ x ∈ V(H - ({s} : Set α)), ((H ∪ P.toGraph) - ({s} : Set α)).ConnBetween t x :=
      fun x hx ↦ hHconn.connBetween (show t ∈ _ by grind) hx |>.mono
        <| deleteVerts_mono_left hP.le_union _
    refine hS.not_connected ?_
    rw [connected_iff_exists_connBetween (show t ∈ _ by grind)]
    rintro v ⟨(hv1 | hvP), (hv2 : v ≠ s)⟩
    · exact ht v ⟨hv1, hv2⟩
    classical
    obtain h|h :=hP.isPath.isWalk.wellFormed.toGraph_deleteVerts_singleton_connBetween_first_or_last
      (x := s) (List.nodup_iff_count.mp hP.isPath.nodup _) (by simpa using hvP) hv2 <;>
      have := h.mono (deleteVerts_mono_left hP.toGraph_le_union _) |>.symm
    · exact ht _ ⟨hPfH, h.right_mem.2⟩ |>.trans this
    · exact ht _ ⟨hPlH, h.right_mem.2⟩ |>.trans this

/-- **Whitney, converse half.** A graph with an ear decomposition is `2`-connected.

No finiteness and no looplessness: the ear list is finite by construction, and an ear is a path, so
no loop of `G` is ever reached — which is why the forward direction below needs `[G.Loopless]`. -/
theorem IsEarDecomposition.connGE_two (h : G.IsEarDecomposition C₀ Ps) : G.ConnGE 2 :=
  EarBuild.rec (motive := fun (A : Graph α β) _ B _ ↦ A ≤ G → A.ConnGE 2 → B.ConnGE 2)
    (fun _ _ hA ↦ hA) (fun hR _ ih hle hA ↦ ih (hR.union_le hle) (hR.connGE_two_union hle hA))
    h.earBuild h.le (h.isCycle.connGE_two h.three_le)

/-- **Whitney, forward half.** Every finite loopless `2`-connected graph has an ear
decomposition. -/
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
    obtain rfl | hHeq := eq_or_ne H G
    · exact ⟨List.nil, EarBuild.nil H⟩
    have hV : V(H).Nontrivial := by
      obtain ⟨x, hx, y, hy, hxy⟩ : V(C₀).Nontrivial := one_lt_encard_iff_nontrivial.1 <|
        (by norm_num : (1 : ℕ∞) < 3).trans_le h3
      exact ⟨x, vertexSet_mono hC₀H hx, y, vertexSet_mono hC₀H hy, hxy⟩
    obtain ⟨P, hP⟩ := hG.exists_isEar hHG hV hHeq
    refine (ih (E(G) \ E(H ∪ P.toGraph)).ncard ?_ (H ∪ P.toGraph) rfl
      (hC₀H.trans hP.le_union) (hP.union_le hHG)).elim fun Ps hPs ↦ ⟨P :: Ps, EarBuild.cons hP hPs⟩
    rw [← hn]
    refine ncard_lt_ncard ?_ (G.edgeSet_finite.subset sdiff_subset)
    have hss : E(G) \ E(H ∪ P.toGraph) ⊆ E(G) \ E(H) := by
      intro e
      simp only [edgeSet_union, toGraph_edgeSet, mem_sdiff, mem_union, not_or, and_imp]
      exact fun heG heH _ ↦ ⟨heG, heH⟩
    obtain ⟨e, heP⟩ := hP.edgeSet_nonempty
    have heP' : e ∈ E(P.toGraph) := by simpa [toGraph_edgeSet] using heP
    refine hss.ssubset_of_not_subset fun hsub ↦ ?_
    have := hsub ⟨edgeSet_mono hP.toGraph_le heP', hP.edge_disjoint.notMem_of_mem_left heP⟩
    simp only [edgeSet_union, toGraph_edgeSet, mem_sdiff, mem_union, mem_edgeSet_iff,
      not_or] at this
    exact this.2.2 heP

/-- **Whitney's theorem.** For a finite loopless graph, `2`-connectivity is exactly the existence of
an ear decomposition. -/
theorem connGE_two_iff_exists_isEarDecomposition [G.Finite] [G.Loopless] :
    G.ConnGE 2 ↔ ∃ C₀ Ps, G.IsEarDecomposition C₀ Ps :=
  ⟨fun hG ↦ hG.exists_isEarDecomposition, fun ⟨_, _, h⟩ ↦ h.connGE_two⟩

end Graph

end
