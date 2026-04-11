import Matroid.Graph.Matching.Defs

variable {α β : Type*} {G H C : Graph α β} {S X Y : Set α} {M M' : Set β} {u v x y z : α} {e f : β}
  {hM : G.IsMatching M} {P P' : WList α β}

open Set symmDiff WList

namespace Graph

end Graph

namespace WList
open Graph

def pathCover : WList α β → Set α
| nil _ => ∅
| cons _ _ (nil v) => {v}
| cons _ _ (cons v _ w) => insert v (pathCover w)

lemma pathCover_subset (P : WList α β) : P.pathCover ⊆ V(P) := by
  match P with
  | nil _ => simp [pathCover]
  | cons _ _ (nil v) => simp [pathCover]
  | cons _ _ (cons v _ w) =>
    simp only [pathCover, cons_vertexSet]
    exact subset_trans (insert_subset_insert w.pathCover_subset) <| subset_insert ..

lemma pathCover_inc {P : WList α β} (hw : P.WellFormed) (he : e ∈ E(P)) :
    e ∈ E(P.toGraph, P.pathCover) := by
  match P with
  | nil _ => simp at he
  | cons u f (nil v) =>
    simp only [cons_edgeSet, nil_edgeSet, insert_empty_eq, mem_singleton_iff,
      mem_setIncEdges_iff] at he ⊢
    subst f
    use v, by simp [pathCover], u
    simp [-toGraph_cons, hw.toGraph_isLink, isLink_cons_iff']
  | cons u e₁ (cons v e₂ w) =>
    simp only [cons_edgeSet, mem_insert_iff, mem_edgeSet_iff] at he
    obtain rfl | rfl | h := he <;> simp only [pathCover, mem_setIncEdges_iff, mem_insert_iff,
    exists_eq_or_imp]
    · left
      use u
      simp [-toGraph_cons, hw, isLink_cons_iff']
    · left
      use w.first
      simp [-toGraph_cons, hw, isLink_cons_iff']
    right
    have hwW : w.WellFormed := hw.of_cons.of_cons
    obtain ⟨x, hx, y, h⟩ := pathCover_inc hwW h
    rw [hwW.toGraph_isLink] at h
    use x, hx, y
    simp [-toGraph_cons, hw.toGraph_isLink, isLink_cons_iff', h]

lemma pathCover_isCover (hw : P.WellFormed) : P.toGraph.IsCover P.pathCover where
  subset := by
    rw [toGraph_vertexSet]
    exact P.pathCover_subset
  cover e he := pathCover_inc hw (by simpa using he)

lemma pathCover_ncard {P : WList α β} (hw : P.vertex.Nodup) :
    P.pathCover.ncard = V(P).ncard / 2 := by
  match P with
  | nil _ => simp [pathCover]
  | cons _ _ (nil v) =>
    simp only [pathCover, ncard_singleton, cons_vertexSet, nil_vertexSet]
    simp only [cons_vertex, nil_vertex, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_false_eq_true, List.nodup_nil, and_self, and_true] at hw
    rw [ncard_pair hw]
  | cons _ _ (cons v _ w) =>
    simp only [cons_vertex, List.nodup_cons, List.mem_cons, mem_vertex, not_or, pathCover,
      cons_vertexSet] at hw ⊢
    obtain ⟨⟨hne, huw⟩, hvw, hw⟩ := hw
    have : w.pathCover.Finite := w.vertexSet_finite.subset w.pathCover_subset
    rw [ncard_insert_of_notMem (fun h ↦ hvw <| w.pathCover_subset h) this,
      ncard_insert_of_notMem (by simp [hne, huw]) (by simp),
      ncard_insert_of_notMem (by simpa) (by simp), pathCover_ncard hw]
    omega

def pathMatching : WList α β → Set β
| nil _ => ∅
| cons _ e (nil _) => {e}
| cons _ e (cons _ _ w) => insert e (pathMatching w)

lemma pathMatching_subset (P : WList α β) : P.pathMatching ⊆ E(P) := by
  match P with
  | nil _ => simp [pathMatching]
  | cons _ e (nil _) => simp [pathMatching]
  | cons _ e (cons _ _ w) =>
    simp only [pathMatching, cons_edgeSet]
    exact insert_subset_insert <| w.pathMatching_subset.trans <| subset_insert ..


-- this is so annoying, `toGraph` is _slightly_ off of being "inductively do `addEdge`".
lemma toGraph_cons_addEdge {w} (h : (cons u e w).WellFormed) :
    (cons u e w).toGraph = w.toGraph.addEdge e u w.first := by
  simp only [toGraph_cons, Graph.addEdge]
  have compat : Compatible (Graph.singleEdge u w.first e) w.toGraph := by
    refine (cons u e w).toGraph.compatible_of_le_le ?_ ?_
    · simp [-toGraph_cons]
      -- simp leaves us in this state:
      -- (cons u e w).toGraph.IsLink e u w.first
      rw [h.toGraph_isLink]
      -- grind fails this??
      exact IsLink.cons_left u e w
    · -- TODO: not a simp lemma?
      simp [toGraph_cons]
  rw [compat.union_comm]

end WList

namespace Graph

@[grind =]
lemma addEdge_isLink_iff' {a b} :
    (G.addEdge e a b).IsLink f x y ↔ (f = e ∧ s(a, b) = s(x, y)) ∨ (f ≠ e ∧ G.IsLink f x y) := by
  classical
  rw [← deleteEdge_addEdge, addEdge_isLink_iff]
  grind

@[grind =]
lemma addEdge_inc_self_iff :
    (G.addEdge e x y).Inc e u ↔ u = x ∨ u = y := by
  refine ⟨?_, ?_⟩
  · rintro ⟨v, h⟩
    have := G.addEdge_isLink e x y
    exact h.left_eq_or_eq this
  rintro (rfl|rfl)
  · exact ⟨y, G.addEdge_isLink e u y⟩
  exact ⟨x, G.addEdge_isLink e x u |>.symm⟩

@[simp, grind .]
lemma addEdge_inc_left : (G.addEdge e x y).Inc e x :=
  G.addEdge_isLink e x y |>.inc_left

@[simp, grind .]
lemma addEdge_inc_right : (G.addEdge e x y).Inc e y :=
  G.addEdge_isLink e x y |>.inc_right

@[grind =]
lemma addEdge_inc_iff :
    (G.addEdge e x y).Inc f u ↔ (f = e ∧ (u = x ∨ u = y)) ∨ (f ≠ e ∧ G.Inc f u) := by
  unfold Inc
  refine ⟨?_, ?_⟩
  · grind
  rintro (h|h)
  · obtain ⟨rfl, (rfl|rfl)⟩ := h
      <;> [use y; use x]
      <;> grind
  obtain ⟨hne, v, h⟩ := h
  use v; grind


-- not sure if you add grind patterns to these sorts of things
-- @[grind =]
lemma addEdge_edgeRestrict_commutes :
    (G.addEdge e x y) ↾ (insert e M) = (G ↾ M).addEdge e x y := by
  apply ext_inc
  · simp
  intro f u
  grind
  -- holy!! `grind` is so powerful

@[simp, grind .]
lemma edgeRestrict_eDegree_le_eDegree {F : Set β} : (G ↾ F).eDegree x ≤ G.eDegree x := by
  -- special case of mono
  exact eDegree_mono edgeRestrict_le x

@[simp, grind .]
lemma ENat.le_zero {i : ℕ∞} : i ≤ 0 ↔ i = 0 := by
  refine ⟨?_, ?_⟩ <;> enat_to_nat! <;> omega

lemma mem_edgeSet_iff_exists_inc : e ∈ E(G) ↔ ∃ x, G.Inc e x := by
  refine ⟨?_, ?_⟩
  · intro he
    obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
    refine ⟨x, hxy.inc_left⟩
  · grind only [→ Inc.edge_mem]

lemma Compatible.union_incEdges_eq (h : G.Compatible H) (x : α) :
    E(G ∪ H, x) = E(G, x) ∪ E(H, x) := by
  ext e
  simp only [mem_incEdges_iff, h.union_inc_iff, mem_union]

lemma union_incEdges_eq (hdj : Disjoint E(G) E(H)) (x : α) :
    E(G ∪ H, x) = E(G, x) ∪ E(H, x) :=
  Compatible.of_disjoint_edgeSet hdj |>.union_incEdges_eq x

@[simp, grind =]
lemma singleEdge_incEdges_left (x y : α) (e : β) : E(Graph.singleEdge x y e, x) = {e} := by
  ext f
  simp

@[simp, grind =]
lemma singleEdge_incEdges_right (x y : α) (e : β) : E(Graph.singleEdge x y e, y) = {e} := by
  ext f
  simp

@[simp, grind =]
lemma singleEdge_incEdges_of_ne (e : β) (hux : u ≠ x) (huy : u ≠ y) :
    E(Graph.singleEdge x y e, u) = ∅ := by
  ext f
  grind

@[simp, grind =]
lemma singleEdge_incEdges_encard_left (x y : α) (e : β) :
    E(Graph.singleEdge x y e, x).encard = 1 := by
  simp

@[simp, grind =]
lemma singleEdge_incEdges_encard_right (x y : α) (e : β) :
    E(Graph.singleEdge x y e, y).encard = 1 := by
  simp

@[simp, grind =]
lemma singleEdge_incEdges_encard_of_ne (e : β) (hux : u ≠ x) (huy : u ≠ y) :
    E(Graph.singleEdge x y e, u).encard = 0 := by
  -- TODO: grind tags for all of ENat?
  grind [encard_empty]

@[simp, grind =]
lemma addEdge_incEdges_left (he : e ∉ E(G)) (x y : α) :
    E(G.addEdge e x y, x) = insert e E(G, x) := by
  simp only [Graph.addEdge]
  rw [union_incEdges_eq _ x] <;> grind

@[simp, grind =]
lemma addEdge_incEdges_right (he : e ∉ E(G)) (x y : α) :
    E(G.addEdge e x y, y) = insert e E(G, y) := by
  simp only [Graph.addEdge]
  rw [union_incEdges_eq _ y] <;> grind

@[simp, grind =]
lemma addEdge_incEdges_of_ne (he : e ∉ E(G)) (hux : u ≠ x) (huy : u ≠ y) :
    E(G.addEdge e x y, u) = E(G, u) := by
  simp only [Graph.addEdge]
  rw [union_incEdges_eq _ u] <;> grind

@[simp, grind =]
lemma addEdge_incEdges_encard_left (he : e ∉ E(G)) (x y : α) :
    E(G.addEdge e x y, x).encard = E(G, x).encard + 1 := by
  -- TODO: grind tags?
  grind [encard_eq_add_one_iff]

@[simp, grind =]
lemma addEdge_incEdges_encard_right (he : e ∉ E(G)) (x y : α) :
    E(G.addEdge e x y, y).encard = E(G, y).encard + 1 := by
  grind only [encard_eq_add_one_iff, = IncEdges.eq_1, = addEdge_incEdges_right, = mem_incEdges_iff,
    → Inc.edge_mem]

@[simp, grind =]
lemma addEdge_incEdges_encard_of_ne (he : e ∉ E(G)) (hux : u ≠ x) (huy : u ≠ y) :
    E(G.addEdge e x y, u).encard = E(G, u).encard := by
  grind only [= IncEdges.eq_1, = addEdge_incEdges_of_ne]

@[simp, grind .]
lemma incEdges_encard_mono (hle : G ≤ H) (x : α) : E(G, x).encard ≤ E(H, x).encard := by
  grind only [encard_le_encard, incEdges_mono]

@[simp, grind .]
lemma edgeRestrict_incEdges_encard_le_encard (F : Set β) (x : α) :
    E(G ↾ F, x).encard ≤ E(G, x).encard := by
  grind

@[simp, grind .]
lemma incEdges_addEdge_of_notMem_left (e : β) (x y : α) (hx : x ∉ V(G)) :
    E(G.addEdge e x y, x) = {e} := by
  grind only [= mem_incEdges_iff, = mem_singleton_iff, = addEdge_inc_iff, → Inc.vertex_mem]

@[simp, grind .]
lemma incEdges_addEdge_of_notMem_right (e : β) (x y : α) (hy : y ∉ V(G)) :
    E(G.addEdge e x y, y) = {e} := by
  grind only [= mem_incEdges_iff, = mem_singleton_iff, = addEdge_inc_iff, → Inc.vertex_mem]

private
lemma gah (hM : G.IsMatching M) (hx : E(G ↾ M, x).encard = 0) (hy : E(G ↾ M, y).encard = 0)
    (he : e ∉ M) :
    (G.addEdge e x y).IsMatching (insert e M) := by
  refine isMatching_of_encard_incEdges_le_one ?_ ?_ ?_
  · grind [hM.subset]
  simp only [addEdge_vertexSet, mem_union, mem_insert_iff, mem_singleton_iff]
  intro u
  have he' : e ∉ E(G ↾ M) := by grind
  obtain (rfl|hux) := em (u = x)
  · -- u = x
    have := addEdge_incEdges_encard_left he'
    rw [addEdge_edgeRestrict_commutes, this, hx]
    enat_to_nat; omega
  obtain (rfl|huy) := em (u = y)
  · -- u = y
    have := addEdge_incEdges_encard_right he'
    rw [addEdge_edgeRestrict_commutes, this, hy]
    enat_to_nat; omega
  rintro ((rfl|rfl)|hu)
    <;> [contradiction ; contradiction ; skip]
  have := hM.incEdges_encard_le_one u
  rw [isMatching_iff_edgeRestrict_isMatching] at hM
  rw [addEdge_edgeRestrict_commutes, addEdge_incEdges_encard_of_ne he' hux huy]
  assumption

private
lemma gah2 (hM : G.IsMatching M) (he : e ∉ M) : (G.addEdge e x y).IsMatching M := by
  rw [isMatching_iff_edgeRestrict_isMatching] at hM
  refine IsMatching.mono_left (G := G ↾ M) ?_ hM
  rw [← deleteEdge_addEdge]
  transitivity (G ＼ {e})
  · rw [edgeDelete_eq_edgeRestrict]
    -- TODO: needs grind tag
    refine G.edgeRestrict_mono_right (by grind [hM.subset])
  refine le_addEdge ?_
  grind

lemma IsPath.pathMatching_isMatching (hP : G.IsPath P) : P.toGraph.IsMatching P.pathMatching := by
  fun_induction WList.pathMatching with
  | case1 => simp
  | case2 => simp
  | case3 u e v f w IH =>
    have w_isPath : G.IsPath w := by simp at hP; grind
    specialize IH w_isPath
    have : (cons u e (cons v f w)).toGraph = (cons v f w).toGraph.addEdge e u v := by
      -- TODO: should have `IsPath.wellformed`
      simp [toGraph_cons_addEdge hP.isWalk.wellFormed]
    rw [this]; clear this
    have hP' : G.IsPath (cons v f w) := by
      rw [cons_isPath_iff] at hP; grind
    have f_not_in : f ∉ w.pathMatching := by
      grind [hP.edge_nodup, pathMatching_subset]
    refine gah ?_ ?_ ?_ ?_
    · rw [toGraph_cons_addEdge hP'.isWalk.wellFormed]
      refine gah2 IH f_not_in
    · have : u ∉ V((cons v f w).toGraph) := by
        simp at hP ⊢; grind
      grw [← ENat.le_zero, encard_inc_le_eDegree, ENat.le_zero]
      exact eDegree_eq_zero_of_notMem this
    · simp only [encard_eq_zero, incEdges_edgeRestrict]
      have v_not_in : v ∉ V(w.toGraph) := by
        -- TODO: needs grind tags
        grind [cons_isPath_iff, toGraph_vertexSet]
      rw [toGraph_cons_addEdge hP'.isWalk.wellFormed,
        incEdges_addEdge_of_notMem_left _ _ _ v_not_in]
      grind
    · grind [hP.edge_nodup, pathMatching_subset]

lemma pathMatching_ncard {P : WList α β} (hvertex_nodup : P.vertex.Nodup)
    (hedge_nodup : P.edge.Nodup) :
    P.pathMatching.ncard = V(P).ncard / 2 := by
  match P with
  | nil _ => simp [pathMatching]
  | cons u _ (nil v) =>
    simp_all [pathMatching]
  | cons u e (cons v f w) =>
    simp_all [pathMatching]
    have IH := pathMatching_ncard (P := w) (by grind) (by grind)
    have pathMatching_finite : w.pathMatching.Finite :=
      w.edgeSet_finite.subset w.pathMatching_subset
    rw [ncard_insert_of_notMem (hs := pathMatching_finite)]
    · omega
    grind [w.pathMatching_subset]

lemma IsPathGraph.konig (h : G.IsPathGraph) : τ(G) = ν(G) := by
  have := h.finite
  obtain ⟨P, hP, rfl⟩ := h
  refine matchingNumber_le_coverNumber.antisymm' <| le_trans (b := ↑(V(P).ncard / 2)) ?_ ?_
  · rw [← pathCover_ncard hP.nodup,
    (this.vertexSet_finite.subset <| by simpa using P.pathCover_subset).cast_ncard_eq]
    exact (pathCover_isCover hP.isWalk.wellFormed).le_encard
  rw [← pathMatching_ncard hP.nodup hP.edge_nodup,
    (this.edgeSet_finite.subset <| by simpa using P.pathMatching_subset).cast_ncard_eq]
  exact hP.pathMatching_isMatching.encard_le

lemma pathCover_odd {w : WList α β} (h : Odd w.length) : w.last ∈ w.pathCover := by
  match w with
  | nil _ => simp at h
  | cons _ _ (nil v) =>
    simp [pathCover]
  | cons u e (cons v f w) =>
    replace h : Odd w.length := by
      -- TODO: grind tag
      grind [cons_length]
    have IH := pathCover_odd h
    grind [pathCover]

lemma IsCycle.konig (hB : G.Bipartite) (h : G.IsCycle) : τ(G) = ν(G) := by
  -- bipartite, so only even cycles
  have G_finite := h.finite
  rw [isCycle_iff_exists_isCyclicWalk_eq] at h
  obtain ⟨C, hC, rfl⟩ := h
  have C_even := hB.length_even_of_isWalk_isClosed hC.isWalk hC.isClosed
  have C_nontrivial : C.Nontrivial := by
    -- TODO: grind tags
    rw [← two_le_length_iff]
    have : 1 ≤ C.length := by grind [hC.nonempty, one_le_length_iff]
    grind
  let P := C.tail
  have P_isPath := hC.tail_isPath
  have pathCover := pathCover_isCover P_isPath.isWalk.wellFormed
  replace pathCover : C.toGraph.IsCover C.tail.pathCover := by
    constructor
    · refine le_trans pathCover.subset ?_
      simp only [toGraph_vertexSet, le_eq_subset]
      -- TODO: there should be some `∀ (w : WList α β), V(w.tail) ⊆ V(w)`
      refine WList.IsSuffix.subset (tail_isSuffix C)
    have := pathCover.cover
    intro e he
    simp
    obtain (heC|heC) := em (e ∈ E(C.tail.toGraph))
    · apply this at heC
      obtain ⟨x, hx, hinc⟩ := heC
      refine ⟨x, hx, ?_⟩
      refine hinc.of_le P_isPath.isWalk.toGraph_le
    cases C with
    | nil => simp at C_nontrivial
    | cons u f w =>
    replace heC : e = f := by
      simp at heC he
      grind
    subst f
    have w_odd : Odd w.length := by grind [cons_length]
    refine ⟨u, ?_, by simp [-toGraph_cons, hC.isWalk.wellFormed.toGraph_inc]⟩
    simp [show (u = w.last) by (have := hC.isClosed; simp at this; assumption)]
    exact pathCover_odd w_odd
  refine matchingNumber_le_coverNumber.antisymm' <| le_trans (b := ↑(V(C.tail).ncard / 2)) ?_ ?_
  · rw [← pathCover_ncard hC.nodup]
    have : C.tail.pathCover.Finite := by
      have : V(C.tail) ⊆ V(C) := WList.IsSuffix.subset (tail_isSuffix C)
      exact G_finite.vertexSet_finite.subset <| by grind [toGraph_vertexSet, C.tail.pathCover_subset]
    rw [this.cast_ncard_eq]
    grw [← pathCover.le_encard]
  rw [← pathMatching_ncard P_isPath.nodup P_isPath.edge_nodup]
  have : C.tail.pathMatching.Finite := by
    have : E(C.tail) ⊆ E(C) := WList.IsSuffix.edge_subset (tail_isSuffix C)
    exact G_finite.edgeSet_finite.subset <| by grind [toGraph_edgeSet, C.tail.pathMatching_subset]
  grw [this.cast_ncard_eq, P_isPath.pathMatching_isMatching.encard_le]
  refine matchingNumber_mono ?_
  exact P_isPath.isWalk.toGraph_le

/-!
### König's Matching Theorem
Source: Romeo Rizzi (2000) [cite: 2]

Theorem: Let G be a bipartite graph. Then ν(G) = τ(G).

Proof:
Let G be a minimal counterexample. Then G is connected, is not a circuit, nor a path. [cite: 14]
So, G has a node of degree at least 3. Let u be such a node and v one of its neighbors. [cite: 15]

Case 1: If ν(G \ v) < ν(G). [cite: 16]
By minimality, G \ v has a cover W' with |W'| < ν(G). [cite: 16]
Hence, W' ∪ {v} is a cover of G with cardinality ν(G) at most. [cite: 17]

Case 2: Assume there exists a maximum matching M of G having no edge incident at v. [cite: 18]
Let f be an edge of G \ M incident at u but not at v. [cite: 18]
Let W' be a cover of G \ f with |W'| = ν(G). [cite: 22]
Since no edge of M is incident at v, it follows that W' does not contain v. [cite: 22]
So W' contains u and is a cover of G. [cite: 22]
-/
theorem Konig'sTheorem [H.Simple] [H.Finite] (hB : H.Bipartite) : τ(H) = ν(H) := by
  refine of_not_exists_minimal (P := fun H ↦ τ(H) = ν(H)) fun G hle _ hMin ↦ ?_
  push_neg at hMin
  replace hB := hB.of_le hle
  have _ : G.Loopless := hB.loopless
  have _ : G.Simple := Simple.mono ‹_› hle
  -- trivial case: `G` is empty.
  obtain (hempty|hnonempty) := em' (V(G).Nonempty)
  · replace hempty : V(G).encard = 0 := by simpa only [encard_eq_zero, ← not_nonempty_iff_eq_empty]
    have hτ : τ(G) = 0 := by have := G.coverNumber_le_vertexSet_encard; enat_to_nat! <;> omega
    have hν : ν(G) = 0 := by
      have := G.matchingNumber_le_coverNumber; enat_to_nat! <;> omega
    grind only [hMin.1]
  simp [minimal_iff_forall_lt] at hMin
  have hcon : G.Connected := by
    /- Otherwise, by def of `Connected`, there is a strictly smaller component of `G`.
    `τ` and `ν` are additive over the components so at least one component must have `τ` or `ν`
    different.
    That component is a smaller counterexample to the theorem, contradicting minimality.-/
    by_contra! hcon
    apply nonempty_separation_of_not_connected hnonempty at hcon
    obtain ⟨S⟩ := hcon
    have hdisj := S.induce_stronglyDisjoint
    have right_lt := S.induce_right_lt
    have left_eq : τ(G[S.left]) = ν(G[S.left]) := hMin.2 S.induce_left_lt
    have right_eq : τ(G[S.right]) = ν(G[S.right]) := hMin.2 S.induce_right_lt
    refine hMin.1 ?_
    rw [S.eq_union, coverNumber_union hdisj, matchingNumber_union hdisj, left_eq, right_eq]

  obtain ⟨u, hu, hdegu⟩ : ∃ u ∈ V(G), 3 ≤ G.degree u := by
    /- Otherwise, by `isPathGraph_or_isCycleGraph_of_maxDegreeLE`, `G` would be a path or cycle,
    By lemmas above, any path graph or cycle graph has `τ = ν`, contradicting `τ ≠ ν` assumption.-/
    by_contra! bad
    replace bad : G.MaxDegreeLE 2 := by
      rw [maxDegreeLE_iff]
      grind only
    refine hMin.1 ?_
    obtain (h|h) := hcon.isPathGraph_or_isCycle_of_maxDegreeLE bad
      <;> [exact IsPathGraph.konig ‹_›; exact IsCycle.konig ‹_› ‹_›]
  obtain ⟨e, v, huv⟩ := G.degree_ne_zero_iff_inc (v := u) |>.mp (by omega)

  /-
  Case 1: If ν(G \ v) < ν(G). [cite: 16]
  By minimality, G \ v has a cover W' with |W'| < ν(G). [cite: 16]
  Hence, W' ∪ {v} is a cover of G with cardinality ν(G) at most. [cite: 17]
  -/
  obtain (ν_ne|ν_eq) := em' (ν(G - v) = ν(G))
  · have ν_le : ν(G - v) ≤ ν(G) :=
      matchingNumber_mono vertexDelete_le
    obtain ⟨W', hW'⟩ := (G - v).exists_isMinCover
    have hlt : G - v < G := vertexDelete_singleton_lt huv.right_mem
    have W_cover : G.IsCover (insert v W') := by
      refine ⟨by grind [huv.right_mem, hW'.subset, vertexSet_mono hlt.le], ?_⟩
      intro e he
      simp only [mem_setIncEdges_iff, mem_insert_iff, exists_eq_or_imp]
      rw [← G.vertexDelete_singleton_edgeSet v] at he
      obtain (he|he) := he
        <;> [right; left]
      · exact setIncEdges_mono hlt.le _ <| hW'.cover he
      exact he
    have W_encard : (insert v W').encard = W'.encard + 1 := by
      refine W'.encard_insert_of_notMem ?_
      have := hW'.subset
      simp at this
      grind only [= subset_def, = mem_diff, = mem_singleton_iff]
    have := W_cover.le_encard
    rw [W_encard, hW'.encard, hMin.2 hlt] at this
    have hle := G.matchingNumber_le_coverNumber
    have τ_finite : τ(G) < ⊤ := by
      have : V(G).encard < ⊤ := encard_lt_top_iff.mpr ‹G.Finite›.vertexSet_finite
      have := G.coverNumber_le_vertexSet_encard
      enat_to_nat!
    enat_to_nat! <;> omega

  /-
  Case 2: Assume there exists a maximum matching M of G having no edge incident at v. [cite: 18]
  Let f be an edge of G \ M incident at u but not at v. [cite: 18]
  Let W' be a cover of G \ f with |W'| = ν(G). [cite: 22]
  Since no edge of M is incident at v, it follows that W' does not contain v. [cite: 22]
  So W' contains u and is a cover of G. [cite: 22]
  -/
  obtain ⟨M, hM⟩ := (G - v).exists_isMaxMatching
  have hMG : G.IsMaxMatching M := by
    refine (hM.mono_left vertexDelete_le).isMaxMatching_of_encard_eq ?_
    rw [hM.encard, ν_eq]
  have no_touch {f} (hf : f ∈ M) : ¬ G.Inc f v := by
    have := hM.subset hf
    simp at this
    obtain ⟨x, y, hxy⟩ := this
    intro bad
    obtain ⟨w, hw⟩ := bad
    grind only [→ IsLink.inc_left, Inc.eq_or_eq_of_isLink]

  -- Let f be an edge of G \ M incident at u but not at v.
  obtain neighbors : 1 < N(G ＼ M, u).ncard := by
    rw [← degree_eq_ncard_adj, degree_eq_ncard_inc]
    have bwah : E(G, u) = E(G ＼ M, u) ∪ (E(G, u) ∩ M) := by
      simp
    have hdisj : Disjoint E(G ＼ M, u) (E(G, u) ∩ M) := by
      grind
    have fin1 : E(G ＼ M, u).Finite :=
      LocallyFinite.finite u
    have GMu_deg : E(G ↾ M, u).encard ≤ ↑(1 : ℕ) := hMG.incEdges_encard_le_one u
    rw [encard_le_coe_iff_finite_ncard_le, incEdges_edgeRestrict] at GMu_deg
    rw [degree_eq_ncard_inc, bwah, ncard_union_eq hdisj fin1 GMu_deg.1] at hdegu
    omega
  obtain ⟨x, hux, hxv_ne⟩ := exists_ne_of_one_lt_ncard neighbors v
  clear neighbors
  obtain ⟨f, hf⟩ := hux

  -- "Let W' be a cover of G \ f with |W'| = ν(G)"
  -- f ∈ E(G \ M), so M ⊆ E(G \ f), so M is still a valid matching for (G \ f),
  -- so ν(G) ≤ ν(G \ f) ≤ ν(G), so ν(G \ f) = ν(G).
  -- Since (G \ f) < G, therefore by minimality assumption τ(G \ f) = ν(G \ f),
  -- so we can find such a cover.
  have hMG' : (G ＼ {f}).IsMatching M := by
    refine hMG.anti_left edgeDelete_le ?_
    have := hf.edge_mem
    simp at this ⊢
    grind [hMG.subset]

  have G'_matchingNumber : ν(G ＼ {f}) = ν(G) := by
    refine le_antisymm (matchingNumber_mono edgeDelete_le) ?_
    rw [← hMG.encard]
    exact hMG'.encard_le
  have hlt : G ＼ {f} < G := by
    refine lt_of_le_of_edgeSet_ssubset edgeDelete_le ?_
    rw [ssubset_iff_subset_ne]
    refine ⟨edgeSet_mono edgeDelete_le, ?_⟩
    simp
    exact edgeSet_mono edgeDelete_le hf.edge_mem
  have G'_coverNumber : τ(G ＼ {f}) = ν(G) := by
    rw [← G'_matchingNumber]
    refine hMin.2 hlt
  obtain ⟨W', hW'⟩ := (G ＼ {f}).exists_isMinCover

  -- "Since no edge of M is incident at v, it follows that W' does not contain v.
  -- M is a matching for G \ f; each edge of M must have one endpoint in W'.
  -- Moreover, each edge contributes a unique vx to W', otherwise two edges in M would
  -- share a vertex.
  -- Since |M| = ν(G) = |W'|, therefore W' ⊆ V(G, M).
  -- And since no edge of M is incident at v, therefore v ∉ V(G, M), therefore v ∉ W'.
  have hvW' : v ∉ W' := by
    have : W' ⊆ V(G, M) := by
      intro x hxW'
      rw [← hMG'.mapToCover_range_eq_of_encard_eq hW'.toIsCover (by grind [hW'.encard, hMG.encard])]
        at hxW'
      simp only [mem_image, mem_range] at hxW'
      obtain ⟨x', ⟨e, he⟩, rfl⟩ := hxW'
      have := hMG'.mapToCover_inc hW'.toIsCover e.2
      rw [he] at this
      simp only [mem_incVertexSet_iff]
      refine ⟨e, e.2, this.of_le edgeDelete_le⟩
    intro bad
    apply this at bad
    simp only [mem_incVertexSet_iff] at bad
    obtain ⟨e, heM, he⟩ := bad
    exact no_touch heM he

  -- "So W' contains u and is a cover of G."
  -- Since uv ∈ E(G), and f ≠ uv, therefore uv ∈ E(G \ f).
  -- Since W' doesn't contain v, it must therefore contain u.
  have huW' : u ∈ W' := by
    have hne : e ≠ f := by
      rintro rfl
      have := hf.of_le edgeDelete_le |>.right_unique huv
      contradiction
    have heG' : e ∈ E(G ＼ {f}) := by grind [edgeDelete_edgeSet]
    grind only [hW'.mem_or_mem_of_isLink (huv.of_le_of_mem edgeDelete_le heG')]
  -- So W' also covers f (since f = ux), so W' is a cover of G
  have hW'G : G.IsCover W' := by
    refine ⟨?_, ?_⟩
    · simpa using hW'.subset
    intro edge hedge
    obtain (h|h) := em' (edge = f)
    · replace h : edge ∈ E(G ＼ {f}) := by grind
      apply hW'.cover at h
      exact setIncEdges_mono edgeDelete_le _ h
    symm at h
    obtain rfl := h
    refine ⟨u, huW', ?_⟩
    exact hf.of_le edgeDelete_le |>.inc_left

  -- so τ(G) ≤ |W'| = ν(G)
  refine hMin.1 ?_
  refine le_antisymm ?_ G.matchingNumber_le_coverNumber
  grw [hW'G.le_encard, ← G'_coverNumber, hW'.encard]

end Graph
