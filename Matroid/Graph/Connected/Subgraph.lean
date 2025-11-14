import Matroid.Graph.Connected.Basic

open Set Function Nat WList

variable {α β : Type*} {G H : Graph α β} {u v x x₁ x₂ y y₁ y₂ z : α} {e e' f g : β}
  {U V S T : Set α} {F F' R R': Set β} {C W P Q : WList α β}

namespace Graph

/-! ### Bridges -/

/-- A bridge is an edge in no cycle-/
@[mk_iff]
structure IsBridge (G : Graph α β) (e : β) : Prop where
  mem_edgeSet : e ∈ E(G)
  notMem_cycle : ∀ ⦃C⦄, G.IsCycle C → e ∉ C.edge

lemma not_isBridge (he : e ∈ E(G)) : ¬ G.IsBridge e ↔ ∃ C, G.IsCycle C ∧ e ∈ C.edge := by
  simp [isBridge_iff, he]

lemma IsCycle.not_isBridge_of_mem (hC : G.IsCycle C) (heC : e ∈ C.edge) : ¬ G.IsBridge e := by
  rw [not_isBridge (hC.isWalk.edgeSet_subset heC)]
  exact ⟨C, hC, heC⟩

lemma IsLink.isBridge_iff_not_connectedBetween (he : G.IsLink e x y) :
    G.IsBridge e ↔ ¬ (G ＼ {e}).ConnectedBetween x y := by
  refine ⟨fun h hconn ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨P, hP, rfl, rfl⟩ := hconn.exists_isPath
    simp only [isPath_edgeDelete_iff, disjoint_singleton_right, mem_edgeSet_iff] at hP
    exact (hP.1.cons_isCycle he hP.2).not_isBridge_of_mem (by simp) h
  contrapose! h
  obtain ⟨C, hC, heC⟩ := (not_isBridge he.edge_mem).1 h
  rw [← hC.isWalk.isLink_iff_isLink_of_mem heC] at he
  exact hC.connectedBetween_deleteEdge_of_mem_of_mem _ he.left_mem he.right_mem

lemma Connected.edgeDelete_singleton_connected (hG : G.Connected) (he : ¬ G.IsBridge e) :
    (G ＼ {e}).Connected := by
  obtain heE | heE := em' <| e ∈ E(G)
  · rwa [edgeDelete_eq_self _ (by simpa)]
  obtain ⟨C, hC, heC⟩ := (not_isBridge heE).1 he
  rw [← (G ＼ {e}).induce_union_edgeDelete (X := V(C)) (by simp [hC.vertexSet_subset])]
  refine Compatible.union_connected_of_forall (G.compatible_of_le_le ?_ (by simp)) ?_ ?_
  · exact le_trans (induce_le (by simp [hC.vertexSet_subset])) edgeDelete_le
  · obtain ⟨P, hP, hPC⟩ := hC.exists_isPath_toGraph_eq_delete_edge heC
    refine (hP.isWalk.toGraph_connected.of_isSpanningSubgraph ⟨?_, ?_⟩)
    · rw [hPC, edgeDelete_induce, hC.isWalk.toGraph_eq_induce_restrict]
      exact edgeDelete_mono_left (by simp) _
    rw [hPC]
    simp
  simp only [edgeDelete_induce, edgeDelete_edgeSet, edgeDelete_edgeDelete, union_diff_self,
    singleton_union, edgeDelete_vertexSet, induce_vertexSet, mem_vertexSet_iff]
  intro x hx
  obtain ⟨y, hy, hconn⟩ := hG.exists_connectedBetween_deleteEdge_set (X := V(C))
    (by simp [inter_eq_self_of_subset_left hC.vertexSet_subset]) hx
  refine ⟨y, hy, ?_⟩
  rwa [insert_eq_of_mem (hC.isWalk.edgeSet_subset_induce_edgeSet heC )]

lemma Connected.edgeDelete_singleton_connected_iff (hG : G.Connected) :
    (G ＼ {e}).Connected ↔ ¬ G.IsBridge e := by
  obtain heE | heE := em' <| e ∈ E(G)
  · simp [edgeDelete_eq_self G (F := {e}) (by simpa), hG, isBridge_iff, heE]
  refine ⟨fun h hbr ↦ ?_, hG.edgeDelete_singleton_connected⟩
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet heE
  obtain ⟨P, hP, rfl, rfl⟩ := (h.connectedBetween hxy.left_mem hxy.right_mem).exists_isPath
  simp only [isPath_edgeDelete_iff, disjoint_singleton_right, mem_edgeSet_iff] at hP
  simpa using hbr.notMem_cycle <| hP.1.cons_isCycle hxy hP.2

lemma Connected.isBridge_iff (hG : G.Connected) : G.IsBridge e ↔ ¬ (G ＼ {e}).Connected := by
  rw [hG.edgeDelete_singleton_connected_iff, not_not]

/-- Every edge of a path is a bridge -/
lemma IsPath.isBridge_of_mem (hP : G.IsPath P) (heP : e ∈ P.edge) : P.toGraph.IsBridge e := by
  rw [hP.isWalk.toGraph_connected.isBridge_iff, hP.isWalk.toGraph_eq_induce_restrict]
  obtain ⟨P₁, P₂, hP₁, hP₂, heP₁, heP₂, hdj, hedj, rfl⟩ := hP.eq_append_cons_of_edge_mem heP
  rw [append_vertexSet_of_eq (by simp)]
  have := vertexSet_disjoint_iff.mpr hdj
  suffices ¬(G[V(P₁) ∪ V(P₂)] ↾ (E(P₁) ∪ E(P₂)) \ {e}).Connected by simpa
  rw [diff_singleton_eq_self (by simp [heP₁, heP₂]), ← edgeRestrict_induce, induce_union,
    edgeRestrict_induce, edgeRestrict_induce]
  · exact union_not_connected_of_disjoint_vertexSet (by simpa) (by simp) (by simp)
  rintro x hx y hy ⟨f, hf⟩
  simp only [edgeRestrict_isLink, mem_union, mem_edgeSet_iff] at hf
  obtain ⟨(hf | hf), hfxy⟩ := hf
  · rw [← hP₁.isWalk.isLink_iff_isLink_of_mem hf] at hfxy
    exact List.disjoint_right.1 hdj hy hfxy.right_mem
  rw [← hP₂.isWalk.isLink_iff_isLink_of_mem hf] at hfxy
  exact List.disjoint_left.1 hdj hx hfxy.left_mem


/-! ### Staying Connected -/

/-- A leaf vertex in a trail is either the first or last vertex of the trail -/
lemma IsLeaf.eq_first_or_eq_last_of_mem_trail {P : WList α β} (hx : G.IsLeaf x)
    (hP : G.IsTrail P) (hxP : x ∈ P) : x = P.first ∨ x = P.last := by
  induction P with
  | nil => simpa using hxP
  | cons u e P ih =>
    simp only [cons_isTrail_iff] at hP
    obtain (rfl : x = u) | (hxP : x ∈ P) := by simpa using hxP
    · simp
    obtain rfl | rfl := (ih hP.1 hxP).symm
    · simp
    obtain v | ⟨v, f, P⟩ := P
    · simp
    simp only [cons_isTrail_iff, first_cons, cons_edge, List.mem_cons, not_or] at hP
    simp [hx.eq_of_inc_inc hP.1.2.1.inc_left hP.2.1.inc_right] at hP

lemma IsLeaf.eq_first_or_eq_last_of_mem_path {P : WList α β} (hx : G.IsLeaf x)
    (hP : G.IsPath P) (hxP : x ∈ P) : x = P.first ∨ x = P.last :=
  hx.eq_first_or_eq_last_of_mem_trail hP.isTrail hxP

lemma IsLeaf.delete_connected (hx : G.IsLeaf x) (hG : G.Connected) : (G - {x}).Connected := by
  obtain ⟨y, hy : G.Adj x y, hu⟩ := hx.exists_unique_adj
  refine connected_of_vertex ⟨hy.right_mem, fun h : y = x ↦ hx.not_adj_self (h ▸ hy)⟩ fun z hz ↦ ?_
  obtain ⟨P, hP, rfl, rfl⟩ := (hG.connectedBetween hz.1 hy.right_mem).exists_isPath
  refine IsWalk.connectedBetween_first_last <| isWalk_vertexDelete_iff.2 ⟨hP.isWalk, ?_⟩
  simp only [disjoint_singleton_right, mem_vertexSet_iff]
  intro hxP
  obtain rfl | rfl := hx.eq_first_or_eq_last_of_mem_path hP hxP
  · simp at hz
  exact hx.not_adj_self hy

/-- Deleting the first vertex of a maximal path of a connected graph gives a connected graph. -/
lemma Connected.delete_first_connected_of_maximal_isPath (hG : G.Connected) (hnt : V(G).Nontrivial)
    (hP : Maximal (fun P ↦ G.IsPath P) P) : (G - {P.first}).Connected := by
  cases P with
  | nil u =>
    obtain ⟨e, y, huy, hne⟩ := hG.exists_isLink_of_mem hnt (x := u) (by simpa using hP.prop)
    exact False.elim <| hne.symm <| by
      simpa [huy, huy.right_mem] using hP.eq_of_ge (y := cons u e (nil y))
  | cons u e P =>
    have ⟨hP', he, huP⟩ : G.IsPath P ∧ G.IsLink e u P.first ∧ u ∉ P := by simpa using hP.prop
    by_contra hcon
    simp only [first_cons] at hcon
    have hP'' : (G - {u}).IsPath P := by simp [isPath_vertexDelete_iff, huP, hP']
    obtain ⟨S, hS⟩ :=
      hP''.isWalk.toGraph_connected.exists_separation_of_le hcon hP''.isWalk.toGraph_le
    have hPS : V(P) ⊆ S.left := by simpa using vertexSet_mono hS
    have huleft : u ∉ S.left := fun huS ↦ by simpa using S.left_subset huS
    have huright : u ∉ S.right := fun huS ↦ by simpa using S.right_subset huS
    suffices hu : ∀ x ∈ S.right, ¬ G.Adj u x by
      refine Separation.not_connected
        ⟨insert u S.left, S.right, by simp, S.nonempty_right, ?_, ?_, ?_⟩ hG
      · simp [S.disjoint, huright]
      · simpa [insert_union, S.union_eq] using he.left_mem
      rintro x y (rfl | hxS) hyS ⟨e, hxy⟩
      · exact hu y hyS hxy.adj
      refine S.not_adj hxS hyS ⟨e, ?_⟩
      simp only [vertexDelete_isLink_iff, hxy, mem_singleton_iff, true_and]
      constructor <;> (rintro rfl; contradiction)
    rintro x hx ⟨f, hux⟩
    have hne : u ≠ x := by rintro rfl; contradiction
    refine S.disjoint.notMem_of_mem_left (hPS ?_) hx
    simpa [hne.symm] using mem_of_adj_first_of_maximal_isPath hP hux.symm.adj

/-- Deleting the last vertex of a maximal path of a connected graph gives a connected graph. -/
lemma Connected.delete_last_connected_of_maximal_isPath (hG : G.Connected) (hnt : V(G).Nontrivial)
    (hP : Maximal (fun P ↦ G.IsPath P) P) : (G - {P.last}).Connected := by
  suffices aux : Maximal (fun P ↦ G.IsPath P) P.reverse by
    simpa using hG.delete_first_connected_of_maximal_isPath hnt aux
  refine ⟨by simpa using hP.prop, fun Q hQ hPQ ↦ ?_⟩
  simp [hP.eq_of_le (y := Q.reverse) (by simpa) (by simpa using IsSublist.reverse hPQ)]

/-- Every finite connected graph on at least two vertices has a vertex whose deletion
preserves its connectedness.
(This requires a finite graph, since otherwise an infinite path is a counterexample.) -/
lemma Connected.exists_delete_vertex_connected [G.Finite] (hG : G.Connected)
    (hnt : V(G).Nontrivial) : ∃ x ∈ V(G), (G - {x}).Connected := by
  obtain ⟨x, hx⟩ := hG.nonempty
  obtain ⟨P, hP⟩ := Finite.exists_maximal G.isPath_finite ⟨nil x, by simpa⟩
  exact ⟨_, hP.prop.isWalk.first_mem, hG.delete_first_connected_of_maximal_isPath hnt hP⟩
