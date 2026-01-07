import Matroid.Graph.Distance
import Matroid.Graph.Connected.Subgraph

variable {α β : Type*} {G H T : Graph α β} {u v x y z : α} {e e' f g : β} {X : Set α} {F : Set β}
{P C Q : WList α β}
open Set WList

namespace Graph

/-- If `P` and `Q` are distinct paths with the same ends, their union contains a cycle. -/
theorem twoPaths (hP : G.IsPath P) (hQ : G.IsPath Q) (hPQ : P ≠ Q) (h0 : P.first = Q.first)
    (h1 : P.last = Q.last) : ∃ C, G.IsCycle C ∧ E(C) ⊆ E(P) ∪ E(Q) := by
  classical
  induction P generalizing Q with
  | nil u => cases Q with | _ => simp_all
  | cons u e P ih =>
    subst h0
    obtain ⟨heP : e ∉ P.edge, -⟩ := by simpa using hP.edge_nodup
    simp only [cons_isPath_iff] at hP
    obtain ⟨x, rfl⟩ | hne := Q.exists_eq_nil_or_nonempty
    · obtain rfl : P.last = x := h1
      simp at hP
    -- If `e` is an edge of `Q`, then since `e` is incident to the first vertex of `cons u f Q`,
    -- it must be equal to `f`. So `P` and `Q` agree on their first edge; apply induction.
    by_cases heQ : e ∈ Q.edge
    · obtain rfl : e = hne.firstEdge := hQ.eq_firstEdge_of_isLink_first heQ hP.2.1.inc_left
      cases hne with | cons u f Q =>
      have hfirst : P.first = Q.first := by
        simp only [Nonempty.firstEdge_cons, first_cons, cons_isPath_iff] at hP hQ
        rw [hP.2.1.isLink_iff_eq] at hQ
        exact hQ.2.1.symm
      obtain ⟨C, hC, hCss⟩ := ih hP.1 hQ.of_cons (by simpa using hPQ) hfirst (by simpa using h1)
      refine ⟨C, hC, hCss.trans ?_⟩
      simp [show E(P) ⊆ insert f E(P) ∪ E(Q) from (subset_insert ..).trans subset_union_left]
    -- Otherwise, `e + P` and `Q` have different first edges. Now `P ∪ Q`
    -- contains a path between the ends of `e` not containing `e`, which gives a cycle.
    have hR_ex : ∃ R, G.IsPath R ∧ e ∉ R.edge ∧
        R.first = Q.first ∧ R.last = P.first ∧ E(R) ⊆ E(P) ∪ E(Q) := by
      refine ⟨(Q ++ P.reverse).dedup, ?_, ?_, ?_, by simp, ?_⟩
      · exact IsWalk.dedup_isPath (hQ.isWalk.append hP.1.isWalk.reverse (by simpa using h1.symm))
      · rw [← mem_edgeSet_iff]
        refine notMem_subset (t := E(Q ++ P.reverse)) ((dedup_isSublist _).edgeSet_subset) ?_
        simp [heQ, heP]
      · simp [append_first_of_nonempty hne]
      exact (dedup_isSublist _).edgeSet_subset.trans <| by simp
    obtain ⟨R, hR, heR, hfirst, hlast, hss⟩ := hR_ex
    refine ⟨_, hR.concat_isCycle ?_ heR, ?_⟩
    · rw [hfirst, hlast]
      exact hP.2.1.symm
    simp only [concat_edgeSet, cons_edgeSet]
    rw [insert_union]
    exact insert_subset_insert hss

def IsForest (G : Graph α β) : Prop := ∀ C, ¬ G.IsCycle C

lemma isForest_iff_forall_isBridge : G.IsForest ↔ ∀ e ∈ E(G), G.IsBridge e := by
  simp only [IsForest, isBridge_iff, forall_and, imp_self, true_and]
  refine ⟨fun h _ _ C hC _ ↦ h C hC, fun h C hC ↦ ?_⟩
  obtain ⟨e, he⟩ := hC.nonempty.edgeSet_nonempty
  exact h e (hC.isWalk.edgeSet_subset he) hC he

lemma IsForest.mono (hG : G.IsForest) (hHG : H ≤ G) : H.IsForest :=
  fun C hC ↦ hG C (hC.isCycle_of_ge hHG)

/-- The union of two forests that intersect in at most one vertex is a forest.  -/
lemma IsForest.union_isForest_of_subsingleton_inter (hG : G.IsForest) (hH : H.IsForest)
    (hi : (V(G) ∩ V(H)).Subsingleton) : (G ∪ H).IsForest := by
  intro C hC
  obtain hC | hC := hC.isCycle_or_isCycle_of_union_of_subsingleton_inter hi
  · exact hG C hC
  exact hH C hC

lemma IsPath.toGraph_isForest (hG : G.IsPath P) : P.toGraph.IsForest := by
  simp only [isForest_iff_forall_isBridge, WList.toGraph_edgeSet, WList.mem_edgeSet_iff]
  exact fun _ ↦ hG.isBridge_of_mem

lemma IsCycle.toGraph_not_isForest (hC : G.IsCycle C) : ¬ C.toGraph.IsForest :=
  fun h ↦ h C hC.isCycle_toGraph

@[simp]
lemma singleEdge_isForest (hxy : x ≠ y) (e : β) : (Graph.singleEdge x y e).IsForest := by
  intro C hC
  obtain ⟨u, f, rfl⟩ | hnt := hC.loop_or_nontrivial
  · obtain ⟨z,z', h⟩ := WList.exists_dInc_of_mem_edge (e := f) (w := .cons u f (.nil u)) (by simp)
    have h' := hC.isWalk.isLink_of_dInc h
    aesop
  refine hnt.firstEdge_ne_lastEdge hC.edge_nodup ?_
  have h_const := hC.isWalk.edgeSet_subset
  simp only [singleEdge_edgeSet, subset_singleton_iff, WList.mem_edgeSet_iff] at h_const
  rw [h_const hnt.nonempty.firstEdge (by simp), h_const hnt.nonempty.lastEdge (by simp)]

lemma IsForest.eq_of_isPath_eq_eq (hG : G.IsForest) (hP : G.IsPath P) (hQ : G.IsPath Q)
    (hfirst : P.first = Q.first) (hlast : P.last = Q.last) : P = Q := by
  by_contra hne
  obtain ⟨C, hC, -⟩ := twoPaths hP hQ hne hfirst hlast
  exact hG C hC

lemma IsCycle.toGraph_eq_of_le {C C₀ : WList α β} (hC : G.IsCycle C) (hC₀ : G.IsCycle C₀)
    (hle : C₀.toGraph ≤ C.toGraph) : C₀.toGraph = C.toGraph := by
  have hCE : E(C₀) ⊆ E(C) := by simpa using edgeSet_mono hle
  have hCV : V(C₀) ⊆ V(C) := by simpa using vertexSet_mono hle
  refine hle.antisymm <| G.le_of_le_le_subset_subset hC.isWalk.toGraph_le
    hC₀.isWalk.toGraph_le (fun x hxC ↦ by_contra fun hxC₀ ↦ ?_)
      (fun e heC ↦ by_contra fun heC₀ ↦ ?_)
  · obtain ⟨y, e, rfl⟩ | hnt := hC.loop_or_nontrivial
    · obtain rfl : x = y := by simpa using hxC
      have hfa : ∀ y ∈ C₀, y = x := by simpa using vertexSet_mono hle
      obtain rfl : C₀.first = x := by simpa using hfa C₀.first
      simp at hxC₀
    obtain ⟨P, hP, hP_eq⟩ := hC.exists_isPath_toGraph_eq_delete_vertex (x := x) hnt
      (by simpa using hxC)
    refine hC₀.toGraph_not_isForest <| hP.toGraph_isForest.mono ?_
    rw [hP_eq, hC.isWalk.toGraph_eq_induce_restrict, hC₀.isWalk.toGraph_eq_induce_restrict,
      edgeRestrict_vertexDelete, induce_vertexDelete]
    refine (edgeRestrict_mono_right _ hCE).trans (edgeRestrict_mono_left (induce_mono_right _ ?_) _)
    simpa [subset_diff, hCV] using hxC₀
  obtain ⟨P, hP, hPC⟩ := hC.exists_isPath_toGraph_eq_delete_edge <| by simpa using heC
  refine hC₀.toGraph_not_isForest <| hP.toGraph_isForest.mono ?_
  rw [hPC, hC.isWalk.toGraph_eq_induce_restrict, hC₀.isWalk.toGraph_eq_induce_restrict,
    edgeRestrict_edgeDelete]
  have hss : E(C₀) ⊆ E(C) \ {e} := subset_diff_singleton hCE (by simpa using heC₀)
  refine (edgeRestrict_mono_right _ hss).trans ?_
  rw [← edgeRestrict_induce, ← edgeRestrict_induce]
  exact induce_mono_right _ hCV

lemma IsCycleGraph.eq_of_le (hG : G.IsCycleGraph) (hH : H.IsCycleGraph) (hle : G ≤ H) :
    G = H := by
  obtain ⟨C', hC', rfl⟩ := by simpa [isCycleGraph_iff_toGraph_isCycle] using hG
  obtain ⟨C'', hC'', rfl⟩ := by simpa [isCycleGraph_iff_toGraph_isCycle] using hH
  exact hC''.toGraph_eq_of_le (hC'.of_le hle) hle

lemma IsCycleGraph.toGraph_of_isCycle {C : WList α β} (hG : G.IsCycleGraph)
    (hC : G.IsCycle C) : C.toGraph = G := by
  obtain ⟨C', hC', rfl⟩ := by simpa [isCycleGraph_iff_toGraph_isCycle] using hG
  exact hC'.toGraph_eq_of_le hC <| hC.isWalk.toGraph_le

lemma isForest_of_minimal_connected (hF : Minimal (fun F ↦ (G ↾ F).Connected) F) :
    (G ↾ F).IsForest := by
  intro C hC
  obtain ⟨e, he⟩ := hC.nonempty.edgeSet_nonempty
  refine hF.notMem_of_prop_diff_singleton (x := e) ?_ (hC.isWalk.edgeSet_subset he).2
  rw [← edgeRestrict_edgeDelete]
  exact hF.prop.edgeDelete_singleton_connected <| hC.not_isBridge_of_mem he

lemma IsForest.isShortestPath_of_isPath (hG : G.IsForest) (hP : G.IsPath P) :
    G.IsShortestPath P := by
  obtain ⟨Q, hQ, h1, h2⟩ := hP.isWalk.connBetween_first_last.exists_isShortestPath
  rwa [hG.eq_of_isPath_eq_eq hP hQ.isPath h1.symm h2.symm]

lemma IsForest.loopless (hG : G.IsForest) : G.Loopless := by
  rw [loopless_iff_forall_ne_of_adj]
  rintro x _ ⟨e, he⟩ rfl
  exact hG (WList.cons x e (nil x)) <| by simp [isCycle_iff, he.left_mem, isLink_self_iff.1 he]

lemma IsForest.simple (hG : G.IsForest) : G.Simple where
  not_isLoopAt := hG.loopless.not_isLoopAt
  eq_of_isLink e f x y he hf := by
    have := hG.loopless
    simpa [isCycle_iff, he.left_mem, hf.symm, he, he.adj.ne.symm] using
      hG (cons x e (cons y f (nil x)))

/-! ### Edge Sets -/

/-- `G.IsCycleSet C` means that `C` is the edge set of a cycle of `G`. -/
def IsCycleSet (G : Graph α β) (C : Set β) : Prop := ∃ C₀, G.IsCycle C₀ ∧ E(C₀) = C

/-- `G.IsAcyclicSet X` means that the subgraph `G ↾ X` is a forest. -/
def IsAcyclicSet (G : Graph α β) (I : Set β) : Prop := I ⊆ E(G) ∧ ∀ C₀, G.IsCycle C₀ → ¬ (E(C₀) ⊆ I)

lemma edgeRestrict_isForest_iff' :
    (G ↾ F).IsForest ↔ ∀ (C : WList α β), E(C) ⊆ F → ¬ G.IsCycle C := by
  refine ⟨fun h C hCF hC ↦ h C ?_, fun h C hC ↦ h C ?_ (hC.isCycle_of_ge <| by simp)⟩
  · exact hC.isCycle_of_le (by simp) <| by simp [hCF, hC.isWalk.edgeSet_subset]
  exact hC.isWalk.edgeSet_subset.trans inter_subset_right

lemma edgeRestrict_isForest_iff (hF : F ⊆ E(G)) : (G ↾ F).IsForest ↔ G.IsAcyclicSet F := by
  rw [edgeRestrict_isForest_iff', IsAcyclicSet]
  aesop

lemma isAcyclicSet_iff : G.IsAcyclicSet F ↔ F ⊆ E(G) ∧ (G ↾ F).IsForest := by
  by_cases hF : F ⊆ E(G)
  · rw [edgeRestrict_isForest_iff hF, and_iff_right hF]
  exact iff_of_false (mt (fun h ↦ h.1) hF) (by simp [hF])

/-! ### Leaves -/

/-- Every forest with at least one edge has a pendant. -/
lemma IsForest.exists_isPendant [G.EdgeFinite] (hG : G.IsForest) (hne : E(G).Nonempty) :
    ∃ e x, G.IsPendant e x := by
  classical
  have := hG.simple
  obtain ⟨e₀, he₀⟩ := hne
  obtain ⟨x₀, y₀, he₀⟩ := exists_isLink_of_mem_edgeSet he₀
  obtain ⟨P, heP, hmax⟩ := exists_le_maximal_isPath (he₀.walk_isPath he₀.adj.ne)
  simp only [IsLink.walk, le_iff_isSublist] at heP
  cases P with | nil => simp at heP | cons u f P =>
  have ⟨hP, hfuP, huP⟩ : G.IsPath P ∧ G.IsLink f u P.first ∧ u ∉ P := by simpa using hmax.prop
  refine ⟨f, u, hfuP.inc_left.isNonloopAt, fun e ⟨w, he⟩ ↦ ?_⟩
  have hwP := mem_of_adj_first_of_maximal_isPath hmax he.symm.adj
  have h_app := prefixUntilVertex_append_suffixFromVertex P w
  obtain rfl | hne := eq_or_ne w P.first
  · exact Simple.eq_of_isLink he hfuP
  have hP' := IsPath.prefix hmax.prop ((cons u f P).prefixUntilVertex_isPrefix w)
  refine False.elim <| hG _ <| (hP'.cons_isCycle_of_nontrivial (e := e) ?_ ?_)
  · simpa only [prefixUntilVertex_first, first_cons, prefixUntilVertex_last hwP]
  rw [prefixUntilVertex_cons_of_ne _ he.adj.ne, cons_nontrivial_iff, ← not_nil_iff]
  contrapose! hne
  replace hne := hne.first_eq_last
  rwa [prefixUntilVertex_last, eq_comm, prefixUntilVertex_first] at hne
  rwa [mem_cons_iff, or_iff_right he.adj.ne.symm] at hwP

lemma IsForest.exists_isLeaf [G.EdgeFinite] (hG : G.IsForest) (hne : E(G).Nonempty) :
    ∃ x, G.IsLeaf x := by
  obtain ⟨e, x, h⟩ := hG.exists_isPendant hne
  exact ⟨x, h.isLeaf⟩
