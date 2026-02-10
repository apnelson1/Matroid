import Matroid.Graph.Distance
import Matroid.Graph.Connected.Subgraph

variable {α β : Type*} {G H T : Graph α β} {u v x y z : α} {e e' f g : β} {X : Set α} {F F' : Set β}
{P C Q : WList α β}
open Set WList

namespace Graph

/-- If `P` and `Q` are distinct paths with the same ends, their union contains a cycle. -/
theorem twoPaths (hP : G.IsPath P) (hQ : G.IsPath Q) (hPQ : P ≠ Q) (h0 : P.first = Q.first)
    (h1 : P.last = Q.last) : ∃ C, G.IsCyclicWalk C ∧ E(C) ⊆ E(P) ∪ E(Q) := by
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
    · obtain rfl : e = hne.firstEdge := hQ.eq_firstEdge_of_isLink_first heQ hP.1.inc_left
      cases hne with | cons u f Q =>
      have hfirst : P.first = Q.first := by
        simp only [Nonempty.firstEdge_cons, first_cons, cons_isPath_iff] at hP hQ
        rw [hP.1.isLink_iff_eq] at hQ
        exact hQ.1.symm
      obtain ⟨C, hC, hCss⟩ := ih hP.2.1 hQ.of_cons (by simpa using hPQ) hfirst (by simpa using h1)
      refine ⟨C, hC, hCss.trans ?_⟩
      simp [show E(P) ⊆ insert f E(P) ∪ E(Q) from (subset_insert ..).trans subset_union_left]
    -- Otherwise, `e + P` and `Q` have different first edges. Now `P ∪ Q`
    -- contains a path between the ends of `e` not containing `e`, which gives a cycle.
    have hR_ex : ∃ R, G.IsPath R ∧ e ∉ R.edge ∧
        R.first = Q.first ∧ R.last = P.first ∧ E(R) ⊆ E(P) ∪ E(Q) := by
      refine ⟨(Q ++ P.reverse).dedup, ?_, ?_, ?_, by simp, ?_⟩
      · exact IsWalk.dedup_isPath (hQ.isWalk.append hP.2.1.isWalk.reverse (by simpa using h1.symm))
      · rw [← mem_edgeSet_iff]
        refine notMem_subset (t := E(Q ++ P.reverse)) ((dedup_isSublist _).edge_subset) ?_
        simp [heQ, heP]
      · simp [append_first_of_nonempty hne]
      exact (dedup_isSublist _).edge_subset.trans <| by simp
    obtain ⟨R, hR, heR, hfirst, hlast, hss⟩ := hR_ex
    refine ⟨_, hR.concat_isCyclicWalk ?_ heR, ?_⟩
    · rw [hfirst, hlast]
      exact hP.1.symm
    simp only [concat_edgeSet, cons_edgeSet]
    rw [insert_union]
    exact insert_subset_insert hss

def IsForest (G : Graph α β) : Prop := ∀ ⦃e⦄, e ∈ E(G) → G.IsBridge e

lemma IsForest.isEdgeSep (hG : G.IsForest) (he : e ∈ E(G)) : G.IsEdgeSep {e} where
  subset_edgeSet := by simpa
  not_connected h := by
    have := hG he
    rw [(h.of_isSpanningSubgraph edgeDelete_isSpanningSubgraph).isBridge_iff_isEdgeSep] at this
    exact this.not_connected h

lemma IsForest.isEdgeCutBetween (hG : G.IsForest) (hl : G.IsLink e x y) :
    G.IsEdgeCutBetween {e} x y where
  subset_edgeSet := by simp [hl.edge_mem]
  not_connBetween := by
    exact (hl.isBridge_iff_isEdgeCutBetween.mp <| hG hl.edge_mem).not_connBetween

lemma IsForest.mono (hG : G.IsForest) (hHG : H ≤ G) : H.IsForest :=
  fun _ he ↦ hG (edgeSet_mono hHG he) |>.anti_of_mem hHG he

/-- The union of two forests that intersect in at most one vertex is a forest.  -/
lemma IsForest.union_isForest_of_subsingleton_inter (hG : G.IsForest) (hH : H.IsForest)
    (hi : (V(G) ∩ V(H)).Subsingleton) : (G ∪ H).IsForest := by
  wlog hc : Compatible G H generalizing H with aux
  · have := aux (hH.mono edgeDelete_le : (H ＼ E(G)).IsForest) (by simpa)
      (Compatible.of_disjoint_edgeSet disjoint_sdiff_right)
    rwa [Graph.union_eq_union_edgeDelete]
  intro e he
  wlog heG : e ∈ E(G) generalizing G H with aux
  · obtain heH := by simpa using he
    rw [inter_comm] at hi
    have := aux hH hG hi hc.symm (by simpa [or_comm]) (heH.resolve_left heG)
    rwa [hc.symm.union_comm] at this
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet heG
  have := hxy.isBridge_iff_not_connBetween.mp (hG (hxy.edge_mem))
  rw [hxy.of_le (Graph.left_le_union ..) |>.isBridge_iff_not_connBetween]
  contrapose! this
  obtain ⟨P, hP, rfl, rfl⟩ := this.exists_isPath
  use P, ?_
  obtain ⟨hP, heP⟩ := by simpa using hP
  simpa [hP.isPath_of_union_of_subsingleton_inter hi hxy.left_mem hxy.right_mem |>.isWalk]

lemma IsForest.of_isCompOf_isForest (h : ∀ H : Graph α β, H.IsCompOf G → H.IsForest) :
    G.IsForest := by
  rintro e he
  rw [G.eq_sUnion_components] at he
  simp only [sUnion_edgeSet, mem_components_iff_isCompOf, mem_iUnion, exists_prop] at he
  obtain ⟨H, hH, heH⟩ := he
  exact h H hH heH |>.of_isClosedSubgraph hH.isClosedSubgraph

lemma IsPath.toGraph_isForest (hG : G.IsPath P) : P.toGraph.IsForest := by
  simp only [IsForest, WList.toGraph_edgeSet, WList.mem_edgeSet_iff]
  exact fun _ ↦ hG.isBridge_of_mem

lemma IsCyclicWalk.toGraph_not_isForest (hC : G.IsCyclicWalk C) : ¬ C.toGraph.IsForest := by
  obtain ⟨u, e, P⟩ := hC.nonempty
  obtain rfl := by simpa using hC.isClosed
  simp only [IsForest, toGraph_edgeSet, cons_edgeSet, mem_insert_iff, mem_edgeSet_iff,
    forall_eq_or_imp, not_and_or]
  left
  obtain ⟨hP, he, heP⟩ := by simpa using hC.isTrail
  rw [(he.of_le_of_mem hC.isWalk.toGraph_le (by simp)).isBridge_iff_not_connBetween, not_not,
    connBetween_comm]
  use P, ?_
  simp only [isWalk_edgeDelete_iff, disjoint_singleton_right, mem_edgeSet_iff, heP,
    not_false_eq_true, and_true]
  exact hP.isWalk.wellFormed.isWalk_toGraph.of_le (Graph.left_le_union ..)

lemma IsCyclicWalk.toGraph_eq_of_le {C C₀ : WList α β} (hC : G.IsCyclicWalk C)
    (hC₀ : G.IsCyclicWalk C₀) (hle : C₀.toGraph ≤ C.toGraph) : C₀.toGraph = C.toGraph := by
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
  obtain ⟨C', hC', rfl⟩ := by simpa [isCycleGraph_iff_toGraph_isCyclicWalk] using hG
  obtain ⟨C'', hC'', rfl⟩ := by simpa [isCycleGraph_iff_toGraph_isCyclicWalk] using hH
  exact hC''.toGraph_eq_of_le (hC'.of_le hle) hle

lemma IsCycleGraph.toGraph_of_isCyclicWalk {C : WList α β} (hG : G.IsCycleGraph)
    (hC : G.IsCyclicWalk C) : C.toGraph = G := by
  obtain ⟨C', hC', rfl⟩ := by simpa [isCycleGraph_iff_toGraph_isCyclicWalk] using hG
  exact hC'.toGraph_eq_of_le hC <| hC.isWalk.toGraph_le

lemma IsForest.not_isTour (hG : G.IsForest) : ¬ G.IsTour P := by
  intro h
  obtain ⟨C, hC, -⟩ := h.exists_isCyclicWalk
  exact hC.toGraph_not_isForest <| hG.mono hC.isWalk.toGraph_le

lemma isForest_iff_not_isCyclicWalk : G.IsForest ↔ ∀ C, ¬ G.IsCyclicWalk C := by
  refine ⟨fun hG C hC ↦ hG.not_isTour hC.isTour, fun h ↦ ?_⟩
  contrapose! h
  obtain ⟨e, he, hb⟩ := by simpa [IsForest] using h
  obtain ⟨C, hC, heC⟩ := exists_isCyclicWalk_of_not_isBridge he hb
  use C


def IsCycle (G : Graph α β) : Prop := Minimal (fun G ↦ ¬ G.IsForest) G

lemma isCycle_iff : G.IsCycle ↔ Minimal (fun G : Graph α β ↦ ∃ e ∈ E(G), ¬ G.IsBridge e) G := by
  simp [IsCycle, IsForest]

lemma IsCycle.edgeSet_nonempty (hG : G.IsCycle) : E(G).Nonempty := by
  obtain ⟨e, he, hb⟩ := isCycle_iff.mp hG |>.prop
  use e

lemma IsCycle.nonempty (hG : G.IsCycle) : V(G).Nonempty := by
  obtain ⟨e, he, hb⟩ := isCycle_iff.mp hG |>.prop
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
  use x, hxy.left_mem

lemma IsCycle.connected (hG : G.IsCycle) : G.Connected := by
  obtain ⟨H, hHc, hHF⟩ := by simpa using mt IsForest.of_isCompOf_isForest hG.prop
  obtain rfl := hG.eq_of_le hHF hHc.le
  exact hHc.connected

lemma IsCyclicWalk.toGraph_isCycle (hC : G.IsCyclicWalk C) : C.toGraph.IsCycle := by
  refine ⟨hC.toGraph_not_isForest, fun H hH hle ↦ ?_⟩
  obtain ⟨e, heC, hb⟩ := by simpa [IsForest] using hH
  obtain ⟨C', hC', heC'⟩ := exists_isCyclicWalk_of_not_isBridge (by simpa) hb
  convert hC'.isWalk.toGraph_le using 1
  apply hC.toGraph_eq_of_le (hC'.of_le <| hle.trans hC.isWalk.toGraph_le) ?_ |>.symm
  exact hC'.isWalk.toGraph_le.trans hle

lemma IsCycle.exists_isCyclicWalk_eq (hG : G.IsCycle) : ∃ C, G.IsCyclicWalk C ∧ C.toGraph = G := by
  obtain ⟨e, he, hb⟩ := isCycle_iff.mp hG |>.prop
  obtain ⟨C, hC, heC⟩ := exists_isCyclicWalk_of_not_isBridge he hb
  use C, hC
  have hle : C.toGraph ≤ G := hC.isWalk.toGraph_le
  exact hG.eq_of_le hC.toGraph_not_isForest hle

lemma isCycle_iff_exists_isCyclicWalk_eq : G.IsCycle ↔ ∃ C, G.IsCyclicWalk C ∧ C.toGraph = G :=
  ⟨fun hG ↦ hG.exists_isCyclicWalk_eq, fun ⟨_, hC, hC_eq⟩ ↦ hC_eq ▸ hC.toGraph_isCycle⟩

lemma IsCycle.not_isBridge (hG : G.IsCycle) : ¬ G.IsBridge e := by
  wlog he : e ∈ E(G)
  · grind
  rw [isCycle_iff_exists_isCyclicWalk_eq] at hG
  obtain ⟨C, hC, rfl⟩ := hG
  exact not_isBridge_of_exists_isCyclicWalk ⟨C, hC, by simpa using he⟩

lemma IsCycle.finite (hG : G.IsCycle) : G.Finite := by
  rw [isCycle_iff_exists_isCyclicWalk_eq] at hG
  obtain ⟨C, hC, rfl⟩ := hG
  infer_instance

@[simp]
lemma singleEdge_isForest (hxy : x ≠ y) (e : β) : (Graph.singleEdge x y e).IsForest := by
  rw [isForest_iff_not_isCyclicWalk]
  intro C hC
  obtain ⟨u, f, rfl⟩ | hnt := hC.loop_or_nontrivial
  · obtain ⟨z, z', h⟩ := WList.exists_dInc_of_mem_edge (e := f) (w := .cons u f (.nil u)) (by simp)
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
  rw [isForest_iff_not_isCyclicWalk] at hG
  exact hG C hC

lemma IsForest.isPath_of_isTrail (hG : G.IsForest) (hP : G.IsTrail P) : G.IsPath P where
  isWalk := hP.isWalk
  nodup := by
    classical
    induction P with
    | nil u => simp
    | cons u e w ih =>
    obtain ⟨hw, hl, hew⟩ := by simpa using hP
    simp only [cons_vertex, List.nodup_cons, mem_vertex, ih hw, and_true]
    rintro huw
    refine hG.not_isTour (P := cons u e <| w.prefixUntilVertex u) ⟨?_, by simp, by simp [huw]⟩
    simp only [cons_isTrail_iff, prefixUntilVertex_first]
    have hp := w.prefixUntilVertex_isPrefix u
    exact ⟨hw.sublist hp.isSublist, hl, mt (hp.mem_edge) hew⟩

lemma IsForest.eq_of_isTrail_eq_eq (hG : G.IsForest) (hP : G.IsTrail P) (hQ : G.IsTrail Q)
    (hfirst : P.first = Q.first) (hlast : P.last = Q.last) : P = Q :=
  hG.eq_of_isPath_eq_eq (hG.isPath_of_isTrail hP) (hG.isPath_of_isTrail hQ) hfirst hlast

lemma isForest_of_minimal_connected (hF : Minimal (fun F ↦ (G ↾ F).Connected) F) :
    (G ↾ F).IsForest := by
  rw [isForest_iff_not_isCyclicWalk]
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
  rw [isForest_iff_not_isCyclicWalk] at hG
  exact hG (WList.cons x e (nil x))
  <| by simp [isCyclicWalk_iff, isTour_iff, he.left_mem, isLink_self_iff.1 he]

lemma IsForest.simple (hG : G.IsForest) : G.Simple where
  not_isLoopAt := hG.loopless.not_isLoopAt
  eq_of_isLink e f x y he hf := by
    have := hG.loopless
    rw [isForest_iff_not_isCyclicWalk] at hG
    simpa [isCyclicWalk_iff, isTour_iff, he.left_mem, hf.symm, he, he.adj.ne.symm] using
      hG (cons x e (cons y f (nil x)))

lemma isForest_iff_isTrail_eq_eq : G.IsForest ↔ ∀ ⦃P Q⦄, G.IsTrail P → G.IsTrail Q →
    P.first = Q.first → P.last = Q.last → P = Q := by
  refine ⟨fun hG P Q hP hQ hfirst hlast ↦ hG.eq_of_isTrail_eq_eq hP hQ hfirst hlast, fun h ↦ ?_⟩
  have hG : G.Loopless := ⟨fun e x hex ↦ by
    simpa using congrArg length
    <| h hex.walk_isTrail (Q := nil x) (by simp [hex.left_mem]) (by simp) (by simp)⟩
  intro e he
  rw [isBridge_iff_notMem_isCyclicWalk he]
  intro C hC heC
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
  have hCxy := hC.isWalk.isLink_iff_isLink_of_mem heC |>.mpr hxy
  obtain ⟨P, hP, hP_eq, rfl, rfl⟩ := hC.exists_isPath_toGraph_eq_delete_edge_of_isLink hCxy
  have hQ := hxy.walk_isPath hxy.adj.ne
  rw [h hP.isTrail hQ.isTrail (by simp) (by simp)] at hP_eq
  simpa using congrArg (fun x : Graph α β ↦ e ∈ E(x)) hP_eq

lemma not_isForest_iff_exists_isCycle : ¬ G.IsForest ↔ ∃ H, H.IsCycle ∧ H ≤ G := by
  simp only [isForest_iff_not_isCyclicWalk, not_forall, not_not, isCycle_iff_exists_isCyclicWalk_eq,
    ↓existsAndEq, and_true]
  exact ⟨fun ⟨C, hC⟩ => ⟨C, hC.isCyclicWalk_toGraph, hC.isWalk.toGraph_le⟩,
    fun ⟨H, hH, hHle⟩ => ⟨H, hH.of_le hHle⟩⟩

lemma isForest_iff_not_isCycle : G.IsForest ↔ ∀ H ≤ G, ¬ H.IsCycle := by
  rw [not_isForest_iff_exists_isCycle.not_right]
  grind

/-! ### Edge Sets -/

/-- `G.IsCycleSet C` means that `C` is the edge set of a cycle of `G`. -/
def IsCycleSet (G : Graph α β) (C : Set β) : Prop := ∃ C₀, G.IsCyclicWalk C₀ ∧ E(C₀) = C

@[simp]
lemma edgeRestrict_isCycleSet_iff (C : Set β) :
    (G ↾ F).IsCycleSet C ↔ G.IsCycleSet C ∧ C ⊆ F := by
  refine ⟨fun ⟨C₀, hC₀, h⟩ ↦ ?_, fun ⟨⟨C₀, hC₀, hss⟩, hsF⟩ ↦
    ⟨C₀, (G.edgeRestrict_isCyclicWalk_iff ..).mpr ⟨hC₀, hss ▸ hsF⟩, hss⟩⟩
  rw [edgeRestrict_isCyclicWalk_iff] at hC₀
  exact ⟨⟨C₀, hC₀.1, h ▸ rfl⟩, h ▸ hC₀.2⟩

@[simp]
lemma edgeDelete_isCycleSet_iff (C : Set β) :
    (G ＼ F).IsCycleSet C ↔ G.IsCycleSet C ∧ Disjoint C F := by
  refine ⟨fun ⟨C₀, hC₀, h⟩ ↦ ?_, fun ⟨⟨C₀, hC₀, hss⟩, hdisj⟩ ↦
    ⟨C₀, (edgeDelete_isCyclicWalk_iff ..).mpr ⟨hC₀, hss ▸ hdisj⟩, hss⟩⟩
  rw [edgeDelete_isCyclicWalk_iff] at hC₀
  exact ⟨⟨C₀, hC₀.1, h⟩, h ▸ hC₀.2⟩

@[simp]
lemma induce_isCycleSet_iff (C : Set β) :
    G[X].IsCycleSet C ↔ ∃ C₀, G.IsCyclicWalk C₀ ∧ V(C₀) ⊆ X ∧ E(C₀) = C := by
  simp only [IsCycleSet, induce_isCyclicWalk_iff, and_assoc]

@[simp]
lemma vertexDelete_isCycleSet_iff (C : Set β) :
    (G - X).IsCycleSet C ↔ ∃ C₀, G.IsCyclicWalk C₀ ∧ Disjoint V(C₀) X ∧ E(C₀) = C := by
  simp only [IsCycleSet, vertexDelete_isCyclicWalk_iff, and_assoc]

lemma IsCycleSet.of_isLink {C : Set β} (h : G.IsCycleSet C)
    (he : ∀ ⦃e x y⦄, G.IsLink e x y → H.IsLink e x y) : H.IsCycleSet C := by
  obtain ⟨C₀, hC₀, h⟩ := h
  exact ⟨C₀, hC₀.of_forall_isLink he, h⟩

/-- `G.IsAcyclicSet X` means that the subgraph `G ↾ X` is a forest. -/
def IsAcyclicSet (G : Graph α β) (I : Set β) : Prop :=
  I ⊆ E(G) ∧ ∀ C₀, G.IsCyclicWalk C₀ → ¬ (E(C₀) ⊆ I)

lemma edgeRestrict_isForest_iff' :
    (G ↾ F).IsForest ↔ ∀ (C : WList α β), E(C) ⊆ F → ¬ G.IsCyclicWalk C := by
  rw [isForest_iff_not_isCyclicWalk]
  refine ⟨fun h C hCF hC ↦ h C ?_, fun h C hC ↦ h C ?_ (hC.of_le <| by simp)⟩
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
  rw [isForest_iff_not_isCyclicWalk] at hG
  obtain ⟨e₀, he₀⟩ := hne
  obtain ⟨x₀, y₀, he₀⟩ := exists_isLink_of_mem_edgeSet he₀
  obtain ⟨P, heP, hmax⟩ := exists_le_maximal_isPath (he₀.walk_isPath he₀.adj.ne)
  simp only [IsLink.walk, le_iff_isSublist] at heP
  cases P with | nil => simp at heP | cons u f P =>
  have ⟨hfuP, hP, huP⟩ : G.IsLink f u P.first ∧ G.IsPath P ∧ u ∉ P := by simpa using hmax.prop
  refine ⟨f, u, hfuP.inc_left.isNonloopAt, fun e ⟨w, he⟩ ↦ ?_⟩
  have hwP := mem_of_adj_first_of_maximal_isPath hmax he.symm.adj
  have h_app := prefixUntilVertex_append_suffixFromVertex P w
  obtain rfl | hne := eq_or_ne w P.first
  · exact Simple.eq_of_isLink he hfuP
  have hP' := IsPath.prefix hmax.prop ((cons u f P).prefixUntilVertex_isPrefix w)
  refine False.elim <| hG _ <| (hP'.cons_isCyclicWalk_of_nontrivial (e := e) ?_ ?_)
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

lemma IsForest.of_edgeDelete_singleton (he : G.IsBridge e) (hG : (G ＼ {e}).IsForest) :
    G.IsForest := by
  by_contra! h
  rw [not_isForest_iff_exists_isCycle] at h
  obtain ⟨H, hH, hHle⟩ := h
  have hHGe : H ≤ G ＼ {e} := by simpa [hHle] using (hH.not_isBridge <| he.anti_of_mem hHle ·)
  rw [isForest_iff_not_isCycle] at hG
  exact hG H hHGe hH

lemma not_isBridge_of_maximal_isAcyclicSet (hF : Maximal G.IsAcyclicSet F) (he : e ∈ E(G) \ F) :
    ¬ (G ↾ insert e F).IsBridge e := by
  intro hb
  have hef : G.IsAcyclicSet (insert e F) := by
    rw [isAcyclicSet_iff]
    simp only [insert_subset_iff, he.1, hF.prop.1, and_self, true_and]
    refine IsForest.of_edgeDelete_singleton hb ?_
    simp only [edgeRestrict_edgeDelete, mem_singleton_iff, insert_diff_of_mem, he.2,
      not_false_eq_true, diff_singleton_eq_self]
    exact isAcyclicSet_iff.mp hF.prop |>.2
  exact he.2 <| insert_eq_self.mp (hF.eq_of_subset hef (by grind)).symm

lemma IsBond.not_disjoint_of_maximal_isAcyclicSet {B} (hF : Maximal G.IsAcyclicSet F)
    (hB : G.IsBond B) : ¬ Disjoint F B := by
  rintro hdj
  have := by rwa [disjoint_comm, disjoint_iff_forall_notMem] at hdj
  obtain ⟨e, heB⟩ := hB.prop.2
  have he := hB.subset_edgeSet heB
  apply not_isBridge_of_maximal_isAcyclicSet hF ⟨he, this heB⟩
  have := by simpa using hB.prop.1.anti (edgeRestrict_le (E₀ := insert e F))
  rwa [(inter_eq_right (s := E(G))).mpr (by simp [hF.prop.1, insert_subset_iff, he]),
    insert_inter_of_mem heB, hdj.inter_eq, insert_empty_eq] at this

-- lemma connBetween_iff_maximal_isAcyclicSet (hF : Maximal G.IsAcyclicSet F) :
--     G.ConnBetween x y ↔ (G ↾ F).ConnBetween x y := by
--   refine ⟨fun h ↦ ?_, fun h ↦ h.mono edgeRestrict_le⟩
  -- have := (walkable_isCompOf h.left_mem).edgeDelete_singleton_isCompOf

lemma isForest_of_maximal_isAcyclicSet (hF : Maximal G.IsAcyclicSet F) : (G ↾ F).IsForest := by
  rw [show G.IsAcyclicSet = fun X ↦ X ⊆ E(G) ∧ (G ↾ X).IsForest by
    ext; exact isAcyclicSet_iff] at hF
  exact hF.prop.2
