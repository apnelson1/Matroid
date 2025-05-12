import Matroid.Graph.Connected
import Matroid.Graph.Subgraph
import Mathlib.Data.Set.Subsingleton
import Mathlib.Order.Minimal

variable {α β : Type*} {G H T : Graph α β} {u v x y z : α} {e e' f g : β} {X : Set α} {F : Set β}
{P C : WList α β}
open Set

namespace Graph

def Acyclic (G : Graph α β) : Prop := ∀ C, ¬ G.IsCycle C

lemma acyclic_iff_forall_isBridge : G.Acyclic ↔ ∀ e ∈ E(G), G.IsBridge e := by
  simp only [Acyclic, isBridge_iff, forall_and, imp_self, true_and]
  refine ⟨fun h _ _ C hC _ ↦ h C hC, fun h C hC ↦ ?_⟩
  obtain ⟨e, he⟩ := hC.nonempty.edgeSet_nonempty
  exact h e (hC.isWalk.edgeSet_subset he) hC he

lemma Acyclic.mono (hG : G.Acyclic) (hHG : H ≤ G) : H.Acyclic :=
  fun C hC ↦ hG C (hC.isCycle_of_ge hHG)

/-- The union of two acyclic graphs that intersect in at most one vertex is acyclic.  -/
lemma Acyclic.union_acyclic_of_subsingleton_inter (hG : G.Acyclic) (hH : H.Acyclic)
    (hi : (V(G) ∩ V(H)).Subsingleton) : (G ∪ H).Acyclic := by
  intro C hC
  obtain hC | hC := hC.isCycle_or_isCycle_of_union_of_subsingleton_inter hi
  · exact hG C hC
  exact hH C hC

lemma IsPath.toGraph_acyclic (hG : G.IsPath P) : P.toGraph.Acyclic := by
  simp only [acyclic_iff_forall_isBridge, WList.toGraph_edgeSet, WList.mem_edgeSet_iff]
  exact fun _ ↦ hG.isBridge_of_mem

lemma IsCycle.toGraph_not_acyclic (hC : G.IsCycle C) : ¬ C.toGraph.Acyclic :=
  fun h ↦ h C hC.isCycle_toGraph
@[simp]
lemma singleEdge_acyclic (hxy : x ≠ y) (e : β) : (Graph.singleEdge x y e).Acyclic := by
  intro C hC
  obtain ⟨u, f, rfl⟩ | hnt := hC.loop_or_nontrivial
  · obtain ⟨z,z', h⟩ := WList.exists_dInc_of_mem_edge (e := f) (w := .cons u f (.nil u)) (by simp)
    have h' := hC.isWalk.inc₂_of_dInc h
    aesop
  refine hnt.firstEdge_ne_lastEdge hC.edge_nodup ?_
  have h_const := hC.isWalk.edgeSet_subset
  simp only [singleEdge_edgeSet, subset_singleton_iff, WList.mem_edgeSet_iff] at h_const
  rw [h_const hnt.nonempty.firstEdge (by simp), h_const hnt.nonempty.lastEdge (by simp)]

lemma edgeRestrict_acyclic_iff : (G ↾ F).Acyclic ↔ ∀ (C : WList α β), C.E ⊆ F → ¬ G.IsCycle C := by
  refine ⟨fun h C hCF hC ↦ h C ?_, fun h C hC ↦ h C ?_ (hC.isCycle_of_ge <| by simp)⟩
  · exact hC.isCycle_of_le (by simp) <| by simp [hCF, hC.isWalk.edgeSet_subset]
  exact hC.isWalk.edgeSet_subset.trans inter_subset_left

/-- If `G` is connected, then a maximally acylic subgraph of `G` is connected.
The correct statement is that any two vertices connected in the big graph are
connected in the small one-/
lemma Connected.connected_of_maximal_acyclic_edgeRestrict (hG : G.Connected) {F : Set β}
    (hF : Maximal (fun F ↦ F ⊆ E(G) ∧ (G ↾ F).Acyclic) F) : (G ↾ F).Connected := by
  by_contra hcon
  obtain ⟨S, e, x, y, heF, hx, hy, hxy⟩ := hG.exists_of_edgeRestrict_not_connected hcon
  have hne : x ≠ y := S.disjoint.ne_of_mem hx hy
  have hx' : x ∉ S.right := S.disjoint.not_mem_of_mem_left hx
  have hy' : y ∉ S.left := S.disjoint.not_mem_of_mem_right hy
  have hFac : (G ↾ F).Acyclic := hF.prop.2
  have h_left : (G ↾ F)[S.left].Acyclic := hFac.mono (induce_le S.left_subset)
  have h_right : (G ↾ F)[S.right].Acyclic := hFac.mono (induce_le S.right_subset)
  have h_left' := h_left.union_acyclic_of_subsingleton_inter (singleEdge_acyclic hne e) ?_; swap
  · rw [induce_vxSet, singleEdge_vxSet, pair_comm, inter_insert_of_not_mem hy']
    exact Subsingleton.inter_singleton
  have h' := h_left'.union_acyclic_of_subsingleton_inter h_right ?_; swap
  · simp only [union_vxSet, induce_vxSet, singleEdge_vxSet, union_insert, union_singleton]
    rw [insert_inter_of_not_mem hx', insert_inter_of_mem hy, S.disjoint.inter_eq]
    simp
  have hins : insert e F ⊆ E(G) := insert_subset hxy.edge_mem hF.prop.1
  refine heF <| hF.mem_of_prop_insert ⟨hins, h'.mono ?_⟩
  rw [(Compatible.of_disjoint_edgeSet (by simp [heF])).union_comm (G := (G ↾ F)[S.left]),
    Graph.union_assoc, ← S.eq_union]
  refine le_of_le_le_subset_subset (G := G) (by simp) (union_le (by simpa) (by simp)) (by simp) ?_
  simp [inter_eq_self_of_subset_left hins, inter_eq_self_of_subset_left hF.prop.1]

lemma IsCycle.toGraph_eq_of_le {C C₀ : WList α β} (hC : G.IsCycle C) (hC₀ : G.IsCycle C₀)
    (hle : C₀.toGraph ≤ C.toGraph) : C₀.toGraph = C.toGraph := by
  have hCE : C₀.E ⊆ C.E := by simpa using edgeSet_subset_of_le hle
  have hCV : C₀.V ⊆ C.V := by simpa using vxSet_subset_of_le hle
  refine hle.antisymm <| G.le_of_le_le_subset_subset hC.isWalk.toGraph_le
    hC₀.isWalk.toGraph_le (fun x hxC ↦ by_contra fun hxC₀ ↦ ?_)
      (fun e heC ↦ by_contra fun heC₀ ↦ ?_)
  · obtain ⟨y, e, rfl⟩ | hnt := hC.loop_or_nontrivial
    · obtain rfl : x = y := by simpa using hxC
      have hfa : ∀ y ∈ C₀, y = x := by simpa using vxSet_subset_of_le hle
      obtain rfl : C₀.first = x := by simpa using hfa C₀.first
      simp at hxC₀
    obtain ⟨P, hP, hP_eq⟩ := hC.exists_isPath_toGraph_eq_delete_vx (x := x) hnt (by simpa using hxC)
    refine hC₀.toGraph_not_acyclic <| hP.toGraph_acyclic.mono ?_
    rw [hP_eq, hC.isWalk.toGraph_eq_induce_restrict, hC₀.isWalk.toGraph_eq_induce_restrict,
      edgeRestrict_vxDelete, induce_vxDelete]
    refine (edgeRestrict_mono_right _ hCE).trans (edgeRestrict_mono_left (induce_mono _ ?_) _)
    simpa [subset_diff, hCV] using hxC₀
  obtain ⟨P, hP, hPC⟩ := hC.exists_isPath_toGraph_eq_delete_edge <| by simpa using heC
  refine hC₀.toGraph_not_acyclic <| hP.toGraph_acyclic.mono ?_
  rw [hPC, hC.isWalk.toGraph_eq_induce_restrict, hC₀.isWalk.toGraph_eq_induce_restrict,
    edgeRestrict_edgeDelete]
  have hss : C₀.E ⊆ C.E \ {e} := subset_diff_singleton hCE (by simpa using heC₀)
  refine (edgeRestrict_mono_right _ hss).trans ?_
  rw [← edgeRestrict_induce, ← edgeRestrict_induce]
  exact induce_mono _ hCV

lemma acyclic_of_minimal_connected (hF : Minimal (fun F ↦ (G ↾ F).Connected) F) :
    (G ↾ F).Acyclic := by
  intro C hC
  obtain ⟨e, he⟩ := hC.nonempty.edgeSet_nonempty
  refine hF.not_mem_of_prop_diff_singleton (x := e) ?_ (hC.isWalk.edgeSet_subset he).1
  rw [← edgeRestrict_edgeDelete]
  exact hF.prop.edgeDelete_singleton_connected <| hC.not_isBridge_of_mem he












  -- obtain ⟨X, hXssu, hXne, hX⟩ := exists_of_not_connected hcon hG.nonempty



-- structure IsTree (T : Graph α β) : Prop where
--   acyclic : T.Acyclic
--   connected : T.Connected

-- lemma Connected.isTree_of_maximal_acyclic_le (hG : G.Connected)
--     (h : Maximal (fun H ↦ H.Acyclic ∧ H ≤ G) T) : T.IsTree := by
--   refine ⟨h.prop.1, by_contra fun hnc ↦ ?_⟩
--   have hV : T.V = V(G) := by
--     refine (vxSet_subset_of_le h.prop.2).
--   have := exists_of_not_connected hnc
