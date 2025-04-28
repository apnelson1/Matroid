import Matroid.ForMathlib.Graph.Connected
import Matroid.ForMathlib.Graph.Subgraph
import Mathlib.Data.Set.Subsingleton
import Mathlib.Order.Minimal

variable {α β : Type*} {G H T : Graph α β} {u v x y z : α} {e e' f g : β} {X : Set α} {F : Set β}

open Set

namespace Graph

def Acyclic (G : Graph α β) : Prop := ∀ C, ¬ G.IsCycle C

lemma Acyclic.mono (hG : G.Acyclic) (hHG : H ≤ G) : H.Acyclic :=
  fun C hC ↦ hG C (hC.isCycle_of_ge hHG)

/-- The union of two acyclic graphs that intersect in at most one vertex is acyclic.  -/
lemma Acyclic.union_acyclic_of_subsingleton_inter (hG : G.Acyclic) (hH : H.Acyclic)
    (hi : (G.V ∩ H.V).Subsingleton) : (G ∪ H).Acyclic := by
  intro C hC
  obtain hC | hC := hC.isCycle_or_isCycle_of_union_of_subsingleton_inter hi
  · exact hG C hC
  exact hH C hC

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






lemma Connected.connected_of_maximal_acyclic_edgeRestrict (hG : G.Connected) {F : Set β}
    (hF : Maximal (fun F ↦ F ⊆ G.E ∧ (G ↾ F).Acyclic) F) : (G ↾ F).Connected := by
  by_contra hcon
  obtain ⟨S, e, x, y, heF, hx, hy, hxy⟩ := hG.exists_of_edgeRestrict_not_connected hcon
  have hne : x ≠ y := S.disjoint.ne_of_mem hx hy
  have hFac : (G ↾ F).Acyclic := hF.prop.2
  have h_left : (G ↾ F)[S.left].Acyclic := hFac.mono (induce_le _ S.left_subset)
  have h_right : (G ↾ F)[S.right].Acyclic := hFac.mono (induce_le _ S.right_subset)
  have h_left' := h_left.union_acyclic_of_subsingleton_inter (singleEdge_acyclic hne e) sorry
  have h' := h_left'.union_acyclic_of_subsingleton_inter h_right sorry
  refine heF <| hF.mem_of_prop_insert (x := e) ⟨insert_subset hxy.edge_mem hF.prop.1, ?_⟩
  refine h'.mono <| le_of_le_le_subset_subset (G := G) (by simp) ?_ ?_ ?_
  · refine union_le (union_le ?_ (by simpa)) ((induce_le _ S.right_subset).trans (by simp))
    · exact (induce_le _ S.left_subset).trans (by simp)
  · simp only [edgeRestrict_vxSet, union_vxSet, induce_vxSet, singleEdge_vxSet, union_insert,
      union_singleton]
    sorry
  sorry





  -- obtain ⟨X, hXssu, hXne, hX⟩ := exists_of_not_connected hcon hG.nonempty



-- structure IsTree (T : Graph α β) : Prop where
--   acyclic : T.Acyclic
--   connected : T.Connected

-- lemma Connected.isTree_of_maximal_acyclic_le (hG : G.Connected)
--     (h : Maximal (fun H ↦ H.Acyclic ∧ H ≤ G) T) : T.IsTree := by
--   refine ⟨h.prop.1, by_contra fun hnc ↦ ?_⟩
--   have hV : T.V = G.V := by
--     refine (vxSet_subset_of_le h.prop.2).
--   have := exists_of_not_connected hnc
