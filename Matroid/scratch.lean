import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Order

variable {V : Type*} {G : SimpleGraph V}

/-- Deleting a non-bridge edge from a connected graph preserves connectedness. -/
lemma SimpleGraph.Connected.connected_del_of_not_isBridge (hG : G.Connected) {x y : V}
    (h : ¬ G.IsBridge s(x, y)) : (G \ fromEdgeSet {s(x, y)}).Connected := by
  classical
  simp only [isBridge_iff, not_and, not_not] at h
  obtain hxy | hxy := em' <| G.Adj x y
  · rwa [Disjoint.sdiff_eq_left (by simpa)]
  refine (connected_iff_exists_forall_reachable _).2 ⟨x, fun w ↦ ?_⟩
  obtain ⟨W⟩ := (hG.preconnected w x)
  let P := W.toPath
  obtain heP | heP := em' <| s(x,y) ∈ P.1.edges
  · exact ⟨(P.1.toDeleteEdges {s(x,y)} (by aesop)).reverse⟩
  have hyP := P.1.snd_mem_support_of_mem_edges heP
  set P₁ := P.1.takeUntil y hyP with hP₁
  have hxP₁ := Walk.endpoint_not_mem_support_takeUntil P.2 hyP hxy.ne
  have heP₁ : s(x,y) ∉ P₁.edges := fun h ↦ hxP₁ <| P₁.fst_mem_support_of_mem_edges h
  refine (h hxy).trans (Reachable.symm ⟨P₁.toDeleteEdges {s(x,y)} (by aesop)⟩)

/-- A minimally connected graph is a tree. -/
lemma SimpleGraph.isTree_of_minimal_connected (h : Minimal SimpleGraph.Connected G) :
    SimpleGraph.IsTree G := by
  rw [isTree_iff, and_iff_right h.prop, isAcyclic_iff_forall_adj_isBridge]
  refine fun v w hvw ↦ by_contra fun hbr ↦ ?_
  refine h.not_prop_of_lt ?_ (h.prop.connected_del_of_not_isBridge hbr)
  rw [← edgeSet_ssubset_edgeSet]
  simpa

/-- Every connected graph on `n` vertices has at least `n-1` edges. -/
lemma SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one [Fintype V] (hG : G.Connected) :
    Nat.card V ≤ Nat.card G.edgeSet + 1 := by
  classical
  obtain ⟨T, hTG, hmin⟩ := {H : SimpleGraph V | H.Connected}.toFinite.exists_minimal_le hG
  have hT : T.IsTree := isTree_of_minimal_connected hmin
  rw [Nat.card_eq_fintype_card, ← hT.card_edgeFinset, Set.Nat.card_coe_set_eq,
    ← Set.ncard_coe_Finset, add_le_add_iff_right]
  exact Set.ncard_mono <| by simpa

lemma SimpleGraph.isTree_iff_connected_and_card [Fintype V] :
    G.IsTree ↔ G.Connected ∧ Nat.card G.edgeSet + 1 = Nat.card V := by
  classical
  refine ⟨fun h ↦ ⟨h.isConnected, by simpa using h.card_edgeFinset⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, ?_⟩⟩
  simp_rw [isAcyclic_iff_forall_adj_isBridge]
  refine fun x y h ↦ by_contra fun hbr ↦ ?_
  refine (h₁.connected_del_of_not_isBridge hbr).card_vert_le_card_edgeSet_add_one.not_lt ?_
  simp only [← h₂, edgeSet_sdiff, edgeSet_fromEdgeSet, edgeSet_sdiff_sdiff_isDiag,
    add_lt_add_iff_right, Set.Nat.card_coe_set_eq]
  exact Set.ncard_diff_singleton_lt_of_mem h
