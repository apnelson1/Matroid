import Matroid.Graph.Minor.Defs
import Matroid.Graph.Forest

variable {α β ι ι' : Type*} {x y z u v w : α} {e f : β} {G G₁ G₂ H H₁ H₂ I : Graph α β}
  {C D F F₁ F₂ : Set β} {X Y : Set α} {Gs Hs : Set (Graph α β)} {w w' P Q c : WList α β}

open Set Function WList

namespace Graph

lemma IsWalk.edgeRemove_contract [DecidablePred (· ∈ C)] (h : G.IsWalk w)
    (φ : (G ↾ C).connPartition.RepFun) : (G /[φ, C]).IsWalk <| (w.map φ).edgeRemove C := by
  induction w with
  | nil x =>
    simp only [nil_isWalk_iff, map_nil, edgeRemove_nil, contract_vertexSet, mem_image] at h ⊢
    grind
  | cons x e w ih =>
    simp_all only [cons_isWalk_iff, map_cons, forall_const, edgeRemove_cons]
    split_ifs with heC
    · exact ih
    obtain ⟨hl, h⟩ := h
    have := edgeRemove_first (φ.of_connPartition_repFun.exists_isLoopAt_of_isWalk h) (h.map φ)
    simp only [cons_isWalk_iff, this, map_first, contract_isLink, heC, not_false_eq_true, and_true,
      ih]
    use x, w.first, hl

-- lemma IsWalk.dedup_contract [DecidableEq α] (h : G.IsWalk P) (φ : (G ↾ C).connPartition.RepFun) :
--     (G /[φ, C]).IsPath (P.map φ).dedup := by
--   classical
--   induction P with
--   | nil x =>
--     simp only [nil_isWalk_iff, map_nil, dedup_nil, nil_isPath_iff, contract_vertexSet,
--       mem_image] at h ⊢
--     grind
--   | cons x e w ih =>
--     simp_all only [cons_isWalk_iff, map_cons, dedup_cons_eq_ite, forall_const]
--     obtain ⟨he, hP⟩ := h
--     split_ifs with hxin
--     · refine ⟨hP.edgeRemove_contract φ |>.sublist ?_, dedup_vertex_nodup ..⟩
--       refine (dedup_isSublist_deloop ..).trans ?_
--       exact deloop_isSublist_mono ((w.map φ).suffixFromVertex_isSuffix (φ x)).isSublist
--     simp only [cons_isPath_iff, ih, dedup_first, map_first, contract_isLink, true_and]
--     refine ⟨⟨?_, fun heC ↦ ?_⟩, mt (w.map φ).dedup_isSublist.mem hxin⟩
--     · grind
--     have := φ.apply_eq_apply
--     <| by simpa using (he.of_le_of_mem edgeRestrict_le ⟨he.edge_mem, heC⟩
--     |>.connBetween)
--     rw [this, ← w.map_first φ] at hxin
--     exact hxin (w.map φ).first_mem

-- lemma IsCycle.edgeRemove_contract [DecidablePred (· ∈ C)] (h : G.IsCycle (cons x e w))
--     (φ : (G ↾ C).connPartition.RepFun) : (G /[φ, C]).IsCycle <| (w.map φ).edgeRemove C where
--   isWalk := h.isWalk.deloop_contract φ
--   edge_nodup := by
--     refine List.Nodup.sublist (w.map φ).deloop_isSublist.edge_sublist ?_
--     simp [h.edge_nodup]
--   nonempty := by
--     sorry
--   isClosed := by
--     simp only [WList.IsClosed, deloop_first, map_first, deloop_last, map_last]
--     exact congrArg φ h.isClosed
--   nodup := by


-- lemma IsForest.contract (φ : (G ↾ C).connPartition.RepFun) (hC : (G ↾ C).IsForest) :
--     ((G /[φ, C]) ↾ F).IsForest ↔ (G ↾ (F ∪ C)).IsForest := by
--   classical
--   rw [isForest_iff_isTrail_eq_eq, isForest_iff_isTrail_eq_eq]
--   sorry

--   sorry

-- lemma IsAcyclicSet.of_contract {φ : (G ↾ C).connPartition.RepFun}
--     (h : (G /[φ, C]).IsAcyclicSet F) : G.IsAcyclicSet (F ∪ C) := by

--   sorry

end Graph
