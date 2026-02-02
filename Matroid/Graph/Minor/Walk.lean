import Matroid.Graph.Minor.Defs
import Matroid.Graph.Forest

variable {α β ι ι' : Type*} {x y z u v w : α} {e f : β} {G G₁ G₂ H H₁ H₂ I : Graph α β}
  {C D F F₁ F₂ : Set β} {X Y : Set α} {Gs Hs : Set (Graph α β)} {w w' P Q c : WList α β}
  {φ : α → α}

open Set Function WList

namespace Graph

lemma IsWalk.edgeRemove_contract [DecidablePred (· ∈ C)] (h : G.IsWalk w)
    (hφ : (G ↾ C).connPartition.IsRepFun φ) : (G /[φ, C]).IsWalk <| (w.map φ).edgeRemove C := by
  induction w with
  | nil x =>
    simp only [nil_isWalk_iff, map_nil, edgeRemove_nil, contract_vertexSet, mem_image] at h ⊢
    grind
  | cons x e w ih =>
    simp_all only [cons_isWalk_iff, map_cons, forall_const, edgeRemove_cons]
    split_ifs with heC
    · exact ih
    obtain ⟨hl, h⟩ := h
    have := edgeRemove_first (hφ.isContractClosed.exists_isLoopAt_of_isWalk h) (h.map φ)
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

lemma IsTrail.edgeRemove_contract [DecidablePred (· ∈ C)] (h : G.IsTrail w)
    (hφ : (G ↾ C).connPartition.IsRepFun φ) : (G /[φ, C]).IsTrail ((w.map φ).edgeRemove C) :=
  ⟨h.isWalk.edgeRemove_contract hφ, h.edge_nodup.sublist <| by simp⟩

lemma IsTour.edgeRemove_contract [DecidablePred (· ∈ C)] (h : G.IsTour w)
    (hφ : (G ↾ C).connPartition.IsRepFun φ) (hne : ∃ e, e ∈ w.edge ∧ e ∉ C) :
    (G /[φ, C]).IsTour ((w.map φ).edgeRemove C) := by
  refine ⟨h.toIsTrail.edgeRemove_contract hφ, ?_, ?_⟩
  · obtain ⟨e, he, heC⟩ := hne
    rw [nonempty_iff_exists_edge]
    use e
    simp [he, heC]
  have := edgeRemove_first (hφ.isContractClosed.exists_isLoopAt_of_isWalk h.isWalk)
  <| h.isWalk.map φ
  simp only [WList.IsClosed, this, map_first, edgeRemove_last, map_last]
  exact congrArg φ h.isClosed

-- lemma IsForest.contract (φ : (G ↾ C).connPartition.RepFun) (hC : (G ↾ C).IsForest) :
--     ((G /[φ, C]) ↾ F).IsForest ↔ (G ↾ (F ∪ C)).IsForest := by
--   classical
--   rw [isForest_iff_isTrail_eq_eq, isForest_iff_isTrail_eq_eq]
--   refine ⟨fun h P Q hP hQ hfirst hlast => ?_, fun h P Q hP hQ hfirst hlast => ?_⟩
--   ·
--   sorry

-- lemma IsAcyclicSet.of_contract {φ : (G ↾ C).connPartition.RepFun}
--     (h : (G /[φ, C]).IsAcyclicSet F) : G.IsAcyclicSet (F ∪ C) := by

--   sorry

end Graph
