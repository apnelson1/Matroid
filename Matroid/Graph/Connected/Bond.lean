import Matroid.Graph.Connected.Basic
import Matroid.Graph.Connected.Vertex.Basic

open Set Function Nat WList symmDiff

variable {α β : Type*} {G H : Graph α β} {u v x x₁ x₂ y y₁ y₂ z : α} {e e' f g : β}
  {U V S T : Set α} {F F' R R' B : Set β} {C W P Q : WList α β}

namespace Graph

/-! ### IsEdgeCut -/

lemma IsWalk.inter_setLinkEdges_nonempty (hWf : W.first ∈ S) (hWl : W.last ∉ S) (hW : G.IsWalk W) :
    (E(W) ∩ δ(G, S)).Nonempty := by
  obtain ⟨e, x, y, hxy, hxS, hyS⟩ := W.exists_isLink_prop_not_prop W.first_mem hWf W.last_mem hWl
  use e, hxy.edge_mem, x, hxS, y
  replace hxy := hW.isLink_of_isLink hxy
  grind

lemma edgeDelete_setLinkEdge_not_connBetween (hx : x ∈ S) (hy : y ∉ S) :
    ¬ (G ＼ δ(G, S)).ConnBetween x y := by
  rintro ⟨P, hP, rfl, rfl⟩
  obtain ⟨e, heP, he⟩ := hP.inter_setLinkEdges_nonempty hx hy
  simp at he

lemma setLinkEdges_eq_empty_iff (hS : S ⊆ V(G)) : δ(G, S) = ∅ ↔ G[S] ≤c G := by
  refine ⟨fun h ↦ ⟨induce_le hS, ?_⟩, fun h ↦ ?_⟩
  · rintro e x ⟨y, hxy⟩ hxS
    rw [induce_edgeSet]
    use x, y, hxy, hxS
    contrapose! h
    use e, x, hxS, y, ⟨hxy.right_mem, h⟩
  ext e
  simp only [mem_setLinkEdges_iff, mem_diff, mem_empty_iff_false, iff_false, not_exists, not_and,
    and_imp]
  rintro x hxS y hy hyS hxy
  exact hyS <| h.isLink_iff_of_mem hxS |>.mpr hxy |>.right_mem

/-- A bond is a subset of edges that separates the graph into two connected components -/
def IsEdgeCut (G : Graph α β) (F : Set β) : Prop :=
  ∃ S : Set α, δ(G, S) = F

lemma IsEdgeCut.exists (hF : G.IsEdgeCut F) : ∃ S ⊆ V(G), δ(G, S) = F := by
  obtain ⟨S, rfl⟩ := hF
  use V(G) ∩ S, inter_subset_left ..
  ext e
  wlog he : e ∈ E(G)
  · grind
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
  simp_rw [hxy.mem_setLinkEdges_iff]
  grind

lemma IsEdgeCut.exists_of_isLink (he : G.IsLink e u v) (heF : e ∈ F) (hF : G.IsEdgeCut F) :
    ∃ S ⊆ V(G), δ(G, S) = F ∧ u ∈ S ∧ v ∉ S := by
  obtain ⟨S, hS, rfl⟩ := hF.exists
  rw [he.mem_setLinkEdges_iff] at heF
  obtain ⟨huS, hvS⟩ | ⟨huS, hvS⟩ := heF
  · use S, hS, rfl, huS, hvS.2
  use V(G) \ S, diff_subset, ?_, huS, by simp [hvS]
  rw [setLinkEdges_comm]
  simp only [sdiff_sdiff_right_self, Set.inf_eq_inter]
  exact setLinkEdges_vertexSet_inter_left G S (V(G) \ S)

lemma IsEdgeCut.subset_edgeSet (hF : G.IsEdgeCut F) : F ⊆ E(G) := by
  obtain ⟨S, rfl⟩ := hF
  exact setLinkEdges_subset G S (V(G) \ S)

lemma IsEdgeCut.not_isLoopAt (hF : G.IsEdgeCut F) (he : e ∈ F) : ¬ G.IsLoopAt e v := by
  obtain ⟨S, rfl⟩ := hF
  simp only [mem_setLinkEdges_iff, mem_diff] at he
  obtain ⟨x, hxS, y, ⟨hy, hyS⟩, hxy⟩ := he
  rintro hev
  obtain ⟨rfl, rfl⟩ := hev.eq_of_isLink hxy
  tauto

@[grind →]
lemma IsEdgeCut.symmDiff (hF : G.IsEdgeCut F) (hF' : G.IsEdgeCut F') : G.IsEdgeCut (F ∆ F') := by
  obtain ⟨S, rfl⟩ := hF
  obtain ⟨S', rfl⟩ := hF'
  use S ∆ S'
  ext e
  wlog he : e ∈ E(G)
  · grind
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
  simp only [hxy.mem_setLinkEdges_iff, mem_symmDiff, mem_diff, not_or, not_and, not_not, and_imp]
  grind

lemma IsEdgeCut.anti (hHG : H ≤ G) (hF : G.IsEdgeCut F) : H.IsEdgeCut (E(H) ∩ F) := by
  obtain ⟨S, rfl⟩ := hF
  use S
  exact setLinkEdges_eq_inter_of_le' hHG S

lemma IsEdgeCut.of_isClosedSubgraph (hGH : G ≤c H) (hF : G.IsEdgeCut F) : H.IsEdgeCut F := by
  obtain ⟨S, hSG, rfl⟩ := hF.exists
  use S
  ext e
  wlog he : e ∈ E(G)
  · refine iff_of_false ?_ (he <| G.setLinkEdges_subset _ _ ·)
    rintro ⟨x, hxS, y, ⟨hy, hyS⟩, hxy⟩
    exact he <| hGH.closed hxy.inc_left (hSG hxS)
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
  rw [hxy.mem_setLinkEdges_iff, (hxy.of_le hGH.le).mem_setLinkEdges_iff]
  simp [hxy.right_mem, hxy.left_mem, (hxy.of_le hGH.le).right_mem, (hxy.of_le hGH.le).left_mem]

lemma IsEdgeCut.not_connBetween_of_isLink (he : G.IsLink e u v) (heF : e ∈ F) (hF : G.IsEdgeCut F) :
    ¬ (G ＼ F).ConnBetween u v := by
  obtain ⟨S, rfl⟩ := hF
  simp only [mem_setLinkEdges_iff, mem_diff] at heF
  obtain ⟨x, hxS, y, ⟨hy, hyS⟩, hxy⟩ := heF
  wlog hxyeq : u = x ∧ v = y
  · obtain ⟨rfl, rfl⟩ := (he.isLink_iff.mp hxy).resolve_left hxyeq
    exact fun h ↦ this he.symm S v hxS u hxy hy hyS (by tauto) h.symm
  obtain ⟨rfl, rfl⟩ := hxyeq
  rintro ⟨w, hw, rfl, rfl⟩
  obtain ⟨e, hew, hxw⟩ := hw.inter_setLinkEdges_nonempty hxS hyS
  simp at hxw

lemma IsEdgeCut.exists_not_connBetween (hFne : F.Nonempty) (hF : G.IsEdgeCut F) :
    ∃ x y, G.ConnBetween x y ∧ ¬ (G ＼ F).ConnBetween x y := by
  obtain ⟨S, rfl⟩ := by exact hF
  obtain ⟨f, hfF⟩ := hFne
  obtain ⟨x, hxS, y, ⟨hy, hyS⟩, hxy⟩ := by exact hfF
  use x, y, hxy.connBetween, hF.not_connBetween_of_isLink hxy hfF

lemma isEdgeCut_subset_of_not_connBetween (hcon : G.ConnBetween x y)
    (hcon' : ¬ (G ＼ F).ConnBetween x y) :
    ∃ F', G.IsEdgeCut F' ∧ F' ⊆ F ∧ F'.Nonempty ∧ ¬ (G ＼ F').ConnBetween x y := by
  let G' := (G ＼ F).walkable x
  have := ((G ＼ F).walkable_isClosedSubgraph (u := x)).setLinkEdges_empty
  rw [setLinkEdges_eq_inter_of_le' edgeDelete_le] at this
  simp only [edgeDelete_edgeSet, diff_inter_right_comm,
    inter_eq_right.mpr (G.setLinkEdges_subset ..), diff_eq_empty] at this
  obtain ⟨P, hP, rfl, rfl⟩ := hcon.exists_isPath
  have hx : P.first ∈ V(G') := mem_walkable <| by simpa using hcon.left_mem
  have hy : P.last ∉ V(G') := by simpa using hcon'
  use δ(G, V(G')), (by use V(G')), this,
    (hP.isWalk.inter_setLinkEdges_nonempty hx hy).mono inter_subset_right
  rintro ⟨w, hw, hwf, hwl⟩
  obtain ⟨e, hew, he⟩ := hw.of_le edgeDelete_le |>.inter_setLinkEdges_nonempty (hwf ▸ hx) (hwl ▸ hy)
  exact hw.edgeSet_subset hew |>.2 he

lemma connBetween_edgeDeleted_eq_iff_subset_not_isEdgeCut : (G.ConnBetween = (G ＼ F).ConnBetween) ↔
    ∀ F' ⊆ F, F'.Nonempty → ¬ G.IsEdgeCut F' := by
  simp only [funext_iff, eq_iff_iff]
  refine ⟨fun h F' hF'F hF'ne hF' ↦ ?_,
    fun h x y ↦ ⟨fun hxy ↦ ?_, fun hxy ↦ hxy.mono edgeDelete_le⟩⟩
  · obtain ⟨x, y, hxy, hxy'⟩ := hF'.exists_not_connBetween hF'ne
    exact hxy' <| h x y |>.mp hxy |>.mono <| G.edgeDelete_anti_right hF'F
  by_contra! hF
  obtain ⟨F', hF', hF'F, hF'ne, hF'xy⟩ := isEdgeCut_subset_of_not_connBetween hxy hF
  exact h F' hF'F hF'ne hF'

/-! ### Bridges -/

/-- A bridge is a singleton edge separation -/
def IsBridge (G : Graph α β) (e : β) : Prop := G.IsEdgeCut {e}

lemma IsBridge.isEdgeCut (he : G.IsBridge e) : G.IsEdgeCut {e} := he

@[grind .]
lemma IsBridge.mem_edgeSet (he : G.IsBridge e) : e ∈ E(G) := by
  simpa using IsEdgeCut.subset_edgeSet he

lemma IsLink.isBridge_iff_not_connBetween (he : G.IsLink e x y) :
    G.IsBridge e ↔ ¬ (G ＼ {e}).ConnBetween x y := by
  refine ⟨fun h ↦ h.not_connBetween_of_isLink he rfl, fun h ↦ ?_⟩
  use V((G ＼ {e}).walkable x)
  ext f
  refine ⟨fun ⟨u, hxu, v, ⟨hv, hxv⟩, hfuv⟩ ↦ ?_, ?_⟩
  · by_contra! hfe
    replace hfuv : (G ＼ {e}).IsLink f u v := by simpa [hfuv]
    exact hxv <| hxu.trans hfuv.connBetween
  rintro rfl
  use x, (by simp [he.left_mem]), y, (by simpa [he.right_mem])

lemma IsLink.isBridge_iff_isEdgeCutBetween (he : G.IsLink e x y) :
    G.IsBridge e ↔ G.IsEdgeCutBetween {e} x y := by
  rw [he.isBridge_iff_not_connBetween, isEdgeCutBetween_iff]
  simp [he.edge_mem]

lemma IsBridge.anti_of_mem (hHG : H ≤ G) (heH : e ∈ E(H)) (he : G.IsBridge e) : H.IsBridge e := by
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet heH
  rw [hxy.isBridge_iff_not_connBetween]
  rw [(hxy.of_le hHG).isBridge_iff_not_connBetween] at he
  contrapose! he
  exact he.mono (by grw [hHG])

lemma not_isBridge_mono_of_mem (hHG : H ≤ G) (he : ¬ H.IsBridge e) (heH : e ∈ E(H)) :
    ¬ G.IsBridge e := by
  contrapose! he
  exact he.anti_of_mem (by grw [hHG]) heH

lemma IsBridge.of_isClosedSubgraph (hcle : H ≤c G) (he : H.IsBridge e) : G.IsBridge e := by
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he.mem_edgeSet
  rw [hxy.isBridge_iff_not_connBetween] at he
  rw [(hxy.of_le hcle.le).isBridge_iff_not_connBetween]
  contrapose! he
  obtain ⟨P, hP, rfl, rfl⟩ := he
  simp only [isWalk_edgeDelete_iff, disjoint_singleton_right, mem_edgeSet_iff] at hP
  use P, ?_
  simp only [isWalk_edgeDelete_iff, disjoint_singleton_right, mem_edgeSet_iff, hP.2,
    not_false_eq_true, and_true]
  exact hP.1.isWalk_isClosedSubgraph hcle ⟨P.first, first_mem, hxy.left_mem⟩

lemma IsClosedSubgraph.isBridge_iff (he : e ∈ E(H)) (h : H ≤c G) : G.IsBridge e ↔ H.IsBridge e :=
  ⟨fun hb ↦ hb.anti_of_mem h.le he, fun hb ↦ hb.of_isClosedSubgraph h⟩

lemma IsBridge.singleton_linkEdges (he : G.IsBridge e) (hl : G.IsLink e u v) :
    E(G, u, v) = {e} := by
  ext f
  rw [mem_linkEdges_iff]
  refine ⟨fun hf ↦ ?_, fun h ↦ h ▸ hl⟩
  obtain ⟨S, hS⟩ := he
  rw [← hS]
  obtain ⟨x, hxS, y, ⟨hy, hyS⟩, hexy⟩ : e ∈ E(G, S, V(G) \ S) := hS ▸ rfl
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hexy.eq_and_eq_or_eq_and_eq hl
  · use x, hxS, y, ⟨hy, hyS⟩, hf
  use x, hxS, y, ⟨hy, hyS⟩, hf.symm

lemma ConnBetween.edgeDelete_singleton_connBetween (h : G.ConnBetween x y) (he : ¬ G.IsBridge e) :
    (G ＼ {e}).ConnBetween x y := by
  by_contra! hecon
  obtain ⟨P, hP, rfl, rfl⟩ := h.exists_isPath
  have heP : e ∈ P.edge := by
    contrapose! hecon
    use P, by simpa [hP.isWalk]
  apply hecon
  obtain ⟨w, w', hw, hw', hew, hew', hVdj, hEdj, rfl⟩ := hP.eq_append_cons_of_edge_mem heP
  have := by simpa using hP.of_append_right
  rw [this.1.isBridge_iff_not_connBetween.not_left] at he
  simp only [first_cons, append_first_of_eq, append_last, last_cons]
  exact trans (trans (by use w; simpa [hw.isWalk]) he) (by use w'; simpa [hw'.isWalk])

lemma Preconnected.edgeDelete_singleton_preconnected (h : G.Preconnected) (he : ¬ G.IsBridge e) :
    (G ＼ {e}).Preconnected :=
  fun u v hu hv ↦ (h u v hu hv).edgeDelete_singleton_connBetween he

lemma Connected.edgeDelete_singleton_connected (hG : G.Connected) (he : ¬ G.IsBridge e) :
    (G ＼ {e}).Connected := by
  rw [connected_iff] at hG ⊢
  use hG.1, hG.2.edgeDelete_singleton_preconnected he

lemma Preconnected.edgeDelete_singleton_preconnected_iff (hG : G.Preconnected) :
    (G ＼ {e}).Preconnected ↔ ¬ G.IsBridge e := by
  refine ⟨fun h he => ?_, hG.edgeDelete_singleton_preconnected⟩
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he.mem_edgeSet
  rw [hxy.isBridge_iff_not_connBetween] at he
  exact he <| h _ _ hxy.left_mem hxy.right_mem

lemma Connected.edgeDelete_singleton_connected_iff (hG : G.Connected) :
    (G ＼ {e}).Connected ↔ ¬ G.IsBridge e := by
  refine ⟨fun h he => ?_, hG.edgeDelete_singleton_connected⟩
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he.mem_edgeSet
  rw [hxy.isBridge_iff_not_connBetween] at he
  exact he <| h.pre _ _ hxy.left_mem hxy.right_mem

lemma Preconnected.isBridge_iff (hG : G.Preconnected) :
    G.IsBridge e ↔ ¬ (G ＼ {e}).Preconnected := by
  rw [hG.edgeDelete_singleton_preconnected_iff.symm.not_right]

lemma Connected.isBridge_iff (hG : G.Connected) : G.IsBridge e ↔ ¬ (G ＼ {e}).Connected :=
  hG.edgeDelete_singleton_connected_iff.symm.not_right

lemma Connected.isBridge_iff_isEdgeSep (hG : G.Connected) (e : β) :
    G.IsBridge e ↔ G.IsEdgeSep {e} := by
  rw [hG.isBridge_iff, isEdgeSep_iff]
  simp only [singleton_subset_iff, iff_and_self]
  rintro hGe
  by_contra! he
  rw [edgeDelete_eq _ (by simpa)] at hGe
  tauto

lemma IsCompOf.edgeDelete_singleton_isCompOf (he : ¬ G.IsBridge e) (h : H.IsCompOf G) :
    (H ＼ {e}).IsCompOf (G ＼ {e}) := by
  obtain ⟨x, hx⟩ := h.nonempty
  exact (h.isClosedSubgraph.edgeDelete _).isCompOf_of_connected
  <| h.connected.edgeDelete_singleton_connected
  <| mt (IsBridge.of_isClosedSubgraph h.isClosedSubgraph) he

/-- Every edge of a path is a bridge -/
lemma IsPath.isBridge_of_mem (hP : G.IsPath P) (heP : e ∈ P.edge) : P.toGraph.IsBridge e := by
  rw [← hP.isWalk.toGraph_connected.edgeDelete_singleton_connected_iff.not_left]
  obtain ⟨P₁, P₂, hP₁, hP₂, heP₁, heP₂, hdj, hedj, rfl⟩ := hP.eq_append_cons_of_edge_mem heP
  rw [hP.isWalk.toGraph_eq_induce_restrict, append_vertexSet_of_eq (by simp)]
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

lemma IsPath.eq_of_isBridge_isLink (hP : G.IsPath P) (he : G.IsBridge e)
    (hl : G.IsLink e P.first P.last) : P = hl.walk := by
  obtain ⟨e, heP, rfl⟩ := hP.isWalk.exists_mem_isEdgeCutBetween
  <| hl.isBridge_iff_isEdgeCutBetween.1 he
  match P with
  | nil u => simp at heP
  | cons u f w =>
    obtain ⟨hl', hw, huw⟩ := by simpa using hP
    simp only [first_cons, last_cons, IsLink.walk, cons.injEq, true_and] at hl ⊢
    obtain ⟨rfl, heq⟩ := hP.first_eq_of_isLink_mem heP hl
    grind [hw.first_eq_last_iff.mp heq |>.eq_nil_last]

lemma IsLink.exists_cons_isCyclicWalk_of_not_isBridge (hb : ¬ G.IsBridge e) (hxy : G.IsLink e x y) :
    ∃ C, G.IsCyclicWalk (cons x e C) ∧ C.first = y := by
  rw [hxy.symm.isBridge_iff_not_connBetween, not_not] at hb
  obtain ⟨P, hP, rfl, rfl⟩ := hb.exists_isPath
  have := by simpa [subset_diff] using hP.isWalk.edgeSet_subset
  use P, (hP.of_le edgeDelete_le).cons_isCyclicWalk hxy.symm this.2

lemma exists_isCyclicWalk_of_not_isBridge (he : e ∈ E(G)) (hb : ¬ G.IsBridge e) :
    ∃ C, G.IsCyclicWalk C ∧ e ∈ C.edge := by
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
  obtain ⟨C, hC, heC⟩ := hxy.exists_cons_isCyclicWalk_of_not_isBridge hb
  use (cons x e C), hC, by simp

lemma not_isBridge_of_exists_isCyclicWalk (hC : ∃ C, G.IsCyclicWalk C ∧ e ∈ C.edge) :
    ¬ G.IsBridge e := by
  obtain ⟨C, hC, heC⟩ := hC
  obtain he := hC.isWalk.edge_mem_of_mem heC
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
  rw [hxy.isBridge_iff_not_connBetween, not_not]
  obtain ⟨P, hP, hPC⟩ := hC.exists_isPath_toGraph_eq_delete_edge heC
  have := hC.isWalk.isLink_iff_isLink_of_mem heC |>.mpr hxy
  have hmem : ∀ z, z ∈ P ↔ z ∈ C := by
    intro z
    rw [← P.mem_vertexSet_iff, ← toGraph_vertexSet, hPC]
    simp
  apply (hP.isWalk.toGraph_connected.pre x y (by simp [hmem, this.left_mem])
    (by simp [hmem, this.right_mem])).mono
  simp [hP.isWalk.toGraph_le]
  rw [← mem_edgeSet_iff, ← toGraph_edgeSet, hPC]
  simp

lemma IsCyclicWalk.not_isBridge_of_mem (hC : G.IsCyclicWalk C) (heC : e ∈ C.edge) :
    ¬ G.IsBridge e :=
  not_isBridge_of_exists_isCyclicWalk ⟨C, hC, heC⟩

@[simp, push, grind =]
lemma not_isBridge_iff_exists_isCyclicWalk (he : e ∈ E(G)) :
    ¬ G.IsBridge e ↔ ∃ C, G.IsCyclicWalk C ∧ e ∈ C.edge :=
  ⟨exists_isCyclicWalk_of_not_isBridge he, not_isBridge_of_exists_isCyclicWalk⟩

lemma isBridge_iff_notMem_isCyclicWalk (he : e ∈ E(G)) :
    G.IsBridge e ↔ ∀ C, G.IsCyclicWalk C → e ∉ C.edge := by
  rw [← not_iff_not]
  simp only [not_forall, not_not, exists_prop]
  exact not_isBridge_iff_exists_isCyclicWalk he

/-- A bond of a graph is a minimal nonempty edge-cut. -/
def IsBond (G : Graph α β) (F : Set β) : Prop :=
  Minimal (fun F ↦ G.IsEdgeCut F ∧ F.Nonempty) F

@[grind →]
lemma IsBond.subset_edgeSet (hB : G.IsBond B) : B ⊆ E(G) := by
  obtain ⟨h, -⟩ := hB.prop
  exact h.subset_edgeSet

lemma IsBond.isEdgeCut (hB : G.IsBond B) : G.IsEdgeCut B := hB.prop.1

lemma IsBond.nonempty (hB : G.IsBond B) : B.Nonempty := hB.prop.2

@[grind .]
lemma IsBridge.isBond (he : G.IsBridge e) : G.IsBond {e} := by
  refine ⟨⟨he, by simp⟩, fun F' hF' hF'e ↦ ?_⟩
  obtain rfl | rfl := subset_singleton_iff_eq.mp hF'e
  · simp at hF'
  exact hF'e

lemma IsBond.isBridge (heB : e ∈ B) (hB : G.IsBond B) : (G ＼ (B \ {e})).IsBridge e := by
  have := hB.prop.1.anti (edgeDelete_le (F := B \ {e}))
  rw [edgeDelete_edgeSet, inter_comm, inter_diff_distrib_left, inter_eq_left.mpr hB.subset_edgeSet,
    inter_eq_right.mpr diff_subset] at this
  simpa [heB] using this

lemma IsBond.of_isClosedSubgraph (hGH : G ≤c H) (hB : G.IsBond B) : H.IsBond B := by
  refine ⟨⟨hB.isEdgeCut.of_isClosedSubgraph hGH, hB.nonempty⟩, fun C ⟨hC, e, heC⟩ hCB ↦ ?_⟩
  exact hB.2 ⟨hC.anti hGH.le, e, hB.subset_edgeSet (hCB heC), heC⟩ (inter_subset_right
  |>.trans hCB) |>.trans inter_subset_right

lemma IsBond.exists_minimal_not_connBetween (hB : G.IsBond B) :
    ∃ x y, G.ConnBetween x y ∧ Minimal (fun F ↦ ¬ (G ＼ F).ConnBetween x y) B := by
  obtain ⟨x, y, hxy, hxy'⟩ := hB.isEdgeCut.exists_not_connBetween hB.nonempty
  use x, y, hxy, hxy'
  intro F hF hFB
  obtain ⟨F', hF', hF'F, hF'ne, hF'xy⟩ := isEdgeCut_subset_of_not_connBetween hxy hF
  exact hB.2 ⟨hF', hF'ne⟩ (hF'F.trans hFB) |>.trans hF'F

lemma isBond_of_conn (hS : S ⊆ V(G)) (hScon : G[S].Preconnected) (hS'con : (G - S).Preconnected)
    (h : δ(G, S).Nonempty) : G.IsBond δ(G, S) := by
  refine ⟨⟨(by use S), h⟩, fun F hF hFδ e he ↦ ?_⟩
  by_contra! heF
  obtain ⟨u, v, huv, huv'⟩ := hF.1.exists_not_connBetween hF.2
  absurd huv'
  clear h huv'
  have hSleF : G[S] ≤ G ＼ F := by
    apply le_of_le_le_subset_subset (induce_le hS) edgeDelete_le hS
    simp only [edgeDelete_edgeSet, subset_diff, induce_edgeSet_subset, true_and]
    apply Disjoint.mono_right <| hFδ.trans <| setLinkEdges_subset_setIncEdges_right ..
    rw [induce_edgeSet_eq_diff]
    exact disjoint_sdiff_left
  have hS'leF : (G - S) ≤ G ＼ F := by
    apply le_of_le_le_subset_subset vertexDelete_le edgeDelete_le (by grind)
    rw [vertexDelete_edgeSet_diff]
    simp only [edgeDelete_edgeSet, subset_diff, diff_subset, disjoint_comm, le_eq_subset,
      hF.1.subset_edgeSet, setIncEdges_subset, disjoint_sdiff_iff_le, true_and]
    exact hFδ.trans <| setLinkEdges_subset_setIncEdges_left ..
  clear hS hFδ
  obtain ⟨huS, hvS⟩ | h1 := em (u ∈ S ∧ v ∈ S)
  · exact hScon u v huS hvS |>.mono hSleF
  obtain ⟨huS, hvS⟩ | h2 := em (u ∉ S ∧ v ∉ S)
  · exact hS'con u v (by simp [huS, huv.left_mem]) (by simp [hvS, huv.right_mem]) |>.mono hS'leF
  wlog huS : u ∈ S
  · have h3 := by simpa using h2
    rw [and_comm] at h1 h2
    exact this hScon hS'con F hF e he heF v u huv.symm hSleF hS'leF h1 h2 (h3 huS) |>.symm
  simp only [huS, true_and] at h1
  obtain ⟨x, hxS, y, ⟨hy, hyS⟩, hxy⟩ := he
  have hxyF : (G ＼ F).IsLink e x y := ⟨hxy, heF⟩
  exact hScon u x huS hxS |>.mono hSleF |>.trans hxyF.connBetween |>.trans
  <| hS'con y v (by simp [hy, hyS]) (by simp [h1, huv.right_mem]) |>.mono hS'leF

lemma walkable_edgeDelete_connBetween_iff :
    (G.walkable x ＼ B).ConnBetween x y ↔ (G ＼ B).ConnBetween x y := by
  refine ⟨fun hBxy => ?_, fun hBxy => ?_⟩ <;> obtain ⟨W, hW, rfl, rfl⟩ := hBxy <;>
    have hcomp := G.walkable_isCompOf (by simpa using hW.first_mem) <;>
    rw [isWalk_edgeDelete_iff] at hW <;> use W, ?_
  · simp [hW.2, hW.1.of_le hcomp.le]
  have := hW.1.isWalk_isClosedSubgraph hcomp.isClosedSubgraph ⟨W.first, first_mem,
    mem_walkable hW.1.first_mem⟩
  simp [hW.2, this]

lemma exists_isBond_subset_of_not_connBetween (hcon : G.ConnBetween x y)
  (hcon' : ¬ (G ＼ F).ConnBetween x y) : ∃ B ⊆ F, G.IsBond B ∧ ¬ (G ＼ B).ConnBetween x y := by
  wlog hG : G.Preconnected
  · have hcomp := G.walkable_isCompOf hcon.left_mem
    have h := hcomp.preconnected x y (mem_walkable hcon.left_mem) hcon
    have hn : ¬(G.walkable x ＼ F).ConnBetween x y := by
      contrapose! hcon'
      rwa [walkable_edgeDelete_connBetween_iff] at hcon'
    obtain ⟨B, hBF, hB, hBxy⟩ := this (G := G.walkable x) h hn hcomp.preconnected
    use B, hBF, hB.of_isClosedSubgraph hcomp.isClosedSubgraph
    contrapose! hBxy
    rwa [walkable_edgeDelete_connBetween_iff]

  let Gx := (G ＼ F).walkable x
  let Gy := (G - V(Gx)).walkable y
  have hxGx : x ∈ V(Gx) := by simpa [mem_walkable, Gx] using hcon.left_mem
  have hxGy : x ∉ V(Gy) := fun h ↦ by simpa [mem_walkable, Gx] using h.right_mem
  have hyGx : y ∉ V(Gx) := hcon'
  have hyGy : y ∈ V(Gy) := by simpa [mem_walkable, Gy, hyGx] using hcon.right_mem
  have hδGx : δ(G, V(Gx)) ⊆ F := by
    rintro e ⟨u, huGx, v, ⟨hv, hvGx⟩, huv⟩
    contrapose! hvGx
    exact huGx.trans (IsLink.connBetween ⟨huv, hvGx⟩)
  have hδGy : δ(G, V(Gy)) ⊆ δ(G, V(Gx)) := by
    rintro e ⟨u, huGy, v, ⟨hv, hvGy⟩, huv⟩
    simp [huv.mem_setLinkEdges_iff, huGy.right_mem.2, huv.left_mem]
    contrapose! hvGy
    exact huGy.trans (IsLink.connBetween ⟨huv, huGy.right_mem, huv.right_mem, hvGy⟩)
  have hnxy : ¬(G ＼ δ(G, V(Gy))).ConnBetween x y := by
    rw [connBetween_comm]
    exact edgeDelete_setLinkEdge_not_connBetween (mem_walkable ⟨hcon.right_mem, hyGx⟩) hxGy
  refine ⟨δ(G, V(Gy)), ?_, ?_, hnxy⟩
  · rintro e ⟨u, huGy, v, ⟨hv, hvGy⟩, huv⟩
    exact hδGx <| hδGy <| by simp [huv.mem_setLinkEdges_iff, hvGy, huv.right_mem, huGy]
  clear hδGy hδGx hcon'
  have hGx : Gx.IsCompOf (G ＼ F) := walkable_isCompOf hcon.left_mem
  have hGxG : Gx ≤ G := hGx.le.trans edgeDelete_le
  have hGy : Gy.IsCompOf (G - V(Gx)) := walkable_isCompOf <| by simp [hyGx, hcon.right_mem]
  have hdj : StronglyDisjoint Gx Gy := by
    rw [StronglyDisjoint_iff_of_le_le hGxG (hGy.le.trans vertexDelete_le)]
    exact (subset_diff.mp hGy.subset).2.symm
  apply isBond_of_conn (hGy.subset.trans diff_subset)
  · have hGyi : Gy.IsInducedSubgraph G :=
      hGy.isInducedSubgraph.trans <| vertexDelete_isInducedSubgraph ..
    rw [hGyi.induce_vertexSet_eq]
    exact hGy.preconnected
  · have hGxcon : ∀ z, z ∈ V(Gx) → (G - V(Gy)).ConnBetween x z := by
      intro z hzGx
      refine hGx.preconnected x z hxGx hzGx |>.mono ?_
      rw [le_vertexDelete_iff]
      use hGxG, hdj.vertex
    refine preconnected_iff_exists_connBetween (⟨hcon.left_mem, hxGy⟩ : x ∈ V(G - V(Gy))) |>.mpr
      fun z hz ↦ ?_
    by_cases hzGx : z ∈ V(Gx)
    · exact hGxcon z hzGx
    rw [vertexDelete_vertexSet] at hz
    obtain ⟨P, hP, rfl, rfl⟩ := hG z y hz.1 hcon.right_mem |>.exists_isPath
    have hPfrom : G.IsWalkFrom ((V(G) \ V(Gy)) \ V(Gx)) V(Gy) P := ⟨hP.isWalk, ⟨hz, hzGx⟩, hyGy⟩
    classical
    let P' := P.prefixUntil (· ∈ V(Gx))
    have hC : G.IsSetCut ((V(G) \ V(Gy)) \ V(Gx)) V(Gy) V(Gx) := by
      use vertexSet_mono hGxG, fun ⟨_, hud, _, hvGy, huv⟩ ↦ hud.1.2 <| hvGy.trans huv.symm
    have := hC.prefixUntil_isWalk_vertexDelete hP.isWalk (⟨hz, hzGx⟩ : _ ∈ _ \ V(Gx)) hyGy
    |>.connBetween_first_last.symm
    rw [hdj.vertex.symm.sdiff_eq_left, prefixUntil_first] at this
    exact (hGxcon P'.last (prefixUntil_prop_last (hPfrom.exists_mem_isSetCut hC))).trans this
  · by_contra! h
    simp [h, hcon] at hnxy

lemma IsEdgeCut.exists_isBond_of_nonempty (hne : F.Nonempty) (hF : G.IsEdgeCut F) :
    ∃ B ⊆ F, G.IsBond B := by
  obtain ⟨x, y, hxy, hFxy⟩ := hF.exists_not_connBetween hne
  obtain ⟨B, hBF, hB, -⟩ := exists_isBond_subset_of_not_connBetween hxy hFxy
  exact ⟨B, hBF, hB⟩

lemma IsEdgeCut.disjoint_union_isBond {F} (hfin : F.Finite) (hF : G.IsEdgeCut F) :
    ∃ S : Set (Set β), S.PairwiseDisjoint id ∧ ⋃₀ S = F ∧ ∀ B ∈ S, G.IsBond B := by
  obtain rfl | hne := F.eq_empty_or_nonempty
  · exact ⟨∅, by simp⟩
  obtain ⟨B, hBF, hB⟩ := hF.exists_isBond_of_nonempty hne
  have hF' := symmDiff_of_ge hBF ▸ hF.symmDiff hB.prop.1
  obtain rfl | hne' := eq_or_ne B F
  · exact ⟨{B}, by simpa⟩
  replace hBF : B ⊂ F := hBF.ssubset_of_ne hne'
  have hencard : (F \ B).encard < F.encard :=
    hfin.diff.encard_lt_encard <| diff_ssubset hBF.subset hB.prop.2
  obtain ⟨S, hSdj, hUS, hSB⟩ := hF'.disjoint_union_isBond hfin.diff
  have hdj : Disjoint B (⋃₀ S) := hUS ▸ disjoint_sdiff_right
  use insert B S, ?_, by simp [hUS, hBF.subset], by simpa [hB]
  refine hSdj.insert_of_notMem ?_ fun B' hB'S ↦ hdj.mono_right <| subset_sUnion_of_mem hB'S
  rintro hBS
  obtain rfl := by simpa using hdj.mono_right <| subset_sUnion_of_mem hBS
  simpa using hB.prop.2
termination_by F.encard

-- lemma edgeConnGE_iff_isEdgeCut (n : ℕ) :
--     G.EdgeConnGE n ↔ ∀ F, G.IsEdgeCut F → n ≤ F.encard := by
--   refine ⟨fun h F hF => ?_, fun h s t hs ht F ⟨hF, hst⟩ => ?_⟩
--   · obtain ⟨x, y, hxy, hFxy⟩ := hF.exists_not_connBetween hFne
--     have := h hxy.left_mem hxy.right_mem (F := E(G) ∩ F) ⟨inter_subset_left, sorry⟩
--     exact this.trans <| encard_le_encard inter_subset_right
--   have := isEdgeCut_subset_of_not_connBetween
--   have := h F

-- lemma edgeConnGE_iff_isBond (n : ℕ) : G.EdgeConnGE n ↔ ∀ b, G.IsBond b → n ≤ b.encard := by
