import Matroid.Graph.Connected.Basic
import Matroid.Graph.Connected.Vertex.Basic

open Set Function Nat WList symmDiff

variable {α β : Type*} {G H : Graph α β} {u v x x₁ x₂ y y₁ y₂ z : α} {e e' f g : β}
  {U V S T : Set α} {F F' R R' B : Set β} {C W P Q : WList α β}

namespace Graph

/-! ### Bonds -/

lemma IsWalk.inter_linkEdgesSet_nonempty (hWf : W.first ∈ S) (hWl : W.last ∉ S) (hW : G.IsWalk W) :
    (E(W) ∩ δ(G, S)).Nonempty := by
  obtain ⟨e, x, y, hxy, hxS, hyS⟩ := W.exists_isLink_prop_not_prop W.first_mem hWf W.last_mem hWl
  use e, hxy.edge_mem, x, hxS, y
  replace hxy := hW.isLink_of_isLink hxy
  grind

lemma linkEdgeSet_eq_empty_iff (hS : S ⊆ V(G)) : δ(G, S) = ∅ ↔ G[S] ≤c G := by
  refine ⟨fun h ↦ ⟨induce_le hS, ?_⟩, fun h ↦ ?_⟩
  · rintro e x ⟨y, hxy⟩ hxS
    rw [induce_edgeSet]
    use x, y, hxy, hxS
    contrapose! h
    use e, x, hxS, y, ⟨hxy.right_mem, h⟩
  ext e
  simp only [mem_linkEdgesSet_iff, mem_diff, mem_empty_iff_false, iff_false, not_exists, not_and,
    and_imp]
  rintro x hxS y hy hyS hxy
  exact hyS <| h.isLink_iff_of_mem hxS |>.mpr hxy |>.right_mem

/-- A bond is a subset of edges that separates the graph into two connected components -/
def IsEdgeCut (G : Graph α β) (F : Set β) : Prop :=
  ∃ S : Set α, δ(G, S) = F

lemma IsEdgeCut.subset_edgeSet (hF : G.IsEdgeCut F) : F ⊆ E(G) := by
  obtain ⟨S, rfl⟩ := hF
  exact linkEdgesSet_subset G S (V(G) \ S)

lemma IsEdgeCut.not_isLoopAt (hF : G.IsEdgeCut F) (he : e ∈ F) : ¬ G.IsLoopAt e v := by
  obtain ⟨S, rfl⟩ := hF
  simp only [mem_linkEdgesSet_iff, mem_diff] at he
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
  grind [hxy.mem_linkEdgesSet_iff]

lemma IsEdgeCut.anti (hHG : H ≤ G) (hF : G.IsEdgeCut F) : H.IsEdgeCut (E(H) ∩ F) := by
  obtain ⟨S, rfl⟩ := hF
  use S
  exact linkEdgesSet_eq_inter_of_le' hHG S

lemma IsEdgeCut.not_connBetween_of_isLink (hF : G.IsEdgeCut F) (he : G.IsLink e u v) (heF : e ∈ F) :
    ¬ (G ＼ F).ConnBetween u v := by
  obtain ⟨S, rfl⟩ := hF
  simp only [mem_linkEdgesSet_iff, mem_diff] at heF
  obtain ⟨x, hxS, y, ⟨hy, hyS⟩, hxy⟩ := heF
  wlog hxyeq : u = x ∧ v = y
  · obtain ⟨rfl, rfl⟩ := (he.isLink_iff.mp hxy).resolve_left hxyeq
    exact fun h ↦ this he.symm S v hxS u hxy hy hyS (by tauto) h.symm
  obtain ⟨rfl, rfl⟩ := hxyeq
  rintro hcon
  obtain ⟨P, hP, rfl, rfl⟩ := hcon.exists_isPath
  obtain ⟨_, x, y, h, hxS, hyS⟩ := exists_dInc_prop_not_prop hxS hyS
  have hy := by simpa using hP.isWalk.vertexSet_subset h.right_mem
  replace h := hP.isWalk.isLink_of_dInc h
  have := by simpa [mem_linkEdgesSet_iff] using h.edge_mem
  exact this.2 x hxS y hy hyS h.1

-- lemma isEdgeCut_subset_of_not_connBetween (hcon : G.ConnBetween x y)
--     (hcon' : ¬ (G ＼ F).ConnBetween x y) : ∃ F', G.IsEdgeCut F' ∧ F' ⊆ F := by
--   let G' := (G ＼ F).walkable x
--   have := ((G ＼ F).walkable_isClosedSubgraph (u := x)).linkEdgesSet_empty
--   rw [linkEdgesSet_eq_inter_of_le' edgeDelete_le] at this
--   simp only [edgeDelete_edgeSet, diff_inter_right_comm,
--     inter_eq_right.mpr (G.linkEdgesSet_subset ..), diff_eq_empty] at this
--   use δ(G, V(G')), ?_
--   use V(G')

def IsBond (G : Graph α β) (F : Set β) : Prop :=
  Minimal (fun F ↦ G.IsEdgeCut F ∧ F.Nonempty) F

lemma IsBond.subset_edgeSet (hB : G.IsBond B) : B ⊆ E(G) := by
  obtain ⟨h, -⟩ := hB.prop
  exact h.subset_edgeSet

lemma IsEdgeCut.exists_isBond_of_nonempty (hfin : F.Finite) (hne : F.Nonempty) (hF : G.IsEdgeCut F):
    ∃ B ⊆ F, G.IsBond B := by
  have := hfin.powerset.subset (by grind : {F₀ | F₀ ⊆ F ∧ G.IsEdgeCut F₀ ∧ F₀.Nonempty} ⊆ _)
  obtain ⟨B, hB⟩ := Finite.exists_minimal this (by use F, by simp)
  use B, hB.prop.1, hB.prop.2, fun B' hB' hB'le ↦ hB.2 ⟨hB'le.trans hB.prop.1, hB'⟩ hB'le

lemma IsEdgeCut.disjoint_union_isBond {F} (hfin : F.Finite) (hF : G.IsEdgeCut F) :
    ∃ S : Set (Set β), S.PairwiseDisjoint id ∧ ⋃₀ S = F ∧ ∀ B ∈ S, G.IsBond B := by
  obtain rfl | hne := F.eq_empty_or_nonempty
  · exact ⟨∅, by simp⟩
  obtain ⟨B, hBF, hB⟩ := hF.exists_isBond_of_nonempty hfin hne
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

-- lemma foo (hcon : G.ConnBetween x y) (hcon' : ¬ (G ＼ F).ConnBetween x y) :
--     ∃ B, G.IsBond B ∧ B ⊆ F := by

/-! ### Bridges -/

/-- A bridge is a singleton edge separation -/
def IsBridge (G : Graph α β) (e : β) : Prop := G.IsEdgeCut {e}

@[grind .]
lemma IsBridge.mem_edgeSet (he : G.IsBridge e) : e ∈ E(G) := by
  simpa using IsEdgeCut.subset_edgeSet he

@[grind .]
lemma IsBridge.isBond (he : G.IsBridge e) : G.IsBond {e} := by
  refine ⟨⟨he, by simp⟩, fun F' hF' hF'e ↦ ?_⟩
  obtain rfl | rfl := subset_singleton_iff_eq.mp hF'e
  · simp at hF'
  exact hF'e

-- This lemma will be proved later using the equivalence with cycles
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

lemma IsBridge.anti_of_mem (he : G.IsBridge e) (hHG : H ≤ G) (heH : e ∈ E(H)) : H.IsBridge e := by
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

lemma exists_isCyclicWalk_of_not_isBridge (he : e ∈ E(G)) (hb : ¬ G.IsBridge e) :
    ∃ C, G.IsCyclicWalk C ∧ e ∈ C.edge := by
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
  rw [hxy.isBridge_iff_not_connBetween, not_not] at hb
  obtain ⟨P, hP, rfl, rfl⟩ := hb.exists_isPath
  use cons P.last e P, ?_, by simp
  have := by simpa [subset_diff] using hP.isWalk.edgeSet_subset
  exact (hP.of_le edgeDelete_le).cons_isCyclicWalk hxy this.2

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

lemma IsLeaf.delete_connected (hx : G.IsLeaf x) (hG : G.Connected) : (G - x).Connected := by
  obtain ⟨y, hy : G.Adj x y, hu⟩ := hx.exists_unique_adj
  refine connected_of_vertex ⟨hy.right_mem, fun h : y = x ↦ hx.not_adj_self (h ▸ hy)⟩ fun z hz ↦ ?_
  obtain ⟨P, hP, rfl, rfl⟩ := (hG.connBetween hz.1 hy.right_mem).exists_isPath
  refine IsWalk.connBetween_first_last <| isWalk_vertexDelete_iff.2 ⟨hP.isWalk, ?_⟩
  simp only [disjoint_singleton_right, mem_vertexSet_iff]
  intro hxP
  obtain rfl | rfl := hx.eq_first_or_eq_last_of_mem_path hP hxP
  · simp at hz
  exact hx.not_adj_self hy

/-- Deleting the first vertex of a maximal path of a connected graph gives a connected graph. -/
lemma Connected.delete_first_connected_of_maximal_isPath (hG : G.Connected) (hnt : V(G).Nontrivial)
    (hP : Maximal (fun P ↦ G.IsPath P) P) : (G - P.first).Connected := by
  cases P with
  | nil u =>
    obtain ⟨e, y, huy, hne⟩ := hG.exists_isLink_of_mem hnt (x := u) (by simpa using hP.prop)
    exact False.elim <| hne.symm <| by
      simpa [huy, huy.right_mem] using hP.eq_of_ge (y := cons u e (nil y))
  | cons u e P =>
    have ⟨he, hP', huP⟩ : G.IsLink e u P.first ∧ G.IsPath P ∧ u ∉ P := by simpa using hP.prop
    by_contra hcon
    simp only [first_cons] at hcon
    have hP'' : (G - u).IsPath P := by simp [isPath_vertexDelete_iff, huP, hP']
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
      simp only [vertexDelete_singleton, vertexDelete_isLink_iff, hxy, mem_singleton_iff, true_and]
      constructor <;> (rintro rfl; contradiction)
    rintro x hx ⟨f, hux⟩
    have hne : u ≠ x := by rintro rfl; contradiction
    refine S.disjoint.notMem_of_mem_left (hPS ?_) hx
    simpa [hne.symm] using mem_of_adj_first_of_maximal_isPath hP hux.symm.adj

/-- Deleting the last vertex of a maximal path of a connected graph gives a connected graph. -/
lemma Connected.delete_last_connected_of_maximal_isPath (hG : G.Connected) (hnt : V(G).Nontrivial)
    (hP : Maximal (fun P ↦ G.IsPath P) P) : (G - P.last).Connected := by
  suffices aux : Maximal (fun P ↦ G.IsPath P) P.reverse by
    simpa using hG.delete_first_connected_of_maximal_isPath hnt aux
  refine ⟨by simpa using hP.prop, fun Q hQ hPQ ↦ ?_⟩
  simp [hP.eq_of_le (y := Q.reverse) (by simpa) (by simpa using IsSublist.reverse hPQ)]

/-- Every finite connected graph on at least two vertices has a vertex whose deletion
preserves its connectedness.
(This requires a finite graph, since otherwise an infinite path is a counterexample.) -/
lemma Connected.exists_delete_vertex_connected [G.Finite] (hG : G.Connected)
    (hnt : V(G).Nontrivial) : ∃ x ∈ V(G), (G - x).Connected := by
  obtain ⟨x, hx⟩ := hG.nonempty
  obtain ⟨P, hP⟩ := Finite.exists_maximal G.isPath_finite ⟨nil x, by simpa⟩
  exact ⟨_, hP.prop.isWalk.first_mem, hG.delete_first_connected_of_maximal_isPath hnt hP⟩

lemma Preconnected.left_mem_of_edgeDelete_linkEdges (h : G.Preconnected)
    (h' : ¬ (G ＼ E(G, u, v)).Preconnected) : u ∈ V(G) := by
  by_contra huv
  simp [huv, h] at h'

lemma Preconnected.right_mem_of_edgeDelete_linkEdges (h : G.Preconnected)
    (h' : ¬ (G ＼ E(G, u, v)).Preconnected) : v ∈ V(G) := by
  by_contra huv
  simp [huv, h] at h'

-- lemma Preconnected.connBetween_of_edgeDelete_linkEdges (h : G.Preconnected)
--     (h' : ¬ (G ＼ E(G, u, v)).Preconnected) (hx : x ∈ V(G)) :
--     (G ＼ E(G, u, v)).ConnBetween u x ∨ (G ＼ E(G, u, v)).ConnBetween v x := by
--   classical
--   obtain ⟨P, hP, rfl, rfl⟩ := h x u hx (h.left_mem_of_edgeDelete_linkEdges h')
--   let H := (Subgraph.ofEdge G E(G, P.first, v))ᶜ
--   have := hP.prefixUntil_isWalk_subgraph (H := H) ?_
--   simp? [H, Subgraph.compl_compl] at this
--   sorry
