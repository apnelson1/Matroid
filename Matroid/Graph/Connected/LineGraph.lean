import Matroid.Graph.Connected.MixedLineGraph

open Set Function WList

variable {α β : Type*} {G : Graph α β} {s t u v : α} {e f : β} {F : Set β}

namespace WList

/-- Walk on `L(G)` whose vertices are the edges of a nonempty walk in `G`. -/
def lineGraphEdgeWalk {w : WList α β} (hw : w.Nonempty) : WList β (Sym2 β) :=
  match w with
  | cons _ e (nil _) => nil e
  | cons _ e (cons u f w') => cons e (s(e, f)) (lineGraphEdgeWalk (Nonempty.cons u f w'))

@[simp]
lemma lineGraphEdgeWalk_firstEdge {w : WList α β} (hw : w.Nonempty) :
    (lineGraphEdgeWalk hw).first = hw.firstEdge := by
  obtain ⟨x, e, w', rfl⟩ := hw.exists_cons
  cases w' <;> simp [lineGraphEdgeWalk, Nonempty.firstEdge_cons]

lemma lineGraphEdgeWalk_lastEdge {w : WList α β} (hw : w.Nonempty) :
    (lineGraphEdgeWalk hw).last = hw.lastEdge := by
  induction w with
  | nil x => cases hw
  | cons x e w ih =>
    cases w with
    | nil y => simp [lineGraphEdgeWalk, lastEdge_cons_nil]
    | cons y f w'' => simp [lineGraphEdgeWalk, Nonempty.lastEdge_cons, ih (Nonempty.cons y f w'')]

end WList

namespace Graph

lemma lineGraph_deleteVerts_deleteEdges (F : Set β) : L(G ＼ F) = L(G) - F := by
  refine Graph.ext (by ext e; simp [vertexSet_LineGraph, edgeSet_deleteEdges, mem_diff]) ?_
  intro a e f
  simp_rw [← restrict_edgeSet_diff_eq_deleteEdges, LineGraph_isLink, deleteVerts_isLink_iff,
    LineGraph_isLink, restrict_inc]
  grind

instance [G.Finite] : L(G).Finite := finite_of_vertexSet_finite <| by simp [vertexSet_LineGraph]

lemma connBetween_restrict_of_inc_same_edge {e : β} (hu : G.Inc e u) (hv : G.Inc e v) :
    (G ↾ ({e} : Set β)).ConnBetween u v := by
  obtain rfl | hne := eq_or_ne u v
  · exact ConnBetween.refl (by simpa [restrict_inc, mem_singleton_iff] using hu.vertex_mem)
  refine ⟨cons u e (nil v), ?_, by simp, by simp⟩
  simp only [cons_isWalk_iff, nil_first, restrict_isLink, mem_singleton_iff, true_and,
    nil_isWalk_iff, vertexSet_restrict]
  use hu.isLink_of_inc_of_ne hv hne, hv.vertex_mem

lemma lineGraph_isWalk_restrict_connBetween {W : WList β (Sym2 β)} (hW : L(G).IsWalk W) :
    ∀ ⦃u v : α⦄, W.first ∈ E(G, u) → W.last ∈ E(G, v) → (G ↾ V(W)).ConnBetween u v := by
  induction hW with
  | @nil e heV =>
    intro u v hu hv
    simpa [nil_vertexSet, singleton_subset_iff, restrict_inc, mem_singleton_iff] using
      connBetween_restrict_of_inc_same_edge hu hv
  | @cons e₀ s12 W' hw' hlink ih =>
    intro u v hu hv
    obtain ⟨rfl, hne, x, he₀, he₁⟩ := hlink
    have hxv_big := (ih (by simpa [mem_incEdges_iff] using he₁) hv).mono
      (restrict_le_restrict (inter_subset_inter_right _ (subset_insert e₀ V(W'))))
    have hux_big := (connBetween_restrict_of_inc_same_edge hu he₀).mono <| restrict_le_restrict
      <| inter_subset_inter_right _ (singleton_subset_iff.mpr (mem_insert e₀ V(W')))
    rw [cons_vertexSet]
    exact hux_big.trans hxv_big

lemma IsPath.lineGraphEdgeWalk_isWalk {w : WList α β} (hw : w.Nonempty) (hP : G.IsPath w) :
    L(G).IsWalk (WList.lineGraphEdgeWalk hw) := by
  obtain ⟨x, e, w', rfl⟩ := hw.exists_cons
  cases w' with
  | nil y => simp [lineGraphEdgeWalk, (cons_isPath_iff.mp hP).1.inc_left.edge_mem]
  | cons y f w'' =>
    have hef : e ≠ f := by grind [hP.isTrail.edge_nodup]
    obtain ⟨heL, ⟨hfL, h1⟩, h2⟩ := by simpa only [cons_isPath_iff] using hP
    simp only [lineGraphEdgeWalk, cons_isWalk_iff, lineGraphEdgeWalk_firstEdge]
    exact ⟨⟨rfl, hef, ⟨y, heL.inc_right, hfL.inc_left⟩⟩,
      hP.of_cons.lineGraphEdgeWalk_isWalk (cons_nonempty y f w'')⟩

lemma connBetween_of_mem_incEdges_same_edge (hu : G.Inc e u) (hv : G.Inc e v) :
    G.ConnBetween u v := by
  obtain ⟨y, huy⟩ := hu
  obtain rfl | rfl := (isLink_iff_inc.mp huy).2.2 v hv
  · exact ConnBetween.refl huy.left_mem
  · exact huy.connBetween

lemma lineGraph_isWalk_connBetween_of_mem_inc {W : WList β (Sym2 β)} (hW : L(G).IsWalk W) :
    ∀ {u v : α}, W.first ∈ E(G, u) → W.last ∈ E(G, v) → G.ConnBetween u v := by
  induction hW with
  | @nil e heV =>
    intro u v hu hv
    exact connBetween_of_mem_incEdges_same_edge hu hv
  | @cons e₀ s12 W' hw' hlink ih =>
    intro u v hu hv
    obtain ⟨rfl, hne, x, he₀, he₁⟩ := hlink
    exact (connBetween_of_mem_incEdges_same_edge hu he₀).trans
      <| ih (by simpa [mem_incEdges_iff] using he₁) hv

lemma IsPath.inc_firstEdge_inc {P : WList α β} (hP : G.IsPath P) (hne : P.first ≠ P.last) :
    G.Inc (((first_ne_last_iff hP.nodup).mp hne).firstEdge P) P.first := by
  obtain ⟨x, e, w', rfl⟩ := (first_ne_last_iff hP.nodup).mp hne |>.exists_cons
  simpa [Nonempty.firstEdge_cons] using (cons_isPath_iff.mp hP).1.inc_left

lemma IsPath.inc_lastEdge_inc {P : WList α β} (hP : G.IsPath P) (hne : P.first ≠ P.last) :
    G.Inc (((first_ne_last_iff hP.nodup).mp hne).lastEdge P) P.last := by
  have hrev : P.reverse.first ≠ P.reverse.last := by
    simpa only [reverse_first, reverse_last, ne_eq] using hne.symm
  simpa [Nonempty.lastEdge, WList.reverse_first, WList.reverse_last, reverse_reverse,
    Nonempty.firstEdge_reverse] using hP.reverse.inc_firstEdge_inc hrev

lemma lineGraph_setConnected_incEdges_iff (G : Graph α β) (hst : s ≠ t) :
    L(G).SetConnected (E(G, s)) (E(G, t)) ↔ G.ConnBetween s t := by
  refine ⟨fun ⟨e₀, he₀, e₁, he₁, W, hW, h1, h2⟩ ↦
    lineGraph_isWalk_connBetween_of_mem_inc hW (h1 ▸ he₀) (h2 ▸ he₁), fun h ↦ ?_⟩
  obtain ⟨P, hP, rfl, rfl⟩ := h.exists_isPath
  have hPne : P.Nonempty := (first_ne_last_iff hP.nodup).mp hst
  refine ⟨hPne.firstEdge P, ?_, hPne.lastEdge P, ?_, P.lineGraphEdgeWalk hPne,
    hP.lineGraphEdgeWalk_isWalk hPne, ?_, ?_⟩
  · simpa [mem_incEdges_iff, Nonempty.firstEdge_mem hPne] using IsPath.inc_firstEdge_inc hP hst
  · simpa [mem_incEdges_iff, Nonempty.lastEdge_mem hPne] using IsPath.inc_lastEdge_inc hP hst
  · simp [lineGraphEdgeWalk_firstEdge]
  · simp [lineGraphEdgeWalk_lastEdge]

lemma lineGraph_deleteVerts_setConnected_incEdges_iff' (G : Graph α β) (hst : s ≠ t) (F : Set β) :
    (L(G) - F).SetConnected (E(G ＼ F, s)) (E(G ＼ F, t)) ↔ (G ＼ F).ConnBetween s t := by
  simpa [lineGraph_deleteVerts_deleteEdges] using
    lineGraph_setConnected_incEdges_iff (G ＼ F) hst

lemma lineGraph_deleteVerts_setConnected_incEdges_iff (G : Graph α β) (hst : s ≠ t) (F : Set β) :
    (L(G) - F).SetConnected (E(G, s)) (E(G, t)) ↔ (G ＼ F).ConnBetween s t :=
  Iff.trans (by grind [SetConnected]) (lineGraph_deleteVerts_setConnected_incEdges_iff' G hst F)

@[simp]
lemma isEdgeCutBetween_iff_lineGraph_isSetCut (hst : s ≠ t) (F : Set β) :
    G.IsEdgeCutBetween F s t ↔ L(G).IsSetCut (E(G, s)) (E(G, t)) F := by
  refine ⟨fun ⟨hF, hnc⟩ ↦ ⟨hF.trans (by simp), fun hcon ↦ ?_⟩,
    fun ⟨hF, hST⟩ ↦ ⟨hF.trans (by simp), fun hcon ↦ ?_⟩⟩
  · exact hnc ((lineGraph_deleteVerts_setConnected_incEdges_iff G hst F).mp hcon)
  · exact hST ((lineGraph_deleteVerts_setConnected_incEdges_iff G hst F).mpr hcon)

@[simp]
lemma edgeConnBetweenGE_iff_lineGraph_setConnGE (hst : s ≠ t) (n : ℕ) :
    G.EdgeConnBetweenGE s t n ↔ L(G).SetConnGE (E(G, s)) (E(G, t)) n := by
  simp only [EdgeConnBetweenGE, SetConnGE, isEdgeCutBetween_iff_lineGraph_isSetCut hst]

end Graph
