import Matroid.Graph.Subgraph.Union
import Matroid.Graph.Constructions.Basic

variable {α β ι ι' : Type*} {a b c x y z u v w : α} {e f : β} {G G₁ G₂ H H₁ H₂ : Graph α β}
  {F F₁ F₂ : Set β} {X Y : Set α} {s t : Set (Graph α β)}

open Set Function

namespace Graph


/-! ### Adding one edge -/

-- @[simp]
-- lemma singleEdge_compatible_iff : Compatible (Graph.singleEdge u v e) G ↔
--     (e ∈ E(G) → G.IsLink e u v ∧ ({{u}, {v}} : Set (Set α)) ⊆ V(G)) := by
--   rw [pair_subset_iff]
--   refine ⟨fun h he ↦ ?_, fun h f a b ⟨hfe, hf⟩ ↦ ?_⟩
--   · simp only [← h ⟨by simp, he⟩, singleEdge_isLink, and_self, true_or, IsLink.symm, true_and]

--     sorry
--   obtain rfl : f = e := by simpa using hfe
--   obtain ⟨hfuv, hu, hv⟩ := h hf
--   simp only [singleEdge_isLink, true_and]
--   refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
--   · obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h
--     · exact hfuv
--     · exact symm hfuv
--   obtain ⟨ha, hb⟩ | ⟨ha, hb⟩ := h.isLink_iff_dup_and_dup_or_dup_and_dup.mp hfuv
--   · obtain rfl : a = u := sorry
--     obtain rfl : b = v := sorry
--     simp
--   · obtain rfl : a = v := sorry
--     obtain rfl : b = u := sorry
--     simp

/-- Add a new edge `e` between vertices `a` and `b`. If `e` is already in the graph,
its ends change to `a` and `b`. -/
@[simps! edgeSet isLink]
protected def addEdge (G : Graph α β) (e : β) (a b : α) : Graph α β :=
  Graph.singleEdge a b e ∪ G

@[simp]
lemma addEdge_labelSet : L(G.addEdge e a b) = {a, b} ∪ L(G) := by
  simp [Graph.addEdge]

@[simp]
lemma addEdge_vertexSet : V(G.addEdge e a b) = V(Graph.singleEdge a b e) ⊔ V(G) := by
  simp [Graph.addEdge]

lemma addEdge_isLink' (G : Graph α β) (e : β) (a b : α) : (G.addEdge e a b).IsLink e a b := by
  rw [Graph.addEdge]
  exact IsLink.le_union_left isLink_singleEdge

lemma addEdge_isLink_of_ne (hf : G.IsLink f x y) (hne : f ≠ e) (a b : α) :
    (G.addEdge e a b).IsLink f x y := by
  rw [Graph.addEdge]
  exact hf.le_union_right_of_not_mem hne

lemma addEdge_isLink_iff (he : e ∉ E(G)) :
    (G.addEdge e a b).IsLink f x y ↔ (f = e ∧ s(a,b) = s(x,y)) ∨ G.IsLink f x y := by
  have hc : Compatible (Graph.singleEdge x y e) G := by simp [he]
  simp only [Graph.addEdge, union_isLink_iff, singleEdge_isLink, singleEdge_edgeSet,
    mem_singleton_iff, edgeDelete_isLink, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
  obtain rfl | hne := eq_or_ne e f
  · have hl : ¬ G.IsLink e x y := fun h ↦ he h.edge_mem
    simp only [true_and, not_true_eq_false, hl, and_self, or_false]
    tauto
  simp [hne.symm]

lemma addEdge_deleteEdge (he : e ∉ E(G)) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    (G.addEdge e x y) ＼ {e} = G := by
  have hc : Compatible (Graph.singleEdge x y e) G := by simp [he]
  simp only [Graph.addEdge, Graph.ext_iff, edgeDelete_vertexSet, union_vertexSet,
    singleEdge_vertexSet, union_eq_right, insert_subset_iff, hx, singleton_subset_iff, hy, and_self,
    edgeDelete_isLink, hc.union_isLink_iff, singleEdge_isLink, mem_singleton_iff, true_and]
  intro f p q
  obtain rfl | hne := eq_or_ne f e
  · suffices ¬ G.IsLink f p q by simpa
    exact fun hf ↦ he hf.edge_mem
  simp [hne]

lemma addEdge_le (hle : H ≤ G) (he : G.IsLink e x y) : H.addEdge e x y ≤ G :=
  Graph.union_le (by simpa) hle

lemma le_addEdge (he : e ∉ E(G)) : G ≤ G.addEdge e x y :=
  Compatible.right_le_union <| by simp [he]

lemma addEdge_mono (hle : H ≤ G) : H.addEdge e x y ≤ G.addEdge e x y :=
  union_mono_right hle

lemma deleteEdge_le_addEdge : G ＼ {e} ≤ G.addEdge e x y := by
  rw [Graph.addEdge, union_eq_union_edgeDelete]
  simp only [singleEdge_edgeSet]
  exact Compatible.right_le_union <| by simp

lemma deleteEdge_addEdge : (G ＼ {e}).addEdge e x y = G.addEdge e x y := by
  refine le_antisymm (addEdge_mono edgeDelete_le) ?_
  unfold Graph.addEdge
  rw [union_le_iff]
  refine ⟨Graph.left_le_union (Graph.singleEdge x y e) (G ＼ {e}), Compatible.right_le_union ?_⟩
  simp

lemma addEdge_eq_self (hbtw : G.IsLink e x y) : G.addEdge e x y = G :=
  le_antisymm (addEdge_le (by simp) hbtw) <| Compatible.right_le_union <| by simp [hbtw]

lemma addEdge_idem : (G.addEdge e x y).addEdge e x y = G.addEdge e x y :=
  addEdge_eq_self <| addEdge_isLink G e x y

lemma isSpanningSubgraph_addEdge (he : e ∉ E(G)) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    G ≤s G.addEdge e x y := by
  nth_rw 1 [← addEdge_deleteEdge he hx hy]
  exact edgeDelete_isSpanningSubgraph

lemma IsLink.deleteEdge_addEdge (h : G.IsLink e x y) : (G ＼ {e}).addEdge e x y = G :=
  ext_of_le_le (addEdge_le (by simp) h) le_rfl (by simp [pair_subset_iff, h.left_mem, h.right_mem])
    <| by simp [h.edge_mem]


end Graph
