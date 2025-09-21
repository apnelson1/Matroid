import Matroid.Graph.Subgraph.Union

variable {α β ι ι' : Type*} {a b c x y z u v w : Set α} {e f : β} {G G₁ G₂ H H₁ H₂ : Graph α β}
  {F F₁ F₂ : Set β} {X Y : Set (Set α)} {s t : Set (Graph α β)} {P Q : Partition (Set α)}

open Set Function

-- This seems useful but not yet in mathlib?
lemma assume_common_imp_of_iff {P1 P2 : Prop} (Q : Prop) (h1 : P1 → Q) (h2 : P2 → Q) :
    (P1 ↔ P2) ↔ (Q → (P1 ↔ P2)) := by
  tauto

namespace Graph


/-! ### Adding one edge -/

/-- Add a new edge `e` between vertices `a` and `b`. If `e` is already in the graph,
its ends change to `a` and `b`. -/
@[simps! vertexSet vertexPartition edgeSet]
protected def addEdge (G : Graph α β) (e : β) (a b : Set α) :
    Graph α β := Graph.banana a b {e} ∪ G

@[simp↓]
lemma addEdge_vertexSet_of_mem (ha : a ∈ V(G)) (hb : b ∈ V(G)) : V(G.addEdge e a b) = V(G) := by
  by_cases hab : a = b
  · subst b
    simp [ha, Graph.addEdge, (G.nonempty_of_mem ha).ne_empty]
  rw [Graph.addEdge, union_vertexSet (banana_dup_agree_of_mem ha hb), banana_vertexSet_of_disjoint
    (G.nonempty_of_mem ha) (G.nonempty_of_mem hb) (G.disjoint_of_mem ha hb hab), insert_union]
  simp [ha, hb]

-- lemma subset_addEdge_vertexSet : V(G) ⊆ V(G.addEdge e a b) := by
--   rw [Partition.subset_iff_rel]
--   rintro x y hx
--   rw [addEdge_dup]
--   simp only [iff_or_self, and_imp]
--   rintro rfl (rfl | rfl) <;> exact Partition.rel_self_of_mem_supp hx

@[simp]
lemma addEdge_isLink (ha : a ∈ V(G)) (hb : b ∈ V(G)) : (G.addEdge e a b).IsLink f x y ↔
    f = e ∧ s(x, y) = s(a, b) ∨ f ≠ e ∧ G.IsLink f x y := by
  rw [Graph.addEdge, union_isLink (banana_dup_agree_of_mem ha hb)]
  by_cases hab : a = b
  · subst b
    simp [G.nonempty_of_mem ha]
    tauto
  simp only [G.nonempty_of_mem ha, G.nonempty_of_mem hb, G.disjoint_of_mem ha hb hab,
    banana_isLink_of_disjoint, mem_singleton_iff, banana_edgeSet, and_true, setOf_eq_eq_singleton]
  tauto

@[simp]
lemma addEdge_isLink_of_edge (ha : a ∈ V(G)) (hb : b ∈ V(G)) : (G.addEdge e a b).IsLink e a b := by
  rw [addEdge_isLink ha hb]
  simp

@[simp]
lemma IsLink.addEdge_of_ne (hf : G.IsLink f x y) (ha : a ∈ V(G)) (hb : b ∈ V(G)) (hne : f ≠ e) :
    (G.addEdge e a b).IsLink f x y := by
  rw [addEdge_isLink ha hb]
  simpa [hne]

@[simp]
lemma addEdge_isLink_of_edge_not_mem (ha : a ∈ V(G)) (hb : b ∈ V(G)) (he : e ∉ E(G)) :
    (G.addEdge e a b).IsLink f x y ↔ (f = e ∧ s(x,y) = s(a,b)) ∨ G.IsLink f x y := by
  rw [addEdge_isLink ha hb]
  refine or_congr_right <| and_iff_right_of_imp ?_
  rintro h rfl
  exact he h.edge_mem

@[simp]
lemma addEdge_isLink_of_ne (ha : a ∈ V(G)) (hb : b ∈ V(G)) (hne : f ≠ e) :
    (G.addEdge e a b).IsLink f x y ↔ G.IsLink f x y := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.addEdge_of_ne ha hb hne⟩
  rw [addEdge_isLink ha hb] at h
  simpa [hne] using h

lemma addEdge_deleteEdge (ha : a ∈ V(G)) (hb : b ∈ V(G)) (he : e ∉ E(G)) :
    (G.addEdge e a b) ＼ {e} = G :=
  Graph.ext (by simp [ha, hb]) fun f x y => by aesop

lemma le_addEdge (ha : a ∈ V(G)) (hb : b ∈ V(G)) (he : e ∉ E(G)) : G ≤ G.addEdge e a b where
  vertexSet_subset := by rw [addEdge_vertexSet_of_mem ha hb]
  isLink_of_isLink f x y hl := by
    rw [addEdge_isLink_of_edge_not_mem ha hb he]
    simp [hl]

lemma addEdge_mono_of_mem (hle : H ≤ G) (ha : a ∈ V(H)) (hb : b ∈ V(H)) :
    H.addEdge e a b ≤ G.addEdge e a b where
  vertexSet_subset := by
    rw [addEdge_vertexSet_of_mem ha hb, addEdge_vertexSet_of_mem (vertexSet_mono hle ha)
      (vertexSet_mono hle hb)]
    exact vertexSet_mono hle
  isLink_of_isLink f x y hl := by
    rw [addEdge_isLink ha hb] at hl
    rw [addEdge_isLink (vertexSet_mono hle ha) (vertexSet_mono hle hb)]
    exact hl.imp id fun ⟨hne, h⟩ => ⟨hne, h.of_le hle⟩

lemma deleteEdge_le_addEdge (ha : a ∈ V(G)) (hb : b ∈ V(G)) : G ＼ {e} ≤ G.addEdge e a b := by
  rw [Graph.addEdge, union_eq_union_edgeDelete, banana_edgeSet_of_nonempty (G.nonempty_of_mem ha)
    (G.nonempty_of_mem hb)]
  exact le_addEdge (by simpa) (by simpa) (by simp)

lemma deleteEdge_addEdge (ha : a ∈ V(G)) (hb : b ∈ V(G)) :
    (G ＼ {e}).addEdge e a b = G.addEdge e a b :=
  Graph.ext (by simp) fun f x y => by
    simp only [addEdge_isLink (show a ∈ V(G ＼ {e}) from ha) (show b ∈ V(G ＼ {e}) from hb),
      edgeDelete_isLink, mem_singleton_iff, addEdge_isLink ha hb]
    tauto

lemma addEdge_eq_self (hbtw : G.IsLink e a b) : G.addEdge e a b = G :=
  Graph.ext (by simp [hbtw.left_mem, hbtw.right_mem]) fun f x y => by
    rw [addEdge_isLink hbtw.left_mem hbtw.right_mem]
    by_cases hne : f = e
    · subst f
      simp [eq_comm, hbtw.isLink_iff_sym2_eq]
    simp [hne]

lemma addEdge_idem (ha : a ∈ V(G)) (hb : b ∈ V(G)) :
    (G.addEdge e a b).addEdge e a b = G.addEdge e a b :=
  addEdge_eq_self <| addEdge_isLink_of_edge ha hb

lemma isSpanningSubgraph_addEdge (he : e ∉ E(G)) (ha : a ∈ V(G)) (hb : b ∈ V(G)) :
    G ≤s G.addEdge e a b := by
  nth_rw 1 [← addEdge_deleteEdge ha hb he]
  exact edgeDelete_isSpanningSubgraph

lemma IsLink.deleteEdge_addEdge (h : G.IsLink e a b) : (G ＼ {e}).addEdge e a b = G :=
  Graph.ext (by simp [h.left_mem, h.right_mem]) fun f x y => by
    obtain rfl | hne := eq_or_ne f e <;>
    simp_all [h.left_mem, h.right_mem, h.isLink_iff_sym2_eq, eq_comm]

end Graph
