import Matroid.Graph.Subgraph.Union
import Matroid.Graph.Constructions.Small

variable {α β ι ι' : Type*} {a b c x y z u v w : α} {e f : β} {F F₁ F₂ : Set β} {X Y : Set α}
  [CompleteLattice α] {G G₁ G₂ H H₁ H₂ : Graph α β} {Gs Hs : Set (Graph α β)} {P Q : Partition α}

open Set Function Partition

-- This seems useful but not yet in mathlib?
lemma assume_common_imp_of_iff {P1 P2 : Prop} (Q : Prop) (h1 : P1 → Q) (h2 : P2 → Q) :
    (P1 ↔ P2) ↔ (Q → (P1 ↔ P2)) := by
  tauto

namespace Graph

@[simp]
lemma isPartition_pair_of_mem_vertexSet (ha : a ∈ V(G)) (hb : b ∈ V(G)) : IsPartition {a, b} := by
  apply isPartition_pair_of_mem <;> rwa [mem_vertexPartition_iff]

@[simp]
lemma bouquet_dup_agree_of_mem (hv : v ∈ V(G)) : (bouquet v F).Dup_agree G := by
  use P(G), ?_
  rintro x ⟨hxbot, rfl⟩
  exact G.vertexSet_eq_parts ▸ hv

@[simp]
lemma bouquet_agree_edgeDelete (hv : v ∈ V(G)) : Agree {bouquet v F, G ＼ F} := by
  rw [agree_pair_iff]
  refine ⟨Compatible.of_disjoint_edgeSet ?_, bouquet_dup_agree_of_mem hv⟩
  by_cases hvbot : v = ⊥ <;> simp [hvbot, disjoint_sdiff_right]

@[simp]
lemma banana_dup_agree_of_mem (hu : u ∈ V(G)) (hv : v ∈ V(G)) : (banana u v F).Dup_agree G := by
  have hP : IsPartition {u, v} := isPartition_pair_of_mem_vertexSet hu hv
  refine agree_of_subset_subset (fun x => ?_) subset_rfl
  simp only [banana_vertexPartition, pair_parts_eq_pair_iff_isPartition.mp hP, vertexSet_eq_parts]
  rintro (rfl | rfl) <;> assumption

@[simp]
lemma banana_agree_edgeDelete (hu : u ∈ V(G)) (hv : v ∈ V(G)) : Agree {banana u v F, G ＼ F} := by
  rw [agree_pair_iff]
  refine ⟨Compatible.of_disjoint_edgeSet ?_, banana_dup_agree_of_mem hu hv⟩
  by_cases huvbot : u = ⊥ <;> by_cases hvbot : v = ⊥ <;> simp [huvbot, hvbot, disjoint_sdiff_right]

@[simp]
lemma singleEdge_dup_agree_of_mem (hu : u ∈ V(G)) (hv : v ∈ V(G)) :
    (Graph.singleEdge e u v).Dup_agree G := banana_dup_agree_of_mem hu hv

@[simp]
lemma singleEdge_agree_edgeDelete (hu : u ∈ V(G)) (hv : v ∈ V(G)) :
    Agree {Graph.singleEdge e u v, G ＼ {e}} := banana_agree_edgeDelete hu hv

/-! ### Adding one edge -/
section AddEdge

/-- Add a new edge `e` between vertices `a` and `b`. If `e` is already in the graph,
its ends change to `a` and `b`. -/
protected noncomputable def addEdge (G : Graph α β) (e : β) (a b : α) : Graph α β :=
  .singleEdge e a b ∪ (G ＼ {e})

@[simp↓]
lemma addEdge_vertexSet_of_mem (ha : a ∈ V(G)) (hb : b ∈ V(G)) : V(G.addEdge e a b) = V(G) := by
  rw [Graph.addEdge, union_vertexSet <| singleEdge_agree_edgeDelete ha hb,
    singleEdge_vertexSet_of_isPartition <| isPartition_pair_of_mem_vertexSet ha hb]
  simp [pair_subset, ha, hb]

lemma subset_addEdge_vertexSet_of_agree (h : Agree {Graph.singleEdge e a b, G ＼ {e}}) :
    V(G) ⊆ V(G.addEdge e a b) := by
  rw [Graph.addEdge, union_vertexSet h]
  exact subset_union_right

@[simp]
lemma addEdge_isLink (ha : a ∈ V(G)) (hb : b ∈ V(G)) : (G.addEdge e a b).IsLink f x y ↔
    f = e ∧ s(x, y) = s(a, b) ∨ f ≠ e ∧ G.IsLink f x y := by
  rw [Graph.addEdge, union_isLink (singleEdge_agree_edgeDelete ha hb),
    singleEdge_isLink_of_isPartition (isPartition_pair_of_mem_vertexSet ha hb)]
  simp [and_comm]

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
  rw [Graph.addEdge]
  exact Graph.right_le_union <| singleEdge_agree_edgeDelete ha hb

lemma deleteEdge_addEdge (ha : a ∈ V(G)) (hb : b ∈ V(G)) :
    (G ＼ {e}).addEdge e a b = G.addEdge e a b :=
  Graph.ext (by simp [Graph.addEdge]) fun f x y => by
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

end AddEdge

section Extend

@[simps! vertexSet vertexPartition]
protected def extend (G : Graph α β) (P : Partition α) : Graph α β where
  vertexPartition := P
  IsLink e := Relation.restrict (G.IsLink e) P.parts
  isLink_symm e he x y hxy := symm hxy
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := G.eq_or_eq_of_isLink_of_isLink
    (Relation.restrict_le _ _ _ _ h) (Relation.restrict_le _ _ _ _ h')
  left_mem_of_isLink _ _ _ h := h.2.1

/-- `G[P]` is the subgraph of `G` induced by the parition `P` of vertices. -/
notation:max G:1000 "[[" P "]]" => Graph.extend G P

lemma extend_le (hP : P ⊆ P(G)) : G[[P]] ≤ G :=
  ⟨by simp; rwa [← G.vertexPartition_parts], fun _ _ _ ↦ Relation.restrict_le _ P.parts _ _⟩

@[simp]
lemma extend_le_iff : G[[P]] ≤ G ↔ P ⊆ P(G) :=
  ⟨vertexPartition_mono, extend_le⟩

@[simp]
lemma extend_isLink_iff : G[[P]].IsLink e x y ↔ G.IsLink e x y ∧ x ∈ P ∧ y ∈ P := Iff.rfl

lemma IsLink.extend (h : G.IsLink e x y) (hx : x ∈ P) (hy : y ∈ P) : G[[P]].IsLink e x y :=
  ⟨h, hx, hy⟩

@[simp]
lemma extend_adj_iff : G[[P]].Adj x y ↔ G.Adj x y ∧ x ∈ P ∧ y ∈ P := by simp [Adj]

lemma Adj.extend (h : G.Adj x y) (hx : x ∈ P) (hy : y ∈ P) : G[[P]].Adj x y :=
  induce_adj_iff.mpr ⟨h, hx, hy⟩

/-- This is too annoying to be a simp lemma. -/
lemma extend_edgeSet (G : Graph α β) (P : Partition α) :
    E(G.extend P) = {e | ∃ x y, G.IsLink e x y ∧ x ∈ P ∧ y ∈ P} := rfl

@[simp]
lemma extend_edgeSet_subset (G : Graph α β) (P : Partition α) : E(G.extend P) ⊆ E(G) := by
  rintro e ⟨x,y,h, -, -⟩
  exact h.edge_mem

lemma IsLink.mem_extend_iff (hG : G.IsLink e x y) : e ∈ E(G[[P]]) ↔ x ∈ P ∧ y ∈ P := by
  simp only [extend_edgeSet, mem_setOf_eq]
  refine ⟨fun ⟨x', y', he, hx', hy'⟩ ↦ ?_, fun h ↦ ⟨x, y, hG, h⟩⟩
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hG.eq_and_eq_or_eq_and_eq he <;> simp [hx', hy']

lemma extend_isLink_iff_of_mem_edgeSet (h : e ∈ E(G[[P]])) :
    G[[P]].IsLink e x y ↔ G.IsLink e x y := by
  obtain ⟨x', y', h', hx', hy'⟩ := h
  have : G[[P]].IsLink e x' y' := by use h'
  rw [h'.isLink_iff, this.isLink_iff]

lemma extend_extend (G : Graph α β) (P Q : Partition α) : G[[P]][[Q]] = G[[Q]] ↾ E(G[[P]]) := by
  refine Graph.ext rfl fun e x y ↦ ?_
  simp only [extend_isLink_iff, edgeRestrict_isLink]
  obtain he | he := em' (G.IsLink e x y)
  · simp [he]
  rw [he.mem_extend_iff]
  tauto

lemma extend_mono_right (G : Graph α β) (hXY : P ⊆ Q) : G[[P]] ≤ G[[Q]] where
  vertexSet_subset := hXY
  isLink_of_isLink _ _ _ := fun ⟨h, h1, h2⟩ ↦ ⟨h, hXY h1, hXY h2⟩

@[simp]
lemma extend_mono_right_iff (G : Graph α β) : G[[P]] ≤ G[[Q]] ↔ P ⊆ Q :=
  ⟨vertexSet_mono, extend_mono_right G⟩

lemma extend_mono_left (h : H ≤ G) (P : Partition α) : H[[P]] ≤ G[[P]] where
  vertexSet_subset := le_rfl
  isLink_of_isLink e x y := by
    simp only [extend_isLink_iff, and_imp]
    exact fun hl hx hy => ⟨hl.of_le h, hx, hy⟩

lemma extend_mono (h : H ≤ G) (hXY : P ⊆ Q) : H[[P]] ≤ G[[Q]] :=
  (extend_mono_left h P).trans (G.extend_mono_right hXY)

@[simp]
lemma extend_vertexSet_self (G : Graph α β) : G[[P(G)]] = G := by
  refine G.ext_of_le_le (by simp) (by simp) (by simp) <| Set.ext fun e ↦
    ⟨fun ⟨_, _, h⟩ ↦ h.1.edge_mem, fun h ↦ ?_⟩
  obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet h
  exact ⟨x, y, h, G.vertexSet_eq_parts ▸ h.left_mem, G.vertexSet_eq_parts ▸ h.right_mem⟩

lemma le_extend_of_le_of_subset (h : H ≤ G) (hV : V(H) ⊆ P) : H ≤ G[[P]] :=
  ⟨hV, fun _ _ _ h' ↦ ⟨h'.of_le h, hV h'.left_mem, hV h'.right_mem⟩⟩

lemma le_extend_self (h : H ≤ G) : H ≤ G[[P(H)]] :=
  le_extend_of_le_of_subset h <| H.vertexPartition_parts ▸ rfl.subset

lemma le_extend_iff (hP : P ⊆ P(G)) : H ≤ G[[P]] ↔ H ≤ G ∧ V(H) ⊆ P.parts :=
  ⟨fun h ↦ ⟨h.trans (by simpa), vertexSet_mono h⟩, fun h ↦ le_extend_of_le_of_subset h.1 h.2⟩

@[simp]
lemma edgeRestrict_extend (G : Graph α β) (P : Partition α) (F : Set β) :
    (G ↾ F)[[P]] = G[[P]] ↾ F := by
  refine Graph.ext (by simp) fun e x y ↦ ?_
  simp only [extend_isLink_iff, edgeRestrict_isLink]
  tauto

end Extend
end Graph
