import Matroid.Graph.Subgraph.Defs

variable {α β : Type*} {x y z u v w : α} {e f : β} {G H K : Graph α β} {F F₁ F₂ : Set β}
  {X Y : Set α}

open Set

namespace Graph

@[simp]
lemma restrict_isNonloopAt_iff : (G ↾ F).IsNonloopAt e x ↔ G.IsNonloopAt e x ∧ e ∈ F := by
  simp_rw [IsNonloopAt]
  aesop

@[grind .]
lemma neighbor_restrict_subset (G : Graph α β) (F : Set β) (x : α) :
    N(G ↾ F, x) ⊆ N(G, x) :=
  neighbor_mono restrict_le

@[grind .]
lemma setNeighbor_restrict_subset (G : Graph α β) (F : Set β) (S : Set α) :
    N(G ↾ F, S) ⊆ N(G, S) :=
  setNeighbor_mono restrict_le S

@[simp, grind =]
lemma incEdges_restrict (G : Graph α β) (F : Set β) (x : α) :
    E(G ↾ F, x) = E(G, x) ∩ F := by
  ext e
  simp [mem_inter_iff]

@[simp, grind =]
lemma setIncEdges_restrict (G : Graph α β) (F : Set β) (S : Set α) :
    E(G ↾ F, S) = E(G, S) ∩ F := by
  ext e
  grind

@[grind =]
lemma endSet_restrict (G : Graph α β) (F : Set β) [DecidablePred (· ∈ F)] (e : β) :
    V(G ↾ F, e) = if e ∈ F then V(G, e) else ∅ := by
  grind

@[simp]
lemma endSet_restrict_of_mem (G : Graph α β) (F : Set β) (he : e ∈ F) :
    V(G ↾ F, e) = V(G, e) := by grind

@[simp]
lemma endSet_restrict_of_not_mem (G : Graph α β) (F : Set β) (he : e ∉ F) :
    V(G ↾ F, e) = ∅ := by grind

@[simp, grind =]
lemma linkEdges_restrict (G : Graph α β) (F : Set β) (u v : α) :
    E(G ↾ F, u, v) = E(G, u, v) ∩ F := by
  ext e
  simp [mem_inter_iff, and_comm]

@[simp, grind =]
lemma setLinkEdges_restrict (G : Graph α β) (F : Set β) (S T : Set α) :
    E(G ↾ F, S, T) = E(G, S, T) ∩ F := by
  ext e
  grind

@[gcongr]
lemma restrict_le_restrict (h : E(G) ∩ F₁ ⊆ E(G) ∩ F₂) : G ↾ F₁ ≤ G ↾ F₂ :=
  le_of_le_le_subset_subset restrict_le restrict_le (by simp) h

lemma restrict_le_restrict_iff (G : Graph α β) (F₁ F₂ : Set β) :
    G ↾ F₁ ≤ G ↾ F₂ ↔ E(G) ∩ F₁ ⊆ E(G) ∩ F₂ :=
  ⟨(·.edgeSet_mono), restrict_le_restrict⟩

lemma restrict_of_superset (G : Graph α β) (hF : E(G) ⊆ F) : G ↾ F = G := by
  rw [← restrict_inter_edgeSet, inter_eq_self_of_subset_right hF, restrict_self]

@[gcongr]
lemma restrict_eq_restrict (h : E(G) ∩ F₁ = E(G) ∩ F₂) : G ↾ F₁ = G ↾ F₂ :=
  ext_of_le_le restrict_le restrict_le rfl h

lemma restrict_eq_restrict_iff (G : Graph α β) (F₁ F₂ : Set β) :
    G ↾ F₁ = G ↾ F₂ ↔ E(G) ∩ F₁ = E(G) ∩ F₂ := by
  refine ⟨fun h => ?_, restrict_eq_restrict⟩
  apply_fun edgeSet at h
  exact h

@[simp, grind =]
lemma le_restrict_iff : H ≤ (G ↾ F) ↔ H ≤ G ∧ E(H) ⊆ F :=
  ⟨fun h ↦ ⟨h.trans (by simp), h.edgeSet_mono.trans (by simp)⟩,
    fun h ↦ le_of_le_le_subset_subset h.1 (by simp) (by simpa using h.1.vertexSet_mono)
    <| subset_inter h.1.edgeSet_mono h.2⟩

@[simp, grind .]
lemma restrict_isSpanningSubgraph : G ↾ F ≤s G :=
  ⟨by simp, by simp⟩

@[gcongr]
lemma restrict_isSpanningSubgraph_restrict (h : E(G) ∩ F₁ ⊆ E(G) ∩ F₂) :
    G ↾ F₁ ≤s G ↾ F₂ where
  vertexSet_eq := by simp
  isLink_mono := le_of_le_le_subset_subset restrict_le restrict_le (by simp) h |>.isLink_mono

@[gcongr]
lemma restrict_isSpanningSubgraph_restrict' (h : F₁ ⊆ F₂) :
    G ↾ F₁ ≤s G ↾ F₂ where
  vertexSet_eq := by simp
  isLink_mono := restrict_mono_right _ h |>.isLink_mono

lemma restrict_isSpanningSubgraph_restrict_iff (G : Graph α β) (F₁ F₂ : Set β) :
    G ↾ F₁ ≤s G ↾ F₂ ↔ E(G) ∩ F₁ ⊆ E(G) ∩ F₂ := by
  refine ⟨fun h ↦ ?_, restrict_isSpanningSubgraph_restrict⟩
  grw [← edgeSet_restrict, ← edgeSet_restrict, (show G ↾ F₁ ≤ _ from h.le)]

@[gcongr]
lemma IsSpanningSubgraph.restrict (h : H ≤s G) (F : Set β) : H ↾ F ≤s G ↾ F :=
  IsSpanningSubgraph.mk' (by simp [h.vertexSet_eq]) <| restrict_mono_left h.le F |>.isLink_mono

@[simp]
lemma deleteEdges_isNonloopAt_iff : (G ＼ F).IsNonloopAt e x ↔ G.IsNonloopAt e x ∧ e ∉ F := by
  simp only [← restrict_edgeSet_diff_eq_deleteEdges, restrict_isNonloopAt_iff, mem_diff,
    and_congr_right_iff, and_iff_right_iff_imp]
  exact fun h _ ↦ h.edge_mem

@[grind .]
lemma neighbor_deleteEdges_subset (G : Graph α β) (F : Set β) (x : α) : N(G ＼ F, x) ⊆ N(G, x) :=
  neighbor_mono deleteEdges_le

@[grind .]
lemma setNeighbor_deleteEdges_subset (G : Graph α β) (F : Set β) (S : Set α) :
    N(G ＼ F, S) ⊆ N(G, S) :=
  setNeighbor_mono deleteEdges_le S

@[simp, grind =]
lemma incEdges_deleteEdges (G : Graph α β) (F : Set β) (x : α) : E(G ＼ F, x) = E(G, x) \ F := by
  ext e
  simp [mem_diff]

@[simp, grind =]
lemma setIncEdges_deleteEdges (G : Graph α β) (F : Set β) (S : Set α) :
    E(G ＼ F, S) = E(G, S) \ F := by
  ext e
  grind

@[simp, grind =]
lemma endSet_deleteEdges_of_mem (G : Graph α β) (F : Set β) (e : β) (he : e ∈ F) :
    V(G ＼ F, e) = ∅ := by grind

@[simp, grind =]
lemma endSet_deleteEdges_of_not_mem (G : Graph α β) (F : Set β) (e : β) (he : e ∉ F) :
    V(G ＼ F, e) = V(G, e) := by grind

@[simp, grind =]
lemma linkEdges_deleteEdges (G : Graph α β) (F : Set β) (u v : α) :
    E(G ＼ F, u, v) = E(G, u, v) \ F := by grind

@[simp]
lemma deleteEdges_inter_edgeSet : G ＼ (F ∩ E(G)) = G ＼ F := by
  rw [← restrict_edgeSet_diff_eq_deleteEdges, ← restrict_edgeSet_diff_eq_deleteEdges,
    diff_inter_self_eq_diff]

@[simp]
lemma edgeSet_deleteEdges_inter : G ＼ (E(G) ∩ F) = G ＼ F := by
  rw [inter_comm, deleteEdges_inter_edgeSet]

@[gcongr]
lemma deleteEdges_anti_right (G : Graph α β) {F₀ F : Set β} (hss : F₀ ⊆ F) : G ＼ F ≤ G ＼ F₀ := by
  simp_rw [← restrict_edgeSet_diff_eq_deleteEdges]
  exact G.restrict_mono_right <| diff_subset_diff_right hss

@[gcongr]
lemma deleteEdges_le_deleteEdges (h : E(G) \ F₁ ⊆ E(G) \ F₂) : G ＼ F₁ ≤ G ＼ F₂ :=
  le_of_le_le_subset_subset deleteEdges_le deleteEdges_le (by simp) h

lemma deleteEdges_le_deleteEdges_iff (G : Graph α β) (F₁ F₂ : Set β) :
    G ＼ F₁ ≤ G ＼ F₂ ↔ E(G) \ F₁ ⊆ E(G) \ F₂ := by
  refine ⟨fun h ↦ ?_, deleteEdges_le_deleteEdges⟩
  apply_fun edgeSet (α := α) (β := β) at h using edgeSet_monotone (α := α) (β := β)
  exact h

@[simp]
lemma restrict_deleteEdges (G : Graph α β) (F₁ F₂ : Set β) : (G ↾ F₁) ＼ F₂ = G ↾ F₁ \ F₂ := by
  rw [← restrict_edgeSet_diff_eq_deleteEdges, restrict_restrict, edgeSet_restrict, diff_eq,
    ← inter_assoc, inter_comm E(G), ← inter_assoc, inter_self, inter_comm F₁, inter_assoc,
    restrict_edgeSet_inter, diff_eq]

lemma restrict_deleteEdges_comm (G : Graph α β) (F₁ F₂ : Set β) :
    (G ↾ F₁) ＼ F₂ = G ＼ F₂ ↾ F₁ := by
  conv_rhs => rw [← restrict_edgeSet_diff_eq_deleteEdges, restrict_restrict,
    diff_inter_right_comm, ← restrict_deleteEdges, G.restrict_edgeSet_inter F₁]

@[simp]
lemma deleteEdges_restrict (G : Graph α β) (F₁ F₂ : Set β) : G ＼ F₁ ↾ F₂ = G ↾ (F₂ \ F₁) := by
  rw [← restrict_deleteEdges_comm, restrict_deleteEdges]

lemma deleteEdges_deleteEdges_comm (G : Graph α β) (F₁ F₂ : Set β) :
    G ＼ F₁ ＼ F₂ = G ＼ F₂ ＼ F₁ := by
  rw [deleteEdges_deleteEdges, union_comm, ← deleteEdges_deleteEdges]

lemma deleteEdges_eq (G : Graph α β) (hF : Disjoint E(G) F) : G ＼ F = G := by
  simp [← restrict_edgeSet_diff_eq_deleteEdges, hF.sdiff_eq_left]

lemma deleteEdges_eq_of_disjoint (hF : Disjoint E(G) F) : G ＼ F = G := by
  rw [← restrict_edgeSet_diff_eq_deleteEdges]
  exact restrict_of_superset _ hF.sdiff_eq_left.symm.subset

lemma deleteEdges_eq_iff (G : Graph α β) (F : Set β) : G ＼ F = G ↔ Disjoint E(G) F := by
  refine ⟨fun h ↦ ?_, deleteEdges_eq_of_disjoint⟩
  apply_fun edgeSet at h
  simpa using h

@[gcongr]
lemma deleteEdges_eq_deleteEdges (h : E(G) \ F₁ = E(G) \ F₂) : G ＼ F₁ = G ＼ F₂ :=
  ext_of_le_le deleteEdges_le deleteEdges_le rfl h

lemma deleteEdges_eq_deleteEdges_iff (G : Graph α β) (F₁ F₂ : Set β) :
    G ＼ F₁ = G ＼ F₂ ↔ E(G) \ F₁ = E(G) \ F₂ := by
  refine ⟨fun h ↦ ?_, deleteEdges_eq_deleteEdges⟩
  apply_fun edgeSet (α := α) (β := β) at h using Graph.edgeSet_monotone (α := α) (β := β)
  exact h

@[simp]
lemma le_deleteEdges_iff : H ≤ G ＼ F ↔ H ≤ G ∧ Disjoint E(H) F := by
  simp only [← restrict_edgeSet_diff_eq_deleteEdges, le_restrict_iff, subset_diff,
    and_congr_right_iff, and_iff_right_iff_imp]
  exact fun hle _ ↦ hle.edgeSet_mono

lemma IsNonloopAt.isLoopAt_delete (h : G.IsNonloopAt e x) : (G ＼ {e}).IsLoopAt = G.IsLoopAt := by
  ext f y
  simp only [← isLink_self_iff, deleteEdges_isLink, mem_singleton_iff, and_iff_left_iff_imp]
  rintro h' rfl
  exact h.not_isLoopAt y h'

lemma IsLoopAt.isNonloopAt_delete (h : G.IsLoopAt e x) : (G ＼ {e}).IsNonloopAt = G.IsNonloopAt := by
  ext f y
  simp only [← restrict_edgeSet_diff_eq_deleteEdges, isNonloopAt_iff_inc_not_isLoopAt, restrict_inc,
    mem_diff, mem_singleton_iff, ← isLink_self_iff, restrict_isLink, not_and, and_imp]
  obtain rfl | hne := eq_or_ne f e
  · simp only [not_true_eq_false, and_false, isLink_self_iff, IsEmpty.forall_iff, implies_true,
    and_true, false_iff, not_and, not_not]
    exact fun h' ↦ by rwa [← h.eq_of_inc h']
  grind

@[simp]
lemma setLinkEdges_deleteEdges (G : Graph α β) (F : Set β) (S T : Set α) :
    E(G ＼ F, S, T) = E(G, S, T) \ F := by grind

@[simp]
lemma deleteEdges_isSpanningSubgraph : G ＼ F ≤s G where
  vertexSet_eq := by simp
  isLink_mono := by simp +contextual

@[gcongr]
lemma deleteEdges_isSpanningSubgraph_deleteEdges (h : E(G) \ F₁ ⊆ E(G) \ F₂) :
    G ＼ F₁ ≤s G ＼ F₂ where
  vertexSet_eq := by simp
  isLink_mono := deleteEdges_le_deleteEdges h |>.isLink_mono

@[gcongr]
lemma deleteEdges_isSpanningSubgraph_anti_right (h : F₁ ⊆ F₂) : G ＼ F₂ ≤s G ＼ F₁ where
  vertexSet_eq := by simp
  isLink_mono := G.deleteEdges_anti_right h |>.isLink_mono

@[simp]
lemma deleteEdges_isSpanningSubgraph_deleteEdges_iff (G : Graph α β) (F₁ F₂ : Set β) :
    G ＼ F₁ ≤s G ＼ F₂ ↔ E(G) \ F₁ ⊆ E(G) \ F₂ := by
  refine ⟨fun h ↦ ?_, deleteEdges_isSpanningSubgraph_deleteEdges⟩
  grw [← edgeSet_deleteEdges, ← edgeSet_deleteEdges, (show G ＼ F₁ ≤ _ from h.le)]

@[gcongr]
lemma IsSpanningSubgraph.deleteEdges (h : H ≤s G) (F : Set β) : H ＼ F ≤s G ＼ F where
  vertexSet_eq := by simp [h.vertexSet_eq]
  vertexSet_mono := h.vertexSet_mono
  isLink_mono := deleteEdges_mono_left h.le F |>.isLink_mono

lemma deleteEdges_eq_noEdge (G : Graph α β) (hF : E(G) ⊆ F) : G ＼ F = Graph.noEdge V(G) β := by
  refine Graph.ext rfl fun e x y ↦ ?_
  simp only [deleteEdges_isLink, noEdge_isLink, iff_false, not_and, not_not]
  exact fun h ↦ hF h.edge_mem


lemma IsLink.induce (h : G.IsLink e x y) (hx : x ∈ X) (hy : y ∈ X) : G[X].IsLink e x y :=
  ⟨h, hx, hy⟩

@[simp, grind =]
lemma induce_adj_iff {X : Set α} : G[X].Adj x y ↔ G.Adj x y ∧ x ∈ X ∧ y ∈ X := by simp [Adj]

@[grind .]
lemma neighbor_induce (G : Graph α β) (X : Set α) [DecidablePred (· ∈ X)] (x : α) :
    N(G[X], x) = if x ∈ X then N(G, x) ∩ X else ∅ := by grind

@[simp]
lemma neighbor_induce_of_notMem (G : Graph α β) (hx : x ∉ X) : N(G[X], x) = ∅ := by grind

@[simp]
lemma neighbor_induce_of_mem (G : Graph α β) (hx : x ∈ X) : N(G[X], x) = N(G, x) ∩ X := by grind

@[simp, grind =]
lemma setLinkEdges_induce (G : Graph α β) (X S T : Set α) :
    E(G[X], S, T) = E(G, S ∩ X, T ∩ X) := by grind

@[grind .]
lemma linkEdges_induce (G : Graph α β) (X : Set α) [DecidablePred (· ∈ X)] (u v : α) :
    E(G[X], u, v) = if u ∈ X ∧ v ∈ X then E(G, u, v) else ∅ := by grind

@[simp]
lemma linkEdges_induce_of_mem (G : Graph α β) (hu : u ∈ X) (hv : v ∈ X) :
    E(G[X], u, v) = E(G, u, v) := by grind

@[simp]
lemma linkEdges_induce_of_left_not_mem (G : Graph α β) (X : Set α) (u v : α) (hu : u ∉ X) :
    E(G[X], u, v) = ∅ := by
  ext e
  simp [hu]

@[simp]
lemma linkEdges_induce_of_right_not_mem (G : Graph α β) (X : Set α) (u v : α) (hv : v ∉ X) :
    E(G[X], u, v) = ∅ := by
  ext e
  simp [hv]

lemma Adj.induce (h : G.Adj x y) (hx : x ∈ X) (hy : y ∈ X) : G[X].Adj x y :=
  induce_adj_iff.mpr ⟨h, hx, hy⟩

@[simp]
lemma edgeSet_induce_subset (G : Graph α β) (X : Set α) : E(G[X]) ⊆ E(G) := by
  rintro e ⟨x, y, h, -, -⟩
  exact h.edge_mem

@[simp]
lemma induce_singleton_edgeSet (G : Graph α β) (x : α) : E(G[{x}]) = {e | G.IsLoopAt e x} := by
  simp [edgeSet_induce]

@[simp]
lemma induce_pair_edgeSet (G : Graph α β) (x y : α) : E(G, x, y) ⊆ E(G[{x, y}]) := by
  intro e he
  use x, y, he, by simp, by simp

lemma IsLink.mem_induce_iff (hG : G.IsLink e x y) : e ∈ E(G[X]) ↔ x ∈ X ∧ y ∈ X := by
  simp only [edgeSet_induce, mem_setOf_eq]
  refine ⟨fun ⟨x', y', he, hx', hy'⟩ ↦ ?_, fun h ↦ ⟨x, y, hG, h⟩⟩
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hG.eq_and_eq_or_eq_and_eq he <;> simp [hx', hy']

lemma induce_isLink_iff_of_mem_edgeSet (h : e ∈ E(G[X])) : G[X].IsLink e x y ↔ G.IsLink e x y := by
  obtain ⟨x', y', h', hx', hy'⟩ := h
  have : G[X].IsLink e x' y' := by use h'
  rw [h'.isLink_iff, this.isLink_iff]

lemma induce_induce (G : Graph α β) (X Y : Set α) : G[X][Y] = G[Y] ↾ E(G[X]) := by
  refine Graph.ext rfl fun e x y ↦ ?_
  simp only [induce_isLink, restrict_isLink]
  obtain he | he := em' (G.IsLink e x y)
  · simp [he]
  rw [he.mem_induce_iff]
  tauto

@[gcongr]
lemma induce_mono_right (G : Graph α β) (hXY : X ⊆ Y) : G[X] ≤ G[Y] where
  vertexSet_mono := hXY
  isLink_mono _ _ _ := fun ⟨h, h1, h2⟩ ↦ ⟨h, hXY h1, hXY h2⟩

@[simp]
lemma induce_mono_right_iff (G : Graph α β) : G[X] ≤ G[Y] ↔ X ⊆ Y :=
  ⟨(·.vertexSet_mono), induce_mono_right G⟩

@[gcongr]
lemma induce_mono_left (h : H ≤ G) (X : Set α) : H[X] ≤ G[X] where
  vertexSet_mono := le_rfl
  isLink_mono e x y := by
    simp only [induce_isLink, and_imp]
    exact fun hl hx hy => ⟨hl.of_le h, hx, hy⟩

lemma induce_mono (h : H ≤ G) (hXY : X ⊆ Y) : H[X] ≤ G[Y] :=
  (induce_mono_left h X).trans (G.induce_mono_right hXY)

@[simp]
lemma induce_eq_self_iff (G : Graph α β) (X : Set α) : G[X] = G ↔ X = V(G) := by
  refine ⟨fun h ↦ h ▸ (by simp), fun h ↦ Graph.ext (by simpa) fun e x y ↦ ?_⟩
  subst h
  simp only [induce_vertexSet]

lemma le_induce_of_le_of_subset (h : H ≤ G) (hV : V(H) ⊆ X) : H ≤ G[X] :=
  ⟨hV, fun _ _ _ h' ↦ ⟨h'.of_le h, hV h'.left_mem, hV h'.right_mem⟩⟩

lemma le_induce_self (h : H ≤ G) : H ≤ G[V(H)] :=
  le_induce_of_le_of_subset h rfl.subset

lemma le_induce_iff (hX : X ⊆ V(G)) : H ≤ G[X] ↔ H ≤ G ∧ V(H) ⊆ X :=
  ⟨fun h ↦ ⟨h.trans (by simpa), h.vertexSet_mono⟩, fun h ↦ le_induce_of_le_of_subset h.1 h.2⟩

lemma diff_subset_isolatedSet_induce (G : Graph α β) (X : Set α) : X \ V(G) ⊆ Isol(G[X]) := by
  intro x ⟨hxX, hx⟩
  simp only [mem_isolatedSet_iff, isolated_iff, vertexSet_induce, hxX, and_true]
  exact fun e he ↦ hx he.isLink_other.1.left_mem

@[simp]
lemma restrict_induce (G : Graph α β) (X : Set α) (F : Set β) : (G ↾ F)[X] = G[X] ↾ F := by
  refine Graph.ext (by simp) fun e x y ↦ ?_
  simp only [induce_isLink, restrict_isLink]
  tauto

@[simp]
lemma IsSubgraph.induce_restrict_eq (h : H ≤ G) : G[V(H)] ↾ E(H) = H := by
  refine ext_of_le_le (restrict_le.trans <| induce_le h.vertexSet_mono) h (by simp) ?_
  simp only [edgeSet_restrict, inter_eq_right, edgeSet_induce]
  intro e he
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
  exact ⟨x, y, hxy.of_le h, hxy.left_mem, hxy.right_mem⟩

lemma induce_isInducedSubgraph (hX : X ⊆ V(G)) : G[X] ≤i G := ⟨by simpa, by simp_all⟩

lemma IsInducedSubgraph.vertexSet_induce_eq (h : H ≤i G) : G[V(H)] = H := by
  have hle : G[V(H)] ≤ G := by simp [h.vertexSet_mono]
  refine G.ext_of_le_le hle h.le (by simp) <| Set.ext fun e ↦ ?_
  simp only [edgeSet_induce, mem_setOf_eq]
  refine ⟨fun ⟨x, y, h', hx, hy⟩ ↦ (h.isLink_of_mem_mem h' hx hy).edge_mem, fun h' ↦ ?_⟩
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet h'
  exact ⟨x, y, hxy.of_le h.le, hxy.left_mem, hxy.right_mem⟩

-- @[gcongr]
lemma induce_isInducedSubgraph_mono_right (h : X ⊆ Y) : G[X] ≤i G[Y] :=
  ⟨G.induce_mono_right h, by simp_all⟩

@[simp]
lemma induce_isInducedSubgraph_induce_iff (G : Graph α β) (X Y : Set α) :
    G[X] ≤i G[Y] ↔ X ⊆ Y := by
  refine ⟨fun h ↦ ?_, induce_isInducedSubgraph_mono_right⟩
  grw [← vertexSet_induce G X, ← vertexSet_induce G Y, h.le']

@[gcongr]
lemma isSpanningSubgraph_of_induce (h : H ≤ G) (X : Set α) : H[X] ≤s G[X] where
  vertexSet_eq := by simp
  isLink_mono := induce_mono_left h X |>.isLink_mono

/-- An induced subgraph is precisely a subgraph of the form `G[X]` for some `X ⊆ V(G)`.
This version of the lemma can be used with `subst` or `obtain rfl` to replace `H` with `G[X]`. -/
lemma IsInducedSubgraph.exists_eq_induce (h : H ≤i G) : ∃ X ⊆ V(G), H = G[X] :=
  ⟨V(H), h.vertexSet_mono, h.vertexSet_induce_eq.symm⟩

lemma IsInducedSubgraph.eq_of_isSpanningSubgraph (hi : H ≤i G) (hs : H ≤s G) : H = G := by
  obtain ⟨X, hX, rfl⟩ := hi.exists_eq_induce
  have := hs.vertexSet_eq.symm
  simp_all

@[simp]
lemma induce_isInducedSubgraph_iff : G[X] ≤i G ↔ X ⊆ V(G) := by
  simp +contextual [isInducedSubgraph_iff]

@[simp, grind .]
lemma deleteVerts_isInducedSubgraph (G : Graph α β) (X : Set α) : G - X ≤i G :=
  ⟨deleteVerts_le, by simp_all⟩

@[simp]
lemma deleteVerts_eq_bot_iff (G : Graph α β) (X : Set α) : G - X = ⊥ ↔ V(G) ⊆ X := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · apply_fun vertexSet at h
    simpa [diff_eq_empty] using h
  simp [deleteVerts_def, diff_eq_empty.mpr h]

@[simp]
lemma bot_deleteVerts : (⊥ : Graph α β) - X = ⊥ := by
  simp [deleteVerts_def]

@[simp, grind =]
lemma deleteVerts_adj_iff (G : Graph α β) (X : Set α) :
    (G - X).Adj x y ↔ G.Adj x y ∧ x ∉ X ∧ y ∉ X := by
  simp [Adj]

@[grind =]
lemma neighbor_deleteVerts (G : Graph α β) (X : Set α) [DecidablePred (· ∈ X)] (x : α) :
    N(G - X, x) = if x ∉ X then N(G, x) \ X else ∅ := by grind

@[simp]
lemma neighbor_deleteVerts_of_mem (G : Graph α β) (hx : x ∈ X) : N(G - X, x) = ∅ := by grind

@[simp]
lemma neighbor_deleteVerts_of_notMem (G : Graph α β) (hx : x ∉ X) :
    N(G - X, x) = N(G, x) \ X := by grind

@[simp]
lemma deleteVerts_vertexSet_inter (G : Graph α β) (X : Set α) : G - (V(G) ∩ X) = G - X := by
  simp [deleteVerts_def]

@[simp]
lemma deleteVerts_eq_self_iff (G : Graph α β) (X : Set α) : G - X = G ↔ Disjoint V(G) X := by
  refine ⟨fun h ↦ ?_, fun h ↦ (G.deleteVerts_isInducedSubgraph X).ext_of_vertexSet (by simpa)⟩
  rw [← h, vertexSet_deleteVerts]
  exact disjoint_sdiff_left

lemma IsLink.mem_deleteVerts_iff (hG : G.IsLink e x y) : e ∈ E(G - X) ↔ x ∉ X ∧ y ∉ X := by
  rw [deleteVerts_def, hG.mem_induce_iff, mem_diff, mem_diff, and_iff_right hG.left_mem,
    and_iff_right hG.right_mem]

lemma IsLink.not_mem_incidentEdges (h : (G - X).IsLink e x y) : e ∉ E(G, X) := by
  simp only [mem_setIncEdges_iff, not_exists, not_and]
  rintro z hzX hz
  obtain rfl | rfl := hz.eq_or_eq_of_isLink (h.of_le deleteVerts_le)
  · simpa [hzX] using h.left_mem
  simpa [hzX] using h.right_mem

@[simp]
lemma Inc.not_mem_of_mem (h : G.Inc e x) (hx : x ∈ X) : e ∉ E(G - X) := by
  simp only [edgeSet_deleteVerts, mem_setOf_eq, not_exists, not_and, not_not]
  rintro u v huv hu
  obtain rfl := h.eq_of_isLink_of_ne_left huv (fun h ↦ (hu <| h ▸ hx).elim)
  exact hx

lemma Inc.not_mem_incEdges (h : (G - X).Inc e x) : e ∉ E(G, X) :=
  h.choose_spec.not_mem_incidentEdges

lemma Inc.not_mem_of_deleteVerts (h : (G - X).Inc e x) : x ∉ X :=
  (h.choose_spec.of_le deleteVerts_le).mem_deleteVerts_iff.mp h.edge_mem |>.1

@[simp, grind .]
lemma deleteVerts_inc_iff (G : Graph α β) (X : Set α) :
    (G - X).Inc e x ↔ G.Inc e x ∧ e ∉ E(G, X) := by
  refine ⟨fun h ↦ ⟨h.of_le deleteVerts_le, h.not_mem_incEdges⟩,
    fun ⟨hex, he⟩ ↦ hex.of_le_of_mem deleteVerts_le ?_⟩
  rw [deleteVerts_edgeSet_diff, mem_diff]
  exact ⟨hex.edge_mem, he⟩

@[simp, grind =]
lemma incEdges_deleteVerts (G : Graph α β) (X : Set α) (x : α) :
    E(G - X, x) = E(G, x) \ E(G, X) := by grind

@[simp, grind =]
lemma setIncEdges_deleteVerts (G : Graph α β) (X S : Set α) :
    E(G - X, S) = E(G, S) \ E(G, X) := by grind

@[simp, grind =]
lemma linkEdges_deleteVerts (G : Graph α β) (X : Set α) (u v : α) :
    E(G - X, u, v) = E(G, u, v) \ E(G, X) := by grind

-- @[simp, grind =]
-- lemma setLinkEdges_deleteVerts (G : Graph α β) (X S T : Set α) :
--     E(G - X, S, T) = E(G, S, T) \ E(G, X) := by grind

@[gcongr]
lemma deleteVerts_mono_left (h : H ≤ G) (X : Set α) : H - X ≤ G - X :=
  induce_mono h <| diff_subset_diff_left h.vertexSet_mono

@[gcongr]
lemma deleteVerts_anti_right (G : Graph α β) (hXY : X ⊆ Y) : G - Y ≤ G - X :=
  induce_mono_right _ <| diff_subset_diff_right hXY

-- lemma deleteVerts_singleton_le_deleteEdges_linkEdges (G : Graph α β) (u v : α) :
--     G - u ≤ G ＼ E(G, u, v) := by
--   refine le_of_le_le_subset_subset deleteVerts_le deleteEdges_le (by simp) ?_
--   rw [deleteVerts_singleton, deleteVerts_edgeSet_diff, edgeSet_deleteEdges,
--setIncEdges_singleton]
--   exact diff_subset_diff_right <| G.linkEdges_subset_incEdges_left u v

lemma restrict_deleteVerts (G : Graph α β) (F : Set β) (D : Set α) :
    (G ↾ F) - D = (G - D) ↾ F := by
  refine Graph.ext rfl fun e x y ↦ ?_
  simp only [deleteVerts_isLink_iff, restrict_isLink]
  tauto

@[simp]
lemma deleteEdges_induce (G : Graph α β) (X : Set α) (F : Set β) : (G ＼ F)[X] = G[X] ＼ F := by
  rw [← restrict_edgeSet_diff_eq_deleteEdges, restrict_induce, ← restrict_edgeSet_inter,
    ← inter_diff_assoc, inter_eq_self_of_subset_left (by simp),
    restrict_edgeSet_diff_eq_deleteEdges]

@[simp]
lemma induce_deleteVerts (G : Graph α β) (X D : Set α) : G[X] - D = G[X \ D] :=
  Graph.ext rfl <| by
  simp only [deleteVerts_isLink_iff, induce_isLink, mem_diff]
  tauto

@[simp]
lemma deleteEdges_deleteVerts (G : Graph α β) (F : Set β) (X : Set α) :
    (G ＼ F) - X = (G - X) ＼ F := by
  rw [← restrict_edgeSet_diff_eq_deleteEdges, restrict_deleteVerts, ← restrict_inter_edgeSet,
    diff_inter_right_comm, inter_eq_right.mpr ((deleteVerts_le : G - X ≤ G).edgeSet_mono),
    ← restrict_edgeSet_diff_eq_deleteEdges]

lemma deleteVerts_deleteEdges_incidentEdges (G : Graph α β) (X : Set α) :
    (G ＼ E(G, X)) - X = G - X := by
  rw [deleteEdges_deleteVerts, deleteEdges_eq_iff, deleteVerts_edgeSet_diff]
  exact disjoint_sdiff_left

lemma deleteVerts_deleteVerts (G : Graph α β) (X Y : Set α) : (G - X) - Y = G - (X ∪ Y) := by
  rw [G.deleteVerts_def, induce_deleteVerts, diff_diff, ← deleteVerts_def]

lemma deleteVerts_deleteVerts_comm (G : Graph α β) (X Y : Set α) : (G - X) - Y = (G - Y) - X := by
  rw [deleteVerts_deleteVerts, deleteVerts_deleteVerts, union_comm]

@[simp]
lemma le_deleteVerts_iff : H ≤ G - X ↔ H ≤ G ∧ Disjoint V(H) X := by
  simp only [deleteVerts_def, le_induce_iff diff_subset, subset_diff, and_congr_right_iff,
    and_iff_right_iff_imp]
  exact fun h _ ↦ h.vertexSet_mono

lemma deleteVerts_le_deleteEdges (h : ∀ e ∈ E(G) ∩ F, ∃ x ∈ X, G.Inc e x) : G - X ≤ G ＼ F := by
  refine ⟨by simp, fun e x y hl ↦ ?_⟩
  simp only [deleteVerts_isLink_iff, deleteEdges_isLink] at hl ⊢
  use hl.1
  rintro heF
  obtain ⟨v, hvX, hev⟩ := h e ⟨hl.1.edge_mem, heF⟩
  obtain rfl | rfl := hev.eq_or_eq_of_isLink hl.1
  · exact hl.2.1 hvX
  exact hl.2.2 hvX

@[simp]
lemma deleteVerts_isInducedSubgraph_deleteVerts_iff (G : Graph α β) (X Y : Set α) :
    G - X ≤i G - Y ↔ V(G) \ X ⊆ V(G) \ Y := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨by simp_all [subset_diff], by simp_all⟩⟩
  grw [← G.vertexSet_deleteVerts X, ← G.vertexSet_deleteVerts Y, h.le']

@[gcongr]
lemma IsInducedSubgraph.deleteVerts (h : H ≤i G) (X : Set α) : H - X ≤i G - X := by
  refine ⟨deleteVerts_mono_left h.le X, fun e x y he hx hy ↦ ?_⟩
  simp_all only [deleteVerts_isLink_iff, vertexSet_deleteVerts, mem_diff, not_false_eq_true,
    and_true, and_self]
  exact h.isLink_of_mem_mem he.1 hx hy

@[gcongr]
lemma IsSpanningSubgraph.deleteVerts (h : H ≤s G) (X : Set α) : H - X ≤s G - X where
  vertexSet_eq := by simp [h.vertexSet_eq]
  vertexSet_mono := by simp [h.vertexSet_eq]
  isLink_mono := deleteVerts_mono_left h.le X |>.isLink_mono

namespace IsClosedSubgraph

@[gcongr]
lemma deleteVerts (h : H ≤c G) (X : Set α) : H - X ≤c G - X :=
  mk' (deleteVerts_mono_left h.le X) <| fun e x he hx ↦ by
    simp only [vertexSet_deleteVerts, mem_diff, deleteVerts_inc_iff, mem_setIncEdges_iff,
      not_exists, not_and, edgeSet_deleteVerts, mem_setOf_eq] at hx he ⊢
    obtain ⟨⟨y, hxy⟩, hinc⟩ := he
    use x, y, h.isLink_congr hx.1 |>.mpr hxy, hx.2, mt (hinc y) (by simp [hxy.inc_right])

lemma deleteVerts_of_disjoint (h : H ≤c G) (hS : Disjoint V(H) X) : H ≤c G - X :=
  mk' ((G.deleteVerts_isInducedSubgraph X).le_of_le_subset h.le
    (by simp [subset_diff, hS, h.vertexSet_mono]))
    fun _ _ hex ↦ h.closed (hex.of_le deleteVerts_le)

lemma diff {H₁ H₂ : Graph α β} (h₁ : H₁ ≤c G) (h₂ : H₂ ≤c G) : H₁ - V(H₂) ≤c G :=
  mk' (deleteVerts_le.trans h₁.le) <| fun e x he hx ↦ by
    simp only [edgeSet_deleteVerts, mem_setOf_eq]
    simp only [vertexSet_deleteVerts, mem_diff] at hx
    obtain ⟨y, hexy⟩ := he
    refine ⟨x, y, (h₁.isLink_congr hx.1).mpr hexy, hx.2, fun hy ↦ hx.2 ?_⟩
    exact ((h₂.isLink_congr hy).mpr hexy.symm).right_mem

lemma diff_edgeSet {H₁ H₂ : Graph α β} (h₁ : H₁ ≤c G) (h₂ : H₂ ≤c G) :
    E(H₁ - V(H₂)) = E(H₁) \ E(H₂) := by
  ext e
  wlog heH₁ : e ∈ E(H₁)
  · grind
  simp only [edgeSet_deleteVerts, mem_setOf_eq, mem_diff, heH₁, true_and]
  refine ⟨fun ⟨x, y, hexy, hx, hy⟩ heH₂ ↦ hx (hexy.of_le h₁.le |>.of_le_of_mem h₂.le heH₂
  |>.left_mem), fun heH₂ ↦ ?_⟩
  obtain ⟨x, y, hexy⟩ := exists_isLink_of_mem_edgeSet heH₁
  have hexy' := hexy.of_le h₁.le
  use x, y, hexy, ?_, ?_ <;> contrapose! heH₂
  · exact (h₂.isLink_congr heH₂).mpr hexy' |>.edge_mem
  exact ((h₂.isLink_congr heH₂).mpr hexy'.symm).edge_mem

lemma compl (h : H ≤c G) : G - V(H) ≤c G := IsClosedSubgraph.rfl.diff h

lemma compl_edgeSet (h : H ≤c G) : E(G - V(H)) = E(G) \ E(H) := IsClosedSubgraph.rfl.diff_edgeSet h

@[simp]
lemma eq_union_deleteVerts (h : H ≤c G) : H ∪ (G - V(H)) = G := by
  refine ext_of_le_le (Graph.union_le h.le deleteVerts_le) le_rfl ?_ ?_
  · simp [union_eq_right.mpr h.vertexSet_mono]
  simp [-edgeSet_deleteVerts, union_eq_right.mpr h.edgeSet_mono, h.compl_edgeSet]

lemma of_deleteEdges_iff (hclF : H ≤c G ＼ F) : H ≤c G ↔ E(G) ∩ F ⊆ E(G - V(H)) := by
  rw [edgeSet_deleteVerts]
  refine ⟨fun hcl f hf ↦ ?_, fun hF ↦ mk' (hclF.le.trans deleteEdges_le) fun e x he hxH => ?_⟩
  · by_contra! hfH
    simp only [mem_setOf_eq, not_exists, not_and, not_not] at hfH
    refine (hclF.edgeSet_mono ?_).2 hf.2
    obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet hf.1
    obtain hx | hy := or_iff_not_imp_left.mpr <| hfH x y hxy
    · exact hcl.closed ⟨_, hxy⟩ hx
    · exact hcl.closed ⟨_, hxy.symm⟩ hy
  · have heF : e ∉ F := fun heF => by
      obtain ⟨u, v, heuv, hunH, hvnH⟩ := hF ⟨he.edge_mem, heF⟩
      obtain rfl | rfl := he.eq_or_eq_of_isLink heuv <;> exact (‹x ∉ V(H)› hxH).elim
    exact hclF.closed (by simp [he, heF]) hxH

@[gcongr, grind =>]
lemma restrict (h : H ≤c G) (F : Set β) : H ↾ F ≤c G ↾ F := mk' (restrict_mono_left h.le F)
  fun e x hex hx ↦ by
    obtain ⟨heG, heF⟩ := by simpa only [edgeSet_restrict, mem_inter_iff] using hex.edge_mem
    exact ⟨h.closed (hex.of_le restrict_le) hx, heF⟩

@[gcongr, grind =>]
lemma deleteEdges (h : H ≤c G) (F : Set β) : H ＼ F ≤c G ＼ F := mk' (deleteEdges_mono_left h.le F)
  fun e x hex hx ↦ by
    obtain ⟨heG, heF⟩ := by simpa only [edgeSet_deleteEdges, mem_diff] using hex.edge_mem
    exact ⟨h.closed (hex.of_le deleteEdges_le) hx, heF⟩

end IsClosedSubgraph
end Graph
