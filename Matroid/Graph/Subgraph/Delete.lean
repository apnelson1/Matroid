import Matroid.Graph.Subgraph.Defs

variable {α β : Type*} {x y z u v w : α} {e f : β} {G H K : Graph α β} {F F₁ F₂ : Set β}
  {X Y : Set α}

open Set

namespace Graph

@[simp]
lemma edgeRestrict_isNonloopAt_iff : (G ↾ F).IsNonloopAt e x ↔ G.IsNonloopAt e x ∧ e ∈ F := by
  simp_rw [IsNonloopAt]
  aesop

@[gcongr]
lemma edgeRestrict_le_edgeRestrict (h : E(G) ∩ F₁ ⊆ E(G) ∩ F₂) : G ↾ F₁ ≤ G ↾ F₂ :=
  le_of_le_le_subset_subset edgeRestrict_le edgeRestrict_le (by simp) h

lemma edgeRestrict_le_edgeRestrict_iff (G : Graph α β) (F₁ F₂ : Set β) :
    G ↾ F₁ ≤ G ↾ F₂ ↔ E(G) ∩ F₁ ⊆ E(G) ∩ F₂ :=
  ⟨edgeSet_mono, edgeRestrict_le_edgeRestrict⟩

lemma edgeRestrict_of_superset (G : Graph α β) (hF : E(G) ⊆ F) : G ↾ F = G := by
  rw [← edgeRestrict_inter_edgeSet, inter_eq_self_of_subset_right hF, edgeRestrict_self]

@[gcongr]
lemma edgeRestrict_eq_edgeRestrict (h : E(G) ∩ F₁ = E(G) ∩ F₂) : G ↾ F₁ = G ↾ F₂ :=
  ext_of_le_le edgeRestrict_le edgeRestrict_le rfl h

lemma edgeRestrict_eq_edgeRestrict_iff (G : Graph α β) (F₁ F₂ : Set β) :
    G ↾ F₁ = G ↾ F₂ ↔ E(G) ∩ F₁ = E(G) ∩ F₂ := by
  refine ⟨fun h => ?_, edgeRestrict_eq_edgeRestrict⟩
  apply_fun edgeSet at h
  exact h

@[simp, grind =]
lemma le_edgeRestrict_iff : H ≤ (G ↾ F) ↔ H ≤ G ∧ E(H) ⊆ F :=
  ⟨fun h ↦ ⟨h.trans (by simp), (edgeSet_mono h).trans (by simp)⟩,
    fun h ↦ le_of_le_le_subset_subset h.1 (by simp) (by simpa using vertexSet_mono h.1)
    <| subset_inter (edgeSet_mono h.1) h.2⟩

@[simp, grind .]
lemma edgeRestrict_isSpanningSubgraph : G ↾ F ≤s G :=
  ⟨by simp, by simp⟩

@[gcongr]
lemma edgeRestrict_isSpanningSubgraph_edgeRestrict (h : E(G) ∩ F₁ ⊆ E(G) ∩ F₂) :
    G ↾ F₁ ≤s G ↾ F₂ where
  vertexSet_eq := by simp
  isLink_of_isLink := le_of_le_le_subset_subset edgeRestrict_le edgeRestrict_le (by simp) h
  |>.isLink_of_isLink

@[gcongr]
lemma edgeRestrict_isSpanningSubgraph_edgeRestrict' (h : F₁ ⊆ F₂) :
    G ↾ F₁ ≤s G ↾ F₂ where
  vertexSet_eq := by simp
  isLink_of_isLink := edgeRestrict_mono_right _ h |>.isLink_of_isLink

lemma edgeRestrict_isSpanningSubgraph_edgeRestrict_iff (G : Graph α β) (F₁ F₂ : Set β) :
    G ↾ F₁ ≤s G ↾ F₂ ↔ E(G) ∩ F₁ ⊆ E(G) ∩ F₂ := by
  refine ⟨fun h ↦ ?_, edgeRestrict_isSpanningSubgraph_edgeRestrict⟩
  grw [← edgeRestrict_edgeSet, ← edgeRestrict_edgeSet, h.le]

@[gcongr]
lemma IsSpanningSubgraph.edgeRestrict (h : H ≤s G) (F : Set β) : H ↾ F ≤s G ↾ F where
  vertexSet_eq := by simp [h.vertexSet_eq]
  isLink_of_isLink := edgeRestrict_mono_left h.le F |>.isLink_of_isLink


@[simp]
lemma edgeDelete_isNonloopAt_iff : (G ＼ F).IsNonloopAt e x ↔ G.IsNonloopAt e x ∧ e ∉ F := by
  simp only [edgeDelete_eq_edgeRestrict, edgeRestrict_isNonloopAt_iff, mem_diff,
    and_congr_right_iff, and_iff_right_iff_imp]
  exact fun h _ ↦ h.edge_mem

@[simp]
lemma edgeDelete_inter_edgeSet : G ＼ (F ∩ E(G)) = G ＼ F := by
  rw [edgeDelete_eq_edgeRestrict, edgeDelete_eq_edgeRestrict, diff_inter_self_eq_diff]

@[simp]
lemma edgeDelete_edgeSet_inter : G ＼ (E(G) ∩ F) = G ＼ F := by
  rw [inter_comm, edgeDelete_inter_edgeSet]

@[gcongr]
lemma edgeDelete_anti_right (G : Graph α β) {F₀ F : Set β} (hss : F₀ ⊆ F) : G ＼ F ≤ G ＼ F₀ := by
  simp_rw [edgeDelete_eq_edgeRestrict]
  exact G.edgeRestrict_mono_right <| diff_subset_diff_right hss

@[gcongr]
lemma edgeDelete_le_edgeDelete (h : E(G) \ F₁ ⊆ E(G) \ F₂) : G ＼ F₁ ≤ G ＼ F₂ :=
  le_of_le_le_subset_subset edgeDelete_le edgeDelete_le (by simp) h

lemma edgeDelete_le_edgeDelete_iff (G : Graph α β) (F₁ F₂ : Set β) :
    G ＼ F₁ ≤ G ＼ F₂ ↔ E(G) \ F₁ ⊆ E(G) \ F₂ := by
  refine ⟨fun h ↦ ?_, edgeDelete_le_edgeDelete⟩
  apply_fun edgeSet (α := α) (β := β) at h using Graph.edgeSet_monotone (α := α) (β := β)
  exact h

@[simp]
lemma edgeRestrict_edgeDelete (G : Graph α β) (F₁ F₂ : Set β) : (G ↾ F₁) ＼ F₂ = G ↾ F₁ \ F₂ := by
  rw [edgeDelete_eq_edgeRestrict, edgeRestrict_edgeRestrict, edgeRestrict_edgeSet, diff_eq,
    ← inter_assoc, inter_comm E(G), ← inter_assoc, inter_self, inter_comm F₁, inter_assoc,
    edgeRestrict_edgeSet_inter, diff_eq]

lemma edgeRestrict_edgeDelete_comm (G : Graph α β) (F₁ F₂ : Set β) :
    (G ↾ F₁) ＼ F₂ = G ＼ F₂ ↾ F₁ := by
  conv_rhs => rw [edgeDelete_eq_edgeRestrict, edgeRestrict_edgeRestrict,
    diff_inter_right_comm, ← edgeRestrict_edgeDelete, G.edgeRestrict_edgeSet_inter F₁]

@[simp]
lemma edgeDelete_edgeRestrict (G : Graph α β) (F₁ F₂ : Set β) : G ＼ F₁ ↾ F₂ = G ↾ (F₂ \ F₁) := by
  rw [← edgeRestrict_edgeDelete_comm, edgeRestrict_edgeDelete]

lemma edgeDelete_edgeDelete_comm (G : Graph α β) (F₁ F₂ : Set β) :
    G ＼ F₁ ＼ F₂ = G ＼ F₂ ＼ F₁ := by
  rw [edgeDelete_edgeDelete, union_comm, ← edgeDelete_edgeDelete]

lemma edgeDelete_eq (G : Graph α β) (hF : Disjoint E(G) F) : G ＼ F = G := by
  simp [edgeDelete_eq_edgeRestrict, hF.sdiff_eq_left]

lemma edgeDelete_eq_of_disjoint (hF : Disjoint E(G) F) : G ＼ F = G := by
  rw [edgeDelete_eq_edgeRestrict]
  exact edgeRestrict_of_superset _ hF.sdiff_eq_left.symm.subset

lemma edgeDelete_eq_iff (G : Graph α β) (F : Set β) : G ＼ F = G ↔ Disjoint E(G) F := by
  refine ⟨fun h ↦ ?_, edgeDelete_eq_of_disjoint⟩
  apply_fun edgeSet at h
  simpa using h

@[gcongr]
lemma edgeDelete_eq_edgeDelete (h : E(G) \ F₁ = E(G) \ F₂) : G ＼ F₁ = G ＼ F₂ :=
  ext_of_le_le edgeDelete_le edgeDelete_le rfl h

lemma edgeDelete_eq_edgeDelete_iff (G : Graph α β) (F₁ F₂ : Set β) :
    G ＼ F₁ = G ＼ F₂ ↔ E(G) \ F₁ = E(G) \ F₂ := by
  refine ⟨fun h ↦ ?_, edgeDelete_eq_edgeDelete⟩
  apply_fun edgeSet (α := α) (β := β) at h using Graph.edgeSet_monotone (α := α) (β := β)
  exact h

@[simp]
lemma le_edgeDelete_iff : H ≤ G ＼ F ↔ H ≤ G ∧ Disjoint E(H) F := by
  simp only [edgeDelete_eq_edgeRestrict, le_edgeRestrict_iff, subset_diff, and_congr_right_iff,
    and_iff_right_iff_imp]
  exact fun hle _ ↦ edgeSet_mono hle

lemma IsNonloopAt.isLoopAt_delete (h : G.IsNonloopAt e x) : (G ＼ {e}).IsLoopAt = G.IsLoopAt := by
  ext f y
  simp only [← isLink_self_iff, edgeDelete_isLink, mem_singleton_iff, and_iff_left_iff_imp]
  rintro h' rfl
  exact h.not_isLoopAt y h'

lemma IsLoopAt.isNonloopAt_delete (h : G.IsLoopAt e x) : (G ＼ {e}).IsNonloopAt = G.IsNonloopAt := by
  ext f y
  simp only [isNonloopAt_iff_inc_not_isLoopAt, edgeDelete_inc_iff, mem_singleton_iff, ←
    isLink_self_iff, edgeDelete_isLink, not_and, not_not]
  obtain rfl | hne := eq_or_ne f e
  · simp only [not_true_eq_false, and_false, isLink_self_iff, implies_true, and_true,
      false_iff, not_and, not_not]
    exact fun h' ↦ by rwa [← h.eq_of_inc h']
  simp [hne]

@[simp]
lemma edgeDelete_isSpanningSubgraph : G ＼ F ≤s G where
  vertexSet_eq := by simp
  isLink_of_isLink := by simp +contextual

@[gcongr]
lemma edgeDelete_isSpanningSubgraph_edgeDelete (h : E(G) \ F₁ ⊆ E(G) \ F₂) :
    G ＼ F₁ ≤s G ＼ F₂ where
  vertexSet_eq := by simp
  isLink_of_isLink := edgeDelete_le_edgeDelete h |>.isLink_of_isLink

@[gcongr]
lemma edgeDelete_isSpanningSubgraph_anti_right (h : F₁ ⊆ F₂) : G ＼ F₂ ≤s G ＼ F₁ where
  vertexSet_eq := by simp
  isLink_of_isLink := G.edgeDelete_anti_right h |>.isLink_of_isLink

@[simp]
lemma edgeDelete_isSpanningSubgraph_edgeDelete_iff (G : Graph α β) (F₁ F₂ : Set β) :
    G ＼ F₁ ≤s G ＼ F₂ ↔ E(G) \ F₁ ⊆ E(G) \ F₂ := by
  refine ⟨fun h ↦ ?_, edgeDelete_isSpanningSubgraph_edgeDelete⟩
  grw [← edgeDelete_edgeSet, ← edgeDelete_edgeSet, h.le]

@[gcongr]
lemma IsSpanningSubgraph.edgeDelete (h : H ≤s G) (F : Set β) : H ＼ F ≤s G ＼ F where
  vertexSet_eq := by simp [h.vertexSet_eq]
  isLink_of_isLink := edgeDelete_mono_left h.le F |>.isLink_of_isLink

lemma edgeDelete_eq_noEdge (G : Graph α β) (hF : E(G) ⊆ F) : G ＼ F = Graph.noEdge V(G) β := by
  refine Graph.ext rfl fun e x y ↦ ?_
  simp only [edgeDelete_isLink, noEdge_isLink, iff_false, not_and, not_not]
  exact fun h ↦ hF h.edge_mem


lemma IsLink.induce (h : G.IsLink e x y) (hx : x ∈ X) (hy : y ∈ X) : G[X].IsLink e x y :=
  ⟨h, hx, hy⟩

@[simp]
lemma induce_adj_iff {X : Set α} : G[X].Adj x y ↔ G.Adj x y ∧ x ∈ X ∧ y ∈ X := by simp [Adj]

lemma Adj.induce (h : G.Adj x y) (hx : x ∈ X) (hy : y ∈ X) : G[X].Adj x y :=
  induce_adj_iff.mpr ⟨h, hx, hy⟩

@[simp]
lemma induce_edgeSet_subset (G : Graph α β) (X : Set α) : E(G[X]) ⊆ E(G) := by
  rintro e ⟨x, y, h, -, -⟩
  exact h.edge_mem

@[simp]
lemma induce_singleton_edgeSet (G : Graph α β) (x : α) : E(G[{x}]) = {e | G.IsLoopAt e x} := by
  simp [induce_edgeSet]

@[simp]
lemma induce_pair_edgeSet (G : Graph α β) (x y : α) : E(G, x, y) ⊆ E(G[{x, y}]) := by
  intro e he
  use x, y, he, by simp, by simp

lemma IsLink.mem_induce_iff (hG : G.IsLink e x y) : e ∈ E(G[X]) ↔ x ∈ X ∧ y ∈ X := by
  simp only [induce_edgeSet, mem_setOf_eq]
  refine ⟨fun ⟨x', y', he, hx', hy'⟩ ↦ ?_, fun h ↦ ⟨x, y, hG, h⟩⟩
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hG.eq_and_eq_or_eq_and_eq he <;> simp [hx', hy']

lemma induce_isLink_iff_of_mem_edgeSet (h : e ∈ E(G[X])) : G[X].IsLink e x y ↔ G.IsLink e x y := by
  obtain ⟨x', y', h', hx', hy'⟩ := h
  have : G[X].IsLink e x' y' := by use h'
  rw [h'.isLink_iff, this.isLink_iff]

lemma induce_induce (G : Graph α β) (X Y : Set α) : G[X][Y] = G[Y] ↾ E(G[X]) := by
  refine Graph.ext rfl fun e x y ↦ ?_
  simp only [induce_isLink, edgeRestrict_isLink]
  obtain he | he := em' (G.IsLink e x y)
  · simp [he]
  rw [he.mem_induce_iff]
  tauto

@[gcongr]
lemma induce_mono_right (G : Graph α β) (hXY : X ⊆ Y) : G[X] ≤ G[Y] where
  vertex_subset := hXY
  isLink_of_isLink _ _ _ := fun ⟨h, h1, h2⟩ ↦ ⟨h, hXY h1, hXY h2⟩

@[simp]
lemma induce_mono_right_iff (G : Graph α β) : G[X] ≤ G[Y] ↔ X ⊆ Y :=
  ⟨vertexSet_mono, induce_mono_right G⟩

@[gcongr]
lemma induce_mono_left (h : H ≤ G) (X : Set α) : H[X] ≤ G[X] where
  vertex_subset := le_rfl
  isLink_of_isLink e x y := by
    simp only [induce_isLink, and_imp]
    exact fun hl hx hy => ⟨hl.of_le h, hx, hy⟩

lemma induce_mono (h : H ≤ G) (hXY : X ⊆ Y) : H[X] ≤ G[Y] :=
  (induce_mono_left h X).trans (G.induce_mono_right hXY)

@[simp]
lemma induce_eq_self_iff (G : Graph α β) (X : Set α) : G[X] = G ↔ X = V(G) := by
  refine ⟨fun h ↦ h ▸ (by simp), fun h ↦ Graph.ext (by simpa) fun e x y ↦ ?_⟩
  subst h
  simp only [induce_vertexSet_self]

lemma le_induce_of_le_of_subset (h : H ≤ G) (hV : V(H) ⊆ X) : H ≤ G[X] :=
  ⟨hV, fun _ _ _ h' ↦ ⟨h'.of_le h, hV h'.left_mem, hV h'.right_mem⟩⟩

lemma le_induce_self (h : H ≤ G) : H ≤ G[V(H)] :=
  le_induce_of_le_of_subset h rfl.subset

lemma le_induce_iff (hX : X ⊆ V(G)) : H ≤ G[X] ↔ H ≤ G ∧ V(H) ⊆ X :=
  ⟨fun h ↦ ⟨h.trans (by simpa), vertexSet_mono h⟩, fun h ↦ le_induce_of_le_of_subset h.1 h.2⟩

lemma diff_subset_isolatedSet_induce (G : Graph α β) (X : Set α) : X \ V(G) ⊆ I(G[X]) := by
  intro x ⟨hxX, hx⟩
  simp only [mem_isolatedSet_iff, isolated_iff, induce_vertexSet, hxX, and_true]
  exact fun e he ↦ hx he.isLink_other.1.left_mem

@[simp]
lemma edgeRestrict_induce (G : Graph α β) (X : Set α) (F : Set β) : (G ↾ F)[X] = G[X] ↾ F := by
  refine Graph.ext (by simp) fun e x y ↦ ?_
  simp only [induce_isLink, edgeRestrict_isLink]
  tauto

lemma induce_isInducedSubgraph (hX : X ⊆ V(G)) : G[X] ≤i G := ⟨by simpa, by simp_all⟩

lemma IsInducedSubgraph.induce_vertexSet_eq (h : H ≤i G) : G[V(H)] = H := by
  have hle : G[V(H)] ≤ G := by simp [h.vertexSet_mono]
  refine G.ext_of_le_le hle h.le (by simp) <| Set.ext fun e ↦ ?_
  simp only [induce_edgeSet, mem_setOf_eq]
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
  grw [← G.induce_vertexSet X, ← G.induce_vertexSet Y, h.le]

@[gcongr]
lemma isSpanningSubgraph_of_induce (h : H ≤ G) (X : Set α) : H[X] ≤s G[X] where
  vertexSet_eq := by simp
  isLink_of_isLink := induce_mono_left h X |>.isLink_of_isLink

/-- An induced subgraph is precisely a subgraph of the form `G[X]` for some `X ⊆ V(G)`.
This version of the lemma can be used with `subst` or `obtain rfl` to replace `H` with `G[X]`. -/
lemma IsInducedSubgraph.exists_eq_induce (h : H ≤i G) : ∃ X ⊆ V(G), H = G[X] :=
  ⟨V(H), h.vertexSet_mono, h.induce_vertexSet_eq.symm⟩

lemma IsInducedSubgraph.eq_of_isSpanningSubgraph (hi : H ≤i G) (hs : H ≤s G) : H = G := by
  obtain ⟨X, hX, rfl⟩ := hi.exists_eq_induce
  have := hs.vertexSet_eq.symm
  simp_all

@[simp]
lemma induce_isInducedSubgraph_iff : G[X] ≤i G ↔ X ⊆ V(G) := by
  simp +contextual [isInducedSubgraph_iff]

@[simp]
lemma vertexDelete_isInducedSubgraph (G : Graph α β) (X : Set α) : G - X ≤i G :=
  ⟨vertexDelete_le, by simp_all⟩

@[simp]
lemma vertexDelete_eq_bot_iff (G : Graph α β) (X : Set α) : G - X = ⊥ ↔ V(G) ⊆ X := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · apply_fun vertexSet at h
    simpa [diff_eq_empty] using h
  simp [vertexDelete_def, diff_eq_empty.mpr h]

@[simp]
lemma bot_vertexDelete : (⊥ : Graph α β) - X = ⊥ := by
  simp [vertexDelete_def]

@[simp]
lemma vertexDelete_adj_iff (G : Graph α β) (X : Set α) :
    (G - X).Adj x y ↔ G.Adj x y ∧ x ∉ X ∧ y ∉ X := by
  simp [Adj]

@[simp]
lemma vertexDelete_vertexSet_inter (G : Graph α β) (X : Set α) : G - (V(G) ∩ X) = G - X := by
  simp [vertexDelete_def]

@[simp]
lemma vertexDelete_eq_self_iff (G : Graph α β) (X : Set α) : G - X = G ↔ Disjoint V(G) X := by
  refine ⟨fun h ↦ ?_, fun h ↦ (G.vertexDelete_isInducedSubgraph X).eq_of_vertexSet (by simpa)⟩
  rw [← h, vertexDelete_vertexSet]
  exact disjoint_sdiff_left

lemma IsLink.mem_vertexDelete_iff (hG : G.IsLink e x y) : e ∈ E(G - X) ↔ x ∉ X ∧ y ∉ X := by
  rw [vertexDelete_def, hG.mem_induce_iff, mem_diff, mem_diff, and_iff_right hG.left_mem,
    and_iff_right hG.right_mem]

lemma IsLink.not_mem_incidentEdges (h : (G - X).IsLink e x y) : e ∉ E(G, X) := by
  simp only [mem_setIncEdges_iff, not_exists, not_and]
  rintro z hzX hz
  obtain rfl | rfl := hz.eq_or_eq_of_isLink (h.of_le vertexDelete_le)
  · simpa [hzX] using h.left_mem
  simpa [hzX] using h.right_mem

@[simp]
lemma Inc.not_mem_of_mem (h : G.Inc e x) (hx : x ∈ X) : e ∉ E(G - X) := by
  simp only [vertexDelete_edgeSet, mem_setOf_eq, not_exists, not_and, not_not]
  rintro u v huv hu
  obtain rfl := h.eq_of_isLink_of_ne_left huv (fun h ↦ (hu <| h ▸ hx).elim)
  exact hx

lemma Inc.not_mem_incEdges (h : (G - X).Inc e x) : e ∉ E(G, X) :=
  h.choose_spec.not_mem_incidentEdges

lemma Inc.not_mem_of_vertexDelete (h : (G - X).Inc e x) : x ∉ X :=
  (h.choose_spec.of_le vertexDelete_le).mem_vertexDelete_iff.mp h.edge_mem |>.1

@[simp]
lemma vertexDelete_inc_iff (G : Graph α β) (X : Set α) :
    (G - X).Inc e x ↔ G.Inc e x ∧ e ∉ E(G, X) := by
  refine ⟨fun h ↦ ⟨h.of_le vertexDelete_le, h.not_mem_incEdges⟩,
    fun ⟨hex, he⟩ ↦ hex.of_le_of_mem vertexDelete_le ?_⟩
  rw [vertexDelete_edgeSet_diff, mem_diff]
  exact ⟨hex.edge_mem, he⟩

@[gcongr]
lemma vertexDelete_mono_left (h : H ≤ G) (X : Set α) : H - X ≤ G - X :=
  induce_mono h <| diff_subset_diff_left <| vertexSet_mono h

@[gcongr]
lemma vertexDelete_anti_right (G : Graph α β) (hXY : X ⊆ Y) : G - Y ≤ G - X :=
  induce_mono_right _ <| diff_subset_diff_right hXY

lemma vertexDelete_singleton_le_edgeDelete_linkEdges (G : Graph α β) (u v : α) :
    G - u ≤ G ＼ E(G, u, v) := by
  refine le_of_le_le_subset_subset vertexDelete_le edgeDelete_le (by simp) ?_
  rw [vertexDelete_singleton, vertexDelete_edgeSet_diff, edgeDelete_edgeSet, setIncEdges_singleton]
  exact diff_subset_diff_right <| G.linkEdges_subset_incEdges_left u v

@[simp]
lemma vertexDelete_linkEdges_of_not_mem (G : Graph α β) (hu : u ∉ X) (hv : v ∉ X) :
    E(G - X, u, v) = E(G, u, v) := by
  ext e
  simp [hu, hv]

lemma edgeRestrict_vertexDelete (G : Graph α β) (F : Set β) (D : Set α) :
    (G ↾ F) - D = (G - D) ↾ F := by
  refine Graph.ext rfl fun e x y ↦ ?_
  simp only [vertexDelete_isLink_iff, edgeRestrict_isLink]
  tauto

@[simp]
lemma edgeDelete_induce (G : Graph α β) (X : Set α) (F : Set β) : (G ＼ F)[X] = G[X] ＼ F := by
  rw [edgeDelete_eq_edgeRestrict, edgeRestrict_induce, ← edgeRestrict_edgeSet_inter,
    ← inter_diff_assoc, inter_eq_self_of_subset_left (by simp), ← edgeDelete_eq_edgeRestrict]

@[simp]
lemma induce_vertexDelete (G : Graph α β) (X D : Set α) : G[X] - D = G[X \ D] :=
  Graph.ext rfl <| by
  simp only [vertexDelete_isLink_iff, induce_isLink, mem_diff]
  tauto

@[simp]
lemma edgeDelete_vertexDelete (G : Graph α β) (F : Set β) (X : Set α) :
    (G ＼ F) - X = (G - X) ＼ F := by
  rw [edgeDelete_eq_edgeRestrict, edgeRestrict_vertexDelete, ← edgeRestrict_inter_edgeSet,
    diff_inter_right_comm, inter_eq_right.mpr (edgeSet_mono vertexDelete_le),
    ← edgeDelete_eq_edgeRestrict]

lemma vertexDelete_edgeDelete_incidentEdges (G : Graph α β) (X : Set α) :
    G ＼ E(G, X) - X = G - X := by
  rw [edgeDelete_vertexDelete, edgeDelete_eq_iff, vertexDelete_edgeSet_diff]
  exact disjoint_sdiff_left

lemma vertexDelete_vertexDelete (G : Graph α β) (X Y : Set α) : (G - X) - Y = G - (X ∪ Y) := by
  rw [G.vertexDelete_def, induce_vertexDelete, diff_diff, ← vertexDelete_def]

lemma vertexDelete_vertexDelete_comm (G : Graph α β) (X Y : Set α) : (G - X) - Y = (G - Y) - X := by
  rw [vertexDelete_vertexDelete, vertexDelete_vertexDelete, union_comm]

@[simp]
lemma le_vertexDelete_iff : H ≤ G - X ↔ H ≤ G ∧ Disjoint V(H) X := by
  simp only [vertexDelete_def, le_induce_iff diff_subset, subset_diff, and_congr_right_iff,
    and_iff_right_iff_imp]
  exact fun h _ ↦ vertexSet_mono h

lemma vertexDelete_le_edgeDelete (h : ∀ e ∈ E(G) ∩ F, ∃ x ∈ X, G.Inc e x) : G - X ≤ G ＼ F := by
  refine ⟨by simp [diff_subset], fun e x y hl ↦ ?_⟩
  simp only [vertexDelete_isLink_iff, edgeDelete_isLink] at hl ⊢
  use hl.1
  rintro heF
  obtain ⟨v, hvX, hev⟩ := h e ⟨hl.1.edge_mem, heF⟩
  obtain rfl | rfl := hev.eq_or_eq_of_isLink hl.1
  · exact hl.2.1 hvX
  exact hl.2.2 hvX

@[simp]
lemma vertexDelete_isInducedSubgraph_vertexDelete_iff (G : Graph α β) (X Y : Set α) :
    G - X ≤i G - Y ↔ V(G) \ X ⊆ V(G) \ Y := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨by simp_all [subset_diff], by simp_all⟩⟩
  grw [← G.vertexDelete_vertexSet X, ← G.vertexDelete_vertexSet Y, h.le]

@[gcongr]
lemma IsInducedSubgraph.vertexDelete (h : H ≤i G) (X : Set α) : H - X ≤i G - X := by
  refine ⟨vertexDelete_mono_left h.le X, fun e x y he hx hy ↦ ?_⟩
  simp_all only [vertexDelete_isLink_iff, vertexDelete_vertexSet, mem_diff, not_false_eq_true,
    and_true, and_self]
  exact h.isLink_of_mem_mem he.1 hx hy

@[gcongr]
lemma IsSpanningSubgraph.vertexDelete (h : H ≤s G) (X : Set α) : H - X ≤s G - X where
  vertexSet_eq := by simp [h.vertexSet_eq]
  isLink_of_isLink := vertexDelete_mono_left h.le X |>.isLink_of_isLink

@[gcongr]
lemma IsClosedSubgraph.vertexDelete (h : H ≤c G) (X : Set α) : H - X ≤c G - X where
  le := vertexDelete_mono_left h.le X
  closed e x he hx := by
    simp only [vertexDelete_vertexSet, mem_diff, vertexDelete_inc_iff, mem_setIncEdges_iff,
      not_exists, not_and, vertexDelete_edgeSet, mem_setOf_eq] at hx he ⊢
    obtain ⟨⟨y, hxy⟩, hinc⟩ := he
    use x, y, h.isLink_iff_of_mem hx.1 |>.mpr hxy, hx.2, mt (hinc y) (by simp [hxy.inc_right])

lemma IsClosedSubgraph.vertexDelete_of_disjoint (h : H ≤c G) (hS : Disjoint V(H) X) :
    H ≤c G - X where
  le := (G.vertexDelete_isInducedSubgraph X).le_of_le_subset h.le
    (by simp [subset_diff, hS, h.vertexSet_mono])
  closed e x hex hx := h.closed (hex.of_le vertexDelete_le) hx

lemma IsClosedSubgraph.diff {H₁ H₂ : Graph α β} (h₁ : H₁ ≤c G) (h₂ : H₂ ≤c G) :
    H₁ - V(H₂) ≤c G where
  le := vertexDelete_le.trans h₁.le
  closed e x he hx := by
    simp only [vertexDelete_edgeSet, mem_setOf_eq]
    simp only [vertexDelete_vertexSet, mem_diff] at hx
    obtain ⟨y, hexy⟩ := he
    refine ⟨x, y, hexy.of_isClosedSubgraph_of_mem h₁ hx.1, hx.2, fun hy ↦ hx.2 ?_⟩
    refine (hexy.symm.of_isClosedSubgraph_of_mem h₂ hy).right_mem

lemma IsClosedSubgraph.compl (h : H ≤c G) : G - V(H) ≤c G :=
  G.isClosedSubgraph_self.diff h

lemma IsClosedSubgraph.of_edgeDelete_iff (hclF : H ≤c G ＼ F) : H ≤c G ↔ E(G) ∩ F ⊆ E(G - V(H)) := by
  rw [vertexDelete_edgeSet]
  refine ⟨fun hcl f hf ↦ ?_, fun hF ↦ ⟨hclF.le.trans edgeDelete_le, fun e x he hxH => ?_⟩⟩
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
lemma IsClosedSubgraph.edgeRestrict (h : H ≤c G) (F : Set β) : H ↾ F ≤c G ↾ F where
  le := by grw [h.le]
  closed e x hex hx := by
    obtain ⟨heG, heF⟩ := by simpa using hex.edge_mem
    exact ⟨h.closed (hex.of_le edgeRestrict_le) hx, heF⟩

@[gcongr, grind =>]
lemma IsClosedSubgraph.edgeDelete (h : H ≤c G) (F : Set β) : H ＼ F ≤c G ＼ F where
  le := by grw [h.le]
  closed e x hex hx := by
    obtain ⟨heG, heF⟩ := by simpa using hex.edge_mem
    exact ⟨h.closed (hex.of_le edgeDelete_le) hx, heF⟩

end Graph
