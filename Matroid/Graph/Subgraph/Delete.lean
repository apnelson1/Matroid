import Matroid.Graph.Constructions.Basic

variable {α β : Type*} [CompleteLattice α] {x y z u v w : α} {e f : β} {G H K : Graph α β}
    {F F₁ F₂ : Set β} {X Y : Set α} {P Q : Partition α}

open Set Partition

open scoped Sym2

namespace Graph


/-- Restrict `G : Graph α β` to the edges in a set `E₀` without removing vertices -/
@[simps]
def edgeRestrict (G : Graph α β) (E₀ : Set β) : Graph α β where
  vertexPartition := P(G)
  vertexSet := V(G)
  vertexSet_eq_parts := G.vertexSet_eq_parts
  edgeSet := E₀ ∩ E(G)
  IsLink e x y := e ∈ E₀ ∧ G.IsLink e x y
  isLink_symm _ _ _ _ h := ⟨h.1, h.2.symm⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := G.eq_or_eq_of_isLink_of_isLink h.2 h'.2
  edge_mem_iff_exists_isLink e := ⟨fun h ↦ by simp [G.exists_isLink_of_mem_edgeSet h.2, h.1],
    fun ⟨x, y, h⟩ ↦ ⟨h.1, h.2.edge_mem⟩⟩
  left_mem_of_isLink _ _ _ h := G.left_mem_of_isLink h.2

/-- `G ↾ F` is the subgraph of `G` restricted to the edges in `F`. Vertices are not changed. -/
scoped infixl:65 " ↾ "  => Graph.edgeRestrict

lemma edgeRestrict_isLink_eq : (G ↾ F).IsLink e = (e ∈ F ∧ G.IsLink e · ·) := rfl

@[simp]
lemma edgeRestrict_le {E₀ : Set β} : G ↾ E₀ ≤ G where
  vertexSet_subset := by simp
  isLink_of_isLink := by simp

@[simp]
lemma edgeRestrict_inc_iff : (G ↾ F).Inc e x ↔ G.Inc e x ∧ e ∈ F := by
  simp [Inc, and_comm]

@[simp]
lemma edgeRestrict_isLoopAt_iff : (G ↾ F).IsLoopAt e x ↔ G.IsLoopAt e x ∧ e ∈ F := by
  simp [← isLink_self_iff, and_comm]

@[simp]
lemma edgeRestrict_isNonloopAt_iff : (G ↾ F).IsNonloopAt e x ↔ G.IsNonloopAt e x ∧ e ∈ F := by
  simp_rw [IsNonloopAt]
  aesop

lemma edgeRestrict_mono_right (G : Graph α β) {F₀ F : Set β} (hss : F₀ ⊆ F) : G ↾ F₀ ≤ G ↾ F where
  vertexSet_subset := by simp [edgeRestrict]
  isLink_of_isLink _ _ _ := fun h ↦ ⟨hss h.1, h.2⟩

lemma edgeRestrict_mono_left (h : H ≤ G) (F : Set β) : H ↾ F ≤ G ↾ F :=
  le_of_le_le_subset_subset (edgeRestrict_le.trans h)
    edgeRestrict_le (by simpa using vertexSet_mono h)
    <| by simp [inter_subset_right.trans (edgeSet_mono h)]

@[simp]
lemma edgeRestrict_inter_edgeSet (G : Graph α β) (F : Set β) : G ↾ (F ∩ E(G)) = G ↾ F :=
  ext_of_le_le (G := G) (by simp) (by simp) (by simp) (by simp)

@[simp]
lemma edgeRestrict_edgeSet_inter (G : Graph α β) (F : Set β) : G ↾ (E(G) ∩ F) = G ↾ F := by
  rw [inter_comm, edgeRestrict_inter_edgeSet]

@[simp]
lemma edgeRestrict_self (G : Graph α β) : G ↾ E(G) = G :=
  ext_of_le_le (G := G) (by simp) (by simp) rfl (by simp)

lemma edgeRestrict_of_superset (G : Graph α β) (hF : E(G) ⊆ F) : G ↾ F = G := by
  rw [← edgeRestrict_inter_edgeSet, inter_eq_self_of_subset_right hF, edgeRestrict_self]

@[simp]
lemma edgeRestrict_edgeRestrict (G : Graph α β) (F₁ F₂ : Set β) : (G ↾ F₁) ↾ F₂ = G ↾ F₁ ∩ F₂ := by
  refine G.ext_of_le_le ?_ (by simp) (by simp) ?_
  · exact edgeRestrict_le.trans (by simp)
  simp only [edgeRestrict_edgeSet]
  rw [← inter_assoc, inter_comm F₂]

@[simp]
lemma le_edgeRestrict_iff : H ≤ (G ↾ F) ↔ H ≤ G ∧ E(H) ⊆ F :=
  ⟨fun h ↦ ⟨h.trans (by simp), (edgeSet_mono h).trans (by simp)⟩,
    fun h ↦ le_of_le_le_subset_subset h.1 (by simp) (by simpa using vertexSet_mono h.1)
    <| subset_inter h.2 (edgeSet_mono h.1)⟩

@[simp]
lemma edgeRestrict_isSpanningSubgraph : G ↾ F ≤s G :=
  ⟨by simp, edgeRestrict_le.isLink_of_isLink⟩


/-- Delete a set `F` of edges from `G`. This is a special case of `edgeRestrict`,
but we define it with `copy` so that the edge set is definitionally equal to `E(G) \ F`. -/
@[simps!]
def edgeDelete (G : Graph α β) (F : Set β) : Graph α β :=
  (G.edgeRestrict (E(G) \ F)).copy (E := E(G) \ F)
  (l := fun e x y ↦ G.IsLink e x y ∧ e ∉ F) rfl rfl
  (by simp only [edgeRestrict_edgeSet, inter_eq_left, diff_subset])
  (fun e x y ↦ by
    simp only [edgeRestrict_isLink, mem_diff, and_comm, and_congr_left_iff, and_iff_left_iff_imp]
    exact fun h _ ↦ h.edge_mem)

/-- `G ＼ F` is the subgraph of `G` with the edges in `F` deleted. Vertices are not changed. -/
scoped infixl:65 " ＼ "  => Graph.edgeDelete

lemma edgeDelete_isLink_eq : (G ＼ F).IsLink e = (G.IsLink e · · ∧ e ∉ F) := rfl

lemma edgeDelete_eq_edgeRestrict (G : Graph α β) (F : Set β) :
    G ＼ F = G ↾ (E(G) \ F) := copy_eq_self ..

@[simp]
lemma edgeDelete_inc_iff : (G ＼ F).Inc e x ↔ G.Inc e x ∧ e ∉ F := by
  simp [Inc, and_comm]

@[simp]
lemma edgeDelete_isLoopAt_iff : (G ＼ F).IsLoopAt e x ↔ G.IsLoopAt e x ∧ e ∉ F := by
  simp only [edgeDelete_eq_edgeRestrict, edgeRestrict_isLoopAt_iff, mem_diff, and_congr_right_iff,
    and_iff_right_iff_imp]
  exact fun h _ ↦ h.edge_mem

@[simp]
lemma edgeDelete_isNonloopAt_iff : (G ＼ F).IsNonloopAt e x ↔ G.IsNonloopAt e x ∧ e ∉ F := by
  simp only [edgeDelete_eq_edgeRestrict, edgeRestrict_isNonloopAt_iff, mem_diff,
    and_congr_right_iff, and_iff_right_iff_imp]
  exact fun h _ ↦ h.edge_mem

@[simp]
lemma edgeDelete_le : G ＼ F ≤ G := by
  simp [edgeDelete_eq_edgeRestrict]

@[simp]
lemma edgeDelete_inter_edgeSet : G ＼ (F ∩ E(G)) = G ＼ F := by
  rw [edgeDelete_eq_edgeRestrict, edgeDelete_eq_edgeRestrict, diff_inter_self_eq_diff]

lemma edgeDelete_anti_right (G : Graph α β) {F₀ F : Set β} (hss : F₀ ⊆ F) : G ＼ F ≤ G ＼ F₀ := by
  simp_rw [edgeDelete_eq_edgeRestrict]
  exact G.edgeRestrict_mono_right <| diff_subset_diff_right hss

lemma edgeDelete_mono_left (h : H ≤ G) (F : Set β) : H ＼ F ≤ G ＼ F := by
  simp_rw [edgeDelete_eq_edgeRestrict]
  refine (edgeRestrict_mono_left h (E(H) \ F)).trans (G.edgeRestrict_mono_right ?_)
  exact diff_subset_diff_left (edgeSet_mono h)

@[simp]
lemma edgeDelete_edgeDelete (G : Graph α β) (F₁ F₂ : Set β) : G ＼ F₁ ＼ F₂ = G ＼ (F₁ ∪ F₂) := by
  simp only [edgeDelete_eq_edgeRestrict, diff_eq_compl_inter, edgeRestrict_inter_edgeSet,
    edgeRestrict_edgeSet, edgeRestrict_edgeRestrict, compl_union]
  rw [← inter_comm, inter_comm F₁ᶜ, inter_assoc, inter_assoc, inter_self, inter_comm,
    inter_assoc, inter_comm, edgeRestrict_inter_edgeSet]

@[simp]
lemma edgeRestrict_edgeDelete (G : Graph α β) (F₁ F₂ : Set β) : G ↾ F₁ ＼ F₂ = G ↾ (F₁ \ F₂) := by
  rw [edgeDelete_eq_edgeRestrict, edgeRestrict_edgeRestrict, edgeRestrict_edgeSet, diff_eq,
    ← inter_assoc, ← inter_assoc, inter_self, inter_comm F₁, inter_assoc,
    edgeRestrict_edgeSet_inter, diff_eq]

lemma edgeDelete_eq_self (G : Graph α β) (hF : Disjoint E(G) F) : G ＼ F = G := by
  simp [edgeDelete_eq_edgeRestrict, hF.sdiff_eq_left]

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

lemma IsLoopAt.isNonloopAt_delete (h : G.IsLoopAt e x) :
    (G ＼ {e}).IsNonloopAt = G.IsNonloopAt := by
  ext f y
  simp only [isNonloopAt_iff_inc_not_isLoopAt, edgeDelete_inc_iff, mem_singleton_iff, ←
    isLink_self_iff, edgeDelete_isLink, not_and, not_not]
  obtain rfl | hne := eq_or_ne f e
  · simp only [not_true_eq_false, and_false, isLink_self_iff, implies_true, and_true,
      false_iff, not_and, not_not]
    exact fun h' ↦ by rwa [← h.eq_of_inc h']
  simp [hne]

@[simp]
lemma edgeDelete_isSpanningSubgraph : G ＼ F ≤s G :=
  ⟨by simp, edgeDelete_le.isLink_of_isLink⟩

@[simps vertexSet vertexPartition isLink]
def induce (G : Graph α β) (X : Set α) : Graph α β where
  vertexPartition := P(G).restrict (V(G) ∩ X) <| G.vertexSet_eq_parts ▸ inter_subset_left
  vertexSet := V(G) ∩ X
  vertexSet_eq_parts := by simp
  IsLink e x y := G.IsLink e x y ∧ x ∈ X ∧ y ∈ X
  isLink_symm _ _ _ _ h := ⟨h.1.symm, h.2.symm⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := G.eq_or_eq_of_isLink_of_isLink h.1 h'.1
  left_mem_of_isLink _ _ _ h := ⟨G.left_mem_of_isLink h.1, h.2.1⟩

/-- `G[P]` is the subgraph of `G` induced by the parition `P` of vertices. -/
notation:max G:1000 "[" S "]" => Graph.induce G S

@[simp]
lemma induce_le : G[X] ≤ G where
  vertexSet_subset := by simp [induce]
  isLink_of_isLink := by simp +contextual [induce]

@[simp]
lemma induce_le_iff : G[X] ≤ G ↔ V(G) ∩ X ⊆ P(G) :=
  ⟨vertexPartition_mono, fun _ => induce_le⟩

lemma IsLink.induce (h : G.IsLink e x y) (hx : x ∈ X) (hy : y ∈ X) : G[X].IsLink e x y :=
  ⟨h, hx, hy⟩

@[simp]
lemma induce_adj_iff : G[X].Adj x y ↔ G.Adj x y ∧ x ∈ X ∧ y ∈ X := by
  simp [Adj]

lemma Adj.induce (h : G.Adj x y) (hx : x ∈ X) (hy : y ∈ X) : G[X].Adj x y :=
  induce_adj_iff.mpr ⟨h, hx, hy⟩

/-- This is too annoying to be a simp lemma. -/
lemma induce_edgeSet (G : Graph α β) (X : Set α) :
    E(G[X]) = {e | ∃ x y, G.IsLink e x y ∧ x ∈ X ∧ y ∈ X} := rfl

@[simp]
lemma induce_edgeSet_subset (G : Graph α β) (X : Set α) : E(G[X]) ⊆ E(G) := by
  rintro e ⟨x,y,h, -, -⟩
  exact h.edge_mem

lemma IsLink.mem_induce_iff (hG : G.IsLink e x y) : e ∈ E(G[X]) ↔ x ∈ X ∧ y ∈ X := by
  simp only [induce_edgeSet, mem_setOf_eq]
  refine ⟨fun ⟨x', y', he, hx', hy'⟩ ↦ ?_, fun h ↦ ⟨x, y, hG, h⟩⟩
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hG.eq_and_eq_or_eq_and_eq he <;> simp [hx', hy']

lemma induce_isLink_iff_of_mem_edgeSet (h : e ∈ E(G[X])) : G[X].IsLink e x y ↔ G.IsLink e x y := by
  obtain ⟨x', y', h', hx', hy'⟩ := h
  have : G[X].IsLink e x' y' := by use h'
  rw [h'.isLink_iff, this.isLink_iff]

lemma induce_induce (G : Graph α β) (X Y : Set α) : G[X][Y] = G[X ∩ Y] := by
  refine Graph.ext (by simp [inter_assoc]) fun e x y ↦ ?_
  simp only [induce_isLink, mem_inter_iff]
  tauto

lemma induce_mono_right (G : Graph α β) (hXY : X ⊆ Y) : G[X] ≤ G[Y] where
  vertexSet_subset := by simp [inter_subset_right.trans hXY]
  isLink_of_isLink _ _ _ := fun ⟨hl, hx, hy⟩ => ⟨hl, hXY hx, hXY hy⟩

lemma induce_vertexSet_inter (G : Graph α β) (X : Set α) : G[V(G) ∩ X] = G[X] := by
  refine Graph.ext (by simp) fun e x y ↦ ?_
  simp only [induce_isLink, mem_inter_iff, and_congr_right_iff]
  exact fun h ↦ by simp [h.left_mem, h.right_mem]

@[simp]
lemma induce_mono_right_iff (G : Graph α β) : G[X] ≤ G[Y] ↔ V(G) ∩ X ⊆ V(G) ∩ Y := by
  refine ⟨vertexSet_mono, fun hsu => ?_⟩
  rw [← G.induce_vertexSet_inter X, ← G.induce_vertexSet_inter Y]
  exact G.induce_mono_right hsu

lemma induce_mono_left (h : H ≤ G) (X : Set α) : H[X] ≤ G[X] where
  vertexSet_subset := by simp [inter_subset_left.trans (vertexSet_mono h)]
  isLink_of_isLink e x y := fun ⟨hl, hx, hy⟩ => ⟨hl.of_le h, hx, hy⟩

lemma induce_mono (h : H ≤ G) (hXY : X ⊆ Y) : H[X] ≤ G[Y] :=
  (induce_mono_left h X).trans (G.induce_mono_right hXY)

@[simp]
lemma induce_vertexSet_self (G : Graph α β) : G[V(G)] = G := by
  refine G.ext_of_le_le (by simp) (by simp) (by simp) <| Set.ext fun e ↦
    ⟨fun ⟨_, _, h⟩ ↦ h.1.edge_mem, fun h ↦ ?_⟩
  obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet h
  exact ⟨x, y, h, G.vertexSet_eq_parts ▸ h.left_mem, G.vertexSet_eq_parts ▸ h.right_mem⟩

lemma le_induce_of_le_of_subset (h : H ≤ G) (hV : V(H) ⊆ X) : H ≤ G[X] where
  vertexSet_subset := by simp [hV, vertexSet_mono h]
  isLink_of_isLink e x y hl := ⟨hl.of_le h, hV hl.left_mem, hV hl.right_mem⟩

lemma le_induce_self (h : H ≤ G) : H ≤ G[V(H)] :=
  le_induce_of_le_of_subset h <| H.vertexPartition_parts ▸ rfl.subset

lemma le_induce_iff : H ≤ G[X] ↔ H ≤ G ∧ V(H) ⊆ X := by
  refine ⟨fun h ↦ ⟨h.trans (by simp_all), ?_⟩, fun h ↦ le_induce_of_le_of_subset h.1 h.2⟩
  have := vertexSet_mono h
  simp_all

@[simp]
lemma edgeRestrict_induce (G : Graph α β) (X : Set α) (F : Set β) :
    (G ↾ F)[X] = G[X] ↾ F := by
  refine Graph.ext (by simp) fun e x y ↦ ?_
  simp only [induce_isLink, edgeRestrict_isLink]
  tauto

/-- The graph obtained from `G` by deleting a set of vertices. -/
protected def vertexDelete (G : Graph α β) (X : Set α) : Graph α β := G[V(G) \ X]

/-- `G - X` is the graph obtained from `G` by deleting the set `X` of vertices. -/
notation:max G:1000 " - " S:1000 => Graph.vertexDelete G S

-- instance instHSub : HSub (Graph α β) (Set α) (Graph α β) where
--   hSub := Graph.vertexDelete

lemma vertexDelete_def (G : Graph α β) (X : Set α) : G - X = G[V(G) \ X] := rfl

@[simp]
lemma vertexDelete_vertexPartition (G : Graph α β) (X : Set α) : P(G - X) = P(G) \ X := by
  simp only [vertexDelete_def, induce_vertexPartition]
  simp_rw [inter_diff_distrib_left, inter_self, diff_inter, diff_self, empty_union]
  apply Partition.ext fun x ↦ by simp

@[simp]
lemma vertexDelete_vertexSet (G : Graph α β) (X : Set α) : V(G - X) = V(G) \ X := by
  rw [← (G - X).vertexPartition_parts, vertexDelete_vertexPartition]
  simp

@[simp]
lemma vertexDelete_isLink_iff (G : Graph α β) (X : Set α) :
    (G - X).IsLink e x y ↔ (G.IsLink e x y ∧ x ∉ X ∧ y ∉ X) := by
  simp only [vertexDelete_def, induce_isLink, and_congr_right_iff]
  exact fun h ↦ by simp [h.left_mem, h.right_mem]

@[simp]
lemma vertexDelete_edgeSet (G : Graph α β) (X : Set α) :
    E(G - X) = {e | ∃ x y, G.IsLink e x y ∧ x ∉ X ∧ y ∉ X} := by
  simp [edgeSet_eq_setOf_exists_isLink]

@[simp]
lemma vertexDelete_empty (G : Graph α β) : G - ∅ = G := by
  simp [vertexDelete_def]

@[simp]
lemma vertexDelete_adj_iff (G : Graph α β) (X : Set α) :
    (G - X).Adj x y ↔ G.Adj x y ∧ x ∉ X ∧ y ∉ X := by
  simp [Adj]

@[simp]
lemma vertexDelete_le : G - X ≤ G := induce_le

lemma IsLink.mem_vertexDelete_iff (hG : G.IsLink e x y) : e ∈ E(G - X) ↔ x ∉ X ∧ y ∉ X := by
  simp [vertexDelete_def, hG.left_mem, hG.right_mem, hG.mem_induce_iff]

lemma vertexDelete_mono_left (h : H ≤ G) (X : Set α) : H - X ≤ G - X :=
  induce_mono h <| diff_subset_diff_left <| vertexSet_mono h

lemma vertexDelete_anti_right (hXY : X ⊆ Y) : G - Y ≤ G - X :=
  induce_mono_right _ <| diff_subset_diff_right hXY

lemma edgeRestrict_vertexDelete (G : Graph α β) (F : Set β) (D : Set α) :
    (G ↾ F) - D = (G - D) ↾ F := by
  refine Graph.ext rfl fun e x y ↦ ?_
  simp only [vertexDelete_isLink_iff, edgeRestrict_isLink]
  tauto

@[simp]
lemma edgeDelete_induce (G : Graph α β) (X : Set α) (F : Set β) :
    (G ＼ F)[X] = G[X] ＼ F := by
  rw [edgeDelete_eq_edgeRestrict, edgeRestrict_induce, ← edgeRestrict_edgeSet_inter,
    ← inter_diff_assoc, inter_eq_self_of_subset_left (by simp), ← edgeDelete_eq_edgeRestrict]

@[simp]
lemma induce_vertexDelete (G : Graph α β) (X D : Set α) :
    G[X] - D = G[X \ D] := Graph.ext (by simp [inter_diff_assoc]) <| by
  simp only [vertexDelete_isLink_iff, induce_isLink, mem_diff]
  tauto

lemma vertexDelete_vertexDelete (G : Graph α β) (X Y : Set α) : (G - X) - Y = G - (X ∪ Y) :=by
  rw [G.vertexDelete_def, induce_vertexDelete, diff_diff, ← vertexDelete_def]

lemma vertexDelete_vertexDelete_comm (G : Graph α β) (X Y : Set α) :
    (G - X) - Y = (G - Y) - X := by
  rw [vertexDelete_vertexDelete, vertexDelete_vertexDelete, union_comm]

@[simp]
lemma le_vertexDelete_iff : H ≤ G - X ↔ H ≤ G ∧ Disjoint V(H) X := by
  simp +contextual [vertexDelete_def, le_induce_iff, subset_diff, vertexSet_mono]

end Graph
