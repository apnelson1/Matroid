import Matroid.Graph.Label
import Matroid.Graph.Constructions.Basic

variable {α β : Type*} {x y z u v w : α} {e f : β} {G H K : Graph α β} {F F₁ F₂ : Set β}
    {X Y : Set α}

open Set Partition

open scoped Sym2

namespace Graph


/-- Restrict `G : Graph α β` to the edges in a set `E₀` without removing vertices -/
@[simps]
def edgeRestrict (G : Graph α β) (E₀ : Set β) : Graph α β where
  vertexSet := V(G)
  edgeSet := E₀ ∩ E(G)
  IsLink e x y := e ∈ E₀ ∧ G.IsLink e x y
  isLink_symm _ _ _ _ h := ⟨h.1, h.2.symm⟩
  isLink_of_dup _ _ _ _ hxy := by simp [isLink_left_rw hxy]
  dup_or_dup_of_isLink_of_isLink _ _ _ _ _ h h' :=
    G.dup_or_dup_of_isLink_of_isLink h.2 h'.2
  edge_mem_iff_exists_isLink e := ⟨fun h ↦ by simp [G.exists_isLink_of_mem_edgeSet h.2, h.1],
    fun ⟨x, y, h⟩ ↦ ⟨h.1, h.2.edge_mem⟩⟩
  mem_vertexSet_of_isLink _ _ _ h := G.mem_vertexSet_of_isLink h.2

/-- `G ↾ F` is the subgraph of `G` restricted to the edges in `F`. Vertices are not changed. -/
scoped infixl:65 " ↾ "  => Graph.edgeRestrict

@[simp]
lemma edgeRestrict_le {E₀ : Set β} : G ↾ E₀ ≤ G where
  vertexSet_subset := by simp [edgeRestrict]
  isLink_of_isLink := by simp

instance [G.Nodup] : Nodup (G ↾ F) := Nodup.of_le (edgeRestrict_le)

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
  le_of_le_isLabelSubgraph_subset_subset (edgeRestrict_le.trans h)
    (isLabelSubgraph_of_le edgeRestrict_le) (by simpa using labelSet_mono h)
    <| by simp [inter_subset_right.trans (edgeSet_mono h)]

@[simp]
lemma edgeRestrict_inter_edgeSet (G : Graph α β) (F : Set β) : G ↾ (F ∩ E(G)) = G ↾ F :=
  ext_of_isLabelSubgraph_eq_Set (G := G) (by simp) (by simp) (by simp) (by simp)

@[simp]
lemma edgeRestrict_edgeSet_inter (G : Graph α β) (F : Set β) : G ↾ (E(G) ∩ F) = G ↾ F := by
  rw [inter_comm, edgeRestrict_inter_edgeSet]

@[simp]
lemma edgeRestrict_self (G : Graph α β) : G ↾ E(G) = G :=
  ext_of_isLabelSubgraph_eq_Set (G := G) (by simp) (by simp) rfl (by simp)

lemma edgeRestrict_of_superset (G : Graph α β) (hF : E(G) ⊆ F) : G ↾ F = G := by
  rw [← edgeRestrict_inter_edgeSet, inter_eq_self_of_subset_right hF, edgeRestrict_self]

@[simp]
lemma edgeRestrict_edgeRestrict (G : Graph α β) (F₁ F₂ : Set β) : (G ↾ F₁) ↾ F₂ = G ↾ F₁ ∩ F₂ := by
  refine G.ext_of_isLabelSubgraph_eq_Set ?_ (by simp) (by simp) ?_
  · exact (isLabelSubgraph_of_le edgeRestrict_le).trans (by simp)
  simp only [edgeRestrict_edgeSet]
  rw [← inter_assoc, inter_comm F₂]

@[simp]
lemma le_edgeRestrict_iff : H ≤ (G ↾ F) ↔ H ≤ G ∧ E(H) ⊆ F :=
  ⟨fun h ↦ ⟨h.trans (by simp), (edgeSet_mono h).trans (by simp)⟩,
    fun h ↦ le_of_le_isLabelSubgraph_subset_subset h.1 (by simp) (by simpa using labelSet_mono h.1)
    <| subset_inter h.2 (edgeSet_mono h.1)⟩

@[simp]
lemma edgeRestrict_isSpanningSubgraph : G ↾ F ≤s G :=
  ⟨by simp, edgeRestrict_le.isLink_of_isLink⟩


/-- Delete a set `F` of edges from `G`. This is a special case of `edgeRestrict`,
but we define it with `copy` so that the edge set is definitionally equal to `E(G) \ F`. -/
@[simps!]
def edgeDelete (G : Graph α β) (F : Set β) : Graph α β :=
  (G.edgeRestrict (E(G) \ F)).copy (E := E(G) \ F)
  (l := fun e x y ↦ G.IsLink e x y ∧ e ∉ F) rfl
  (by simp [diff_subset])
  (fun e x y ↦ by
    simp only [edgeRestrict_isLink, mem_diff, and_comm, and_congr_left_iff, and_iff_left_iff_imp]
    exact fun h _ ↦ h.edge_mem)

/-- `G ＼ F` is the subgraph of `G` with the edges in `F` deleted. Vertices are not changed. -/
scoped infixl:65 " ＼ "  => Graph.edgeDelete

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

instance [G.Nodup] : Nodup (G ＼ F) := Nodup.of_le (edgeDelete_le)

@[simp]
lemma edgeDelete_inter_edgeSet : G ＼ (F ∩ E(G)) = G ＼ F := by
  rw [edgeDelete_eq_edgeRestrict, edgeDelete_eq_edgeRestrict, diff_inter_self_eq_diff]

lemma edgeDelete_anti_right (G : Graph α β) {F₀ F : Set β} (hss : F₀ ⊆ F) : G ＼ F ≤ G ＼ F₀ := by
  simp_rw [edgeDelete_eq_edgeRestrict]
  exact G.edgeRestrict_mono_right <| diff_subset_diff_right hss

lemma edgeDelete_mono_left (h : H ≤ G) : H ＼ F ≤ G ＼ F := by
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
    exact fun h' ↦ h.dup (h.dup_of_inc h')
  simp [hne]

@[simp]
lemma edgeDelete_isSpanningSubgraph : G ＼ F ≤s G :=
  ⟨by simp, edgeDelete_le.isLink_of_isLink⟩


/-- The subgraph of `G` induced by a set `X` of vertices.
The edges are the edges of `G` with both ends in `X`.
(`X` is not required to be a subset of `V(G)` for this definition to work,
even though this is the standard use case) -/
@[simps! vertexSet isLink]
protected def induce (G : Graph α β) (X : Set α) : Graph α β :=
  Graph.mk_of_domp (V(G).cover X) (fun e ↦ Relation.restrict (G.IsLink e) X)
    (fun e ↦ btwVx_cover (G.dup_or_dup_of_isLink_of_isLink (e := e)))

/-- `G[X]` is the subgraph of `G` induced by the set `X` of vertices. -/
notation:max G:1000 "[" S "]" => Graph.induce G S

@[simp↓]
lemma mem_induce_labelSet_iff_exists_mem : x ∈ L(G[X]) ↔ ∃ y ∈ X, V(G) x y := by
  simp only [induce_vertexSet, cover_supp, mem_parts, SetLike.mem_coe, sSup_eq_sUnion, mem_sUnion,
    mem_setOf_eq, and_assoc, rel_iff_exists, not_disjoint_iff]
  simp_rw [← exists_and_right, ← exists_and_left]
  rw [exists_comm]
  apply exists₂_congr fun y t => ?_
  tauto

@[simp]
lemma induce_labelSet : L(G[X]) = {x | ∃ y ∈ X, V(G) x y} := by
  ext y
  simp

lemma induce_isLink_le : G[X].IsLink ≤ G.IsLink := by
  rintro e x y ⟨x', hx', y', hy'x', hy'⟩
  have hle := rel_le_of_subset <| V(G).cover_subset X
  rw [isLink_left_rw (hle _ _ hx'), isLink_right_rw (symm <| hle _ _ hy')]
  exact (Relation.restrict_le _ _ _ _ hy'x').symm

lemma IsLink.induce (h : G.IsLink e x y) (hx : x ∈ X) (hy : y ∈ X) : G[X].IsLink e x y := by
  refine ⟨x, ?_, y, by simp [Relation.restrict, hx, hy, h], ?_⟩ <;>
  · apply rel_le_of_le (V(G).induce_le_cover X)
    simp [hx, h.left_refl, hy, h.right_refl]

/-- If you need to use this lemma, you made a wrong choice of `X` or `x`/`y`.
  Please consider revising them and using `IsLink.induce` instead. -/
lemma IsLink.induce_of_mem_labelSet (h : G.IsLink e x y) (hx : x ∈ L(G[X])) (hy : y ∈ L(G[X])) :
    G[X].IsLink e x y := by
  obtain ⟨x', hx'X, hx⟩ := induce_labelSet ▸ hx
  obtain ⟨y', hy'X, hy⟩ := induce_labelSet ▸ hy
  rw [isLink_left_rw hx, isLink_right_rw hy] at h
  refine ⟨x', ?_, y', by simp [Relation.restrict, hx'X, hy'X, h], ?_⟩ <;>
  simp [hx'X, hy'X, hx, symm hy]

@[simp↓]
lemma induce_isLink_iff_of_mem (hxX : x ∈ X) (hyX : y ∈ X) :
    G[X].IsLink e x y ↔ G.IsLink e x y :=
  ⟨induce_isLink_le _ _ _, fun h ↦ h.induce hxX hyX⟩

/-- If you need to use this lemma, you made a wrong choice of `X` or `x`/`y`.
  Please consider revising them and using `induce_isLink_iff_of_mem` instead. -/
@[simp↓]
lemma induce_isLink_iff_of_mem_labelSet (hxX : x ∈ L(G[X])) (hyX : y ∈ L(G[X])) :
    G[X].IsLink e x y ↔ G.IsLink e x y :=
  ⟨induce_isLink_le _ _ _, fun h ↦ h.induce_of_mem_labelSet hxX hyX⟩

@[simp↓]
lemma induce_adj_iff_of_mem (hxX : x ∈ X) (hyX : y ∈ X) : G[X].Adj x y ↔ G.Adj x y := by
  simp [Adj, hxX, hyX]

lemma Adj.induce (h : G.Adj x y) (hx : x ∈ X) (hy : y ∈ X) : G[X].Adj x y :=
  (induce_adj_iff_of_mem hx hy).mpr h

/-- This is too annoying to be a simp lemma. -/
lemma induce_edgeSet (G : Graph α β) (X : Set α) : E(G[X]) =
    {e | ∃ x y, Relation.Domp (⇑(V(G).cover X)) (Relation.restrict (G.IsLink e) X) x y} := by
  simp [edgeSet_eq_setOf_exists_isLink]

@[simp]
lemma induce_edgeSet_subset (G : Graph α β) (X : Set α) : E(G.induce X) ⊆ E(G) := by
  rintro e ⟨x, y, x', hx', y', h, hy'⟩
  exact (Relation.restrict_le _ _ _ _ h).edge_mem

-- lemma IsLink.mem_induce_iff [G.Nodup] {X : Set α} (hG : G.IsLink e x y) :
--     e ∈ E(G[X]) ↔ x ∈ X ∧ y ∈ X := by
--   simp only [induce_edgeSet, mem_setOf_eq]
--   refine ⟨fun ⟨x', y', he, hx', hy'⟩ ↦ ?_, fun h ↦ ⟨x, y, hG, h⟩⟩
--   obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hG.eq_and_eq_or_eq_and_eq he <;> simp [hx', hy']

-- lemma induce_induce (G : Graph α β) [G.Nodup] (X Y : Set α) : G[X][Y] = G[Y] ↾ E(G[X]) := by
--   refine Graph.ext ?_ fun e x y ↦ ?_
--   · ext x y
--     simp only [induce_dup, dup_iff_eq, edgeRestrict_dup]
--     tauto
--   simp only [induce_isLink_iff, edgeRestrict_isLink]
--   obtain he | he := em' (G.IsLink e x y)
--   · simp [he]
--   rw [he.mem_induce_iff]
--   tauto

lemma induce_isLabelSubgraph : G[X] ≤l G where
  vertexSet_isInducedSubpartition := isInducedSubpartition_of_subset (cover_subset _)
  isLink_of_isLink := induce_isLink_le

-- instance [G.Nodup] : Nodup (G[X]) where
--   NodupAt x y hdup := by
--     rw [induce_dup, dup_iff_eq] at hdup
--     obtain ⟨-, -, (⟨rfl, -⟩ | rfl)⟩ := hdup <;> rfl

-- @[simp]
-- lemma induce_isLabelSubgraph_iff : G[X] ≤l G ↔ X ⊆ V(G) :=
--   ⟨IsLabelSubgraph.vertexSet, induce_isLabelSubgraph⟩

-- lemma induce_mono_right (G : Graph α β) (hXY : X ⊆ Y) : G[X] ≤l G[Y] where
--   dup_iff x y hx hy := by
--     simp only [induce_vertexSet] at hx hy
--     simp [hx, hy, hXY hx, hXY hy]
--   isLink_of_isLink _ _ _ := fun ⟨h, h1, h2⟩ ↦ ⟨h, hXY h1, hXY h2⟩

-- @[simp]
-- lemma induce_mono_right_iff (G : Graph α β) : G[X] ≤l G[Y] ↔ X ⊆ Y :=
--   ⟨IsLabelSubgraph.vertexSet, induce_mono_right G⟩

-- lemma induce_mono_left [G.Nodup] (h : H ≤l G) (X : Set α) : H[X] ≤l G[X] := by
--   have := Nodup.of_isLabelSubgraph h
--   rw [isLabelSubgraph_iff]
--   exact ⟨by simp, fun e x y ⟨hl, hx, hy⟩ => ⟨hl.of_isLabelSubgraph h, hx, hy⟩⟩

-- lemma induce_mono [G.Nodup] (h : H ≤l G) (hXY : X ⊆ Y) : H[X] ≤l G[Y] :=
--   (induce_mono_left h X).trans (G.induce_mono_right hXY)

-- @[simp]
-- lemma induce_vertexSet_self (G : Graph α β) : G[V(G)] = G := by
--   refine G.ext_of_isLabelSubgraph_eq_Set (by simp) (by simp) rfl <| Set.ext fun e ↦
--     ⟨fun ⟨_, _, h⟩ ↦ h.1.edge_mem, fun h ↦ ?_⟩
--   obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet h
--   exact ⟨x, y, h, h.left_mem, h.right_mem⟩

-- lemma le_induce_of_le_of_subset (h : H ≤ G) (hV : V(H) ⊆ X) : H ≤ G[X] where
--   dup_iff x y hx hy := by
--     simp only [induce_dup, hV hx, hV hy, h.dup_iff hx hy, true_and, or_iff_left_iff_imp]
--     rintro rfl
--     rwa [← H.dup_refl_iff]
--   isLink_of_isLink _ _ _ h' := ⟨h'.of_le h, hV h'.left_mem, hV h'.right_mem⟩
--   dup_closed x y hxy hx := by
--     obtain ⟨hxX, hyX, hdup | rfl⟩ := hxy
--     · exact h.dup_closed hdup hx
--     exact hx

-- lemma le_induce_self (h : H ≤ G) : H ≤ G[V(H)] :=
--   le_induce_of_le_of_subset h rfl.subset

-- -- lemma le_induce_iff (hX : X ⊆ V(G)) : H ≤ G[X] ↔ H ≤ G ∧ V(H) ⊆ X :=
-- --   ⟨fun h ↦ ⟨h.trans (by simpa), vertexSet_mono h⟩, fun h ↦ le_induce_of_le_of_subset h.1 h.2⟩

-- @[simp]
-- lemma edgeRestrict_induce (G : Graph α β) (X : Set α) (F : Set β) : (G ↾ F)[X] = G[X] ↾ F := by
--   refine Graph.ext (by ext ; simp) fun e x y ↦ ?_
--   simp only [induce_isLink_iff, edgeRestrict_isLink]
--   tauto

-- @[simp]
-- lemma edgeDelete_induce (G : Graph α β) (X : Set α) (F : Set β) : (G ＼ F)[X] = G[X] ＼ F := by
--   rw [edgeDelete_eq_edgeRestrict, edgeRestrict_induce, ← edgeRestrict_edgeSet_inter,
--     ← inter_diff_assoc, inter_eq_self_of_subset_left (by simp), ← edgeDelete_eq_edgeRestrict]


/-- The graph obtained from `G` by deleting a set of vertices. -/
@[simps]
protected def vertexDelete (G : Graph α β) (X : Set α) : Graph α β where
  Dup := G.Dup.induce Xᶜ
  vertexSet := V(G) \ X
  vertexSet_eq := by aesop
  IsLink e x y := G.IsLink e x y ∧ x ∉ X ∧ y ∉ X
  isLink_symm e he a b := by
    intro ⟨hlab, ha, hb⟩
    exact ⟨hlab.symm, hb, ha⟩
  dup_or_dup_of_isLink_of_isLink e a b c d := by
    rintro ⟨hl, ha, hb⟩ ⟨hl', hc, hd⟩
    simp only [induce_apply, mem_compl_iff, ha, not_false_eq_true, hc, true_and, hd]
    exact (G.dup_or_dup_of_isLink_of_isLink hl hl').imp id id
  isLink_of_dup e x y z := by
    rintro ⟨S, hS, hxS, hyS⟩ ⟨hl, hxX, hzX⟩
    obtain ⟨hx, hy, hdup⟩ := G.Dup.induce_apply.mp <| rel_of_mem_of_mem hS hxS hyS
    use trans' hdup hl, hx
  mem_vertexSet_of_isLink := by
    rintro e x y ⟨hl, hx, hy⟩
    simp [hx, G.mem_vertexSet_of_isLink hl]

/-- `G - X` is the graph obtained from `G` by deleting the set `X` of vertices. -/
notation:max G:1000 " - " S:1000 => Graph.vertexDelete G S

-- instance instHSub : HSub (Graph α β) (Set α) (Graph α β) where
--   hSub := Graph.vertexDelete

-- lemma vertexDelete_def (G : Graph α β) (X : Set α) : G - X = G [V(G) \ X] := rfl

@[simp]
lemma vertexDelete_dup_apply (G : Graph α β) (X : Set α) (x y : α) :
    (G - X).Dup x y ↔ G.Dup x y ∧ x ∉ X ∧ y ∉ X := by
  ac_change G.Dup.induce _ x y ↔ x ∉ X ∧ y ∉ X ∧ G.Dup x y
  · exact and_rotate
  simp

@[simp]
lemma vertexDelete_empty (G : Graph α β) : G - ∅ = G := by
  ext a b c <;> simp

@[simp]
lemma vertexDelete_adj_iff (G : Graph α β) (X : Set α) :
    (G - X).Adj x y ↔ G.Adj x y ∧ x ∉ X ∧ y ∉ X := by
  simp [Adj]

lemma vertexDelete_mono_left (h : H ≤ G) : H - X ≤ G - X where
  dup_subset := induce_subset_induce_of_subset h.dup_subset _
  isLink_of_isLink _ _ _ h' := by simp_all [h.isLink_of_isLink h'.1]

lemma vertexDelete_anti_right_iff : G - Y ≤l G - X ↔ V(G) \ Y ⊆ V(G) \ X := by
  refine ⟨fun h ↦ by simpa using h.vertexSet, fun h ↦ ⟨?_, fun e x y ⟨hl, hx, hy⟩ => ?_⟩⟩
  · refine G.Dup.induce_induce.trans (induce_eq_induce_iff.mpr ?_)
    simp only [vertexDelete_vertexSet, inf_eq_inter, vertexSet_def]
    rw [inter_assoc, ← diff_eq_compl_inter, ← diff_eq_compl_inter, inter_eq_left.mpr h]
  simp [hl, (h ⟨hl.left_mem, hx⟩).2, (h ⟨hl.right_mem, hy⟩).2]

lemma vertexDelete_anti_right (hXY : X ⊆ Y) : G - Y ≤l G - X := by
  rw [vertexDelete_anti_right_iff]
  exact diff_subset_diff_right hXY

lemma vertexDelete_eq_vertexDelete_iff (G : Graph α β) (X Y : Set α) :
    G - X = G - Y ↔ V(G) \ X = V(G) \ Y := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← vertexDelete_vertexSet, ← vertexDelete_vertexSet, h]
  apply Graph.ext
  · exact induce_eq_induce_iff.mpr (by simpa [← diff_eq_compl_inter, G.vertexSet_def])
  simp [Set.ext_iff] at h
  simp only [vertexDelete_isLink, and_congr_right_iff]
  exact fun e x y hl ↦ and_congr (h x hl.left_mem) (h y hl.right_mem)

@[simp]
lemma vertexDelete_isLabelSubgraph : G - X ≤l G where
  dup_induce := induce_eq_induce_iff.mpr <| by aesop
  isLink_of_isLink _ _ _ h := h.1

instance [G.Nodup] : Nodup (G - X) :=
  Nodup.of_isLabelSubgraph (vertexDelete_isLabelSubgraph)

lemma IsLink.mem_vertexDelete_iff [G.Nodup] {X : Set α} (hG : G.IsLink e x y) :
    e ∈ E(G - X) ↔ x ∉ X ∧ y ∉ X := by
  rw [vertexDelete_edgeSet, mem_setOf_eq]
  refine ⟨fun ⟨x, y, hl, hx, hy⟩ ↦ ?_, fun ⟨hx, hy⟩ ↦ ⟨x, y, hG, hx, hy⟩⟩
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hG.eq_and_eq_or_eq_and_eq hl <;> simp [hx, hy]

lemma edgeRestrict_vertexDelete (G : Graph α β) (F : Set β) (D : Set α) :
    (G ↾ F) - D = (G - D) ↾ F := by
  refine Graph.ext rfl fun e x y ↦ ?_
  simp only [vertexDelete_isLink, edgeRestrict_isLink]
  tauto

-- @[simp]
-- lemma induce_vertexDelete (G : Graph α β) (X D : Set α) : G[X] - D = G[X \ D] :=
--   Graph.ext (by ext; simp +contextual [iff_def]) <| by
--   simp only [vertexDelete_isLink_iff, induce_isLink_iff, mem_diff]
--   tauto

lemma vertexDelete_vertexDelete (G : Graph α β) (X Y : Set α) : (G - X) - Y = G - (X ∪ Y) :=
  Graph.ext (by rw [union_comm]; ext; simp +contextual) <| by simp +contextual [iff_def]

lemma vertexDelete_vertexDelete_comm (G : Graph α β) (X Y : Set α) : (G - X) - Y = (G - Y) - X := by
  rw [vertexDelete_vertexDelete, vertexDelete_vertexDelete, union_comm]

-- @[simp]
-- lemma le_vertexDelete_iff : H ≤ G - X ↔ H ≤ G ∧ Disjoint V(H) X := by
--   simp only [vertexDelete_def]
--   exact fun h _ ↦ vertexSet_mono h

lemma IsClosedSubgraph.of_edgeDelete_iff (hclF : H ≤c G ＼ F) : H ≤c G ↔ E(G) ∩ F ⊆ E(G - V(H)) := by
  rw [vertexDelete_edgeSet]
  refine ⟨fun hcl f hf ↦ ?_, fun hF ↦ ⟨hclF.le.trans edgeDelete_le, ?_⟩⟩
  · by_contra! hfH
    simp only [mem_setOf_eq, not_exists, not_and, not_not] at hfH
    refine (hclF.edgeSet ?_).2 hf.2
    obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet hf.1
    obtain hx | hy := or_iff_not_imp_left.mpr <| hfH x y hxy
    · exact hcl.closed ⟨_, hxy⟩ hx
    · exact hcl.closed ⟨_, hxy.symm⟩ hy
  · rintro e x he hxH
    have : ∀ y, G.Dup x y → y ∈ V(H) :=
      fun y h ↦ dup_right_mem (dup_of_le_of_mem hclF.le hxH <| edgeDelete_isSpanningSubgraph.dup h)
    have heF : e ∉ F := fun heF => by
      obtain ⟨u, v, heuv, hunH, hvnH⟩ := hF ⟨he.edge_mem, heF⟩
      obtain hxu | hxv := he.dup_or_dup_of_isLink heuv
      · exact hunH (this u hxu)
      · exact hvnH (this v hxv)
    exact hclF.closed (by simp [he, heF]) hxH

end Graph
