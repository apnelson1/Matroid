import Matroid.Graph.Subgraph
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Finite.Basic

variable {α β : Type*} {x y z u v w : α} {e f : β} {G H : Graph α β} {F F₁ F₂ : Set β} {X Y : Set α}

open Set Function

open scoped Sym2

namespace Graph

/-- Map `G : Graph α β` to a `Graph α' β` with the same edge set
by applying a function `f : α → α'` to each vertex.
Edges between identified vertices become loops. -/
@[simps]
def vertexMap {α' : Type*} (G : Graph α β) (f : α → α') : Graph α' β where
  vertexSet := f '' V(G)
  edgeSet := E(G)
  IsLink e x' y' := ∃ x y, G.IsLink e x y ∧ x' = f x ∧ y' = f y
  isLink_symm := by
    rintro e he - - ⟨x, y, h, rfl, rfl⟩
    exact ⟨y, x, h.symm, rfl, rfl⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro e - - - - ⟨x, y, hxy, rfl, rfl⟩ ⟨z, w, hzw, rfl, rfl⟩
    obtain rfl | rfl := hxy.left_eq_or_eq hzw <;> simp
  edge_mem_iff_exists_isLink e := by
    refine ⟨fun h ↦ ?_, ?_⟩
    · obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet h
      exact ⟨_, _, _, _, hxy, rfl, rfl⟩
    rintro ⟨-, -, x, y, h, rfl, rfl⟩
    exact h.edge_mem
  left_mem_of_isLink := by
    rintro e - - ⟨x, y, h, rfl, rfl⟩
    exact Set.mem_image_of_mem _ h.left_mem

/-- The graph with vertex set `V` and no edges -/
@[simps]
protected def noEdge (V : Set α) (β : Type*) : Graph α β where
  vertexSet := V
  edgeSet := ∅
  IsLink _ _ _ := False
  isLink_symm := by simp
  eq_or_eq_of_isLink_of_isLink := by simp
  edge_mem_iff_exists_isLink := by simp
  left_mem_of_isLink := by simp

lemma eq_empty_or_vertexSet_nonempty (G : Graph α β) : G = Graph.noEdge ∅ β ∨ V(G).Nonempty := by
  refine V(G).eq_empty_or_nonempty.elim (fun he ↦ .inl (Graph.ext he fun e x y ↦ ?_)) Or.inr
  simp only [noEdge_isLink, iff_false]
  exact fun h ↦ by simpa [he] using h.left_mem

@[simp]
lemma noEdge_le_iff {V : Set α} : Graph.noEdge V β ≤ G ↔ V ⊆ V(G) := by
  simp [le_iff]

@[simp]
lemma noEdge_not_inc {V : Set α} : ¬ (Graph.noEdge V β).Inc e x := by
  simp [Inc]

@[simp]
lemma noEdge_not_isLoopAt {V : Set α} : ¬ (Graph.noEdge V β).IsLoopAt e x := by
  simp [← isLink_self_iff]

@[simp]
lemma noEdge_not_isNonloopAt {V : Set α} : ¬ (Graph.noEdge V β).IsNonloopAt e x := by
  simp [IsNonloopAt]

@[simp]
lemma noEdge_not_adj {V : Set α} : ¬ (Graph.noEdge V β).Adj x y := by
  simp [Adj]

lemma edgeDelete_eq_noEdge (G : Graph α β) (hF : E(G) ⊆ F) : G ＼ F = Graph.noEdge V(G) β := by
  refine Graph.ext rfl fun e x y ↦ ?_
  simp only [edgeDelete_isLink, noEdge_isLink, iff_false, not_and, not_not]
  exact fun h ↦ hF h.edge_mem

lemma edgeSet_eq_empty_iff : E(G) = ∅ ↔ G = Graph.noEdge V(G) β := by
  refine ⟨fun h ↦ Graph.ext rfl ?_, fun h ↦ by rw [h, noEdge_edgeSet]⟩
  simp only [noEdge_isLink, iff_false]
  refine fun e x y he ↦ ?_
  have := h ▸ he.edge_mem
  simp at this


/-- A graph with a single edge `e` from `u` to `v` -/
@[simps]
protected def singleEdge (u v : α) (e : β) : Graph α β where
  vertexSet := {u,v}
  edgeSet := {e}
  IsLink e' x y := e' = e ∧ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))
  isLink_symm := by tauto
  eq_or_eq_of_isLink_of_isLink := by aesop
  edge_mem_iff_exists_isLink := by tauto
  left_mem_of_isLink := by tauto

lemma singleEdge_comm (u v : α) (e : β) : Graph.singleEdge u v e = Graph.singleEdge v u e := by
  ext <;> simp [or_comm]

lemma singleEdge_isLink_iff :
    (Graph.singleEdge u v e).IsLink f x y ↔ (f = e) ∧ s(x,y) = s(u,v) := by
  simp [Graph.singleEdge]

@[simp]
lemma singleEdge_inc_iff :
    (Graph.singleEdge u v e).Inc f x ↔ f = e ∧ (x = u ∨ x = v) := by
  simp only [Inc, singleEdge_isLink, exists_and_left, and_congr_right_iff]
  aesop

@[simp]
lemma singleEdge_adj_iff :
    (Graph.singleEdge u v e).Adj x y ↔ (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  simp [Adj]

@[simp] lemma singleEdge_le_iff : Graph.singleEdge u v e ≤ G ↔ G.IsLink e u v := by
  simp only [le_iff, singleEdge_vertexSet, Set.pair_subset_iff, singleEdge_isLink_iff, and_imp,
    Sym2.eq_iff]
  refine ⟨fun h ↦ h.2 rfl (.inl ⟨rfl, rfl⟩), fun h ↦ ⟨⟨h.left_mem, h.right_mem⟩, ?_⟩⟩
  rintro e x y rfl (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · assumption
  exact h.symm

/-- The union of two graphs `G` and `H`. If there is an edge `e` whose `G`-ends differ from
its `H`-ends, then `G` is favoured, so this is not commutative in general.

(If `G` and `H` are `Compatible`, this doesn't occur.)  -/
protected def union (G H : Graph α β) : Graph α β where
  vertexSet := V(G) ∪ V(H)
  edgeSet := E(G) ∪ E(H)
  IsLink e x y := G.IsLink e x y ∨ (e ∉ E(G) ∧ H.IsLink e x y)
  isLink_symm e he x y := by simp [G.isLink_comm (x := x), H.isLink_comm (x := x)]
  eq_or_eq_of_isLink_of_isLink := by
    rintro e x y v w (h | h) (h' | h')
    · exact h.left_eq_or_eq h'
    · exact False.elim <| h'.1 h.edge_mem
    · exact False.elim <| h.1 h'.edge_mem
    exact h.2.left_eq_or_eq h'.2
  edge_mem_iff_exists_isLink e := by
    refine ⟨?_, fun ⟨x, y, h⟩ ↦ h.elim (fun h' ↦ .inl h'.edge_mem) (fun h' ↦ .inr h'.2.edge_mem)⟩
    rw [← Set.union_diff_self]
    rintro (he | ⟨heH, heG⟩)
    · obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet he
      exact ⟨x, y, .inl h⟩
    obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet heH
    exact ⟨x, y, .inr ⟨heG, h⟩⟩
  left_mem_of_isLink := by
    rintro e x y (h | h)
    · exact .inl h.left_mem
    exact .inr h.2.left_mem

instance : Union (Graph α β) where union := Graph.union

@[simp]
lemma union_vertexSet (G H : Graph α β) : V(G ∪ H) = V(G) ∪ V(H) := rfl

@[simp]
lemma union_edgeSet (G H : Graph α β) : E(G ∪ H) = E(G) ∪ E(H) := rfl

lemma union_isLink_iff :
  (G ∪ H).IsLink e x y ↔ G.IsLink e x y ∨ (e ∉ E(G) ∧ H.IsLink e x y) := Iff.rfl

lemma union_inc_iff : (G ∪ H).Inc e x ↔ G.Inc e x ∨ (e ∉ E(G) ∧ H.Inc e x) := by
  simp_rw [Inc, union_isLink_iff]
  aesop

lemma union_isLoopAt_iff : (G ∪ H).IsLoopAt e x ↔ G.IsLoopAt e x ∨ (e ∉ E(G) ∧ H.IsLoopAt e x) := by
  simp_rw [← isLink_self_iff, union_isLink_iff]

lemma union_isNonloopAt_iff :
    (G ∪ H).IsNonloopAt e x ↔ G.IsNonloopAt e x ∨ (e ∉ E(G) ∧ H.IsNonloopAt e x) := by
  simp_rw [IsNonloopAt, union_isLink_iff]
  aesop

lemma union_le {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) : H₁ ∪ H₂ ≤ G := by
  suffices ∀ ⦃e : β⦄ ⦃x y : α⦄, H₁.IsLink e x y ∨ e ∉ E(H₁) ∧ H₂.IsLink e x y → G.IsLink e x y by
    simpa [le_iff, vertexSet_mono h₁, vertexSet_mono h₂, union_isLink_iff]
  rintro e x y (h | ⟨-, h⟩) <;>
  exact h.of_le <| by assumption

lemma isLink_or_isLink_of_union (h : (G ∪ H).IsLink e x y) : G.IsLink e x y ∨ H.IsLink e x y := by
  rw [union_isLink_iff] at h
  tauto

@[simp]
lemma left_le_union (G H : Graph α β) : G ≤ G ∪ H := by
  simp_rw [le_iff, union_isLink_iff]
  tauto

protected lemma union_assoc (G₁ G₂ G₃ : Graph α β) : (G₁ ∪ G₂) ∪ G₃ = G₁ ∪ (G₂ ∪ G₃) := by
  refine Graph.ext (Set.union_assoc ..) fun e x y ↦ ?_
  simp [union_isLink_iff]
  tauto

/-! ### Unions -/

/-- Two graphs are `Compatible` if the edges in their intersection agree on their ends -/
def Compatible (G H : Graph α β) : Prop := ∀ ⦃e⦄, e ∈ E(G) → e ∈ E(H) → G.IsLink e = H.IsLink e

lemma Compatible.symm (h : G.Compatible H) : H.Compatible G :=
  fun _ hH hG ↦ (h hG hH).symm

lemma compatible_comm : G.Compatible H ↔ H.Compatible G :=
  ⟨Compatible.symm, Compatible.symm⟩

/-- Two subgraphs of the same graph are compatible. -/
lemma compatible_of_le_le {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) : H₁.Compatible H₂ := by
  intro e he₁ he₂
  ext x y
  rw [← isLink_iff_isLink_of_le_of_mem h₁ he₁, ← isLink_iff_isLink_of_le_of_mem h₂ he₂]

lemma compatible_self (G : Graph α β) : G.Compatible G := by
  simp [Compatible]

lemma Compatible.union_isLink_iff (h : Compatible G H) :
    (G ∪ H).IsLink e x y ↔ G.IsLink e x y ∨ H.IsLink e x y := by
  by_cases heG : e ∈ E(G)
  · simp only [Graph.union_isLink_iff, heG, not_true_eq_false, false_and, or_false, iff_self_or]
    exact fun heH ↦ by rwa [h heG heH.edge_mem]
  simp [Graph.union_isLink_iff, heG]

@[simp]
lemma singleEdge_compatible_iff :
    (Graph.singleEdge x y e).Compatible G ↔ (e ∈ E(G) → G.IsLink e x y) := by
  refine ⟨fun h he ↦ by simp [← h (by simp) he, singleEdge_isLink_iff] , fun h f hf hfE ↦ ?_⟩
  obtain rfl : f = e := by simpa using hf
  ext u v
  rw [(h hfE).isLink_iff, Graph.singleEdge_isLink_iff, and_iff_right rfl, Sym2.eq_iff]
  tauto

lemma Compatible.union_inc_iff (h : G.Compatible H) : (G ∪ H).Inc e x ↔ G.Inc e x ∨ H.Inc e x := by
  simp_rw [Inc, h.union_isLink_iff]
  aesop

lemma Compatible.union_isLoopAt_iff (h : G.Compatible H) :
    (G ∪ H).IsLoopAt e x ↔ G.IsLoopAt e x ∨ H.IsLoopAt e x := by
  simp_rw [← isLink_self_iff, h.union_isLink_iff]

lemma Compatible.union_isNonloopAt_iff (h : G.Compatible H) :
    (G ∪ H).IsNonloopAt e x ↔ G.IsNonloopAt e x ∨ H.IsNonloopAt e x := by
  simp_rw [IsNonloopAt, h.union_isLink_iff]
  aesop

lemma Compatible.union_adj_iff (h : G.Compatible H) : (G ∪ H).Adj x y ↔ G.Adj x y ∨ H.Adj x y := by
  simp [Adj, h.union_isLink_iff, exists_or]

lemma Compatible.union_comm (h : Compatible G H) : G ∪ H = H ∪ G :=
  Graph.ext (Set.union_comm ..)
    fun _ _ _ ↦ by rw [h.union_isLink_iff, h.symm.union_isLink_iff, or_comm]

lemma Compatible.right_le_union (h : Compatible G H) : H ≤ G ∪ H := by
  simp [h.union_comm]

lemma Compatible.union_le_iff {H₁ H₂ : Graph α β} (h_compat : H₁.Compatible H₂) :
    H₁ ∪ H₂ ≤ G ↔ H₁ ≤ G ∧ H₂ ≤ G :=
  ⟨fun h ↦ ⟨(left_le_union ..).trans h, (h_compat.right_le_union ..).trans h⟩,
    fun h ↦ union_le h.1 h.2⟩

lemma Compatible.of_disjoint_edgeSet (h : Disjoint E(G) E(H)) : Compatible G H :=
  fun _ heG heH ↦ False.elim <| h.not_mem_of_mem_left heG heH

@[simp]
lemma compatible_edgeDelete_right : G.Compatible (H ＼ E(G)) :=
  Compatible.of_disjoint_edgeSet disjoint_sdiff_right

lemma union_eq_union_edgeDelete (G H : Graph α β) : G ∪ H = G ∪ (H ＼ E(G)) :=
  Graph.ext rfl fun e x y ↦ by rw [union_isLink_iff,
    (Compatible.of_disjoint_edgeSet disjoint_sdiff_right).union_isLink_iff,
    edgeDelete_isLink, and_comm]

lemma Compatible.mono_left {G₀ : Graph α β} (h : Compatible G H) (hG₀ : G₀ ≤ G) :
    Compatible G₀ H := by
  intro e heG heH
  ext x y
  rw [← isLink_iff_isLink_of_le_of_mem hG₀ heG, h (edgeSet_mono hG₀ heG) heH]

lemma Compatible.mono_right {H₀ : Graph α β} (h : Compatible G H) (hH₀ : H₀ ≤ H) :
    Compatible G H₀ :=
  (h.symm.mono_left hH₀).symm

lemma Compatible.mono {G₀ H₀ : Graph α β} (h : G.Compatible H) (hG : G₀ ≤ G) (hH : H₀ ≤ H) :
    G₀.Compatible H₀ :=
  (h.mono_left hG).mono_right hH

lemma union_eq_self_of_le_left (hle : G ≤ H) : G ∪ H = H :=
  (union_le hle rfl.le).antisymm (Compatible.right_le_union (H.compatible_self.mono_left hle))

lemma union_eq_self_of_le_right (hle : G ≤ H) : H ∪ G = H :=
  (union_le rfl.le hle).antisymm <| left_le_union ..

lemma Compatible.induce_left (h : Compatible G H) (X : Set α) : G[X].Compatible H := by
  intro e heG heH
  ext x y
  obtain ⟨u, v, heuv : G.IsLink e u v, hu, hv⟩ := heG
  simp only [induce_isLink_iff, ← h heuv.edge_mem heH, and_iff_left_iff_imp]
  intro h
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h.eq_and_eq_or_eq_and_eq heuv <;> simp_all

lemma Compatible.induce_right (h : Compatible G H) (X : Set α) :
    G.Compatible H[X] :=
  (h.symm.induce_left X).symm

lemma Compatible.induce (h : Compatible G H) {X : Set α} :
    G[X].Compatible H[X] :=
  (h.induce_left X).induce_right X

@[simp]
lemma Compatible.induce_induce : G[X].Compatible G[Y] :=
  Compatible.induce_left (Compatible.induce_right G.compatible_self _) _

lemma Compatible.induce_union (h : G.Compatible H) (X : Set α) : (G ∪ H)[X] = G[X] ∪ H[X] := by
  refine Graph.ext (by simp) fun e x y ↦ ?_
  simp only [induce_isLink_iff, h.union_isLink_iff, h.induce.union_isLink_iff]
  tauto

lemma induce_union (G : Graph α β) (X Y : Set α) (hX : ∀ x ∈ X, ∀ y ∈ Y, ¬ G.Adj x y) :
    G [X ∪ Y] = G [X] ∪ G [Y] := by
  refine Graph.ext rfl fun e x y ↦ ?_
  simp only [induce_isLink_iff, mem_union, Compatible.induce_induce.union_isLink_iff]
  by_cases hxy : G.IsLink e x y
  · by_cases hx : x ∈ X
    · simp [hx, show y ∉ Y from fun hy ↦ hX x hx y hy hxy.adj]
    by_cases hy : y ∈ X
    · simp [hy, show x ∉ Y from fun hx ↦ hX _ hy _ hx hxy.symm.adj, hxy]
    simp [hx, hy]
  simp [hxy]

lemma Compatible.vertexDelete_union (h : G.Compatible H) (X : Set α) :
    (G ∪ H) - X = (G - X) ∪ (H - X) := by
  refine Graph.ext union_diff_distrib fun e x y ↦ ?_
  simp only [vertexDelete_isLink_iff, union_vertexSet, mem_union]
  rw [vertexDelete_def, vertexDelete_def, ((h.induce_left _).induce_right _).union_isLink_iff,
    h.union_isLink_iff]
  simp only [induce_isLink_iff, mem_diff]
  by_cases hG : G.IsLink e x y
  · simp +contextual [hG, hG.left_mem, hG.right_mem]
  by_cases hH : H.IsLink e x y
  · simp +contextual [hH, hH.left_mem, hH.right_mem]
  simp [hG, hH]

lemma edgeRestrict_union (G : Graph α β) (F₁ F₂ : Set β) : (G ↾ (F₁ ∪ F₂)) = G ↾ F₁ ∪ (G ↾ F₂) := by
  refine Graph.ext (by simp) fun e x y ↦ ?_
  rw [(G.compatible_self.mono (by simp) (by simp)).union_isLink_iff]
  simp only [edgeRestrict_isLink, mem_union]
  tauto

lemma edgeRestrict_union_edgeDelete (G : Graph α β) (F : Set β) : (G ↾ F) ∪ (G ＼ F) = G := by
  rw [edgeDelete_eq_edgeRestrict, ← edgeRestrict_union, ← edgeRestrict_inter_edgeSet]
  simp only [union_diff_self, edgeRestrict_inter_edgeSet, edgeRestrict_union, edgeRestrict_self]
  exact union_eq_self_of_le_left (by simp)

lemma edgeDelete_union_edgeRestrict (G : Graph α β) (F : Set β) : (G ＼ F) ∪ (G ↾ F) = G := by
  convert G.edgeRestrict_union_edgeDelete F using 1
  rw [Compatible.union_comm]
  apply G.compatible_of_le_le (by simp) (by simp)

lemma induce_union_edgeDelete (G : Graph α β) (hX : X ⊆ V(G)) : G[X] ∪ (G ＼ E(G[X])) = G := by
  rw [← union_eq_union_edgeDelete, union_eq_self_of_le_left (induce_le hX)]

lemma edgeDelete_union_induce (G : Graph α β) (hX : X ⊆ V(G)) : (G ＼ E(G[X])) ∪ G[X] = G := by
  rw [(Compatible.of_disjoint_edgeSet _).union_comm, induce_union_edgeDelete _ hX]
  simp [disjoint_sdiff_left]

/-! ### Adding one edge -/

/-- Add a new edge `e` between vertices `a` and `b`. If `e` is already in the graph,
its ends change to `a` and `b`. -/
@[simps! edgeSet vertexSet]
protected def addEdge (G : Graph α β) (e : β) (a b : α) : Graph α β :=
  Graph.singleEdge a b e ∪ G

lemma addEdge_isLink (G : Graph α β) (e : β) (a b : α) : (G.addEdge e a b).IsLink e a b := by
  simp [Graph.addEdge, union_isLink_iff]

lemma addEdge_isLink_of_ne (hf : G.IsLink f x y) (hne : f ≠ e) (a b : α) :
    (G.addEdge e a b).IsLink f x y := by
  simpa [Graph.addEdge, union_isLink_iff, hne]

lemma addEdge_isLink_iff {a b : α} (he : e ∉ E(G)) :
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

lemma addEdge_le (hle : H ≤ G) (he : G.IsLink e x y) : H.addEdge e x y ≤ G where
  vertex_subset := union_subset (by simp [pair_subset_iff, he.left_mem, he.right_mem])
    (vertexSet_mono hle)
  isLink_of_isLink f z w hH := by
    simp only [Graph.addEdge, union_isLink_iff, singleEdge_isLink, singleEdge_edgeSet,
      mem_singleton_iff] at hH
    obtain (⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩) | ⟨-, hzw⟩ := hH
    · exact he
    · exact he.symm
    exact hzw.of_le hle

lemma IsLink.deleteEdge_addEdge (h : G.IsLink e x y) : (G ＼ {e}).addEdge e x y = G :=
  ext_of_le_le (addEdge_le (by simp) h) le_rfl (by simp [pair_subset_iff, h.left_mem, h.right_mem])
    <| by simp [h.edge_mem]

/-! ### Disjointness -/

/-- Two graphs are disjoint if their edge sets and vertex sets are disjoint -/
@[mk_iff]
protected structure Disjoint (G H : Graph α β) : Prop where
  vertex : Disjoint V(G) V(H)
  edge : Disjoint E(G) E(H)

lemma Disjoint.symm (h : G.Disjoint H) : H.Disjoint G :=
  ⟨h.1.symm, h.2.symm⟩

lemma Compatible.disjoint_of_vertexSet_disjoint (h : G.Compatible H) (hV : Disjoint V(G) V(H)) :
    G.Disjoint H := by
  refine ⟨hV, disjoint_left.2 fun e he he' ↦ ?_⟩
  obtain ⟨x, y, hexy⟩ := exists_isLink_of_mem_edgeSet he
  exact hV.not_mem_of_mem_left hexy.left_mem (h he he' ▸ hexy).left_mem

lemma Disjoint.compatible (h : G.Disjoint H) : G.Compatible H :=
  Compatible.of_disjoint_edgeSet h.edge

/-- useful with `Pairwise` and `Set.Pairwise`.-/
@[simp]
lemma disjoint_le_compatible : Graph.Disjoint (α := α) (β := β) ≤ Graph.Compatible := by
  refine fun _ _ ↦ Disjoint.compatible

/-! ### Families of Graphs -/

variable {ι : Type*} {H : ι → Graph α β} {s : Set (Graph α β)}

/-- An indexed family of graphs is `UCompatible` if no two of them disagree on incidences,
or equivalently if there is a common supergraph of all the graphs in the family.
TODO : Change this to `Pairwise (Compatible on H)`.
  -/
def UCompatible (H : ι → Graph α β) : Prop :=
  ∀ ⦃i j e x y⦄, (H i).IsLink e x y → e ∈ E(H j) → (H j).IsLink e x y

lemma uCompatible_iff_pairwise_compatible : UCompatible H ↔ Pairwise (Compatible on H) := by
  refine ⟨fun h i j hne e hei hej ↦ ?_, fun h i j e x y hei hej ↦ ?_⟩
  · ext x y
    exact ⟨fun h' ↦ h h' hej, fun h' ↦ h h' hei⟩
  obtain rfl | hne := eq_or_ne i j
  · assumption
  rwa [(h hne).symm hej hei.edge_mem]

lemma UCompatible.of_forall_subgraph (h : ∀ i, H i ≤ G) : UCompatible H :=
  fun i j _ _ _ hi hj ↦ (hi.of_le (h i)).of_le_of_mem (h j) hj

lemma Compatible.UCompatible_cond {H : Graph α β} (h : G.Compatible H) :
    UCompatible (fun b : Bool ↦ bif b then G else H) := by
  rintro (rfl | rfl) (rfl | rfl) e x y
  · simp +contextual
  · simp only [cond_false, cond_true]
    exact fun he heG ↦ by rwa [h heG he.edge_mem]
  · simp only [cond_false, cond_true]
    exact fun he heH ↦ by rwa [h.symm heH he.edge_mem]
  simp +contextual

lemma UCompatible.of_disjoint_edgeSet (h : Pairwise (Disjoint on (fun i ↦ E(H i)))) :
    UCompatible H := by
  refine fun i j e x y hi hj ↦ ?_
  obtain rfl | hne := eq_or_ne i j
  · assumption
  exact False.elim <| (disjoint_left.1 <| h hne) hi.edge_mem hj

lemma UCompatible.of_disjoint (h : Pairwise (Graph.Disjoint on H)) : UCompatible H :=
  UCompatible.of_disjoint_edgeSet <| h.mono fun _ _ ↦ Graph.Disjoint.edge

/-- The union of a `UCompatible` collection of graphs. -/
@[simps]
protected def UCompatible.iUnion (H : ι → Graph α β) (hH : UCompatible H) : Graph α β where
  vertexSet := ⋃ i, V(H i)
  edgeSet := ⋃ i, E(H i)
  IsLink e x y := ∃ i, (H i).IsLink e x y
  isLink_symm := by
    simp only [mem_iUnion, Symmetric, forall_exists_index]
    rintro e i hei x y j hi
    exact ⟨j, hi.symm⟩
  eq_or_eq_of_isLink_of_isLink :=
    fun e x y v w ⟨i, hexy⟩ ⟨j, hevw⟩ ↦ (hH hexy hevw.edge_mem).left_eq_or_eq hevw
  edge_mem_iff_exists_isLink := by
    simp_rw [mem_iUnion]
    refine fun e ↦ ⟨fun ⟨i, hei⟩ ↦ ?_, fun ⟨x, y, i, h⟩ ↦ ⟨i, h.edge_mem⟩⟩
    obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet hei
    exact ⟨_, _, _, h⟩
  left_mem_of_isLink := fun e x y ⟨i, h⟩ ↦ mem_iUnion.2 ⟨i, h.left_mem⟩

lemma UCompatible.le_iUnion (hH : UCompatible H) (i : ι) : H i ≤ hH.iUnion H :=
  ⟨subset_iUnion (fun i ↦ V(H i)) i , by aesop⟩

@[simp]
lemma UCompatible.iUnion_le_iff (hH : UCompatible H) : hH.iUnion H ≤ G ↔ ∀ i, H i ≤ G := by
  refine ⟨fun h i ↦ (hH.le_iUnion i).trans h, fun h ↦ ⟨?_, fun e x y ⟨i, hexy⟩ ↦ hexy.of_le (h i)⟩⟩
  simpa using fun i ↦ vertexSet_mono (h i)

lemma Compatible.union_eq_iUnion {H : Graph α β} (h : G.Compatible H) :
    G ∪ H = h.UCompatible_cond.iUnion _ := by
  refine Graph.ext ?_ fun e x y ↦ ?_
  · simp only [union_vertexSet, UCompatible.iUnion_vertexSet, Bool.apply_cond]
    rw [← Set.union_eq_iUnion]
  simp [h.union_isLink_iff, or_comm]

@[simps!]
protected def sUnion (s : Set (Graph α β)) (hs : s.Pairwise Compatible) : Graph α β :=
  UCompatible.iUnion (fun G : s ↦ G.1) <|
    uCompatible_iff_pairwise_compatible.2 <| (pairwise_subtype_iff_pairwise_set s Compatible).2 hs

protected lemma le_sUnion (hs : s.Pairwise Compatible) (hG : G ∈ s) : G ≤ Graph.sUnion s hs :=
  UCompatible.le_iUnion (H := Subtype.val) (i := ⟨G, hG⟩) _

@[simp]
protected lemma sUnion_le_iff (hs : s.Pairwise Compatible) :
    Graph.sUnion s hs ≤ G ↔ ∀ H ∈ s, H ≤ G := by
  convert UCompatible.iUnion_le_iff (H := fun i : s ↦ i.1) (G := G) _
  simp
