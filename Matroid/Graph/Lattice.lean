import Matroid.Graph.Subgraph
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Finite.Basic

variable {α β : Type*} {x y z u v w : α} {e f : β} {G G₁ G₂ H H₁ H₂ : Graph α β} {F F₁ F₂ : Set β}
  {X Y : Set α}

open Set Function

/- For Mathlib -/

lemma Pairwise.of_refl {ι α : Type*} {r : α → α → Prop} [IsRefl α r] {f : ι → α}
    (h : Pairwise (r on f)) (i j : ι) : r (f i) (f j) :=
  (eq_or_ne i j).elim (fun hij ↦ hij ▸ refl (f i)) fun hne ↦ h hne

open scoped Sym2

namespace Graph


/-! ### Disjointness -/

/-- Two graphs are disjoint if their edge sets and vertex sets are disjoint -/
@[mk_iff]
protected structure Disjoint (G H : Graph α β) : Prop where
  vertex : Disjoint V(G) V(H)
  edge : Disjoint E(G) E(H)

lemma Disjoint.symm (h : G.Disjoint H) : H.Disjoint G :=
  ⟨h.1.symm, h.2.symm⟩

protected lemma disjoint_iff_of_le_le (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) :
    Graph.Disjoint H₁ H₂ ↔ Disjoint V(H₁) V(H₂) := by
  refine ⟨Disjoint.vertex, fun h ↦ ⟨h, disjoint_left.2 fun e he₁ he₂ ↦ ?_⟩⟩
  obtain ⟨x, y, he₁⟩ := exists_isLink_of_mem_edgeSet he₁
  exact h.not_mem_of_mem_left he₁.left_mem ((he₁.of_le h₁).of_le_of_mem h₂ he₂).left_mem

/-! ### Compatibility -/

/-- Two graphs are `Compatible` if the edges in their intersection agree on their ends -/
def Compatible (G H : Graph α β) : Prop := EqOn G.IsLink H.IsLink (E(G) ∩ E(H))

lemma Compatible.isLink_eq (h : G.Compatible H) (heG : e ∈ E(G)) (heH : e ∈ E(H)) :
    G.IsLink e = H.IsLink e :=
  h ⟨heG, heH⟩

lemma Compatible.symm (h : G.Compatible H) : H.Compatible G := by
  rwa [Compatible, inter_comm, eqOn_comm]

instance : IsSymm (Graph α β) Compatible where
  symm _ _ := Compatible.symm

@[simp]
lemma compatible_symmetric : Symmetric (@Compatible α β) :=
  fun _ _ ↦ Compatible.symm

lemma compatible_comm : G.Compatible H ↔ H.Compatible G :=
  ⟨Compatible.symm, Compatible.symm⟩

/-- Two subgraphs of the same graph are compatible. -/
lemma compatible_of_le_le {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) : H₁.Compatible H₂ :=
  ((isLink_eqOn_of_le h₁).mono inter_subset_left).trans <|
    (isLink_eqOn_of_le h₂).symm.mono inter_subset_right

lemma IsLink.of_compatible (h : G.IsLink e x y) (hGH : G.Compatible H) (heH : e ∈ E(H)) :
    H.IsLink e x y := by
  rwa [← hGH ⟨h.edge_mem, heH⟩]

@[simp]
lemma compatible_self (G : Graph α β) : G.Compatible G :=
  eqOn_refl ..

instance : IsRefl (Graph α β) Compatible where
  refl G := G.compatible_self

lemma Compatible.of_disjoint_edgeSet (h : Disjoint E(G) E(H)) : Compatible G H := by
  simp [Compatible, h.inter_eq]

@[simp]
lemma compatible_edgeDelete_right : G.Compatible (H ＼ E(G)) :=
  Compatible.of_disjoint_edgeSet disjoint_sdiff_right

/-- Used to simplify the definition of the union of a pair. -/
@[simp]
lemma pairwise_compatible_edgeDelete : ({G, H ＼ E(G)} : Set (Graph α β)).Pairwise Compatible := by
  simp [pairwise_iff_of_refl, compatible_edgeDelete_right.symm]

lemma Compatible.mono_left {G₀ : Graph α β} (h : Compatible G H) (hG₀ : G₀ ≤ G) :
    Compatible G₀ H :=
  ((isLink_eqOn_of_le hG₀).mono inter_subset_left).trans
    (h.mono (inter_subset_inter_left _ (edgeSet_mono hG₀)))

lemma Compatible.mono_right {H₀ : Graph α β} (h : Compatible G H) (hH₀ : H₀ ≤ H) :
    Compatible G H₀ :=
  (h.symm.mono_left hH₀).symm

lemma Compatible.mono {G₀ H₀ : Graph α β} (h : G.Compatible H) (hG : G₀ ≤ G) (hH : H₀ ≤ H) :
    G₀.Compatible H₀ :=
  (h.mono_left hG).mono_right hH

lemma Compatible.induce_left (h : Compatible G H) (X : Set α) : G[X].Compatible H := by
  intro e ⟨heG, heX⟩
  ext x y
  obtain ⟨u, v, heuv : G.IsLink e u v, hu, hv⟩ := heG
  simp only [induce_isLink_iff, ← h ⟨heuv.edge_mem, heX⟩, and_iff_left_iff_imp]
  intro h
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h.eq_and_eq_or_eq_and_eq heuv <;> simp_all

lemma Compatible.induce_right (h : Compatible G H) (X : Set α) :
    G.Compatible H[X] :=
  (h.symm.induce_left X).symm

lemma Compatible.induce (h : Compatible G H) {X : Set α} : G[X].Compatible H[X] :=
  (h.induce_left X).induce_right X

lemma Compatible.vertexDelete (h : Compatible G H) {X : Set α} : (G - X).Compatible (H - X) :=
  h.mono vertexDelete_le vertexDelete_le

lemma Compatible.edgeDelete (h : Compatible G H) {F : Set β} : (G ＼ F).Compatible (H ＼ F) :=
  h.mono edgeDelete_le edgeDelete_le

lemma Compatible.edgeRestrict (h : Compatible G H) {F : Set β} : (G ↾ F).Compatible (H ↾ F) :=
  h.mono edgeRestrict_le edgeRestrict_le

@[simp]
lemma Compatible.induce_induce : G[X].Compatible G[Y] :=
  Compatible.induce_left (Compatible.induce_right G.compatible_self _) _

lemma Compatible.disjoint_of_vertexSet_disjoint (h : G.Compatible H) (hV : Disjoint V(G) V(H)) :
    G.Disjoint H := by
  refine ⟨hV, disjoint_left.2 fun e he he' ↦ ?_⟩
  obtain ⟨x, y, hexy⟩ := exists_isLink_of_mem_edgeSet he
  exact hV.not_mem_of_mem_left hexy.left_mem (h ⟨he, he'⟩ ▸ hexy).left_mem

lemma Disjoint.compatible (h : G.Disjoint H) : G.Compatible H :=
  Compatible.of_disjoint_edgeSet h.edge

/-- useful with `Pairwise` and `Set.Pairwise`.-/
@[simp]
lemma disjoint_le_compatible : @Graph.Disjoint α β ≤ Graph.Compatible := by
  refine fun _ _ ↦ Disjoint.compatible

/-! ### Indexed unions -/

variable {ι : Type*} {s : Set (Graph α β)}

/-- The union of an indexed family of pairwise compatible graphs. -/
@[simps]
protected def iUnion (G : ι → Graph α β) (hG : Pairwise (Graph.Compatible on G)) : Graph α β where
  vertexSet := ⋃ i, V(G i)
  edgeSet := ⋃ i, E(G i)
  IsLink e x y := ∃ i, (G i).IsLink e x y
  isLink_symm := by simp +contextual [Symmetric, isLink_comm]
  eq_or_eq_of_isLink_of_isLink :=
    fun e x y v w ⟨i, hi⟩ ⟨j, hj⟩ ↦ (hi.of_compatible (hG.of_refl i j) hj.edge_mem).left_eq_or_eq hj
  edge_mem_iff_exists_isLink := by
    simp only [mem_iUnion, edge_mem_iff_exists_isLink]
    aesop
  left_mem_of_isLink := fun e x y ⟨i, hi⟩ ↦ mem_iUnion.2 ⟨i, hi.left_mem⟩

@[simp]
protected lemma le_iUnion {G : ι → Graph α β}  (hG : Pairwise (Graph.Compatible on G)) (i : ι) :
    G i ≤ Graph.iUnion G hG where
  vertex_subset := subset_iUnion (fun i ↦ V(G i)) i
  isLink_of_isLink := fun _ _ _ he ↦ ⟨i, he⟩

@[simp]
protected lemma iUnion_le_iff {G : ι → Graph α β} (hG : Pairwise (Graph.Compatible on G)) :
    Graph.iUnion G hG ≤ H ↔ ∀ i, G i ≤ H :=
  ⟨fun h i ↦ (Graph.le_iUnion hG i).trans h,
    fun h' ↦ ⟨by simp [fun i ↦ vertexSet_mono (h' i)], fun e x y ⟨i, h⟩ ↦ h.of_le (h' i)⟩⟩

@[simp]
lemma iUnion_inc_iff {G : ι → Graph α β} (hG : Pairwise (Graph.Compatible on G)) :
    (Graph.iUnion G hG).Inc e x ↔ ∃ i, (G i).Inc e x := by
  simpa [Inc] using exists_comm

@[simp]
lemma iUnion_isLoopAt_iff {G : ι → Graph α β} (hG : Pairwise (Graph.Compatible on G)) :
    (Graph.iUnion G hG).IsLoopAt e x ↔ ∃ i, (G i).IsLoopAt e x := by
  simp [← isLink_self_iff]

@[simp]
lemma iUnion_isNonloopAt_iff {G : ι → Graph α β} (hG : Pairwise (Graph.Compatible on G)) :
    (Graph.iUnion G hG).IsNonloopAt e x ↔ ∃ i, (G i).IsNonloopAt e x := by
  simp only [IsNonloopAt, ne_eq, iUnion_isLink]
  aesop

@[simp]
lemma induce_iUnion [Nonempty ι] {G : ι → Graph α β} (hG : Pairwise (Graph.Compatible on G))
    (X : Set α) :
    (Graph.iUnion G hG)[X] = .iUnion (fun i ↦ (G i)[X]) (fun _ _ hij ↦ (hG hij).induce ..) :=
  Graph.ext (by simp [iUnion_const]) (by simp)

@[simp]
lemma Compatible.vertexDelete_iUnion {G : ι → Graph α β} (hG : Pairwise (Graph.Compatible on G))
    (X : Set α) :
    (Graph.iUnion G hG) - X = .iUnion (fun i ↦ (G i) - X) (fun _ _ hij ↦ (hG hij).vertexDelete) :=
  Graph.ext (by simp [iUnion_diff]) (by simp)

@[simp]
lemma Compatible.edgeDelete_iUnion {G : ι → Graph α β} (hG : Pairwise (Graph.Compatible on G))
    (F : Set β) :
    (Graph.iUnion G hG) ＼ F = .iUnion (fun i ↦ (G i) ＼ F) (fun _ _ hij ↦ (hG hij).edgeDelete) := by
  ext <;> simp

@[simp]
lemma Compatible.edgeRestrict_iUnion {G : ι → Graph α β} (hG : Pairwise (Graph.Compatible on G))
    (F : Set β) : (Graph.iUnion G hG) ↾ F =
    .iUnion (fun i ↦ (G i) ↾ F) (fun _ _ hij ↦ (hG hij).edgeRestrict) := by
  ext <;> simp

/-! ### Set unions -/

/-- The union of a set of pairwise compatible graphs. -/
@[simps!]
protected def sUnion (s : Set (Graph α β)) (hs : s.Pairwise Compatible) : Graph α β :=
  .iUnion (fun G : s ↦ G.1) <| (pairwise_subtype_iff_pairwise_set s Compatible).2 hs

@[simp]
protected lemma le_sUnion (hs : s.Pairwise Graph.Compatible) (hG : G ∈ s) :
    G ≤ Graph.sUnion s hs := by
  convert Graph.le_iUnion (ι := s) _ ⟨G, hG⟩
  rfl

@[simp]
protected lemma sUnion_le_iff (hs : s.Pairwise Graph.Compatible) :
    Graph.sUnion s hs ≤ H ↔ ∀ G ∈ s, G ≤ H := by
  simp [Graph.sUnion]

@[simp]
lemma sUnion_inc_iff (hs : s.Pairwise Graph.Compatible) :
    (Graph.sUnion s hs).Inc e x ↔ ∃ G ∈ s, G.Inc e x := by
  simp [Graph.sUnion]

@[simp]
lemma sUnion_isLoopAt_iff (hs : s.Pairwise Graph.Compatible) :
    (Graph.sUnion s hs).IsLoopAt e x ↔ ∃ G ∈ s, G.IsLoopAt e x := by
  simp [← isLink_self_iff]

@[simp]
lemma sUnion_isNonloopAt_iff (hs : s.Pairwise Graph.Compatible) :
    (Graph.sUnion s hs).IsNonloopAt e x ↔ ∃ G ∈ s, G.IsNonloopAt e x := by
  simp [Graph.sUnion]

@[simp]
protected lemma sUnion_singleton (G : Graph α β) : Graph.sUnion {G} (by simp) = G := by
  ext <;> simp

/-! ### Unions of pairs -/

/-- The union of two graphs `G` and `H`. If there is an edge `e` whose `G`-ends differ from
its `H`-ends, then `G` is favoured, so this is not commutative in general.
If `G` and `H` are `Compatible`, this doesn't occur.
We define this in terms of `sUnion` and `Graph.copy` so the vertex and edge sets are
definitionally unions. -/
protected def union (G H : Graph α β) := Graph.copy (V := V(G) ∪ V(H)) (E := E(G) ∪ E(H))
  (Graph.sUnion {G, H ＼ E(G)} (by simp)) (by simp) (by simp) (fun _ _ _ ↦ Iff.rfl)

instance : Union (Graph α β) where union := Graph.union

@[simp]
lemma union_vertexSet (G H : Graph α β) : V(G ∪ H) = V(G) ∪ V(H) := rfl

@[simp]
lemma union_edgeSet (G H : Graph α β) : E(G ∪ H) = E(G) ∪ E(H) := rfl

lemma union_eq_sUnion (G H : Graph α β) : G ∪ H = Graph.sUnion {G, H ＼ E(G)} (by simp) := by
  simp_rw [Union.union, Graph.union, Graph.copy]
  ext <;> simp

lemma union_isLink_iff :
    (G ∪ H).IsLink e x y ↔ G.IsLink e x y ∨ (H.IsLink e x y ∧ e ∉ E(G)) := by
  simp [union_eq_sUnion]

lemma union_inc_iff : (G ∪ H).Inc e x ↔ G.Inc e x ∨ (H.Inc e x ∧ e ∉ E(G)) := by
  simp [union_eq_sUnion]

lemma union_isLoopAt_iff : (G ∪ H).IsLoopAt e x ↔ G.IsLoopAt e x ∨ (H.IsLoopAt e x ∧ e ∉ E(G)) := by
  simp [union_eq_sUnion]

lemma union_isNonloopAt_iff :
    (G ∪ H).IsNonloopAt e x ↔ G.IsNonloopAt e x ∨ (H.IsNonloopAt e x ∧ e ∉ E(G)) := by
  simp only [IsNonloopAt, ne_eq, union_isLink_iff]
  aesop

lemma union_eq_union_edgeDelete (G H : Graph α β) : G ∪ H = G ∪ (H ＼ E(G)) := by
  simp [union_eq_sUnion, union_eq_sUnion]

@[simp]
protected lemma left_le_union (G H : Graph α β) : G ≤ G ∪ H := by
  simp_rw [le_iff, union_isLink_iff]
  tauto

protected lemma union_le {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) : H₁ ∪ H₂ ≤ G := by
  simp [union_eq_sUnion, h₁, edgeDelete_le.trans h₂]

@[simp]
protected lemma union_self (G : Graph α β) : G ∪ G = G :=
  (Graph.union_le le_rfl le_rfl).antisymm <| Graph.left_le_union ..

protected lemma union_assoc (G₁ G₂ G₃ : Graph α β) : (G₁ ∪ G₂) ∪ G₃ = G₁ ∪ (G₂ ∪ G₃) := by
  refine Graph.ext (Set.union_assoc ..) fun e x y ↦ ?_
  simp [union_isLink_iff]
  tauto

lemma isLink_or_isLink_of_union (h : (G ∪ H).IsLink e x y) : G.IsLink e x y ∨ H.IsLink e x y :=
  (union_isLink_iff.1 h).elim .inl fun h' ↦ .inr h'.1

lemma Compatible.union_isLink_iff (h : G.Compatible H) :
    (G ∪ H).IsLink e x y ↔ G.IsLink e x y ∨ H.IsLink e x y := by
  by_cases heG : e ∈ E(G)
  · simp only [Graph.union_isLink_iff, heG, not_true_eq_false, and_false, or_false, iff_self_or]
    exact fun he ↦ by rwa [h.isLink_eq heG he.edge_mem]
  simp [heG, Graph.union_isLink_iff]

lemma edgeRestrict_union (G : Graph α β) (F₁ F₂ : Set β) : (G ↾ (F₁ ∪ F₂)) = G ↾ F₁ ∪ (G ↾ F₂) := by
  refine Graph.ext (by simp) fun e x y ↦ ?_
  rw [(G.compatible_self.mono (by simp) (by simp)).union_isLink_iff]
  simp only [edgeRestrict_isLink, mem_union]
  tauto

lemma Compatible.union_eq_sUnion (h : G.Compatible H) :
    G ∪ H = Graph.sUnion {G, H} (by simp [Set.pairwise_iff_of_refl, h, h.symm]) :=
  Graph.ext (by simp) fun e x y ↦ by simp [h.union_isLink_iff]

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

lemma Compatible.union_le_iff {H₁ H₂ : Graph α β} (h_compat : H₁.Compatible H₂) :
    H₁ ∪ H₂ ≤ G ↔ H₁ ≤ G ∧ H₂ ≤ G := by
  simp [h_compat.union_eq_sUnion]

lemma Compatible.right_le_union (h : G.Compatible H) : H ≤ G ∪ H := by
  simp [h.union_comm]

lemma union_eq_self_of_le_left (hle : G ≤ H) : G ∪ H = H :=
  (Graph.union_le hle rfl.le).antisymm (H.compatible_self.mono_left hle).right_le_union

lemma union_eq_self_of_le_right (hle : G ≤ H) : H ∪ G = H :=
  (Graph.union_le rfl.le hle).antisymm <| Graph.left_le_union ..

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

lemma Compatible.union_eq_iUnion (h : G.Compatible H) :
    G ∪ H = Graph.iUnion (fun b ↦ bif b then G else H) (by simpa [pairwise_on_bool]) := by
  generalize_proofs h'
  simp only [le_antisymm_iff, h.union_le_iff, Graph.iUnion_le_iff, Bool.forall_bool, cond_false,
    h.right_le_union, cond_true, Graph.left_le_union, and_self, and_true]
  exact ⟨Graph.le_iUnion h' true, Graph.le_iUnion h' false⟩

lemma Compatible.induce_union (h : G.Compatible H) (X : Set α) : (G ∪ H)[X] = G[X] ∪ H[X] := by
  refine Graph.ext (by simp) fun e x y ↦ ?_
  simp only [induce_isLink_iff, h.union_isLink_iff, h.induce.union_isLink_iff]
  tauto

lemma Compatible.vertexDelete_union (h : G.Compatible H) (X : Set α) :
    (G ∪ H) - X = (G - X) ∪ (H - X) := by
  simp only [h.union_eq_iUnion, vertexDelete_iUnion, Bool.apply_cond (f := fun G ↦ G - X),
    ← h.vertexDelete.union_eq_iUnion]

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

/-! ### Indexed Intersections -/

/-- The intersection of a nonempty family of pairwise compatible graphs. -/
@[simps]
protected def iInter [Nonempty ι] (G : ι → Graph α β) (hG : Pairwise (Compatible on G)) :
    Graph α β where
  vertexSet := ⋂ i, V(G i)
  edgeSet := ⋂ i, E(G i)
  IsLink e x y := ∀ i, (G i).IsLink e x y
  isLink_symm e he x y := by simp [isLink_comm]
  eq_or_eq_of_isLink_of_isLink e _ _ _ _ h h' :=
    (h (Classical.arbitrary ι)).left_eq_or_eq (h' (Classical.arbitrary ι))
  edge_mem_iff_exists_isLink e := by
    simp only [mem_iInter, edge_mem_iff_exists_isLink]
    refine ⟨fun h ↦ ?_, fun ⟨x, y, he⟩ ↦ fun i ↦ ⟨x, y, he i⟩⟩
    let j := Classical.arbitrary ι
    obtain ⟨x, y, he⟩ := h j
    refine ⟨x, y, fun i ↦ ?_⟩
    rwa [hG.of_refl i j]
    exact ⟨(h i).choose_spec.choose_spec.edge_mem, he.edge_mem⟩
  left_mem_of_isLink e x y h := mem_iInter.2 fun i ↦ (h i).left_mem

@[simp]
protected lemma iInter_le {G : ι → Graph α β} (hG : Pairwise (Compatible on G)) (i : ι) :
    @Graph.iInter _ _ _ ⟨i⟩ G hG ≤ G i where
  vertex_subset := iInter_subset (fun i ↦ V(G i)) i
  isLink_of_isLink _ _ _ h := h i

@[simp]
lemma le_iInter_iff [Nonempty ι] {G : ι → Graph α β} (hG : Pairwise (Compatible on G)) :
    H ≤ Graph.iInter G hG ↔ ∀ i, H ≤ G i := by
  let j := Classical.arbitrary ι
  refine ⟨fun h i ↦ h.trans (Graph.iInter_le hG i),
    fun h ↦ le_of_le_le_subset_subset (h j) (by simp) ?_ ?_⟩
  · simp [fun i ↦ vertexSet_mono (h i)]
  simp [fun i ↦ edgeSet_mono (h i)]

/-! ### Set Intersections -/

/-- The intersection of a nonempty set of pairwise compatible graphs. -/
@[simps!]
protected def sInter (s : Set (Graph α β)) (hs : s.Pairwise Compatible) (hne : s.Nonempty) :
    Graph α β :=
  @Graph.iInter _ _ _ hne.to_subtype (fun G : s ↦ G.1) <|
    (pairwise_subtype_iff_pairwise_set s Compatible).2 hs

@[simp]
protected lemma sInter_le (s : Set (Graph α β)) (hs : s.Pairwise Compatible) (hG : G ∈ s) :
    Graph.sInter s hs ⟨G, hG⟩ ≤ G := by
  rw [Graph.sInter]
  generalize_proofs h h'
  exact Graph.iInter_le h' ⟨G, hG⟩

@[simp]
protected lemma le_sInter_iff (s) (hs : s.Pairwise Compatible) (hne : s.Nonempty) :
    H ≤ Graph.sInter s hs hne ↔ ∀ G ∈ s, H ≤ G := by
  simp [Graph.sInter]

/-! ### Intersections -/

/-- The intersection of two graphs `G` and `H`. There seems to be no good way to
defined junk values so that this has the right edge and vertex set, so the
edges are precisely those on which `G` and `H` agree, and the edge set is a subset
of `E(G) ∩ E(H)`,
with equality if `G` and `H` are compatible.   -/
protected def inter (G H : Graph α β) : Graph α β where
  vertexSet := V(G) ∩ V(H)
  IsLink e x y := G.IsLink e x y ∧ H.IsLink e x y
  isLink_symm _ _ _ _ h := ⟨h.1.symm, h.2.symm⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := h.1.left_eq_or_eq h'.1
  edge_mem_iff_exists_isLink e := by simp
  left_mem_of_isLink e x y h := ⟨h.1.left_mem, h.2.left_mem⟩

instance : Inter (Graph α β) where inter := Graph.inter

@[simp]
lemma inter_vertexSet (G H : Graph α β) : V(G ∩ H) = V(G) ∩ V(H) := rfl

@[simp]
lemma inter_isLink_iff : (G ∩ H).IsLink e x y ↔ G.IsLink e x y ∧ H.IsLink e x y := Iff.rfl

protected lemma inter_comm (G H : Graph α β) : G ∩ H = H ∩ G :=
  Graph.ext (Set.inter_comm ..) <| by simp [and_comm]

lemma inter_edgeSet (G H : Graph α β) :
    E(G ∩ H) = {e ∈ E(G) ∩ E(H) | G.IsLink e = H.IsLink e} := by
  simp only [edgeSet_eq_setOf_exists_isLink, inter_isLink_iff, mem_inter_iff, mem_setOf_eq,
    funext_iff, eq_iff_iff, Set.ext_iff]
  exact fun e ↦ ⟨fun ⟨x, y, hfG, hfH⟩ ↦ ⟨⟨⟨_, _, hfG⟩, ⟨_, _, hfH⟩⟩,
    fun z w ↦ by rw [hfG.isLink_iff_sym2_eq, hfH.isLink_iff_sym2_eq]⟩,
    fun ⟨⟨⟨x, y, hexy⟩, ⟨z, w, hezw⟩⟩, h⟩ ↦ ⟨x, y, hexy, by rwa [← h]⟩⟩

@[simp]
lemma inter_inc_iff : (G ∩ H).Inc e x ↔ ∃ y, G.IsLink e x y ∧ H.IsLink e x y := by
  simp [Inc]

@[simp]
lemma inter_isLoopAt_iff : (G ∩ H).IsLoopAt e x ↔ G.IsLoopAt e x ∧ H.IsLoopAt e x := by
  simp [← isLink_self_iff]

@[simp]
lemma inter_isNonloopAt_iff :
    (G ∩ H).IsNonloopAt e x ↔ ∃ y ≠ x, G.IsLink e x y ∧ H.IsLink e x y := by
  simp [IsNonloopAt]

@[simp]
lemma inter_le_left : G ∩ H ≤ G where
  vertex_subset := inter_subset_left
  isLink_of_isLink := by simp +contextual

@[simp]
lemma inter_le_right : G ∩ H ≤ H :=
  Graph.inter_comm _ _ ▸ inter_le_left

lemma Compatible.inter_edgeSet (h : G.Compatible H) : E(G ∩ H) = E(G) ∩ E(H) := by
  rw [Graph.inter_edgeSet]
  exact le_antisymm (fun e he ↦ he.1) fun e he ↦ ⟨he, h he⟩

lemma Compatible.inter_eq_iInter (h : G.Compatible H) :
    G ∩ H = Graph.iInter (fun b ↦ bif b then G else H) (by simpa [pairwise_on_bool]) :=
  Graph.ext (by simp [Set.inter_eq_iInter, Bool.apply_cond]) (by simp [and_comm])





-- lemma Compatible.le_iInter_iff {G₁ G₂ : Graph α β} (h : G₁.Compatible G₂) :
--     H ≤ G₁ ∩ G₂ ↔ H ≤ G₁ ∧ H ≤ G₂ := by
--   refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩


/-! ### Subgraphs -/


variable {H : ι → Graph α β} {H₁ H₂ : Graph α β}

lemma pairwise_compatible_of_subgraph {H : ι → Graph α β} (h : ∀ i, (H i) ≤ G) :
    Pairwise (Compatible on H) :=
  fun i j _ ↦ compatible_of_le_le (h i) (h j)

lemma set_pairwise_compatible_of_subgraph (h : ∀ ⦃H⦄, H ∈ s → H ≤ G) :
    s.Pairwise Compatible :=
  fun _ hi _ hj _ ↦ compatible_of_le_le (h hi) (h hj)

protected lemma iUnion_le_of_forall_le (h : ∀ i, H i ≤ G) :
    Graph.iUnion H (pairwise_compatible_of_subgraph h) ≤ G := by
  simpa

protected lemma sUnion_le_of_forall_le (h : ∀ ⦃H⦄, H ∈ s → H ≤ G) :
    Graph.sUnion s (set_pairwise_compatible_of_subgraph h) ≤ G := by
  simpa

protected lemma iInter_le_of_forall_le [Nonempty ι] (h : ∀ i, H i ≤ G) :
    Graph.iInter H (pairwise_compatible_of_subgraph h) ≤ G :=
  (Graph.iInter_le _ (Classical.arbitrary ι)).trans <| h _

protected lemma sInter_le_of_forall_le (h : ∀ ⦃H⦄, H ∈ s → H ≤ G) (hne : s.Nonempty) :
    Graph.sInter s (set_pairwise_compatible_of_subgraph h) hne ≤ G :=
  have := hne.to_subtype
  Graph.iInter_le_of_forall_le (by simpa)

/-- A union of closed subgraphs of `G` is a closed subgraph of `G`. -/
lemma iUnion_isClosedSubgraph (h : ∀ i, H i ≤c G) :
    Graph.iUnion H (pairwise_compatible_of_subgraph (fun i ↦ (h i).le)) ≤c G where
  le := Graph.iUnion_le_of_forall_le fun i ↦ (h i).le
  closed e x he := by
    simp only [iUnion_vertexSet, mem_iUnion, iUnion_edgeSet, forall_exists_index]
    exact fun i hxi ↦ ⟨_, (he.of_isClosedSubgraph_of_mem (h i) hxi).edge_mem⟩

/-- A nonempty union of spanning subgraphs of `G` is a spanning subgraph of `G`. -/
lemma iUnion_isSpanningSubgraph [Nonempty ι] (h : ∀ i, H i ≤s G) :
    Graph.iUnion H (pairwise_compatible_of_subgraph (fun i ↦ (h i).le)) ≤s G where
  le := Graph.iUnion_le_of_forall_le fun i ↦ (h i).le
  vertexSet_eq := by simp [(h _).vertexSet_eq, iUnion_const]

/-- A nonempty intersection of induced subgraphs `G` is an induced subgraph of `G`-/
lemma iInter_isInducedSubgraph [Nonempty ι] (h : ∀ i, H i ≤i G) :
    Graph.iInter H (pairwise_compatible_of_subgraph (fun i ↦ (h i).le)) ≤i G where
  le := Graph.iInter_le_of_forall_le fun i ↦ (h i).le
  isLink_of_mem_mem := by
    simp only [iInter_vertexSet, mem_iInter, iInter_isLink]
    exact fun e x y he hx hy i ↦ (h i).isLink_of_mem_mem he (hx i) (hy i)

/-- A nonempty intersection of closed subgraphs `G` is an induced subgraph of `G`-/
lemma iInter_isClosedSubgraph [Nonempty ι] (h : ∀ i, H i ≤c G) :
    Graph.iInter H (pairwise_compatible_of_subgraph (fun i ↦ (h i).le)) ≤c G where
  le := Graph.iInter_le_of_forall_le fun i ↦ (h i).le
  closed e x he := by
    simp only [iInter_vertexSet, mem_iInter, iInter_edgeSet]
    exact fun hx i ↦ (he.of_isClosedSubgraph_of_mem (h i) (hx i)).edge_mem

lemma sUnion_isClosedSubgraph (hs : ∀ ⦃H⦄, H ∈ s → H ≤c G) :
    Graph.sUnion s (set_pairwise_compatible_of_subgraph (fun _ h ↦ (hs h).le)) ≤c G :=
  iUnion_isClosedSubgraph <| by simpa

lemma sUnion_isSpanningSubgraph (hs : ∀ ⦃H⦄, H ∈ s → H ≤s G) (hne : s.Nonempty) :
    Graph.sUnion s (set_pairwise_compatible_of_subgraph (fun _ h ↦ (hs h).le)) ≤s G :=
  have := hne.to_subtype
  iUnion_isSpanningSubgraph <| by simpa

lemma sInter_isInducedSubgraph (hs : ∀ ⦃H⦄, H ∈ s → H ≤i G) (hne : s.Nonempty) :
    Graph.sInter s (set_pairwise_compatible_of_subgraph (fun _ h ↦ (hs h).le)) hne ≤i G :=
  have := hne.to_subtype
  iInter_isInducedSubgraph <| by simpa

lemma sInter_isClosedSubgraph (hs : ∀ ⦃H⦄, H ∈ s → H ≤c G) (hne : s.Nonempty) :
    Graph.sInter s (set_pairwise_compatible_of_subgraph (fun _ h ↦ (hs h).le)) hne ≤c G :=
  have := hne.to_subtype
  iInter_isClosedSubgraph <| by simpa

lemma isClosedSubgraph_iUnion_of_disjoint (h : Pairwise (Graph.Disjoint on H)) (i : ι) :
    H i ≤c Graph.iUnion H (h.mono fun _ _ ↦ Disjoint.compatible) where
  le := Graph.le_iUnion ..
  closed e x he hx := by
    obtain ⟨j, hj : (H j).Inc e x⟩ := (iUnion_inc_iff ..).1 he
    obtain rfl | hne := eq_or_ne i j
    · exact hj.edge_mem
    exact False.elim <| (h hne).vertex.not_mem_of_mem_left hx hj.vertex_mem

lemma isClosedSubgraph_sUnion_of_disjoint (s : Set (Graph α β)) (hs : s.Pairwise Graph.Disjoint)
    (hG : G ∈ s) : G ≤c Graph.sUnion s (hs.mono' (by simp)) :=
  isClosedSubgraph_iUnion_of_disjoint ((pairwise_subtype_iff_pairwise_set ..).2 hs) ⟨G, hG⟩

lemma IsClosedSubgraph.union (h₁ : H₁ ≤c G) (h₂ : H₂ ≤c G) : H₁ ∪ H₂ ≤c G := by
  rw [(compatible_of_le_le h₁.le h₂.le).union_eq_iUnion]
  exact iUnion_isClosedSubgraph <| by simp [h₁,h₂]

lemma IsSpanningSubgraph.union (h₁ : H₁ ≤s G) (h₂ : H₂ ≤s G) : H₁ ∪ H₂ ≤s G := by
  rw [(compatible_of_le_le h₁.le h₂.le).union_eq_iUnion]
  exact iUnion_isSpanningSubgraph <| by simp [h₁,h₂]

lemma IsInducedSubgraph.inter (h₁ : H₁ ≤i G) (h₂ : H₂ ≤i G) : H₁ ∩ H₂ ≤i G := by
  rw [(compatible_of_le_le h₁.le h₂.le).inter_eq_iInter]
  exact iInter_isInducedSubgraph <| by simp [h₁,h₂]

lemma IsClosedSubgraph.inter (h₁ : H₁ ≤c G) (h₂ : H₂ ≤c G) : H₁ ∩ H₂ ≤c G := by
  rw [(compatible_of_le_le h₁.le h₂.le).inter_eq_iInter]
  exact iInter_isClosedSubgraph <| by simp [h₁,h₂]

lemma IsClosedSubgraph.inter_le {K G H : Graph α β} (hKG : K ≤c G) (hle : H ≤ G) : K ∩ H ≤c H where
  le := inter_le_right
  closed e x hex hx := by
    rw [inter_vertexSet] at hx
    have heK := ((hex.of_le hle).of_isClosedSubgraph_of_mem hKG hx.1).edge_mem
    rw [(compatible_of_le_le hKG.le hle).inter_edgeSet]
    exact ⟨heK, hex.edge_mem⟩




-- More API TODO

-- lemma Compatible.le_inter_iff {G₁ G₂ : Graph α β} (h : G₁.Compatible G₂) :
--     H ≤ G₁ ∩ G₂ ↔ H ≤ G₁ ∧ H ≤ G₂ := by
--   _







-- /-! ### Unions -/







--   refine Graph.ext union_diff_distrib fun e x y ↦ ?_
--   simp only [vertexDelete_isLink_iff, union_vertexSet, mem_union]
--   rw [vertexDelete_def, vertexDelete_def, ((h.induce_left _).induce_right _).union_isLink_iff,
--     h.union_isLink_iff]
--   simp only [induce_isLink_iff, mem_diff]
--   by_cases hG : G.IsLink e x y
--   · simp +contextual [hG, hG.left_mem, hG.right_mem]
--   by_cases hH : H.IsLink e x y
--   · simp +contextual [hH, hH.left_mem, hH.right_mem]
--   simp [hG, hH]
