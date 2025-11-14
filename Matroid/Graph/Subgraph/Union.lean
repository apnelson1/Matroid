import Matroid.Graph.Subgraph.Compatible

variable {α β ι ι' : Type*} {x y z u v w : α} {e f : β} {F F₁ F₂ : Set β} {X Y : Set α}
  {Gs Gs' Hs : Set (Graph α β)} {G G' G₁ G₂ H H' H₁ H₂ : Graph α β} {Gι Hι : ι → Graph α β}
  {Gι' Hι' : ι' → Graph α β}

open Set Function Partition

namespace Graph
/-! ### Indexed unions -/

protected def iUnion' (G : ι → Graph α β) : Graph α β where
  vertexSet := ⋃ i, V(G i)
  IsLink e x y := (∃ i, (G i).IsLink e x y) ∧ Pairwise ((CompatibleAt e) on G)
  isLink_symm := fun e he x y ⟨⟨i, hi⟩, h'⟩ ↦ ⟨⟨i, hi.symm⟩, h'⟩
  eq_or_eq_of_isLink_of_isLink := by
    refine fun e x y v w ⟨⟨i, hi⟩, h⟩ ⟨⟨j, hj⟩, _⟩ ↦ ?_
    rw [← h.of_refl i j hi.edge_mem hj.edge_mem] at hj
    exact hi.left_eq_or_eq hj
  left_mem_of_isLink := fun e x y ⟨⟨i, hi⟩,h⟩ ↦ mem_iUnion.2 ⟨i, hi.left_mem⟩

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
protected lemma iUnion_const [Nonempty ι] (G : Graph α β) :
    Graph.iUnion (fun (_ : ι) ↦ G) (Pairwise.const_of_refl G) = G := by
  apply le_antisymm ?_ (Graph.le_iUnion (Pairwise.const_of_refl G) (Classical.arbitrary ι))
  rw [Graph.iUnion_le_iff]
  exact fun i ↦ le_refl G

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

lemma iUnion_map_le_iUnion {G : ι → Graph α β} (hG : Pairwise (Graph.Compatible on G)) (f : ι' → ι):
    (Graph.iUnion (G ∘ f) (hG.onFun_comp_of_refl f)) ≤ Graph.iUnion G hG := by
  rw [Graph.iUnion_le_iff]
  exact fun i ↦ Graph.le_iUnion hG (f i)

lemma iUnion_left_le_iUnion_sum {G : ι → Graph α β} {H : ι' → Graph α β}
    (hGH : Pairwise (Graph.Compatible on Sum.elim G H)) :
    Graph.iUnion G hGH.sum_left ≤ Graph.iUnion (Sum.elim G H) hGH := by
  rw [Graph.iUnion_le_iff]
  exact fun i ↦ le_trans (by simp) (Graph.le_iUnion hGH (Sum.inl i))

lemma iUnion_right_le_iUnion_sum {G : ι → Graph α β} {H : ι' → Graph α β}
    (hGH : Pairwise (Graph.Compatible on Sum.elim G H)) :
    Graph.iUnion H hGH.sum_right ≤ Graph.iUnion (Sum.elim G H) hGH := by
  rw [Graph.iUnion_le_iff]
  exact fun i ↦ le_trans (by simp) (Graph.le_iUnion hGH (Sum.inr i))

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

protected lemma iUnion_comp_le {f : ι' → ι} {G : ι → Graph α β} (hG : Pairwise (Compatible on G)) :
    Graph.iUnion (fun i ↦ G (f i)) (hG.onFun_comp_of_refl f) ≤ Graph.iUnion G hG := by
  rw [Graph.iUnion_le_iff]
  exact fun i ↦ Graph.le_iUnion hG (f i)

lemma iUnion_comp_eq_of_surj {f : ι' → ι} {G : ι → Graph α β} (hG : Pairwise (Compatible on G))
    (hf : Function.Surjective f) :
    Graph.iUnion G hG = Graph.iUnion (fun i ↦ G (f i)) (hG.onFun_comp_of_refl f) := by
  refine le_antisymm ?_ (Graph.iUnion_comp_le hG)
  rw [Graph.iUnion_le_iff]
  rintro i
  obtain ⟨i', rfl⟩ := hf i
  exact Graph.le_iUnion (hG.onFun_comp_of_refl f) i'

lemma iUnion_range {f : ι' → ι} {G : (Set.range f) → Graph α β}
    (hG : Pairwise (Graph.Compatible on G)) :
    Graph.iUnion G hG = Graph.iUnion (G <| Set.rangeFactorization f ·)
    (hG.onFun_comp_of_refl <| rangeFactorization f) :=
  iUnion_comp_eq_of_surj hG rangeFactorization_surjective

/-! ### Set unions -/

/-- The union of a set of pairwise compatible graphs. -/
@[simps!]
protected def sUnion (s : Set (Graph α β)) (hs : s.Pairwise Compatible) : Graph α β :=
  .iUnion (fun G : s ↦ G.1) <| (pairwise_subtype_iff_pairwise_set s Compatible).2 hs

protected lemma le_sUnion (hGs : Gs.Pairwise Graph.Compatible) (hG : G ∈ Gs) :
    G ≤ Graph.sUnion Gs hGs := by
  convert Graph.le_iUnion (ι := Gs) _ ⟨G, hG⟩
  rfl

@[simp]
protected lemma sUnion_le_iff (hGs : Gs.Pairwise Graph.Compatible) :
    Graph.sUnion Gs hGs ≤ H ↔ ∀ G ∈ Gs, G ≤ H := by
  simp [Graph.sUnion]

@[simp]
lemma sUnion_inc_iff (hGs : Gs.Pairwise Graph.Compatible) :
    (Graph.sUnion Gs hGs).Inc e x ↔ ∃ G ∈ Gs, G.Inc e x := by
  simp [Graph.sUnion]

@[simp]
lemma sUnion_isLoopAt_iff (hGs : Gs.Pairwise Graph.Compatible) :
    (Graph.sUnion Gs hGs).IsLoopAt e x ↔ ∃ G ∈ Gs, G.IsLoopAt e x := by
  simp [← isLink_self_iff]

@[simp]
lemma sUnion_isNonloopAt_iff (hGs : Gs.Pairwise Graph.Compatible) :
    (Graph.sUnion Gs hGs).IsNonloopAt e x ↔ ∃ G ∈ Gs, G.IsNonloopAt e x := by
  simp [Graph.sUnion]

@[simp]
protected lemma sUnion_singleton (G : Graph α β) : Graph.sUnion {G} (by simp) = G := by
  ext <;> simp

protected lemma sUnion_image {s : Set ι} {f : ι → Graph α β}
    (hs : s.Pairwise (Graph.Compatible on f)) :
    Graph.sUnion (f '' s) hs.image = .iUnion (f · : s → _) (Pairwise.restrict.mpr hs) := by
  rw [Graph.sUnion]
  let f' : s → ↑(f '' s) := fun i ↦ ⟨f i, ⟨i, i.2, rfl⟩⟩
  exact Graph.iUnion_comp_eq_of_surj (f := f') _ (fun ⟨_, i, hGs, rfl⟩ ↦ ⟨⟨i, hGs⟩, rfl⟩)

protected lemma sUnion_range {f : ι → Graph α β} (h : Pairwise (Graph.Compatible on f)) :
    Graph.sUnion (Set.range f) h.range_pairwise = .iUnion f h := by
  unfold Graph.sUnion
  exact Graph.iUnion_comp_eq_of_surj (f := Set.rangeFactorization f) _ rangeFactorization_surjective

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

lemma union_le_iff {H₁ H₂ : Graph α β} : H₁ ∪ H₂ ≤ G ↔ H₁ ≤ G ∧ H₂ ＼ E(H₁) ≤ G := by
  simp [union_eq_sUnion]

lemma union_mono_right (h : H₁ ≤ H₂) : G ∪ H₁ ≤ G ∪ H₂ := by
  simp only [union_eq_sUnion, Graph.sUnion_le_iff, mem_insert_iff, mem_singleton_iff,
    forall_eq_or_imp, forall_eq]
  exact ⟨Graph.le_sUnion _ (by simp), le_trans (edgeDelete_mono_left h E(G)) <|
    Graph.le_sUnion _ (by simp : H₂ ＼ E(G) ∈ _)⟩

@[simp]
protected lemma union_self (G : Graph α β) : G ∪ G = G :=
  (Graph.union_le le_rfl le_rfl).antisymm <| Graph.left_le_union ..

protected lemma union_assoc (G₁ G₂ G₃ : Graph α β) : (G₁ ∪ G₂) ∪ G₃ = G₁ ∪ (G₂ ∪ G₃) := by
  refine Graph.ext (Set.union_assoc ..) fun e x y ↦ ?_
  simp [union_isLink_iff]
  tauto

instance : Std.Associative (α := Graph α β) (· ∪ ·) where
  assoc := Graph.union_assoc

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

lemma Compatible.union_mono_left (h : H₂.Compatible G) (hle : H₁ ≤ H₂) : H₁ ∪ G ≤ H₂ ∪ G := by
  rw [h.union_comm, (h.mono_left hle).union_comm]
  exact union_mono_right hle

lemma Compatible.union_mono (hleG : G₁ ≤ G₂) (hleH : H₁ ≤ H₂) (h : G₂.Compatible H₁) :
    G₁ ∪ H₁ ≤ G₂ ∪ H₂ := le_trans (h.union_mono_left hleG) (union_mono_right hleH)

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

end Graph
