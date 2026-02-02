import Matroid.Graph.Subgraph.Compatible

variable {α β ι ι' : Type*} {x y z u v w : α} {e f : β} {F F₁ F₂ : Set β} {X Y : Set α}
  {Gs Gs' Hs : Set (Graph α β)} {G G' G₁ G₂ H H' H₁ H₂ : Graph α β} {Gι Hι : ι → Graph α β}
  {Gι' Hι' : ι' → Graph α β}

open Set Function

namespace Graph
/-! ### Indexed unions -/

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

lemma union_mono_right (h : H₁ ≤ H₂) : G ∪ H₁ ≤ G ∪ H₂ := by
  simp only [union_eq_sUnion, Graph.sUnion_le_iff, mem_insert_iff, mem_singleton_iff,
    forall_eq_or_imp, forall_eq]
  exact ⟨Graph.le_sUnion _ (by simp), le_trans (edgeDelete_mono_left h E(G)) <|
    Graph.le_sUnion _ (by simp : H₂ ＼ E(G) ∈ _)⟩

lemma isLink_or_isLink_of_union (h : (G ∪ H).IsLink e x y) : G.IsLink e x y ∨ H.IsLink e x y :=
  (union_isLink_iff.1 h).elim .inl fun h' ↦ .inr h'.1

lemma edgeRestrict_union (G : Graph α β) (F₁ F₂ : Set β) : (G ↾ (F₁ ∪ F₂)) = G ↾ F₁ ∪ (G ↾ F₂) := by
  refine Graph.ext (by simp) fun e x y ↦ ?_
  rw [(G.compatible_self.mono (by simp) (by simp)).union_isLink_iff]
  simp only [edgeRestrict_isLink, mem_union]
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

lemma union_eq_self_of_le_left (hle : G ≤ H) : G ∪ H = H :=
  (Graph.union_le hle rfl.le).antisymm (H.compatible_self.mono_left hle).right_le_union

lemma union_eq_self_of_le_right (hle : G ≤ H) : H ∪ G = H :=
  (Graph.union_le rfl.le hle).antisymm <| Graph.left_le_union ..

lemma Compatible.union_mono_left (h : H₂.Compatible G) (hle : H₁ ≤ H₂) : H₁ ∪ G ≤ H₂ ∪ G := by
  rw [h.union_comm, (h.mono_left hle).union_comm]
  exact union_mono_right hle

lemma compatible_iff_exists_le_le (G H : Graph α β) : G.Compatible H ↔ ∃ I, G ≤ I ∧ H ≤ I :=
  ⟨fun h => ⟨G ∪ H, G.left_le_union .., h.right_le_union ..⟩,
    fun ⟨_, hGI, hHI⟩ ↦ compatible_of_le_le hGI hHI⟩

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
  simp only [induce_isLink, h.union_isLink_iff, h.induce.union_isLink_iff]
  tauto

lemma Compatible.vertexDelete_union (h : G.Compatible H) (X : Set α) :
    (G ∪ H) - X = (G - X) ∪ (H - X) := by
  simp only [h.union_eq_iUnion, vertexDelete_iUnion, Bool.apply_cond (f := fun G ↦ G - X),
    ← h.vertexDelete.union_eq_iUnion]

lemma induce_union (G : Graph α β) (X Y : Set α) (hX : ∀ x ∈ X, ∀ y ∈ Y, ¬ G.Adj x y) :
    G [X ∪ Y] = G [X] ∪ G [Y] := by
  refine Graph.ext rfl fun e x y ↦ ?_
  simp only [induce_isLink, mem_union, Compatible.induce_induce.union_isLink_iff]
  by_cases hxy : G.IsLink e x y
  · by_cases hx : x ∈ X
    · simp [hx, show y ∉ Y from fun hy ↦ hX x hx y hy hxy.adj]
    by_cases hy : y ∈ X
    · simp [hy, show x ∉ Y from fun hx ↦ hX _ hy _ hx hxy.symm.adj, hxy]
    simp [hx, hy]
  simp [hxy]

protected lemma inter_distrib_iUnion {H : ι → Graph α β} (hH : Pairwise (Compatible on H)) :
    G ∩ (Graph.iUnion H hH) = Graph.iUnion (fun i ↦ G ∩ (H i))
      (fun _ _ hne ↦ (hH hne).mono Graph.inter_le_right Graph.inter_le_right) :=
  Graph.ext (by simp [inter_iUnion]) (by simp)

protected lemma inter_distrib_sUnion (hs : Gs.Pairwise Compatible) :
    G ∩ (Graph.sUnion Gs hs) = Graph.sUnion ((fun K ↦ G ∩ K) '' Gs) (by
      rintro _ ⟨K₁, hK₁, rfl⟩ _ ⟨K₂, hK₂, rfl⟩ -
      exact (hs.of_refl hK₁ hK₂).mono Graph.inter_le_right Graph.inter_le_right) := by
  ext <;> aesop

lemma Pairwise.union_compatible {s t : Set (Graph α β)} (hst : (s ∪ t).Pairwise Compatible) :
    (Graph.sUnion s (hst.mono subset_union_left)).Compatible
    (Graph.sUnion t (hst.mono subset_union_right)) := by
  refine compatible_of_le_le (G := Graph.sUnion (s ∪ t) hst) ?_ ?_ <;> rw [Graph.sUnion_le_iff]
  <;> exact fun G hG ↦ Graph.le_sUnion hst (by simp [hG])

lemma sUnion_union_sUnion {s t : Set (Graph α β)} (hst : (s ∪ t).Pairwise Compatible) :
    Graph.sUnion s (hst.mono subset_union_left) ∪ Graph.sUnion t (hst.mono subset_union_right) =
    Graph.sUnion (s ∪ t) hst := by
  have hs : s.Pairwise Compatible := hst.mono subset_union_left
  have ht : t.Pairwise Compatible := hst.mono subset_union_right
  refine Graph.ext (by aesop) fun e x y ↦ ?_
  rw [(Pairwise.union_compatible hst).union_isLink_iff]
  aesop

lemma Compatible.sum_compatible {G : ι → Graph α β} {H : ι' → Graph α β}
    (hGH : Pairwise (Compatible on (Sum.elim G H))) :
    (Graph.iUnion G (hGH.sum_left)).Compatible (Graph.iUnion H (hGH.sum_right)) :=
  compatible_of_le_le (iUnion_left_le_iUnion_sum hGH) <| iUnion_right_le_iUnion_sum hGH

protected lemma iUnion_sum [Nonempty ι] [Nonempty ι'] {G : ι → Graph α β}
    {H : ι' → Graph α β} (hGH : Pairwise (Compatible on (Sum.elim G H))) :
    Graph.iUnion (Sum.elim G H) hGH = (.iUnion G hGH.sum_left) ∪ (.iUnion H hGH.sum_right) := by
  refine le_antisymm ?_ <| Graph.union_le (iUnion_left_le_iUnion_sum hGH)
    (iUnion_right_le_iUnion_sum hGH)
  rw [Graph.iUnion_le_iff]
  rintro (i | i) <;> simp only [Sum.elim_inl, Sum.elim_inr]
  · exact le_trans (Graph.le_iUnion hGH.sum_left i) (Graph.left_le_union _ _)
  · exact le_trans (Graph.le_iUnion hGH.sum_right i)
      (Compatible.right_le_union (Compatible.sum_compatible hGH))

section Subgraph

/-! ### Subgraphs -/

variable {H : ι → Graph α β} {H₁ H₂ : Graph α β}

lemma pairwise_compatible_of_subgraph {H : ι → Graph α β} (h : ∀ i, H i ≤ G) :
    Pairwise (Compatible on H) :=
  fun i j _ ↦ compatible_of_le_le (h i) (h j)

lemma set_pairwise_compatible_of_subgraph (h : ∀ ⦃H⦄, H ∈ Gs → H ≤ G) :
    Gs.Pairwise Compatible :=
  fun _ hi _ hj _ ↦ compatible_of_le_le (h hi) (h hj)

protected lemma iUnion_le_of_forall_le (h : ∀ i, H i ≤ G) :
    Graph.iUnion H (pairwise_compatible_of_subgraph h) ≤ G := by
  simpa

protected lemma sUnion_le_of_forall_le (h : ∀ ⦃H⦄, H ∈ Gs → H ≤ G) :
    Graph.sUnion Gs (set_pairwise_compatible_of_subgraph h) ≤ G := by
  simpa

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
  vertexSet_eq := by simp [(h _).vertexSet_eq, iUnion_const]
  isLink_of_isLink := (Graph.iUnion_le_of_forall_le fun i ↦ (h i).le).isLink_of_isLink

-- A weakening of the previous lemma.
lemma iUnion_isSpanningSubgraph_of_exists_isSpanningSubgraph_of_forall_le [Nonempty ι]
    (h : ∀ i, H i ≤ G) (hH : ∃ i, H i ≤s G) :
    Graph.iUnion H (pairwise_compatible_of_subgraph h) ≤s G where
  vertexSet_eq := by
    apply le_antisymm
    · simp only [iUnion_vertexSet, le_eq_subset, iUnion_subset_iff]
      exact fun i ↦ (h i).vertex_subset
    obtain ⟨i, hi⟩ := hH
    rw [← hi.vertexSet_eq]
    exact subset_iUnion_of_subset i fun ⦃a⦄ a ↦ a
  isLink_of_isLink := (Graph.iUnion_le_of_forall_le h).isLink_of_isLink

lemma sUnion_isClosedSubgraph (hs : ∀ ⦃H⦄, H ∈ Gs → H ≤c G) :
    Graph.sUnion Gs (set_pairwise_compatible_of_subgraph (fun _ h ↦ (hs h).le)) ≤c G :=
  iUnion_isClosedSubgraph <| by simpa

lemma sUnion_isSpanningSubgraph (hs : ∀ ⦃H⦄, H ∈ Gs → H ≤s G) (hne : Gs.Nonempty) :
    Graph.sUnion Gs (set_pairwise_compatible_of_subgraph (fun _ h ↦ (hs h).le)) ≤s G :=
  have := hne.to_subtype
  iUnion_isSpanningSubgraph <| by simpa

end Subgraph
end Graph
