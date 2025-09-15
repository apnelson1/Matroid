import Matroid.Graph.Subgraph.Compatible

variable {α β ι ι' : Type*} {x y z u v w : Set α} {e f : β} {G G₁ G₂ H H₁ H₂ : Graph α β}
  {F F₁ F₂ : Set β} {X Y : Set (Set α)} {s t : Set (Graph α β)} {P : Partition (Set α)}

open Set Function Partition

namespace Graph


/-! ### Set unions -/

variable {s : Set (Graph α β)} {G : Graph α β}

/-- The union of a set of pairwise compatible graphs. -/
@[simps! vertexPartition]
protected def sUnion (s : Set (Graph α β)) : Graph α β where
  vertexPartition := ⨆ G ∈ s, P(G)
  IsLink e x y := ∃ (u v : Set α) (h : ∃ G ∈ s, G.IsLink e u v), s.Pairwise (CompatibleAt e) ∧
    Partition.foo (⨆ G ∈ s, P(G)) u h.choose_spec.2.left_mem_vertexPartition = x ∧
    Partition.foo (⨆ G ∈ s, P(G)) v h.choose_spec.2.right_mem_vertexPartition = y
  isLink_symm e he u v := by
    rintro ⟨u, v, ⟨G, hG, huv⟩, hs, rfl, rfl⟩
    exact ⟨v, u, ⟨G, hG, huv.symm⟩, hs, rfl, rfl⟩
  eq_or_eq_of_isLink_of_isLink e a b c d := by
    rintro ⟨u, v, ⟨G, hG, huv⟩, hs, rfl, rfl⟩ ⟨u', v', ⟨G', hG', hvw⟩, -, rfl, rfl⟩
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := G.eq_or_eq_of_isLink_of_isLink huv <|
      hvw.of_compatibleAt (hs.of_refl hG' hG) huv.edge_mem <;> tauto
  left_mem_of_isLink e a b := by
    rintro ⟨u, v, ⟨G, hG, huv⟩, -, rfl, rfl⟩
    refine Partition.foo_mem _ fun a ha ↦ ?_
    simp only [iSup_supp, iSup_supp_prop, mem_iUnion, exists_prop]
    exact ⟨G, hG, mem_supp_iff.mpr ⟨u, huv.left_mem_vertexPartition, ha⟩⟩

@[simp]
lemma sUnion_vertexSet (hs' : s.Pairwise Dup_agree) : V(Graph.sUnion s) = ⋃ G ∈ s, V(G) := by
  rw [← Graph.vertexSet_eq_parts, sUnion_vertexPartition, ← sSup_image, sSup_parts_of_agree]
  simp_rw [← sUnion_image, image_image, Graph.vertexSet_eq_parts]
  rwa [← pairwise_dup_agree_eq_pairwise_image]

@[simp]
lemma sUnion_isLink (hs : s.Pairwise Graph.Compatible) (hs' : s.Pairwise Dup_agree) :
    (Graph.sUnion s).IsLink e x y ↔ ∃ G ∈ s, G.IsLink e x y := by
  refine ⟨fun ⟨u, v, ⟨G, hGs, huv⟩, hs, A, B⟩ => ⟨G, hGs, ?_⟩,
    fun h => ⟨x, y, h, hs.imp  fun _ _ hGH ↦ hGH.compatibleAt e, ?_⟩⟩
  · subst A B
    convert huv <;> rw [foo_eq_iff, ← sSup_image,
      mem_sSup_iff_of_agree (by rwa [← pairwise_dup_agree_eq_pairwise_image])]
    · use P(G), (by use G), huv.left_mem_vertexPartition
    · use P(G), (by use G), huv.right_mem_vertexPartition
  · obtain ⟨G, hGs, huv⟩ := h
    constructor <;> rw [foo_eq_iff, ← sSup_image,
      mem_sSup_iff_of_agree (by rwa [← pairwise_dup_agree_eq_pairwise_image])]
    · use P(G), (by use G), huv.left_mem_vertexPartition
    · use P(G), (by use G), huv.right_mem_vertexPartition

lemma sUnion_isLink_not_agree (hs : s.Pairwise Graph.Compatible) :
    (Graph.sUnion s).IsLink e x y ↔ ∃ (u v : Set α) (h : ∃ G ∈ s, G.IsLink e u v),
    Partition.foo (⨆ G ∈ s, P(G)) u h.choose_spec.2.left_mem_vertexPartition = x ∧
    Partition.foo (⨆ G ∈ s, P(G)) v h.choose_spec.2.right_mem_vertexPartition = y := by
  refine exists₃_congr (fun u v h => ?_)
  rw [and_iff_right]
  exact hs.imp  fun _ _ hGH ↦ hGH.compatibleAt e

@[simp]
lemma sUnion_edgeSet (hs : s.Pairwise Graph.Compatible) :
    E(Graph.sUnion s) = ⋃ G ∈ s, E(G) := by
  ext e
  simp only [edgeSet_eq_setOf_exists_isLink, sUnion_isLink_not_agree hs, mem_setOf_eq, mem_iUnion,
    exists_prop]
  tauto

protected lemma le_sUnion (hs : s.Pairwise Graph.Compatible) (hs' : s.Pairwise Dup_agree)
    (hG : G ∈ s) : G ≤ Graph.sUnion s where
  vertexSet_subset := by
    rw [sUnion_vertexSet hs']
    exact subset_biUnion_of_mem hG
  isLink_of_isLink e x y h := by
    rw [sUnion_isLink hs hs']
    use G

@[simp]
protected lemma sUnion_le_iff (hs : s.Pairwise Graph.Compatible) (hs' : s.Pairwise Dup_agree) :
    Graph.sUnion s ≤ H ↔ ∀ G ∈ s, G ≤ H := by
  simp only [le_iff, sUnion_vertexSet hs', iUnion_subset_iff, sUnion_isLink hs hs',
    forall_exists_index, and_imp]
  exact ⟨fun h G hGs => ⟨h.1 G hGs, fun _ _ _ => h.2 G hGs⟩,
    fun h => ⟨fun G hGs => (h G hGs).1, fun e x y G hGs H => (h G hGs).2 H⟩⟩

@[simp]
lemma sUnion_inc_iff (hs : s.Pairwise Graph.Compatible) (hs' : s.Pairwise Dup_agree) :
    (Graph.sUnion s).Inc e x ↔ ∃ G ∈ s, G.Inc e x := by
  simp only [Inc, hs, hs', sUnion_isLink]
  tauto

@[simp]
lemma sUnion_isLoopAt_iff (hs : s.Pairwise Graph.Compatible) (hs' : s.Pairwise Dup_agree) :
    (Graph.sUnion s).IsLoopAt e x ↔ ∃ G ∈ s, G.IsLoopAt e x := by
  simp [← isLink_self_iff, hs, hs']

@[simp]
lemma sUnion_isNonloopAt_iff (hs : s.Pairwise Graph.Compatible) (hs' : s.Pairwise Dup_agree) :
    (Graph.sUnion s).IsNonloopAt e x ↔ ∃ G ∈ s, G.IsNonloopAt e x := by
  simp only [isNonloopAt_iff_inc_not_isLoopAt, hs, hs', sUnion_inc_iff, sUnion_isLoopAt_iff,
    not_exists, not_and]
  exact ⟨fun ⟨⟨G, hGs, hG⟩, h⟩ => ⟨G, hGs, hG, h G hGs⟩, fun ⟨G, hGs, hG, h⟩ =>
    ⟨⟨G, hGs, hG⟩, fun H hHs hH ↦ h <| hH.of_compatible (hs.of_refl hGs hHs).symm hG.edge_mem⟩⟩

@[simp]
protected lemma sUnion_singleton (G : Graph α β) : Graph.sUnion {G} = G := by
  ext <;> simp

-- protected lemma sUnion_image {s : Set ι} {f : ι → Graph α β}
--     (hs : s.Pairwise (Graph.Compatible on f)) :
--     Graph.sUnion (f '' s) hs.image = .iUnion (f · : s → _) (Pairwise.restrict.mpr hs) := by
--   rw [Graph.sUnion]
--   let f' : s → ↑(f '' s) := fun i ↦ ⟨f i, ⟨i, i.2, rfl⟩⟩
--   exact Graph.iUnion_comp_eq_of_surj (f := f') _ (fun ⟨_, i, hGs, rfl⟩ ↦ ⟨⟨i, hGs⟩, rfl⟩)

-- protected lemma sUnion_range {f : ι → Graph α β} (h : Pairwise (Graph.Compatible on f)) :
--     Graph.sUnion (Set.range f) h.range_pairwise = .iUnion f h := by
--   unfold Graph.sUnion
--   exact Graph.iUnion_comp_eq_of_surj (f := Set.rangeFactorization f) _ surjective_onto_range

/-! ### Indexed unions -/

/-- The union of an indexed family of pairwise compatible graphs. -/
protected def iUnion (G : ι → Graph α β) : Graph α β := Graph.sUnion (Set.range G)

variable {G : ι → Graph α β} {G' : ι' → Graph α β}

@[simp]
lemma iUnion_vertexPartition : P(Graph.iUnion G) = ⨆ i, P(G i) := by
  rw [Graph.iUnion, sUnion_vertexPartition, iSup_range]

@[simp]
lemma iUnion_vertexSet (hG : Pairwise (Dup_agree on G)) : V(Graph.iUnion G) = ⋃ i, V(G i) := by
  simp [Graph.iUnion, sUnion_vertexSet hG.range_pairwise]

@[simp]
lemma iUnion_isLink (hG : Pairwise (Graph.Compatible on G)) (hG' : Pairwise (Dup_agree on G)) :
    (Graph.iUnion G).IsLink e x y ↔ ∃ i, (G i).IsLink e x y := by
  simp [Graph.iUnion, sUnion_isLink hG.range_pairwise hG'.range_pairwise]

@[simp]
lemma iUnion_edgeSet (hG : Pairwise (Graph.Compatible on G)) :
    E(Graph.iUnion G) = ⋃ i, E(G i) := by
  simp [Graph.iUnion, sUnion_edgeSet hG.range_pairwise]

protected lemma le_iUnion (hG : Pairwise (Graph.Compatible on G)) (hG' : Pairwise (Dup_agree on G))
    (i : ι) : G i ≤ Graph.iUnion G :=
  Graph.le_sUnion hG.range_pairwise hG'.range_pairwise (by use i)

@[simp]
protected lemma iUnion_le_iff (hG : Pairwise (Graph.Compatible on G))
    (hG' : Pairwise (Dup_agree on G)) : Graph.iUnion G ≤ H ↔ ∀ i, G i ≤ H := by
  convert Graph.sUnion_le_iff hG.range_pairwise hG'.range_pairwise
  simp

@[simp]
protected lemma iUnion_const [Nonempty ι] (G : Graph α β) : Graph.iUnion (fun (_ : ι)↦ G) = G := by
  refine le_antisymm ?_ <| Graph.le_iUnion (Pairwise.const_of_refl G) (Pairwise.const_of_refl G)
    (Classical.arbitrary ι)
  rw [Graph.iUnion_le_iff (Pairwise.const_of_refl G) (Pairwise.const_of_refl G)]
  exact fun i ↦ le_refl G

@[simp]
lemma iUnion_inc_iff (hG : Pairwise (Graph.Compatible on G)) (hG' : Pairwise (Dup_agree on G)) :
    (Graph.iUnion G).Inc e x ↔ ∃ i, (G i).Inc e x := by
  simp [Graph.iUnion, sUnion_inc_iff hG.range_pairwise hG'.range_pairwise]

@[simp]
lemma iUnion_isLoopAt_iff (hG : Pairwise (Graph.Compatible on G)) (h' : Pairwise (Dup_agree on G)) :
    (Graph.iUnion G).IsLoopAt e x ↔ ∃ i, (G i).IsLoopAt e x := by
  simp [← isLink_self_iff, hG, h']

@[simp]
lemma iUnion_isNonloopAt_iff (hG : Pairwise (Graph.Compatible on G))
    (hG' : Pairwise (Dup_agree on G)) :
    (Graph.iUnion G).IsNonloopAt e x ↔ ∃ i, (G i).IsNonloopAt e x := by
  simp only [IsNonloopAt, ne_eq, iUnion_isLink hG hG']
  aesop

lemma iUnion_map_le_iUnion (hG : Pairwise (Graph.Compatible on G)) (hG' : Pairwise (Dup_agree on G))
    (f : ι' → ι): (Graph.iUnion (G ∘ f)) ≤ Graph.iUnion G := by
  rw [Graph.iUnion_le_iff (hG.onFun_comp_of_refl f) (hG'.onFun_comp_of_refl f)]
  exact fun i ↦ Graph.le_iUnion hG hG' (f i)

lemma iUnion_left_le_iUnion_sum (hGH : Pairwise (Graph.Compatible on Sum.elim G G'))
    (hGH' : Pairwise (Dup_agree on Sum.elim G G')) :
    Graph.iUnion G ≤ Graph.iUnion (Sum.elim G G') := by
  rw [Graph.iUnion_le_iff hGH.sum_left hGH'.sum_left]
  exact fun i ↦ le_trans (by simp) (Graph.le_iUnion hGH hGH' (Sum.inl i))

lemma iUnion_right_le_iUnion_sum (hGH : Pairwise (Graph.Compatible on Sum.elim G G'))
    (hGH' : Pairwise (Dup_agree on Sum.elim G G')) :
    Graph.iUnion G' ≤ Graph.iUnion (Sum.elim G G') := by
  rw [Graph.iUnion_le_iff hGH.sum_right hGH'.sum_right]
  exact fun i ↦ le_trans (by simp) (Graph.le_iUnion hGH hGH' (Sum.inr i))

@[simp]
lemma induce_iUnion [Nonempty ι] (hG : Pairwise (Graph.Compatible on G))
    (hG' : Pairwise (Dup_agree on G)) (P : Partition (Set α)) :
    (Graph.iUnion G)[P] = .iUnion (fun i ↦ (G i)[P]) :=
  Graph.ext (by rw [iUnion_vertexSet (Pairwise.const_of_refl P)]; simp [iUnion_const]) <| by
    rintro e x y
    rw [induce_isLink_iff, iUnion_isLink hG hG', iUnion_isLink
      (hG.mono (fun _ _ ↦ Compatible.induce)) (hG'.mono (fun _ _ _ ↦ Dup_agree.induce P))]
    simp

@[simp]
lemma Compatible.vertexDelete_iUnion (hG : Pairwise (Graph.Compatible on G))
    (hG' : Pairwise (Dup_agree on G)) (X : Set (Set α)) :
    (Graph.iUnion G) - X = .iUnion (fun i ↦ (G i) - X) := by
  refine Graph.ext ?_ fun e x y ↦ ?_
  · rw [iUnion_vertexSet (hG'.mono (fun _ _ ↦ Dup_agree.vertexDelete X))]
    simp [iUnion_diff, iUnion_vertexSet hG']
  · rw [vertexDelete_isLink_iff, iUnion_isLink hG hG', iUnion_isLink
      (hG.mono (fun _ _ ↦ Compatible.vertexDelete))
      (hG'.mono (fun _ _ ↦ Dup_agree.vertexDelete X))]
    simp

@[simp]
lemma Compatible.edgeDelete_iUnion (hG : Pairwise (Graph.Compatible on G))
    (hG' : Pairwise (Dup_agree on G)) (F : Set β) :
    (Graph.iUnion G) ＼ F = .iUnion (fun i ↦ (G i) ＼ F) := by
  refine Graph.ext ?_ fun e x y ↦ ?_
  · rw [iUnion_vertexSet (hG'.mono (fun _ _ ↦ Dup_agree.edgeDelete F))]
    simp [iUnion_vertexSet hG']
  · rw [edgeDelete_isLink, iUnion_isLink hG hG', iUnion_isLink
      (hG.mono (fun _ _ ↦ Compatible.edgeDelete))
      (hG'.mono (fun _ _ ↦ Dup_agree.edgeDelete F))]
    simp

@[simp]
lemma Compatible.edgeRestrict_iUnion (hG : Pairwise (Graph.Compatible on G))
    (hG' : Pairwise (Dup_agree on G)) (F : Set β) :
    (Graph.iUnion G) ↾ F = .iUnion (fun i ↦ (G i) ↾ F) := by
  refine Graph.ext ?_ fun e x y ↦ ?_
  · rw [iUnion_vertexSet (hG'.mono (fun _ _ ↦ Dup_agree.edgeRestrict F))]
    simp [iUnion_vertexSet hG']
  · rw [edgeRestrict_isLink, iUnion_isLink hG hG', iUnion_isLink
      (hG.mono (fun _ _ ↦ Compatible.edgeRestrict))
      (hG'.mono (fun _ _ ↦ Dup_agree.edgeRestrict F))]
    simp

protected lemma iUnion_comp_le {f : ι' → ι} (hG : Pairwise (Compatible on G))
    (hG' : Pairwise (Dup_agree on G)) : Graph.iUnion (fun i ↦ G (f i)) ≤ Graph.iUnion G := by
  change Graph.iUnion (G ∘ f) ≤ Graph.iUnion G
  rw [Graph.iUnion_le_iff (hG.onFun_comp_of_refl f) (hG'.onFun_comp_of_refl f)]
  exact fun i ↦ Graph.le_iUnion hG hG' (f i)

lemma iUnion_comp_eq_of_surj {f : ι' → ι} (hG : Pairwise (Compatible on G))
    (hG' : Pairwise (Dup_agree on G)) (hf : Function.Surjective f) :
    Graph.iUnion G = Graph.iUnion (fun i ↦ G (f i)) := by
  refine le_antisymm ?_ (Graph.iUnion_comp_le hG hG')
  rw [Graph.iUnion_le_iff hG hG']
  rintro i
  obtain ⟨i', rfl⟩ := hf i
  exact Graph.le_iUnion (hG.onFun_comp_of_refl f) (hG'.onFun_comp_of_refl f) i'

lemma iUnion_range {f : ι' → ι} {G : (Set.range f) → Graph α β}
    (hG : Pairwise (Graph.Compatible on G)) (hG' : Pairwise (Dup_agree on G)) :
    Graph.iUnion G = Graph.iUnion (G <| Set.rangeFactorization f ·) :=
  iUnion_comp_eq_of_surj hG hG' rangeFactorization_surjective


/-! ### Unions of pairs -/

/-- The union of two graphs `G` and `H`. If there is an edge `e` whose `G`-ends differ from
its `H`-ends, then `G` is favoured, so this is not commutative in general.
If `G` and `H` are `Compatible`, this doesn't occur.
We define this in terms of `sUnion` and `Graph.copy` so the vertex and edge sets are
definitionally unions. -/
@[simps! vertexPartition edgeSet]
protected def union (G H : Graph α β) := Graph.copy (P := P(G) ⊔ P(H)) (X := (P(G) ⊔ P(H)).parts)
  (E := E(G) ∪ E(H)) (Graph.sUnion {G, H ＼ E(G)}) (by
    rw [sUnion_vertexPartition, ← sSup_image, image_pair]; simp)
    (by rw [← Graph.vertexPartition_parts, sUnion_vertexPartition, ← sSup_image, image_pair]; simp)
    (by rw [sUnion_edgeSet pairwise_compatible_edgeDelete]; simp)
    (fun e x y ↦ by rw [sUnion_isLink_not_agree pairwise_compatible_edgeDelete])

instance : Union (Graph α β) where union := Graph.union

variable {G H H₁ H₂ : Graph α β}

lemma union_eq_sUnion (G H : Graph α β) : G ∪ H = Graph.sUnion {G, H ＼ E(G)} := by
  simp_rw [Union.union, Graph.union]
  apply copy_eq_self

@[simp]
lemma union_vertexSet (hG : G.Dup_agree H) : V(G ∪ H) = V(G) ∪ V(H) := by
  change (P(G) ⊔ P(H)).parts = V(G) ∪ V(H)
  rw [Agree.sup_parts hG, vertexPartition_parts, vertexPartition_parts]

@[simp]
lemma union_isLink (hG' : G.Dup_agree H) :
    (G ∪ H).IsLink e x y ↔ G.IsLink e x y ∨ (H.IsLink e x y ∧ e ∉ E(G)) := by
  rw [union_eq_sUnion, sUnion_isLink pairwise_compatible_edgeDelete hG'.pair_edgeDelete]
  simp

lemma union_inc_iff (hG' : G.Dup_agree H) :
    (G ∪ H).Inc e x ↔ G.Inc e x ∨ (H.Inc e x ∧ e ∉ E(G)) := by
  simp [union_eq_sUnion, hG']

lemma union_isLoopAt_iff (hG' : G.Dup_agree H) :
    (G ∪ H).IsLoopAt e x ↔ G.IsLoopAt e x ∨ (H.IsLoopAt e x ∧ e ∉ E(G)) := by
  simp [union_eq_sUnion, hG']

lemma union_isNonloopAt_iff (hG' : G.Dup_agree H) :
    (G ∪ H).IsNonloopAt e x ↔ G.IsNonloopAt e x ∨ (H.IsNonloopAt e x ∧ e ∉ E(G)) := by
  simp only [IsNonloopAt, ne_eq, union_isLink hG']
  aesop

lemma union_eq_union_edgeDelete (G H : Graph α β) : G ∪ H = G ∪ (H ＼ E(G)) := by
  simp [union_eq_sUnion]

@[simp]
protected lemma left_le_union (hG' : G.Dup_agree H) : G ≤ G ∪ H := by
  simp_rw [le_iff, union_isLink hG', union_vertexSet hG']
  tauto

lemma right_edgeDelete_le_union (hG' : G.Dup_agree H) : H ＼ E(G) ≤ G ∪ H := by
  simp_rw [le_iff, union_isLink hG', union_vertexSet hG', edgeDelete_isLink]
  tauto

lemma union_le_edgeDelete (h₁ : H₁ ≤ G) (h₂ : H₂ ＼ E(H₁) ≤ G) : H₁ ∪ H₂ ≤ G := by
  have hG' : H₁.Dup_agree H₂ :=
    ⟨P(G), vertexPartition_mono h₁, (vertexPartition_mono h₂ : P(H₂ ＼ E(H₁)) ⊆ _)⟩
  rw [union_eq_sUnion, Graph.sUnion_le_iff pairwise_compatible_edgeDelete hG'.pair_edgeDelete]
  simp [h₁, h₂]

protected lemma union_le (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) : H₁ ∪ H₂ ≤ G := by
  have hG' : H₁.Dup_agree H₂ :=
    ⟨P(G), vertexPartition_mono h₁, vertexPartition_mono h₂⟩
  rw [union_eq_sUnion, Graph.sUnion_le_iff pairwise_compatible_edgeDelete hG'.pair_edgeDelete]
  simp [h₁, edgeDelete_le.trans h₂]

lemma union_le_iff (hG' : H₁.Dup_agree H₂) : H₁ ∪ H₂ ≤ G ↔ H₁ ≤ G ∧ H₂ ＼ E(H₁) ≤ G :=
  ⟨fun h => ⟨(Graph.left_le_union hG').trans h, (Graph.right_edgeDelete_le_union hG').trans h⟩,
    fun ⟨h₁, h₂⟩ => Graph.union_le_edgeDelete h₁ h₂⟩

lemma union_mono_right (hG₁ : G.Dup_agree H₁) (hG₂ : G.Dup_agree H₂) (h : H₁ ≤ H₂) :
    G ∪ H₁ ≤ G ∪ H₂ := by
  simp [union_eq_sUnion, Graph.sUnion_le_iff pairwise_compatible_edgeDelete hG₁.pair_edgeDelete,
    Graph.le_sUnion pairwise_compatible_edgeDelete hG₂.pair_edgeDelete,
    le_trans (edgeDelete_mono_left h) <|
    Graph.le_sUnion pairwise_compatible_edgeDelete hG₂.pair_edgeDelete (by simp : H₂ ＼ E(G) ∈ _)]

@[simp]
protected lemma union_self (G : Graph α β) : G ∪ G = G :=
  (Graph.union_le le_rfl le_rfl).antisymm <| Graph.left_le_union dup_agree_rfl ..

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
