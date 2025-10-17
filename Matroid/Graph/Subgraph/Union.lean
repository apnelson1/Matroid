import Matroid.Graph.Subgraph.Compatible
import Matroid.ForMathlib.Partition.Foo

variable {α β ι ι' : Type*} [Order.Frame α] {x y z u v w : α} {G G₁ G₂ H H₁ H₂ : Graph α β}
  {e f : β} {F F₁ F₂ : Set β} {X Y : Set α} {Gs Hs : Set (Graph α β)} {P Q : Partition α}
  {Gι Hι : ι → Graph α β} {Gι' Hι' : ι' → Graph α β}

open Set Function Partition

namespace Graph


/-! ### Set unions -/

/-- The union of a set of pairwise compatible graphs. -/
@[simps! vertexPartition]
protected def sUnion (s : Set (Graph α β)) : Graph α β where
  vertexPartition := ⨆ G ∈ s, P(G)
  IsLink e x y := s.Pairwise (CompatibleAt e) ∧ (⨆ G ∈ s, P(G)).fuzzyRel (⨆ G ∈ s, G.IsLink e) x y
  edgeSet := {e | s.Pairwise (CompatibleAt e) ∧ ∃ G ∈ s, e ∈ E(G)}
  edge_mem_iff_exists_isLink e := by
    simp only [edge_mem_iff_exists_isLink, mem_setOf_eq, exists_and_left, and_congr_right_iff]
    rintro he
    refine ⟨fun ⟨G, hGs, x, y, hGxy⟩ => ?_, fun ⟨x, y, hxy⟩ => ?_⟩
    · rw [← fuzzyRel.stuff (le_biSup _ hGs) ?_]
      simp only [iSup_apply, iSup_Prop_eq, exists_prop]
      use x, y, G, hGs
      · simp only [iSup_apply, iSup_Prop_eq, exists_prop, mem_vertexPartition_iff,
        forall_exists_index, and_imp]
        rintro a b H hHs hHab
        have := hHab.of_compatibleAt (he.of_refl hHs hGs) hGxy.edge_mem
        use this.left_mem, this.right_mem
    · simp only [fuzzyRel, iSup_apply, iSup_Prop_eq, exists_prop] at hxy
      obtain ⟨hx, hy, u, v, ⟨G, hGs, huv⟩, hux, hvy⟩ := hxy
      use G, hGs, u, v
  isLink_symm e he u v := by
    rintro ⟨he, hxy⟩
    use he
    apply hxy.symmetric _
    rw [← sSup_image]
    refine Relation.sSup_symmtric fun r ⟨G, hGs, hGr⟩ ↦ ?_
    subst r
    exact instIsSymmIsLink
  eq_or_eq_of_isLink_of_isLink e a b c d := by
    rintro ⟨he, ha, hb, u, v, huv, hua, -⟩ ⟨-, hc, hd, u', v', hu'v', hu'c, hv'd⟩
    simp only [iSup_apply, iSup_Prop_eq, exists_prop] at huv hu'v'
    obtain ⟨G, hG, huv⟩ := huv
    obtain ⟨G', hG', hu'v'⟩ := hu'v'
    apply (G.eq_or_eq_of_isLink_of_isLink huv <| hu'v'.of_compatibleAt (he.of_refl hG' hG)
      huv.edge_mem).imp <;> rintro rfl <;> exact (⨆ G ∈ s, P(G)).eq_of_not_disjoint ha
      (by assumption) <| not_disjoint_of_le_le hua (by assumption) (G.ne_bot_of_mem huv.left_mem)
  left_mem_of_isLink e a b h := h.2.1

@[simp]
lemma sUnion_vertexSet (hs' : Gs.Pairwise Dup_agree) : V(Graph.sUnion Gs) = ⋃ G ∈ Gs, V(G) := by
  rw [← Graph.vertexSet_eq_parts, sUnion_vertexPartition, ← sSup_image, sSup_parts_of_agree]
  simp_rw [← sUnion_image, image_image, Graph.vertexSet_eq_parts]
  rwa [← pairwise_dup_agree_eq_pairwise_image]

@[simp]
lemma sUnion_isLink_of_not_compat (hs' : Gs.Pairwise Dup_agree) :
    (Graph.sUnion Gs).IsLink e x y ↔ Gs.Pairwise (CompatibleAt e) ∧ ∃ G ∈ Gs, G.IsLink e x y := by
  have : ∀ (a b : α), (⨆ G ∈ Gs, G.IsLink e) a b → a ∈ ⨆ G ∈ Gs, P(G) ∧ b ∈ ⨆ G ∈ Gs, P(G) := by
    simp only [iSup_apply, iSup_Prop_eq, exists_prop, ← sSup_image, ← mem_parts,
      sSup_parts_of_agree (pairwise_dup_agree_eq_pairwise_image.mp hs'), mem_image, iUnion_exists,
      biUnion_and', iUnion_iUnion_eq_right, vertexPartition_parts, mem_iUnion, forall_exists_index,
      and_imp]
    refine fun a b G hGs hab => ⟨?_, ?_⟩ <;> use G, hGs, by simp [hab.left_mem, hab.right_mem]
  simp [Graph.sUnion, fuzzyRel.eq_self.mpr this]

@[simp]
lemma sUnion_isLink (hs : Gs.Pairwise Graph.Compatible) (hs' : Gs.Pairwise Dup_agree) :
    (Graph.sUnion Gs).IsLink e x y ↔ ∃ G ∈ Gs, G.IsLink e x y := by
  simp [sUnion_isLink_of_not_compat hs', hs]

lemma sUnion_isLink_not_agree (hs : Gs.Pairwise Graph.Compatible) :
    (Graph.sUnion Gs).IsLink e x y ↔ (⨆ G ∈ Gs, P(G)).fuzzyRel (⨆ G ∈ Gs, G.IsLink e) x y := by
  simp [Graph.sUnion, hs]

@[simp]
lemma sUnion_edgeSet (hs : Gs.Pairwise Graph.Compatible) : E(Graph.sUnion Gs) = ⋃ G ∈ Gs, E(G) := by
  ext e
  simp only [edgeSet_eq_setOf_exists_isLink, sUnion_isLink_not_agree hs, fuzzyRel, iSup_apply,
    iSup_Prop_eq, exists_prop, exists_and_left, mem_setOf_eq, mem_iUnion]
  refine ⟨fun ⟨x, hx, y, hy, u, v, ⟨G, hGs, huv⟩, hux, hvy⟩ => ⟨G, hGs, u, v, huv⟩,
    fun ⟨G, hGs, u, v, huv⟩ => ?_⟩
  let f := leFun <| le_biSup Graph.vertexPartition hGs
  exact ⟨f ⟨u, huv.left_mem'⟩, Subtype.prop _, f ⟨v, huv.right_mem'⟩, Subtype.prop _, u, v,
    (by use G), le_leFun _ ⟨u, huv.left_mem'⟩, le_leFun _ ⟨v, huv.right_mem'⟩⟩

protected lemma le_sUnion (hs : Gs.Pairwise Graph.Compatible) (hs' : Gs.Pairwise Dup_agree)
    (hG : G ∈ Gs) : G ≤ Graph.sUnion Gs where
  vertexSet_subset := by
    rw [sUnion_vertexSet hs']
    exact subset_biUnion_of_mem hG
  isLink_of_isLink e x y h := by
    rw [sUnion_isLink hs hs']
    use G

@[simp]
protected lemma sUnion_le_iff (hs : Gs.Pairwise Graph.Compatible) (hs' : Gs.Pairwise Dup_agree) :
    Graph.sUnion Gs ≤ H ↔ ∀ G ∈ Gs, G ≤ H := by
  simp only [le_iff, sUnion_vertexSet hs', iUnion_subset_iff, sUnion_isLink hs hs',
    forall_exists_index, and_imp]
  exact ⟨fun h G hGs => ⟨h.1 G hGs, fun _ _ _ => h.2 G hGs⟩,
    fun h => ⟨fun G hGs => (h G hGs).1, fun e x y G hGs H => (h G hGs).2 H⟩⟩

@[simp]
lemma sUnion_inc_iff (hs : Gs.Pairwise Graph.Compatible) (hs' : Gs.Pairwise Dup_agree) :
    (Graph.sUnion Gs).Inc e x ↔ ∃ G ∈ Gs, G.Inc e x := by
  simp only [Inc, hs, hs', sUnion_isLink]
  tauto

@[simp]
lemma sUnion_isLoopAt_iff (hs : Gs.Pairwise Graph.Compatible) (hs' : Gs.Pairwise Dup_agree) :
    (Graph.sUnion Gs).IsLoopAt e x ↔ ∃ G ∈ Gs, G.IsLoopAt e x := by
  simp [← isLink_self_iff, hs, hs']

@[simp]
lemma sUnion_isNonloopAt_iff (hs : Gs.Pairwise Graph.Compatible) (hs' : Gs.Pairwise Dup_agree) :
    (Graph.sUnion Gs).IsNonloopAt e x ↔ ∃ G ∈ Gs, G.IsNonloopAt e x := by
  simp only [isNonloopAt_iff_inc_not_isLoopAt, hs, hs', sUnion_inc_iff, sUnion_isLoopAt_iff,
    not_exists, not_and]
  exact ⟨fun ⟨⟨G, hGs, hG⟩, h⟩ => ⟨G, hGs, hG, h G hGs⟩, fun ⟨G, hGs, hG, h⟩ =>
    ⟨⟨G, hGs, hG⟩, fun H hHs hH ↦ h <| hH.of_compatible (hs.of_refl hGs hHs).symm hG.edge_mem⟩⟩

@[simp]
protected lemma sUnion_singleton (G : Graph α β) : Graph.sUnion {G} = G := by
  ext <;> simp

/-! ### Indexed unions -/

/-- The union of an indexed family of pairwise compatible graphs. -/
protected def iUnion (G : ι → Graph α β) : Graph α β := Graph.sUnion (Set.range G)

@[simp]
lemma iUnion_vertexPartition : P(Graph.iUnion Gι) = ⨆ i, P(Gι i) := by
  rw [Graph.iUnion, sUnion_vertexPartition, iSup_range]

@[simp]
lemma iUnion_vertexSet (hG : Pairwise (Dup_agree on Gι)) : V(Graph.iUnion Gι) = ⋃ i, V(Gι i) := by
  simp [Graph.iUnion, sUnion_vertexSet hG.range_pairwise]

@[simp]
lemma iUnion_isLink (hG : Pairwise (Graph.Compatible on Gι)) (hG' : Pairwise (Dup_agree on Gι)) :
    (Graph.iUnion Gι).IsLink e x y ↔ ∃ i, (Gι i).IsLink e x y := by
  simp [Graph.iUnion, sUnion_isLink hG.range_pairwise hG'.range_pairwise]

@[simp]
lemma iUnion_edgeSet (hG : Pairwise (Graph.Compatible on Gι)) :
    E(Graph.iUnion Gι) = ⋃ i, E(Gι i) := by
  simp [Graph.iUnion, sUnion_edgeSet hG.range_pairwise]

protected lemma le_iUnion (hG : Pairwise (Graph.Compatible on Gι))
    (hG' : Pairwise (Dup_agree on Gι)) (i : ι) : Gι i ≤ Graph.iUnion Gι :=
  Graph.le_sUnion hG.range_pairwise hG'.range_pairwise (by use i)

@[simp]
protected lemma iUnion_le_iff (hG : Pairwise (Graph.Compatible on Gι))
    (hG' : Pairwise (Dup_agree on Gι)) : Graph.iUnion Gι ≤ H ↔ ∀ i, Gι i ≤ H := by
  convert Graph.sUnion_le_iff hG.range_pairwise hG'.range_pairwise
  simp

@[simp]
protected lemma iUnion_const [Nonempty ι] (G : Graph α β) : Graph.iUnion (fun (_ : ι)↦ G) = G := by
  refine le_antisymm ?_ <| Graph.le_iUnion (Pairwise.const_of_refl G) (Pairwise.const_of_refl G)
    (Classical.arbitrary ι)
  rw [Graph.iUnion_le_iff (Pairwise.const_of_refl G) (Pairwise.const_of_refl G)]
  exact fun i ↦ le_refl G

@[simp]
lemma iUnion_inc_iff (hG : Pairwise (Graph.Compatible on Gι)) (hG' : Pairwise (Dup_agree on Gι)) :
    (Graph.iUnion Gι).Inc e x ↔ ∃ i, (Gι i).Inc e x := by
  simp [Graph.iUnion, sUnion_inc_iff hG.range_pairwise hG'.range_pairwise]

@[simp]
lemma iUnion_isLoopAt_iff (hG : Pairwise (Graph.Compatible on Gι))
    (hG' : Pairwise (Dup_agree on Gι)) :
    (Graph.iUnion Gι).IsLoopAt e x ↔ ∃ i, (Gι i).IsLoopAt e x := by
  simp [← isLink_self_iff, hG, hG']

@[simp]
lemma iUnion_isNonloopAt_iff (hG : Pairwise (Graph.Compatible on Gι))
    (hG' : Pairwise (Dup_agree on Gι)) :
    (Graph.iUnion Gι).IsNonloopAt e x ↔ ∃ i, (Gι i).IsNonloopAt e x := by
  simp only [IsNonloopAt, ne_eq, iUnion_isLink hG hG']
  aesop

lemma iUnion_map_le_iUnion (hG : Pairwise (Graph.Compatible on Gι))
    (hG' : Pairwise (Dup_agree on Gι)) (f : ι' → ι): (Graph.iUnion (Gι ∘ f)) ≤ Graph.iUnion Gι := by
  rw [Graph.iUnion_le_iff (hG.onFun_comp_of_refl f) (hG'.onFun_comp_of_refl f)]
  exact fun i ↦ Graph.le_iUnion hG hG' (f i)

lemma iUnion_left_le_iUnion_sum (hGH : Pairwise (Graph.Compatible on Sum.elim Gι Gι'))
    (hGH' : Pairwise (Dup_agree on Sum.elim Gι Gι')) :
    Graph.iUnion Gι ≤ Graph.iUnion (Sum.elim Gι Gι') := by
  rw [Graph.iUnion_le_iff hGH.sum_left hGH'.sum_left]
  exact fun i ↦ le_trans (by simp) (Graph.le_iUnion hGH hGH' (Sum.inl i))

lemma iUnion_right_le_iUnion_sum (hGH : Pairwise (Graph.Compatible on Sum.elim Gι Gι'))
    (hGH' : Pairwise (Dup_agree on Sum.elim Gι Gι')) :
    Graph.iUnion Gι' ≤ Graph.iUnion (Sum.elim Gι Gι') := by
  rw [Graph.iUnion_le_iff hGH.sum_right hGH'.sum_right]
  exact fun i ↦ le_trans (by simp) (Graph.le_iUnion hGH hGH' (Sum.inr i))

@[simp]
lemma induce_iUnion [Nonempty ι] (hG : Pairwise (Graph.Compatible on Gι))
    (hG' : Pairwise (Dup_agree on Gι)) (P : Set α) :
    (Graph.iUnion Gι)[P] = Graph.iUnion (fun i ↦ (Gι i)[P]) := by
  refine Graph.ext ?_ ?_
  · rw [iUnion_vertexSet (hG'.mono (fun _ _ ↦ Dup_agree.induce P))]
    simp [iUnion_vertexSet hG', iUnion_inter]
  · rintro e x y
    rw [induce_isLink, iUnion_isLink hG hG', iUnion_isLink
      (hG.mono (fun _ _ ↦ Compatible.induce)) (Pairwise.induce_dup_agree hG' P)]
    simp

@[simp]
lemma Compatible.vertexDelete_iUnion (hG : Pairwise (Graph.Compatible on Gι))
    (hG' : Pairwise (Dup_agree on Gι)) (X : Set α) :
    (Graph.iUnion Gι) - X = Graph.iUnion (fun i ↦ (Gι i) - X) := by
  refine Graph.ext ?_ fun e x y ↦ ?_
  · rw [iUnion_vertexSet (hG'.mono (fun _ _ ↦ Dup_agree.vertexDelete X))]
    simp [iUnion_diff, iUnion_vertexSet hG']
  · rw [vertexDelete_isLink_iff, iUnion_isLink hG hG', iUnion_isLink
      (hG.mono (fun _ _ ↦ Compatible.vertexDelete))
      (hG'.mono (fun _ _ ↦ Dup_agree.vertexDelete X))]
    simp

@[simp]
lemma Compatible.edgeDelete_iUnion (hG : Pairwise (Graph.Compatible on Gι))
    (hG' : Pairwise (Dup_agree on Gι)) (F : Set β) :
    (Graph.iUnion Gι) ＼ F = .iUnion (fun i ↦ (Gι i) ＼ F) := by
  refine Graph.ext ?_ fun e x y ↦ ?_
  · rw [iUnion_vertexSet (hG'.mono (fun _ _ ↦ Dup_agree.edgeDelete F))]
    simp [iUnion_vertexSet hG']
  · rw [edgeDelete_isLink, iUnion_isLink hG hG', iUnion_isLink
      (hG.mono (fun _ _ ↦ Compatible.edgeDelete))
      (hG'.mono (fun _ _ ↦ Dup_agree.edgeDelete F))]
    simp

@[simp]
lemma Compatible.edgeRestrict_iUnion (hG : Pairwise (Graph.Compatible on Gι))
    (hG' : Pairwise (Dup_agree on Gι)) (F : Set β) :
    (Graph.iUnion Gι) ↾ F = .iUnion (fun i ↦ (Gι i) ↾ F) := by
  refine Graph.ext ?_ fun e x y ↦ ?_
  · rw [iUnion_vertexSet (hG'.mono (fun _ _ ↦ Dup_agree.edgeRestrict F))]
    simp [iUnion_vertexSet hG']
  · rw [edgeRestrict_isLink, iUnion_isLink hG hG', iUnion_isLink
      (hG.mono (fun _ _ ↦ Compatible.edgeRestrict))
      (hG'.mono (fun _ _ ↦ Dup_agree.edgeRestrict F))]
    simp

protected lemma iUnion_comp_le {f : ι' → ι} (hG : Pairwise (Compatible on Gι))
    (hG' : Pairwise (Dup_agree on Gι)) : Graph.iUnion (fun i ↦ Gι (f i)) ≤ Graph.iUnion Gι := by
  change Graph.iUnion (Gι ∘ f) ≤ Graph.iUnion Gι
  rw [Graph.iUnion_le_iff (hG.onFun_comp_of_refl f) (hG'.onFun_comp_of_refl f)]
  exact fun i ↦ Graph.le_iUnion hG hG' (f i)

lemma iUnion_comp_eq_of_surj {f : ι' → ι} (hG : Pairwise (Compatible on Gι))
    (hG' : Pairwise (Dup_agree on Gι)) (hf : Function.Surjective f) :
    Graph.iUnion Gι = Graph.iUnion (fun i ↦ Gι (f i)) := by
  refine le_antisymm ?_ (Graph.iUnion_comp_le hG hG')
  rw [Graph.iUnion_le_iff hG hG']
  rintro i
  obtain ⟨i', rfl⟩ := hf i
  exact Graph.le_iUnion (hG.onFun_comp_of_refl f) (hG'.onFun_comp_of_refl f) i'

lemma iUnion_range {f : ι' → ι} {Gf : (Set.range f) → Graph α β}
    (hG : Pairwise (Graph.Compatible on Gf)) (hG' : Pairwise (Dup_agree on Gf)) :
    Graph.iUnion Gf = Graph.iUnion (Gf <| Set.rangeFactorization f ·) :=
  iUnion_comp_eq_of_surj hG hG' rangeFactorization_surjective


/-! ### Unions of pairs -/

/-- The union of two graphs `G` and `H`. If there is an edge `e` whose `G`-ends differ from
its `H`-ends, then `G` is favoured, so this is not commutative in general.
If `G` and `H` are `Compatible`, this doesn't occur.
We define this in terms of `sUnion` and `Graph.copy` so the vertex and edge sets are
definitionally unions. -/
-- @[simps! vertexPartition edgeSet]
protected def union (G H : Graph α β) := Graph.copy (P := P(G) ⊔ P(H)) (X := (P(G) ⊔ P(H)).parts)
  (E := E(G) ∪ E(H)) (Graph.sUnion {G, H ＼ E(G)}) (by
    rw [sUnion_vertexPartition, ← sSup_image, image_pair]; simp)
    (by rw [← Graph.vertexPartition_parts, sUnion_vertexPartition, ← sSup_image, image_pair]; simp)
    (by rw [sUnion_edgeSet pairwise_compatible_edgeDelete]; simp)
    (fun e x y ↦ by rw [sUnion_isLink_not_agree pairwise_compatible_edgeDelete])

instance : Union (Graph α β) where union := Graph.union

variable {G H H₁ H₂ : Graph α β}

@[simp] lemma union_vertexPartition (G H : Graph α β) : P(G ∪ H) = P(G) ⊔ P(H) := rfl

private lemma union_vertexPartition_supp : P(G ∪ H).supp = P(G).supp ⊔ P(H).supp := by
  simp

@[simp] lemma union_edgeSet (G H : Graph α β) : E(G ∪ H) = E(G) ∪ E(H) := rfl

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

lemma union_isLink_not_agree : (G ∪ H).IsLink e =
    (P(G) ⊔ P(H ＼ E(G))).fuzzyRel (G.IsLink e ⊔ (H ＼ E(G)).IsLink e) := by
  ext x y
  simp_rw [union_eq_sUnion, sUnion_isLink_not_agree pairwise_compatible_edgeDelete, ← sSup_image,
    image_pair, sSup_pair]

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

private lemma subset_union_supp_of_mem_left (h : u ∈ V(G)) : u ≤ P(G ∪ H).supp :=
  le_trans (le_supp_of_mem <| mem_vertexPartition_iff.mpr h) (supp_le_of_le le_sup_left)

private lemma subset_union_supp_of_mem_right (h : u ∈ V(H)) : u ≤ P(G ∪ H).supp :=
  le_trans (le_supp_of_mem <| mem_vertexPartition_iff.mpr h) (supp_le_of_le le_sup_right)

lemma union_union_isLink_not_agree {G₁ G₂ G₃ : Graph α β} : (G₁ ∪ G₂ ∪ G₃).IsLink e =
    P(G₁ ∪ G₂ ∪ G₃).fuzzyRel (G₁.IsLink e) ⊔ P(G₁ ∪ G₂ ∪ G₃).fuzzyRel ((G₂ ＼ E(G₁)).IsLink e) ⊔
    P(G₁ ∪ G₂ ∪ G₃).fuzzyRel ((G₃ ＼ E(G₁ ∪ G₂)).IsLink e) := by
  simp_rw [union_isLink_not_agree, fuzzyRel.sup_right]
  congr 2 <;> rw [← fuzzyRel.eq_self.mpr Graph.forall_isLink_mem] <;>
    exact fuzzyRel.fuzzyRel₃_eq_fuzzyRel₂_of_le_le (by simp) le_sup_left

lemma union_union_isLink_not_agree' {G₁ G₂ G₃ : Graph α β} : (G₁ ∪ (G₂ ∪ G₃)).IsLink e =
    P(G₁ ∪ G₂ ∪ G₃).fuzzyRel (G₁.IsLink e) ⊔ (P(G₁ ∪ G₂ ∪ G₃).fuzzyRel ((G₂ ＼ E(G₁)).IsLink e) ⊔
    P(G₁ ∪ G₂ ∪ G₃).fuzzyRel ((G₃ ＼ E(G₁ ∪ G₂)).IsLink e)) := by
  have : (fun _ _ => False : α → α → Prop) = ⊥ := rfl
  have hP : P(G₁ ∪ G₂ ∪ G₃) = P(G₁ ∪ (G₂ ∪ G₃)) := by simp [union_vertexPartition, sup_assoc]
  simp_rw [union_isLink_not_agree, fuzzyRel.sup_right, edgeDelete_isLink_eq, hP]
  by_cases he : e ∈ E(G₁)
  · simp [← sup_assoc, this, he]
  simp only [he, not_false_eq_true, and_true, union_edgeSet, mem_union, false_or]
  congr 2
  simp_rw [union_isLink_not_agree, fuzzyRel.sup_right, edgeDelete_isLink_eq]
  congr 1 <;> rw [← fuzzyRel.eq_self.mpr Graph.forall_isLink_mem]
  · exact fuzzyRel.fuzzyRel₃_eq_fuzzyRel₂_of_le_le le_sup_left le_sup_right
  simp only [← fuzzyRel.and_const]
  exact fuzzyRel.fuzzyRel₃_eq_fuzzyRel₂_of_le_le le_sup_right le_sup_right

protected lemma union_assoc (G₁ G₂ G₃ : Graph α β) : (G₁ ∪ G₂) ∪ G₃ = G₁ ∪ (G₂ ∪ G₃) := by
  refine Graph.ext ?_ fun e x y ↦ ?_
  · simp_rw [← vertexSet_eq_parts, union_vertexPartition, sup_assoc]
  rw [union_union_isLink_not_agree, union_union_isLink_not_agree', sup_assoc]

lemma union_eq_union_edgeDelete (G H : Graph α β) : G ∪ H = G ∪ (H ＼ E(G)) := by
  simp [union_eq_sUnion]

@[simp]
lemma left_vertexPartition_le_union : P(G) ≤ P(G ∪ H) := by
  simp [union_vertexPartition]

@[simp]
lemma right_vertexPartition_le_union : P(H) ≤ P(G ∪ H) := by
  simp [union_vertexPartition]

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

lemma isLink_or_isLink_of_union (hG' : G.Dup_agree H) (h : (G ∪ H).IsLink e x y) :
    G.IsLink e x y ∨ H.IsLink e x y :=
  ((union_isLink hG').1 h).elim .inl fun h' ↦ .inr h'.1

lemma Compatible.union_isLink (h : G.Compatible H) (hG' : G.Dup_agree H) :
    (G ∪ H).IsLink e x y ↔ G.IsLink e x y ∨ H.IsLink e x y := by
  by_cases heG : e ∈ E(G)
  · simp only [Graph.union_isLink hG', heG, not_true_eq_false, and_false, or_false, iff_self_or]
    exact fun he ↦ by rwa [h.isLink_eq heG he.edge_mem]
  simp [heG, Graph.union_isLink hG']

lemma edgeRestrict_union (G : Graph α β) (F₁ F₂ : Set β) : (G ↾ (F₁ ∪ F₂)) = G ↾ F₁ ∪ (G ↾ F₂) := by
  have hG' : (G ↾ F₁).Dup_agree (G ↾ F₂) := dup_agree_rfl
  refine Graph.ext (by simp [hG']) fun e x y ↦ ?_
  rw [(G.compatible_self.mono (by simp) (by simp)).union_isLink hG']
  simp only [edgeRestrict_isLink, mem_union]
  tauto

lemma union_edgeRestrict_distrib (G H : Graph α β) (F : Set β) : (G ∪ H) ↾ F = G ↾ F ∪ (H ↾ F) :=
  Graph.ext rfl fun e x y ↦ by
  by_cases he : e ∈ F <;> simp [union_isLink_not_agree, edgeRestrict_isLink_eq, and_comm,
    he, edgeDelete_isLink_eq]

lemma Compatible.union_eq_sUnion (h : G.Compatible H) (hG' : G.Dup_agree H) :
    G ∪ H = Graph.sUnion {G, H} :=
  Graph.ext (by simp [hG', hG'.pair]) fun e x y ↦ by
    simp [h.union_isLink hG', sUnion_isLink h.pair hG'.pair]

lemma Compatible.union_inc_iff (h : G.Compatible H) (hG' : G.Dup_agree H) :
    (G ∪ H).Inc e x ↔ G.Inc e x ∨ H.Inc e x := by
  simp_rw [Inc, h.union_isLink hG']
  aesop

lemma Compatible.union_isLoopAt_iff (h : G.Compatible H) (hG' : G.Dup_agree H) :
    (G ∪ H).IsLoopAt e x ↔ G.IsLoopAt e x ∨ H.IsLoopAt e x := by
  simp_rw [← isLink_self_iff, h.union_isLink hG']

lemma Compatible.union_isNonloopAt_iff (h : G.Compatible H) (hG' : G.Dup_agree H) :
    (G ∪ H).IsNonloopAt e x ↔ G.IsNonloopAt e x ∨ H.IsNonloopAt e x := by
  simp_rw [IsNonloopAt, h.union_isLink hG']
  aesop

lemma Compatible.union_adj_iff (h : G.Compatible H) (hG' : G.Dup_agree H) :
    (G ∪ H).Adj x y ↔ G.Adj x y ∨ H.Adj x y := by
  simp [Adj, h.union_isLink hG', exists_or]

lemma Compatible.union_comm (h : Compatible G H) (hG' : G.Dup_agree H) : G ∪ H = H ∪ G :=
  Graph.ext (by simp [hG', hG'.symm, Set.union_comm])
    fun _ _ _ ↦ by rw [h.union_isLink hG', h.symm.union_isLink hG'.symm, or_comm]

lemma Compatible.union_le_iff (h_compat : H₁.Compatible H₂) (hG' : H₁.Dup_agree H₂) :
    H₁ ∪ H₂ ≤ G ↔ H₁ ≤ G ∧ H₂ ≤ G := by
  simp [h_compat.union_eq_sUnion hG', h_compat.pair, hG'.pair]

lemma Compatible.right_le_union (h : G.Compatible H) (hG' : G.Dup_agree H) : H ≤ G ∪ H := by
  simp [h.union_comm hG', hG'.symm]

lemma union_eq_self_of_le_left (hle : G ≤ H) : G ∪ H = H :=
  (Graph.union_le hle rfl.le).antisymm <| (H.compatible_self.mono_left hle).right_le_union <|
    dup_agree_of_le hle

lemma union_eq_self_of_le_right (hle : G ≤ H) : H ∪ G = H :=
  (Graph.union_le rfl.le hle).antisymm <| Graph.left_le_union (dup_agree_of_le hle).symm ..

lemma Compatible.union_mono_left (h : H₂.Compatible G) (hle : H₁ ≤ H₂) (h₁ : H₁.Dup_agree G)
    (h₂ : H₂.Dup_agree G) : H₁ ∪ G ≤ H₂ ∪ G := by
  rw [h.union_comm h₂, (h.mono_left hle).union_comm h₁]
  exact union_mono_right h₁.symm h₂.symm hle

lemma Compatible.union_mono (hleG : G₁ ≤ G₂) (hleH : H₁ ≤ H₂) (h : G₂.Compatible H₁)
    (h₂ : G₂.Dup_agree H₂) : G₁ ∪ H₁ ≤ G₂ ∪ H₂ := by
  have h₂₁ : G₂.Dup_agree H₁ := h₂.mono_right hleH
  have h₁ : G₁.Dup_agree H₁ := h₂₁.mono_left hleG
  exact le_trans (h.union_mono_left hleG h₁ h₂₁) (union_mono_right h₂₁ h₂ hleH)

lemma edgeRestrict_union_edgeDelete (G : Graph α β) (F : Set β) : (G ↾ F) ∪ (G ＼ F) = G := by
  rw [edgeDelete_eq_edgeRestrict, ← edgeRestrict_union, ← edgeRestrict_inter_edgeSet]
  simp only [union_diff_self, edgeRestrict_inter_edgeSet, edgeRestrict_union, edgeRestrict_self]
  exact union_eq_self_of_le_left (by simp)

lemma edgeDelete_union_edgeRestrict (G : Graph α β) (F : Set β) : (G ＼ F) ∪ (G ↾ F) = G := by
  convert G.edgeRestrict_union_edgeDelete F using 1
  rw [Compatible.union_comm (G.compatible_of_le_le (by simp) (by simp)) (by exact dup_agree_rfl)]

lemma induce_union_edgeDelete (G : Graph α β) : G[P] ∪ (G ＼ E(G[P])) = G := by
  rw [← union_eq_union_edgeDelete, union_eq_self_of_le_left induce_le]

lemma edgeDelete_union_induce (G : Graph α β) : (G ＼ E(G[P])) ∪ G[P] = G := by
  rw [(Compatible.of_disjoint_edgeSet _).union_comm, induce_union_edgeDelete _]
  · exact agree_of_subset_subset subset_rfl (restrict_subset <| by simp)
  simp [disjoint_sdiff_left]

lemma Compatible.union_eq_iUnion (h : G.Compatible H) (hG' : G.Dup_agree H) :
    G ∪ H = Graph.iUnion (fun b ↦ bif b then G else H) := by
  have h' : Pairwise (Compatible on fun b ↦ bif b then G else H) := by
    simpa [pairwise_on_bool]
  have hG'' : Pairwise (Dup_agree on fun b ↦ bif b then G else H) := by
    simpa [pairwise_on_bool]
  simp only [le_antisymm_iff, h.union_le_iff hG', Graph.iUnion_le_iff h' hG'', Bool.forall_bool,
    cond_false, h.right_le_union hG', cond_true, Graph.left_le_union hG', and_self, and_true]
  exact ⟨Graph.le_iUnion h' hG'' true, Graph.le_iUnion h' hG'' false⟩

lemma Compatible.induce_union (h : G.Compatible H) (hG' : G.Dup_agree H) (P : Set α) :
    (G ∪ H)[P] = G[P] ∪ H[P] := by
  refine Graph.ext (by simp [hG', union_inter_distrib_right]) fun e x y ↦ ?_
  simp only [induce_isLink, h.union_isLink hG', h.induce.union_isLink (hG'.induce P)]
  tauto

lemma Compatible.vertexDelete_union (h : G.Compatible H) (hG' : G.Dup_agree H) (X : Set α) :
    (G ∪ H) - X = (G - X) ∪ (H - X) := by
  rw [h.union_eq_iUnion hG', vertexDelete_iUnion]
  simp [Bool.apply_cond (f := fun G ↦ G - X),
    ← h.vertexDelete.union_eq_iUnion (hG'.vertexDelete X)]
  all_goals simpa [pairwise_on_bool]

-- lemma induce_union (G : Graph α β) (hPQ : P.Agree Q) (hX : ∀ x ∈ P, ∀ y ∈ Q, ¬ G.Adj x y) :
--     G[P ⊔ Q] = G[P] ∪ G[Q] := by
--   refine Graph.ext ?_ fun e x y ↦ ?_
--   · rw [union_vertexSet]
--     simp [inter_union_distrib_left]
--     sorry
--   simp only [induce_isLink, hPQ.mem_sup_iff, Compatible.induce_induce.union_isLink hPQ]
--   by_cases hxy : G.IsLink e x y
--   · by_cases hx : x ∈ P
--     · simp [hx, show y ∉ Q from fun hy ↦ hX x hx y hy hxy.adj]
--     by_cases hy : y ∈ P
--     · simp [hy, show x ∉ Q from fun hx ↦ hX _ hy _ hx hxy.symm.adj, hxy]
--     simp [hx, hy]
--   simp [hxy]

-- lemma sUnion_insert (G : Graph α β) (s : Set (Graph α β))
-- (hG' : (insert G s).Pairwise Dup_agree) :
--     Graph.sUnion (insert G s) = G ∪ Graph.sUnion Gs := by
--   refine Graph.ext ?_ fun e x y ↦ ?_
--   · rw [union_vertexSet, Graph.sUnion_union]

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

-- @[simp]
-- lemma noEdge_union_eq_self : Graph.noEdge P β ∪ G = G ↔ P ≤ P(G) := by
--   refine ⟨fun h => ?_, fun h => ?_⟩
--   · rw [← h]
--     convert left_vertexPartition_le_union
--     rfl
--   refine vertexPartition_ext (by simpa) fun e x y ↦ ?_
--   simp only [union_isLink_not_agree, noEdge_edgeSet, mem_empty_iff_false, not_false_eq_true,
--     not_isLink_of_notMem_edgeSet, and_true, false_or, union_vertexPartition,
--noEdge_vertexPartition,
--     h, sup_of_le_right]
--   refine ⟨?_, fun h => ⟨x, y, h, foo_eq_self_of_mem h.left_mem',
--     foo_eq_self_of_mem h.right_mem'⟩⟩
--   rintro ⟨u, v, h, rfl, rfl⟩
--   rwa [foo_eq_self_of_mem h.left_mem', foo_eq_self_of_mem h.right_mem']

-- @[simp]
-- lemma union_noEdge_eq_self : G ∪ Graph.noEdge P β = G ↔ P ≤ P(G) := by
--   refine ⟨fun h => ?_, fun h => ?_⟩
--   · rw [← h]
--     convert right_vertexPartition_le_union
--     rfl
--   refine vertexPartition_ext (by simpa) fun e x y ↦ ?_
--   simp only [union_isLink_not_agree, noEdge_edgeSet, mem_empty_iff_false, not_false_eq_true,
--     not_isLink_of_notMem_edgeSet, false_and, or_false, union_vertexPartition,
--     noEdge_vertexPartition, h, sup_of_le_left]
--   refine ⟨?_, fun h => ⟨x, y, h, foo_eq_self_of_mem h.left_mem',
--     foo_eq_self_of_mem h.right_mem'⟩⟩
--   rintro ⟨u, v, h, rfl, rfl⟩
--   rwa [foo_eq_self_of_mem h.left_mem', foo_eq_self_of_mem h.right_mem']

end Graph
