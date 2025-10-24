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
def contractsUnion (s : Set (Graph α β)) : Graph α β where
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
lemma contractsUnion_vertexSet (hs' : Gs.Pairwise Dup_agree) :
    V(Graph.contractsUnion Gs) = ⋃ G ∈ Gs, V(G) := by
  rw [← Graph.vertexSet_eq_parts, contractsUnion_vertexPartition, ← sSup_image, sSup_parts_of_agree]
  simp_rw [← sUnion_image, image_image, Graph.vertexSet_eq_parts]
  rwa [← pairwise_dup_agree_eq_pairwise_image]

@[simp]
lemma contractsUnion_isLink_of_not_compat (hs' : Gs.Pairwise Dup_agree) :
    (Graph.contractsUnion Gs).IsLink e x y ↔
    Gs.Pairwise (CompatibleAt e) ∧ ∃ G ∈ Gs, G.IsLink e x y := by
  have : ∀ (a b : α), (⨆ G ∈ Gs, G.IsLink e) a b → a ∈ ⨆ G ∈ Gs, P(G) ∧ b ∈ ⨆ G ∈ Gs, P(G) := by
    simp only [iSup_apply, iSup_Prop_eq, exists_prop, ← sSup_image, ← mem_parts,
      sSup_parts_of_agree (pairwise_dup_agree_eq_pairwise_image.mp hs'), mem_image, iUnion_exists,
      biUnion_and', iUnion_iUnion_eq_right, vertexPartition_parts, mem_iUnion, forall_exists_index,
      and_imp]
    refine fun a b G hGs hab => ⟨?_, ?_⟩ <;> use G, hGs, by simp [hab.left_mem, hab.right_mem]
  simp [Graph.contractsUnion, fuzzyRel.eq_self.mpr this]

@[simp]
lemma contractsUnion_isLink (hs : Gs.Pairwise Graph.Compatible) (hs' : Gs.Pairwise Dup_agree) :
    (Graph.contractsUnion Gs).IsLink e x y ↔ ∃ G ∈ Gs, G.IsLink e x y := by
  simp [contractsUnion_isLink_of_not_compat hs', hs]

lemma contractsUnion_isLink_not_agree (hs : Gs.Pairwise Graph.Compatible) :
    (Graph.contractsUnion Gs).IsLink e x y ↔
    (⨆ G ∈ Gs, P(G)).fuzzyRel (⨆ G ∈ Gs, G.IsLink e) x y := by
  simp [Graph.contractsUnion, hs]

@[simp]
lemma contractsUnion_edgeSet (hs : Gs.Pairwise Graph.Compatible) :
    E(Graph.contractsUnion Gs) = ⋃ G ∈ Gs, E(G) := by
  ext e
  simp only [edgeSet_eq_setOf_exists_isLink, contractsUnion_isLink_not_agree hs, fuzzyRel,
    iSup_apply, iSup_Prop_eq, exists_prop, exists_and_left, mem_setOf_eq, mem_iUnion]
  refine ⟨fun ⟨x, hx, y, hy, u, v, ⟨G, hGs, huv⟩, hux, hvy⟩ => ⟨G, hGs, u, v, huv⟩,
    fun ⟨G, hGs, u, v, huv⟩ => ?_⟩
  let f := leFun <| le_biSup Graph.vertexPartition hGs
  exact ⟨f ⟨u, huv.left_mem'⟩, Subtype.prop _, f ⟨v, huv.right_mem'⟩, Subtype.prop _, u, v,
    (by use G), le_leFun _ ⟨u, huv.left_mem'⟩, le_leFun _ ⟨v, huv.right_mem'⟩⟩

lemma le_contractsUnion (hs : Gs.Pairwise Graph.Compatible) (hs' : Gs.Pairwise Dup_agree)
    (hG : G ∈ Gs) : G ≤ Graph.contractsUnion Gs where
  vertexSet_subset := by
    rw [contractsUnion_vertexSet hs']
    exact subset_biUnion_of_mem hG
  isLink_of_isLink e x y h := by
    rw [contractsUnion_isLink hs hs']
    use G

@[simp]
lemma contractsUnion_le_iff (hs : Gs.Pairwise Graph.Compatible)
    (hs' : Gs.Pairwise Dup_agree) : Graph.contractsUnion Gs ≤ H ↔ ∀ G ∈ Gs, G ≤ H := by
  simp only [le_iff, contractsUnion_vertexSet hs', iUnion_subset_iff, contractsUnion_isLink hs hs',
    forall_exists_index, and_imp]
  exact ⟨fun h G hGs => ⟨h.1 G hGs, fun _ _ _ => h.2 G hGs⟩,
    fun h => ⟨fun G hGs => (h G hGs).1, fun e x y G hGs H => (h G hGs).2 H⟩⟩

@[simp]
lemma contractsUnion_inc_iff (hs : Gs.Pairwise Graph.Compatible) (hs' : Gs.Pairwise Dup_agree) :
    (Graph.contractsUnion Gs).Inc e x ↔ ∃ G ∈ Gs, G.Inc e x := by
  simp only [Inc, hs, hs', contractsUnion_isLink]
  tauto

@[simp]
lemma contractsUnion_isLoopAt_iff (hs : Gs.Pairwise Graph.Compatible)
    (hs' : Gs.Pairwise Dup_agree) :
    (Graph.contractsUnion Gs).IsLoopAt e x ↔ ∃ G ∈ Gs, G.IsLoopAt e x := by
  simp [← isLink_self_iff, hs, hs']

@[simp]
lemma contractsUnion_isNonloopAt_iff (hs : Gs.Pairwise Graph.Compatible)
    (hs' : Gs.Pairwise Dup_agree) :
    (Graph.contractsUnion Gs).IsNonloopAt e x ↔ ∃ G ∈ Gs, G.IsNonloopAt e x := by
  simp only [isNonloopAt_iff_inc_not_isLoopAt, hs, hs', contractsUnion_inc_iff,
    contractsUnion_isLoopAt_iff, not_exists, not_and]
  exact ⟨fun ⟨⟨G, hGs, hG⟩, h⟩ => ⟨G, hGs, hG, h G hGs⟩, fun ⟨G, hGs, hG, h⟩ =>
    ⟨⟨G, hGs, hG⟩, fun H hHs hH ↦ h <| hH.of_compatible (hs.of_refl hGs hHs).symm hG.edge_mem⟩⟩

@[simp]
lemma contractsUnion_singleton (G : Graph α β) : Graph.contractsUnion {G} = G := by
  ext <;> simp

/-! ### Indexed unions -/

/-- The union of an indexed family of pairwise compatible graphs. -/
def contractiUnion (G : ι → Graph α β) : Graph α β := Graph.contractsUnion (Set.range G)

@[simp]
lemma contractiUnion_vertexPartition : P(Graph.contractiUnion Gι) = ⨆ i, P(Gι i) := by
  rw [Graph.contractiUnion, contractsUnion_vertexPartition, iSup_range]

@[simp]
lemma contractiUnion_vertexSet (hG : Pairwise (Dup_agree on Gι)) :
    V(Graph.contractiUnion Gι) = ⋃ i, V(Gι i) := by
  simp [Graph.contractiUnion, contractsUnion_vertexSet hG.range_pairwise]

@[simp]
lemma contractiUnion_isLink (hG : Pairwise (Graph.Compatible on Gι))
    (hG' : Pairwise (Dup_agree on Gι)) :
    (Graph.contractiUnion Gι).IsLink e x y ↔ ∃ i, (Gι i).IsLink e x y := by
  simp [Graph.contractiUnion, contractsUnion_isLink hG.range_pairwise hG'.range_pairwise]

@[simp]
lemma contractiUnion_edgeSet (hG : Pairwise (Graph.Compatible on Gι)) :
    E(Graph.contractiUnion Gι) = ⋃ i, E(Gι i) := by
  simp [Graph.contractiUnion, contractsUnion_edgeSet hG.range_pairwise]

lemma le_contractiUnion (hG : Pairwise (Graph.Compatible on Gι))
    (hG' : Pairwise (Dup_agree on Gι)) (i : ι) : Gι i ≤ Graph.contractiUnion Gι :=
  Graph.le_contractsUnion hG.range_pairwise hG'.range_pairwise (by use i)

@[simp]
lemma contractiUnion_le_iff (hG : Pairwise (Graph.Compatible on Gι))
    (hG' : Pairwise (Dup_agree on Gι)) : Graph.contractiUnion Gι ≤ H ↔ ∀ i, Gι i ≤ H := by
  convert Graph.contractsUnion_le_iff hG.range_pairwise hG'.range_pairwise
  simp

@[simp]
lemma contractiUnion_const [Nonempty ι] (G : Graph α β) :
    Graph.contractiUnion (fun (_ : ι)↦ G) = G := by
  refine le_antisymm ?_ <| Graph.le_contractiUnion (Pairwise.const_of_refl G)
    (Pairwise.const_of_refl G) (Classical.arbitrary ι)
  rw [Graph.contractiUnion_le_iff (Pairwise.const_of_refl G) (Pairwise.const_of_refl G)]
  exact fun i ↦ le_refl G

@[simp]
lemma contractiUnion_inc_iff (hG : Pairwise (Graph.Compatible on Gι))
    (hG' : Pairwise (Dup_agree on Gι)) :
    (Graph.contractiUnion Gι).Inc e x ↔ ∃ i, (Gι i).Inc e x := by
  simp [Graph.contractiUnion, contractsUnion_inc_iff hG.range_pairwise hG'.range_pairwise]

@[simp]
lemma contractiUnion_isLoopAt_iff (hG : Pairwise (Graph.Compatible on Gι))
    (hG' : Pairwise (Dup_agree on Gι)) :
    (Graph.contractiUnion Gι).IsLoopAt e x ↔ ∃ i, (Gι i).IsLoopAt e x := by
  simp [← isLink_self_iff, hG, hG']

@[simp]
lemma contractiUnion_isNonloopAt_iff (hG : Pairwise (Graph.Compatible on Gι))
    (hG' : Pairwise (Dup_agree on Gι)) :
    (Graph.contractiUnion Gι).IsNonloopAt e x ↔ ∃ i, (Gι i).IsNonloopAt e x := by
  simp only [IsNonloopAt, ne_eq, contractiUnion_isLink hG hG']
  aesop

lemma contractiUnion_map_le_contractiUnion (hG : Pairwise (Graph.Compatible on Gι))
    (hG' : Pairwise (Dup_agree on Gι)) (f : ι' → ι):
    (Graph.contractiUnion (Gι ∘ f)) ≤ Graph.contractiUnion Gι := by
  rw [Graph.contractiUnion_le_iff (hG.onFun_comp_of_refl f) (hG'.onFun_comp_of_refl f)]
  exact fun i ↦ Graph.le_contractiUnion hG hG' (f i)

lemma contractiUnion_left_le_contractiUnion_sum
    (hGH : Pairwise (Graph.Compatible on Sum.elim Gι Gι'))
    (hGH' : Pairwise (Dup_agree on Sum.elim Gι Gι')) :
    Graph.contractiUnion Gι ≤ Graph.contractiUnion (Sum.elim Gι Gι') := by
  rw [Graph.contractiUnion_le_iff hGH.sum_left hGH'.sum_left]
  exact fun i ↦ le_trans (by simp) (Graph.le_contractiUnion hGH hGH' (Sum.inl i))

lemma contractiUnion_right_le_contractiUnion_sum
    (hGH : Pairwise (Graph.Compatible on Sum.elim Gι Gι'))
    (hGH' : Pairwise (Dup_agree on Sum.elim Gι Gι')) :
    Graph.contractiUnion Gι' ≤ Graph.contractiUnion (Sum.elim Gι Gι') := by
  rw [Graph.contractiUnion_le_iff hGH.sum_right hGH'.sum_right]
  exact fun i ↦ le_trans (by simp) (Graph.le_contractiUnion hGH hGH' (Sum.inr i))

@[simp]
lemma induce_contractiUnion [Nonempty ι] (hG : Pairwise (Graph.Compatible on Gι))
    (hG' : Pairwise (Dup_agree on Gι)) (P : Set α) :
    (Graph.contractiUnion Gι)[P] = Graph.contractiUnion (fun i ↦ (Gι i)[P]) := by
  refine Graph.ext ?_ ?_
  · rw [contractiUnion_vertexSet (hG'.mono (fun _ _ ↦ Dup_agree.induce P))]
    simp [contractiUnion_vertexSet hG', iUnion_inter]
  · rintro e x y
    rw [induce_isLink, contractiUnion_isLink hG hG', contractiUnion_isLink
      (hG.mono (fun _ _ ↦ Compatible.induce)) (Pairwise.induce_dup_agree hG' P)]
    simp

@[simp]
lemma Compatible.vertexDelete_contractiUnion (hG : Pairwise (Graph.Compatible on Gι))
    (hG' : Pairwise (Dup_agree on Gι)) (X : Set α) :
    (Graph.contractiUnion Gι) - X = Graph.contractiUnion (fun i ↦ (Gι i) - X) := by
  refine Graph.ext ?_ fun e x y ↦ ?_
  · rw [contractiUnion_vertexSet (hG'.mono (fun _ _ ↦ Dup_agree.vertexDelete X))]
    simp [iUnion_diff, contractiUnion_vertexSet hG']
  · rw [vertexDelete_isLink_iff, contractiUnion_isLink hG hG', contractiUnion_isLink
      (hG.mono (fun _ _ ↦ Compatible.vertexDelete))
      (hG'.mono (fun _ _ ↦ Dup_agree.vertexDelete X))]
    simp

@[simp]
lemma Compatible.edgeDelete_contractiUnion (hG : Pairwise (Graph.Compatible on Gι))
    (hG' : Pairwise (Dup_agree on Gι)) (F : Set β) :
    (Graph.contractiUnion Gι) ＼ F = .contractiUnion (fun i ↦ (Gι i) ＼ F) := by
  refine Graph.ext ?_ fun e x y ↦ ?_
  · rw [contractiUnion_vertexSet (hG'.mono (fun _ _ ↦ Dup_agree.edgeDelete F))]
    simp [contractiUnion_vertexSet hG']
  · rw [edgeDelete_isLink, contractiUnion_isLink hG hG', contractiUnion_isLink
      (hG.mono (fun _ _ ↦ Compatible.edgeDelete))
      (hG'.mono (fun _ _ ↦ Dup_agree.edgeDelete F))]
    simp

@[simp]
lemma Compatible.edgeRestrict_contractiUnion (hG : Pairwise (Graph.Compatible on Gι))
    (hG' : Pairwise (Dup_agree on Gι)) (F : Set β) :
    (Graph.contractiUnion Gι) ↾ F = .contractiUnion (fun i ↦ (Gι i) ↾ F) := by
  refine Graph.ext ?_ fun e x y ↦ ?_
  · rw [contractiUnion_vertexSet (hG'.mono (fun _ _ ↦ Dup_agree.edgeRestrict F))]
    simp [contractiUnion_vertexSet hG']
  · rw [edgeRestrict_isLink, contractiUnion_isLink hG hG', contractiUnion_isLink
      (hG.mono (fun _ _ ↦ Compatible.edgeRestrict))
      (hG'.mono (fun _ _ ↦ Dup_agree.edgeRestrict F))]
    simp

lemma contractiUnion_comp_le {f : ι' → ι} (hG : Pairwise (Compatible on Gι))
    (hG' : Pairwise (Dup_agree on Gι)) :
    Graph.contractiUnion (fun i ↦ Gι (f i)) ≤ Graph.contractiUnion Gι := by
  change Graph.contractiUnion (Gι ∘ f) ≤ Graph.contractiUnion Gι
  rw [Graph.contractiUnion_le_iff (hG.onFun_comp_of_refl f) (hG'.onFun_comp_of_refl f)]
  exact fun i ↦ Graph.le_contractiUnion hG hG' (f i)

lemma contractiUnion_comp_eq_of_surj {f : ι' → ι} (hG : Pairwise (Compatible on Gι))
    (hG' : Pairwise (Dup_agree on Gι)) (hf : Function.Surjective f) :
    Graph.contractiUnion Gι = Graph.contractiUnion (fun i ↦ Gι (f i)) := by
  refine le_antisymm ?_ (Graph.contractiUnion_comp_le hG hG')
  rw [Graph.contractiUnion_le_iff hG hG']
  rintro i
  obtain ⟨i', rfl⟩ := hf i
  exact Graph.le_contractiUnion (hG.onFun_comp_of_refl f) (hG'.onFun_comp_of_refl f) i'

lemma contractiUnion_range {f : ι' → ι} {Gf : (Set.range f) → Graph α β}
    (hG : Pairwise (Graph.Compatible on Gf)) (hG' : Pairwise (Dup_agree on Gf)) :
    Graph.contractiUnion Gf = Graph.contractiUnion (Gf <| Set.rangeFactorization f ·) :=
  contractiUnion_comp_eq_of_surj hG hG' rangeFactorization_surjective


/-! ### Unions of pairs -/

/-- The union of two graphs `G` and `H`. If there is an edge `e` whose `G`-ends differ from
its `H`-ends, then `G` is favoured, so this is not commutative in general.
If `G` and `H` are `Compatible`, this doesn't occur.
We define this in terms of `contractsUnion` and `Graph.copy` so the vertex and edge sets are
definitionally unions. -/
def contractunion (G H : Graph α β) := Graph.copy (P := P(G) ⊔ P(H)) (X := (P(G) ⊔ P(H)).parts)
  (E := E(G) ∪ E(H)) (Graph.contractsUnion {G, H ＼ E(G)}) (by
    rw [contractsUnion_vertexPartition, ← sSup_image, image_pair]; simp)
    (by rw [← Graph.vertexPartition_parts, contractsUnion_vertexPartition, ← sSup_image,
      image_pair]; simp)
    (by rw [contractsUnion_edgeSet pairwise_compatible_edgeDelete]; simp)
    (fun e x y ↦ by rw [contractsUnion_isLink_not_agree pairwise_compatible_edgeDelete])

-- instance : Union (Graph α β) where union := Graph.contractunion
infix:100 " ∪ᶜ " => Graph.contractunion


variable {G H H₁ H₂ : Graph α β}

@[simp] lemma contractunion_vertexPartition (G H : Graph α β) : P(G ∪ᶜ H) = P(G) ⊔ P(H) := rfl

private lemma contractunion_vertexPartition_supp : P(G ∪ᶜ H).supp = P(G).supp ⊔ P(H).supp := by
  simp

@[simp] lemma contractunion_edgeSet (G H : Graph α β) : E(G ∪ᶜ H) = E(G) ∪ E(H) := rfl

lemma contractunion_eq_contractsUnion (G H : Graph α β) :
    G ∪ᶜ H = Graph.contractsUnion {G, H ＼ E(G)} := by
  simp_rw [Graph.contractunion]
  apply copy_eq_self

@[simp]
lemma contractunion_vertexSet (hG : G.Dup_agree H) : V(G ∪ᶜ H) = V(G) ∪ V(H) := by
  change (P(G) ⊔ P(H)).parts = V(G) ∪ V(H)
  rw [Agree.sup_parts hG, vertexPartition_parts, vertexPartition_parts]

@[simp]
lemma contractunion_isLink (hG' : G.Dup_agree H) :
    (G ∪ᶜ H).IsLink e x y ↔ G.IsLink e x y ∨ (H.IsLink e x y ∧ e ∉ E(G)) := by
  rw [contractunion_eq_contractsUnion,
    contractsUnion_isLink pairwise_compatible_edgeDelete hG'.pair_edgeDelete]
  simp

lemma contractunion_isLink_not_agree : (G ∪ᶜ H).IsLink e =
    (P(G) ⊔ P(H ＼ E(G))).fuzzyRel (G.IsLink e ⊔ (H ＼ E(G)).IsLink e) := by
  ext x y
  simp_rw [contractunion_eq_contractsUnion, contractsUnion_isLink_not_agree
    pairwise_compatible_edgeDelete, ← sSup_image, image_pair, sSup_pair]

lemma contractunion_inc_iff (hG' : G.Dup_agree H) :
    (G ∪ᶜ H).Inc e x ↔ G.Inc e x ∨ (H.Inc e x ∧ e ∉ E(G)) := by
  simp [contractunion_eq_contractsUnion, hG']

lemma contractunion_isLoopAt_iff (hG' : G.Dup_agree H) :
    (G ∪ᶜ H).IsLoopAt e x ↔ G.IsLoopAt e x ∨ (H.IsLoopAt e x ∧ e ∉ E(G)) := by
  simp [contractunion_eq_contractsUnion, hG']

lemma contractunion_isNonloopAt_iff (hG' : G.Dup_agree H) :
    (G ∪ᶜ H).IsNonloopAt e x ↔ G.IsNonloopAt e x ∨ (H.IsNonloopAt e x ∧ e ∉ E(G)) := by
  simp only [IsNonloopAt, ne_eq, contractunion_isLink hG']
  aesop

private lemma subset_contractunion_supp_of_mem_left (h : u ∈ V(G)) : u ≤ P(G ∪ᶜ H).supp :=
  le_trans (le_supp_of_mem <| mem_vertexPartition_iff.mpr h) (supp_le_of_le le_sup_left)

private lemma subset_contractunion_supp_of_mem_right (h : u ∈ V(H)) : u ≤ P(G ∪ᶜ H).supp :=
  le_trans (le_supp_of_mem <| mem_vertexPartition_iff.mpr h) (supp_le_of_le le_sup_right)

lemma contractunion_contractunion_isLink_not_agree {G₁ G₂ G₃ : Graph α β} :
    ((G₁ ∪ᶜ G₂) ∪ᶜ G₃).IsLink e = P((G₁ ∪ᶜ G₂) ∪ᶜ G₃).fuzzyRel (G₁.IsLink e) ⊔
    P((G₁ ∪ᶜ G₂) ∪ᶜ G₃).fuzzyRel ((G₂ ＼ E(G₁)).IsLink e) ⊔
    P((G₁ ∪ᶜ G₂) ∪ᶜ G₃).fuzzyRel ((G₃ ＼ E(G₁ ∪ᶜ G₂)).IsLink e) := by
  simp_rw [contractunion_isLink_not_agree, fuzzyRel.sup_right]
  congr 2 <;> rw [← fuzzyRel.eq_self.mpr Graph.forall_isLink_mem] <;>
    exact fuzzyRel.fuzzyRel₃_eq_fuzzyRel₂_of_le_le (by simp) le_sup_left

lemma contractunion_contractunion_isLink_not_agree' {G₁ G₂ G₃ : Graph α β} :
    (G₁ ∪ᶜ (G₂ ∪ᶜ G₃)).IsLink e = P((G₁ ∪ᶜ G₂) ∪ᶜ G₃).fuzzyRel (G₁.IsLink e) ⊔
    (P((G₁ ∪ᶜ G₂) ∪ᶜ G₃).fuzzyRel ((G₂ ＼ E(G₁)).IsLink e) ⊔
    P((G₁ ∪ᶜ G₂) ∪ᶜ G₃).fuzzyRel ((G₃ ＼ E(G₁ ∪ᶜ G₂)).IsLink e)) := by
  have : (fun _ _ => False : α → α → Prop) = ⊥ := rfl
  have hP : P((G₁ ∪ᶜ G₂) ∪ᶜ G₃) = P(G₁ ∪ᶜ (G₂ ∪ᶜ G₃)) := by
    simp [contractunion_vertexPartition, sup_assoc]
  simp_rw [contractunion_isLink_not_agree, fuzzyRel.sup_right, edgeDelete_isLink_eq, hP]
  by_cases he : e ∈ E(G₁)
  · simp [← sup_assoc, this, he]
  simp only [he, not_false_eq_true, and_true, contractunion_edgeSet, mem_union, false_or]
  congr 2
  simp_rw [contractunion_isLink_not_agree, fuzzyRel.sup_right, edgeDelete_isLink_eq]
  congr 1 <;> rw [← fuzzyRel.eq_self.mpr Graph.forall_isLink_mem]
  · exact fuzzyRel.fuzzyRel₃_eq_fuzzyRel₂_of_le_le le_sup_left le_sup_right
  simp only [← fuzzyRel.and_const]
  exact fuzzyRel.fuzzyRel₃_eq_fuzzyRel₂_of_le_le le_sup_right le_sup_right

lemma contractunion_assoc (G₁ G₂ G₃ : Graph α β) : (G₁ ∪ᶜ G₂) ∪ᶜ G₃ = G₁ ∪ᶜ (G₂ ∪ᶜ G₃) := by
  refine Graph.ext ?_ fun e x y ↦ ?_
  · simp_rw [← vertexSet_eq_parts, contractunion_vertexPartition, sup_assoc]
  rw [contractunion_contractunion_isLink_not_agree, contractunion_contractunion_isLink_not_agree',
    sup_assoc]

lemma contractunion_eq_contractunion_edgeDelete (G H : Graph α β) : G ∪ᶜ H = G ∪ᶜ (H ＼ E(G)) := by
  simp [contractunion_eq_contractsUnion]

@[simp]
lemma left_vertexPartition_le_contractunion : P(G) ≤ P(G ∪ᶜ H) := by
  simp [contractunion_vertexPartition]

@[simp]
lemma right_vertexPartition_le_contractunion : P(H) ≤ P(G ∪ᶜ H) := by
  simp [contractunion_vertexPartition]

@[simp]
lemma left_le_contractunion (hG' : G.Dup_agree H) : G ≤ G ∪ᶜ H := by
  simp_rw [le_iff, contractunion_isLink hG', contractunion_vertexSet hG']
  tauto

lemma right_edgeDelete_le_contractunion (hG' : G.Dup_agree H) : H ＼ E(G) ≤ G ∪ᶜ H := by
  simp_rw [le_iff, contractunion_isLink hG', contractunion_vertexSet hG', edgeDelete_isLink]
  tauto

lemma contractunion_le_edgeDelete (h₁ : H₁ ≤ G) (h₂ : H₂ ＼ E(H₁) ≤ G) : H₁ ∪ᶜ H₂ ≤ G := by
  have hG' : H₁.Dup_agree H₂ :=
    ⟨P(G), vertexPartition_mono h₁, (vertexPartition_mono h₂ : P(H₂ ＼ E(H₁)) ⊆ _)⟩
  rw [contractunion_eq_contractsUnion, contractsUnion_le_iff pairwise_compatible_edgeDelete
    hG'.pair_edgeDelete]
  simp [h₁, h₂]

lemma contractunion_le (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) : H₁ ∪ᶜ H₂ ≤ G := by
  have hG' : H₁.Dup_agree H₂ :=
    ⟨P(G), vertexPartition_mono h₁, vertexPartition_mono h₂⟩
  rw [contractunion_eq_contractsUnion, Graph.contractsUnion_le_iff pairwise_compatible_edgeDelete
    hG'.pair_edgeDelete]
  simp [h₁, edgeDelete_le.trans h₂]

lemma contractunion_le_iff (hG' : H₁.Dup_agree H₂) : H₁ ∪ᶜ H₂ ≤ G ↔ H₁ ≤ G ∧ H₂ ＼ E(H₁) ≤ G :=
  ⟨fun h => ⟨(Graph.left_le_contractunion hG').trans h,
    (Graph.right_edgeDelete_le_contractunion hG').trans h⟩,
    fun ⟨h₁, h₂⟩ => Graph.contractunion_le_edgeDelete h₁ h₂⟩

lemma contractunion_mono_right (hG₁ : G.Dup_agree H₁) (hG₂ : G.Dup_agree H₂) (h : H₁ ≤ H₂) :
    G ∪ᶜ H₁ ≤ G ∪ᶜ H₂ := by
  simp [contractunion_eq_contractsUnion, Graph.contractsUnion_le_iff pairwise_compatible_edgeDelete
    hG₁.pair_edgeDelete, Graph.le_contractsUnion pairwise_compatible_edgeDelete hG₂.pair_edgeDelete,
    le_trans (edgeDelete_mono_left h _) <| Graph.le_contractsUnion pairwise_compatible_edgeDelete
    hG₂.pair_edgeDelete (by simp : H₂ ＼ E(G) ∈ _)]

@[simp]
lemma contractunion_self (G : Graph α β) : G ∪ᶜ G = G :=
  (Graph.contractunion_le le_rfl le_rfl).antisymm <| Graph.left_le_contractunion dup_agree_rfl ..

lemma isLink_or_isLink_of_contractunion (hG' : G.Dup_agree H) (h : (G ∪ᶜ H).IsLink e x y) :
    G.IsLink e x y ∨ H.IsLink e x y :=
  ((contractunion_isLink hG').1 h).elim .inl fun h' ↦ .inr h'.1

lemma Compatible.contractunion_isLink (h : G.Compatible H) (hG' : G.Dup_agree H) :
    (G ∪ᶜ H).IsLink e x y ↔ G.IsLink e x y ∨ H.IsLink e x y := by
  by_cases heG : e ∈ E(G)
  · simp only [Graph.contractunion_isLink hG', heG, not_true_eq_false, and_false, or_false,
      iff_self_or]
    exact fun he ↦ by rwa [h.isLink_eq heG he.edge_mem]
  simp [heG, Graph.contractunion_isLink hG']

lemma edgeRestrict_contractunion (G : Graph α β) (F₁ F₂ : Set β) :
    (G ↾ (F₁ ∪ F₂)) = (G ↾ F₁) ∪ᶜ (G ↾ F₂) := by
  have hG' : (G ↾ F₁).Dup_agree (G ↾ F₂) := dup_agree_rfl
  refine Graph.ext (by simp [hG']) fun e x y ↦ ?_
  rw [(G.compatible_self.mono (by simp) (by simp)).contractunion_isLink hG']
  simp only [edgeRestrict_isLink, mem_union]
  tauto

lemma contractunion_edgeRestrict_distrib (G H : Graph α β) (F : Set β) :
    (G ∪ᶜ H) ↾ F = (G ↾ F) ∪ᶜ (H ↾ F) :=
  Graph.ext rfl fun e x y ↦ by
  by_cases he : e ∈ F <;> simp [contractunion_isLink_not_agree, edgeRestrict_isLink_eq, and_comm,
    he, edgeDelete_isLink_eq]

lemma Compatible.contractunion_eq_contractsUnion (h : G.Compatible H) (hG' : G.Dup_agree H) :
    G ∪ᶜ H = Graph.contractsUnion {G, H} :=
  Graph.ext (by simp [hG', hG'.pair]) fun e x y ↦ by
    simp [h.contractunion_isLink hG', contractsUnion_isLink h.pair hG'.pair]

lemma Compatible.contractunion_inc_iff (h : G.Compatible H) (hG' : G.Dup_agree H) :
    (G ∪ᶜ H).Inc e x ↔ G.Inc e x ∨ H.Inc e x := by
  simp_rw [Inc, h.contractunion_isLink hG']
  aesop

lemma Compatible.contractunion_isLoopAt_iff (h : G.Compatible H) (hG' : G.Dup_agree H) :
    (G ∪ᶜ H).IsLoopAt e x ↔ G.IsLoopAt e x ∨ H.IsLoopAt e x := by
  simp_rw [← isLink_self_iff, h.contractunion_isLink hG']

lemma Compatible.contractunion_isNonloopAt_iff (h : G.Compatible H) (hG' : G.Dup_agree H) :
    (G ∪ᶜ H).IsNonloopAt e x ↔ G.IsNonloopAt e x ∨ H.IsNonloopAt e x := by
  simp_rw [IsNonloopAt, h.contractunion_isLink hG']
  aesop

lemma Compatible.contractunion_adj_iff (h : G.Compatible H) (hG' : G.Dup_agree H) :
    (G ∪ᶜ H).Adj x y ↔ G.Adj x y ∨ H.Adj x y := by
  simp [Adj, h.contractunion_isLink hG', exists_or]

lemma Compatible.contractunion_comm (h : Compatible G H) (hG' : G.Dup_agree H) : G ∪ᶜ H = H ∪ᶜ G :=
  Graph.ext (by simp [hG', hG'.symm, Set.union_comm])
    fun _ _ _ ↦ by rw [h.contractunion_isLink hG', h.symm.contractunion_isLink hG'.symm, or_comm]

lemma Compatible.contractunion_le_iff (h_compat : H₁.Compatible H₂) (hG' : H₁.Dup_agree H₂) :
    H₁ ∪ᶜ H₂ ≤ G ↔ H₁ ≤ G ∧ H₂ ≤ G := by
  simp [h_compat.contractunion_eq_contractsUnion hG', h_compat.pair, hG'.pair]

lemma Compatible.right_le_contractunion (h : G.Compatible H) (hG' : G.Dup_agree H) :
    H ≤ G ∪ᶜ H := by
  simp [h.contractunion_comm hG', hG'.symm]

lemma contractunion_eq_self_of_le_left (hle : G ≤ H) : G ∪ᶜ H = H :=
  (Graph.contractunion_le hle rfl.le).antisymm <|
    (H.compatible_self.mono_left hle).right_le_contractunion <| dup_agree_of_le hle

lemma contractunion_eq_self_of_le_right (hle : G ≤ H) : H ∪ᶜ G = H :=
  (Graph.contractunion_le rfl.le hle).antisymm <|
    Graph.left_le_contractunion (dup_agree_of_le hle).symm ..

lemma Compatible.contractunion_mono_left (h : H₂.Compatible G) (hle : H₁ ≤ H₂) (h₁ : H₁.Dup_agree G)
    (h₂ : H₂.Dup_agree G) : H₁ ∪ᶜ G ≤ H₂ ∪ᶜ G := by
  rw [h.contractunion_comm h₂, (h.mono_left hle).contractunion_comm h₁]
  exact contractunion_mono_right h₁.symm h₂.symm hle

lemma Compatible.contractunion_mono (hleG : G₁ ≤ G₂) (hleH : H₁ ≤ H₂) (h : G₂.Compatible H₁)
    (h₂ : G₂.Dup_agree H₂) : G₁ ∪ᶜ H₁ ≤ G₂ ∪ᶜ H₂ := by
  have h₂₁ : G₂.Dup_agree H₁ := h₂.mono_right hleH
  have h₁ : G₁.Dup_agree H₁ := h₂₁.mono_left hleG
  exact le_trans (h.contractunion_mono_left hleG h₁ h₂₁) (contractunion_mono_right h₂₁ h₂ hleH)

lemma edgeRestrict_contractunion_edgeDelete (G : Graph α β) (F : Set β) :
    (G ↾ F) ∪ᶜ (G ＼ F) = G := by
  rw [edgeDelete_eq_edgeRestrict, ← edgeRestrict_contractunion, ← edgeRestrict_inter_edgeSet]
  simp only [union_diff_self, edgeRestrict_inter_edgeSet, edgeRestrict_contractunion,
    edgeRestrict_self]
  exact contractunion_eq_self_of_le_left (by simp)

lemma edgeDelete_contractunion_edgeRestrict (G : Graph α β) (F : Set β) :
    (G ＼ F) ∪ᶜ (G ↾ F) = G := by
  convert G.edgeRestrict_contractunion_edgeDelete F using 1
  rw [Compatible.contractunion_comm (G.compatible_of_le_le (by simp) (by simp))
    (by exact dup_agree_rfl)]

lemma induce_contractunion_edgeDelete (G : Graph α β) : G[P] ∪ᶜ (G ＼ E(G[P])) = G := by
  rw [← contractunion_eq_contractunion_edgeDelete, contractunion_eq_self_of_le_left induce_le]

lemma edgeDelete_contractunion_induce (G : Graph α β) : (G ＼ E(G[P])) ∪ᶜ G[P] = G := by
  rw [(Compatible.of_disjoint_edgeSet _).contractunion_comm, induce_contractunion_edgeDelete _]
  · exact agree_of_subset_subset subset_rfl (restrict_subset <| by simp)
  simp [disjoint_sdiff_left]

lemma Compatible.contractunion_eq_contractiUnion (h : G.Compatible H) (hG' : G.Dup_agree H) :
    G ∪ᶜ H = Graph.contractiUnion (fun b ↦ bif b then G else H) := by
  have h' : Pairwise (Compatible on fun b ↦ bif b then G else H) := by
    simpa [pairwise_on_bool]
  have hG'' : Pairwise (Dup_agree on fun b ↦ bif b then G else H) := by
    simpa [pairwise_on_bool]
  simp only [le_antisymm_iff, h.contractunion_le_iff hG', Graph.contractiUnion_le_iff h' hG'',
    Bool.forall_bool, cond_false, h.right_le_contractunion hG', cond_true,
    Graph.left_le_contractunion hG', and_self, and_true]
  exact ⟨Graph.le_contractiUnion h' hG'' true, Graph.le_contractiUnion h' hG'' false⟩

lemma Compatible.induce_contractunion (h : G.Compatible H) (hG' : G.Dup_agree H) (P : Set α) :
    (G ∪ᶜ H)[P] = G[P] ∪ᶜ H[P] := by
  refine Graph.ext (by simp [hG', union_inter_distrib_right]) fun e x y ↦ ?_
  simp only [induce_isLink, h.contractunion_isLink hG',
    h.induce.contractunion_isLink (hG'.induce P)]
  tauto

lemma Compatible.vertexDelete_contractunion (h : G.Compatible H) (hG' : G.Dup_agree H) (X : Set α) :
    (G ∪ᶜ H) - X = (G - X) ∪ᶜ (H - X) := by
  rw [h.contractunion_eq_contractiUnion hG', vertexDelete_contractiUnion]
  simp [Bool.apply_cond (f := fun G ↦ G - X),
    ← h.vertexDelete.contractunion_eq_contractiUnion (hG'.vertexDelete X)]
  all_goals simpa [pairwise_on_bool]

-- lemma induce_contractunion (G : Graph α β) (hPQ : P.Agree Q)
--     (hX : ∀ x ∈ P, ∀ y ∈ Q, ¬ G.Adj x y) : G[P ⊔ Q] = G[P] ∪ᶜ G[Q] := by
--   refine Graph.ext ?_ fun e x y ↦ ?_
--   · rw [contractunion_vertexSet]
--     simp [inter_contractunion_distrib_left]
--     sorry
--   simp only [induce_isLink, hPQ.mem_sup_iff, Compatible.induce_induce.contractunion_isLink hPQ]
--   by_cases hxy : G.IsLink e x y
--   · by_cases hx : x ∈ P
--     · simp [hx, show y ∉ Q from fun hy ↦ hX x hx y hy hxy.adj]
--     by_cases hy : y ∈ P
--     · simp [hy, show x ∉ Q from fun hx ↦ hX _ hy _ hx hxy.symm.adj, hxy]
--     simp [hx, hy]
--   simp [hxy]

-- lemma contractsUnion_insert (G : Graph α β) (s : Set (Graph α β))
-- (hG' : (insert G s).Pairwise Dup_agree) :
--     Graph.contractsUnion (insert G s) = G ∪ᶜ Graph.contractsUnion Gs := by
--   refine Graph.ext ?_ fun e x y ↦ ?_
--   · rw [contractunion_vertexSet, Graph.contractsUnion_contractunion]

-- lemma contractsUnion_image {s : Set ι} {f : ι → Graph α β}
--     (hs : s.Pairwise (Graph.Compatible on f)) :
--     Graph.contractsUnion (f '' s) hs.image = .contractiUnion (f · : s → _)
--(Pairwise.restrict.mpr hs) := by
--   rw [Graph.contractsUnion]
--   let f' : s → ↑(f '' s) := fun i ↦ ⟨f i, ⟨i, i.2, rfl⟩⟩
--   exact Graph.contractiUnion_comp_eq_of_surj (f := f') _ (fun ⟨_, i, hGs, rfl⟩ ↦ ⟨⟨i, hGs⟩, rfl⟩)

-- lemma contractsUnion_range {f : ι → Graph α β} (h : Pairwise (Graph.Compatible on f)) :
--     Graph.contractsUnion (Set.range f) h.range_pairwise = .contractiUnion f h := by
--   unfold Graph.contractsUnion
--   exact Graph.contractiUnion_comp_eq_of_surj (f := Set.rangeFactorization f) _
--surjective_onto_range

-- @[simp]
-- lemma noEdge_contractunion_eq_self : Graph.noEdge P β ∪ᶜ G = G ↔ P ≤ P(G) := by
--   refine ⟨fun h => ?_, fun h => ?_⟩
--   · rw [← h]
--     convert left_vertexPartition_le_contractunion
--     rfl
--   refine vertexPartition_ext (by simpa) fun e x y ↦ ?_
--   simp only [contractunion_isLink_not_agree, noEdge_edgeSet, mem_empty_iff_false,
--not_false_eq_true,
--     not_isLink_of_notMem_edgeSet, and_true, false_or, contractunion_vertexPartition,
--noEdge_vertexPartition,
--     h, sup_of_le_right]
--   refine ⟨?_, fun h => ⟨x, y, h, foo_eq_self_of_mem h.left_mem',
--     foo_eq_self_of_mem h.right_mem'⟩⟩
--   rintro ⟨u, v, h, rfl, rfl⟩
--   rwa [foo_eq_self_of_mem h.left_mem', foo_eq_self_of_mem h.right_mem']

-- @[simp]
-- lemma contractunion_noEdge_eq_self : G ∪ᶜ Graph.noEdge P β = G ↔ P ≤ P(G) := by
--   refine ⟨fun h => ?_, fun h => ?_⟩
--   · rw [← h]
--     convert right_vertexPartition_le_contractunion
--     rfl
--   refine vertexPartition_ext (by simpa) fun e x y ↦ ?_
--   simp only [contractunion_isLink_not_agree, noEdge_edgeSet, mem_empty_iff_false,
--not_false_eq_true,
--     not_isLink_of_notMem_edgeSet, false_and, or_false, contractunion_vertexPartition,
--     noEdge_vertexPartition, h, sup_of_le_left]
--   refine ⟨?_, fun h => ⟨x, y, h, foo_eq_self_of_mem h.left_mem',
--     foo_eq_self_of_mem h.right_mem'⟩⟩
--   rintro ⟨u, v, h, rfl, rfl⟩
--   rwa [foo_eq_self_of_mem h.left_mem', foo_eq_self_of_mem h.right_mem']

-- lemma sUnion_powerset_pairwise_dup_agree (hs : Gs.Pairwise Dup_agree) :
--     (Graph.sUnion '' Gs.powerset).Pairwise Dup_agree := by
--   have hs' : (vertexPartition '' Gs).Pairwise Partition.Agree := by rwa [pairwise_image_of_refl]
--   rintro _ ⟨S, hS, rfl⟩ _ ⟨T, hT, rfl⟩ -
--   rw [mem_powerset_iff] at hS hT
--   unfold Dup_agree onFun
--   apply (Partition.powerset_sSup_pairwise_agree hs').of_refl
--   <;> rw [sUnion_vertexPartition, ← sSup_image]
--   <;> exact mem_image_of_mem sSup <| mem_powerset <| image_mono (by assumption)

-- lemma sUnion_dup_agree_sUnion_of_subset (hs : Gs.Pairwise Dup_agree)
--     (hHs : Hs ⊆ Gs) (hH's : H's ⊆ Gs) : (Graph.sUnion Hs).Dup_agree (Graph.sUnion H's) := by
--   apply (sUnion_powerset_pairwise_dup_agree hs).of_refl
--   <;> exact mem_image_of_mem Graph.sUnion (by assumption)

-- lemma sUnion_powerset_pairwise_compatible (hs : Gs.Pairwise Compatible)
--     (hs' : Gs.Pairwise Dup_agree): (Graph.sUnion '' Gs.powerset).Pairwise Compatible := by
--   rintro _ ⟨S, hS, rfl⟩ _ ⟨T, hT, rfl⟩ - e ⟨heS, heT⟩
--   rw [mem_powerset_iff] at hS hT
--   ext u v
--   simp only [hs.mono hS, sUnion_edgeSet, mem_iUnion, exists_prop, hs.mono hT] at heS heT
--   obtain ⟨G, hGS, heG⟩ := heS
--   obtain ⟨H, hHT, heH⟩ := heT
--   rw [sUnion_isLink (hs.mono hS) (hs'.mono hS), sUnion_isLink (hs.mono hT) (hs'.mono hT)]
--   refine ⟨fun ⟨G, hGS, heG⟩ => ⟨H, hHT, ?_⟩, fun ⟨H, hHT, heH⟩ => ⟨G, hGS, ?_⟩⟩
--   · rwa [hs.of_refl (hT hHT) (hS hGS) ⟨heH, heG.edge_mem⟩]
--   · rwa [hs.of_refl (hS hGS) (hT hHT) ⟨heG, heH.edge_mem⟩]

-- lemma sUnion_compatible_sUnion_of_subset (hs : Gs.Pairwise Compatible)
-- (hs' : Gs.Pairwise Dup_agree)
--     (hHs : Hs ⊆ Gs) (hH's : H's ⊆ Gs) : (Graph.sUnion Hs).Compatible (Graph.sUnion H's) := by
--   apply (sUnion_powerset_pairwise_compatible hs hs').of_refl
--   <;> exact mem_image_of_mem Graph.sUnion (by assumption)

-- lemma Pairwise.union_compatible (hst : (Gs ∪ Hs).Pairwise Compatible)
--     (hst' : (Gs ∪ Hs).Pairwise Dup_agree): (Graph.sUnion Gs).Compatible (Graph.sUnion Hs) := by
--   have hs : Gs.Pairwise Compatible := hst.mono subset_union_left
--   have ht : Hs.Pairwise Compatible := hst.mono subset_union_right
--   have hs' : Gs.Pairwise Dup_agree := hst'.mono subset_union_left
--   have ht' : Hs.Pairwise Dup_agree := hst'.mono subset_union_right
--   refine compatible_of_le_le (G := Graph.sUnion (Gs ∪ Hs)) ?_ ?_
--   <;> rw [Graph.sUnion_le_iff (by assumption) (by assumption)]
--   <;> exact fun G hG ↦ Graph.le_sUnion (by assumption) (by assumption) (by simp [hG])

-- lemma sUnion_union_sUnion (hst : (Gs ∪ Hs).Pairwise Compatible)
--     (hst' : (Gs ∪ Hs).Pairwise Dup_agree) :
--     Graph.sUnion Gs ∪ Graph.sUnion Hs = Graph.sUnion (Gs ∪ Hs) := by
--   have hs : Gs.Pairwise Compatible := hst.mono subset_union_left
--   have ht : Hs.Pairwise Compatible := hst.mono subset_union_right
--   have hs' : Gs.Pairwise Dup_agree := hst'.mono subset_union_left
--   have ht' : Hs.Pairwise Dup_agree := hst'.mono subset_union_right
--   have hST : (Graph.sUnion Gs).Compatible (Graph.sUnion Hs) :=
--     sUnion_compatible_sUnion_of_subset hst hst' subset_union_left subset_union_right
--   have hST' : (Graph.sUnion Gs).Dup_agree (Graph.sUnion Hs) :=
--     sUnion_dup_agree_sUnion_of_subset hst' subset_union_left subset_union_right
--   refine Graph.ext ?_ fun e x y ↦ ?_
--   · rw [sUnion_vertexSet hst', union_vertexSet hST', sUnion_vertexSet hs', sUnion_vertexSet ht']
--     exact (biUnion_union Gs Hs vertexSet).symm
--   rw [sUnion_isLink hst hst', hST.union_isLink hST', sUnion_isLink hs hs', sUnion_isLink ht ht']
--   aesop

-- lemma Compatible.sum_compatible (hGH : Pairwise (Compatible on (Sum.elim Gι Hι')))
--     (hGH' : Pairwise (Dup_agree on (Sum.elim Gι Hι'))) :
--     (Graph.iUnion Gι).Compatible (Graph.iUnion Hι') :=
--   compatible_of_le_le (iUnion_left_le_iUnion_sum hGH hGH') <| iUnion_right_le_iUnion_sum hGH hGH'

-- protected lemma iUnion_sum (hGH : Pairwise (Compatible on (Sum.elim Gι Hι')))
--     (hGH' : Pairwise (Dup_agree on (Sum.elim Gι Hι'))) :
--     Graph.iUnion (Sum.elim Gι Hι') = (.iUnion Gι) ∪ (.iUnion Hι') := by
--   refine le_antisymm ?_ <| Graph.union_le (iUnion_left_le_iUnion_sum hGH hGH')
--     (iUnion_right_le_iUnion_sum hGH hGH')
--   rw [Graph.iUnion_le_iff hGH hGH']
--   have H : (Graph.iUnion Gι).Dup_agree (Graph.iUnion Hι') := by
--     refine sUnion_dup_agree_sUnion_of_subset (Gs := range Gι ∪ range Hι') ?_ (by simp) (by simp)
--     simpa [← pairwise_image_of_refl, image_univ, Sum.elim_range] using hGH'.set_pairwise univ
--   rintro (i | i) <;> simp only [Sum.elim_inl, Sum.elim_inr]
--   · exact (Graph.le_iUnion hGH.sum_left hGH'.sum_left i).trans (Graph.left_le_union H)
--   · exact (Graph.le_iUnion hGH.sum_right hGH'.sum_right i).trans
--       (Compatible.sum_compatible hGH hGH' |>.right_le_union H)


-- protected lemma iUnion_le_of_forall_le (h : ∀ i, Hι i ≤ G) : .iUnion Hι ≤ G := by
--   rwa [Graph.iUnion_le_iff]
--   · exact compatible_of_forall_map_le h
--   · exact dup_agree_of_forall_map_le h

-- protected lemma sUnion_le_of_forall_le (h : ∀ ⦃H⦄, H ∈ Gs → H ≤ G) : .sUnion Gs ≤ G := by
--   rwa [Graph.sUnion_le_iff]
--   · exact compatible_of_forall_mem_le h
--   · exact dup_agree_of_forall_mem_le h

-- /-- A union of closed subgraphs of `G` is a closed subgraph of `G`. -/
-- lemma iUnion_isClosedSubgraph (h : ∀ i, Hι i ≤c G) : .iUnion Hι ≤c G where
--   toIsSubgraph := Graph.iUnion_le_of_forall_le fun i ↦ (h i).le
--   closed e x he := by
--     rw [iUnion_vertexSet, iUnion_edgeSet]
--     simp only [mem_iUnion, forall_exists_index]
--     exact fun i hxi ↦ ⟨_, (he.of_isClosedSubgraph_of_mem (h i) hxi).edge_mem⟩
--     · exact compatible_of_forall_map_le (fun a ↦ (h a).le)
--     · exact dup_agree_of_forall_map_le (fun a ↦ (h a).le)

-- /-- A nonempty union of spanning subgraphs of `G` is a spanning subgraph of `G`. -/
-- lemma iUnion_isSpanningSubgraph [Nonempty ι] (h : ∀ i, Hι i ≤s G) : .iUnion Hι ≤s G where
--   vertexSet_eq := by
--     rw [iUnion_vertexSet, iUnion_eq_const (fun i ↦ (h i).vertexSet_eq)]
--     exact dup_agree_of_forall_map_le (fun a ↦ (h a).le)
--   isLink_of_isLink := (Graph.iUnion_le_of_forall_le fun i ↦ (h i).le).isLink_of_isLink

-- -- A weakening of the previous lemma.
-- lemma iUnion_isSpanningSubgraph_of_exists_isSpanningSubgraph_of_forall_le
--     (h : ∀ i, Hι i ≤ G) (hH : ∃ i, Hι i ≤s G) : .iUnion Hι ≤s G where
--   vertexSet_eq := by
--     apply le_antisymm
--     · simp only [iUnion_vertexSet (dup_agree_of_forall_map_le (fun a ↦ h a)), le_eq_subset,
--         iUnion_subset_iff]
--       exact fun i ↦ (h i).vertexSet_subset
--     obtain ⟨i, hi⟩ := hH
--     rw [← hi.vertexSet_eq, iUnion_vertexSet (dup_agree_of_forall_map_le (fun a ↦ h a))]
--     exact subset_iUnion_of_subset i fun ⦃a⦄ a ↦ a
--   isLink_of_isLink := (Graph.iUnion_le_of_forall_le h).isLink_of_isLink

-- lemma sUnion_isClosedSubgraph (hsc : ∀ ⦃H⦄, H ∈ Gs → H ≤c G) : .sUnion Gs ≤c G := by
--   let f : Gs → Graph α β := Subtype.val
--   have : .iUnion f ≤c G := iUnion_isClosedSubgraph <| by
--     rintro ⟨H, hHs⟩
--     simp [f, hsc hHs]
--   convert this
--   simp [f, Graph.iUnion]

-- lemma sUnion_isSpanningSubgraph (hs : ∀ ⦃H⦄, H ∈ Gs → H ≤s G) (hne : Gs.Nonempty) :
--     .sUnion Gs ≤s G := by
--   let f : Gs → Graph α β := Subtype.val
--   have hne := hne.to_subtype
--   have : .iUnion f ≤s G := iUnion_isSpanningSubgraph <| by
--     rintro ⟨H, hHs⟩
--     simp [f, hs hHs]
--   convert this
--   simp [f, Graph.iUnion]

-- lemma IsClosedSubgraph.union (h₁ : H₁ ≤c G) (h₂ : H₂ ≤c G) : H₁ ∪ H₂ ≤c G := by
--   rw [(compatible_of_le_le h₁.le h₂.le).union_eq_iUnion (dup_agree_of_le_le h₁.le h₂.le)]
--   exact iUnion_isClosedSubgraph <| by simp [h₁,h₂]

-- lemma IsSpanningSubgraph.union (h₁ : H₁ ≤s G) (h₂ : H₂ ≤s G) : H₁ ∪ H₂ ≤s G := by
--   rw [(compatible_of_le_le h₁.le h₂.le).union_eq_iUnion (dup_agree_of_le_le h₁.le h₂.le)]
--   exact iUnion_isSpanningSubgraph <| by simp [h₁,h₂]

-- lemma IsSpanningSubgraph.union_left (h₁ : H₁ ≤s G) (h₂ : H₂ ≤ G) : H₁ ∪ H₂ ≤s G := by
--   rw [(compatible_of_le_le h₁.le h₂).union_eq_iUnion (dup_agree_of_le_le h₁.le h₂)]
--   exact iUnion_isSpanningSubgraph_of_exists_isSpanningSubgraph_of_forall_le (by simp [h₁.le, h₂])
--     ⟨True, h₁⟩

-- lemma IsSpanningSubgraph.union_right (h₁ : H₁ ≤ G) (h₂ : H₂ ≤s G) : H₁ ∪ H₂ ≤s G := by
--   rw [(compatible_of_le_le h₁ h₂.le).union_eq_iUnion (dup_agree_of_le_le h₁ h₂.le)]
--   exact iUnion_isSpanningSubgraph_of_exists_isSpanningSubgraph_of_forall_le (by simp [h₁, h₂.le])
--     ⟨False, h₂⟩


end Graph
