import Matroid.Graph.Subgraph.Add
import Matroid.Graph.Subgraph.Inter

variable {α β ι ι' : Type*} {x y z u v w : α} {e f : β} {F F₁ F₂ : Set β} {X Y : Set α}

open Set Function

namespace Graph

section CompleteLattice

variable [CompleteLattice α] {P Q : Partition α} {Gs Hs : Set (Graph α β)}
  {G G₁ G₂ H H₁ H₂ : Graph α β} [Nonempty ι] {Gι Hι : ι → Graph α β} {H'ι : ι' → Graph α β}

@[simp↓]
lemma iInter_inc_of_compatible (hG' : Pairwise (Compatible on Gι)) :
    (Graph.iInter Gι).Inc e x ↔ ∀ i, (Gι i).Inc e x := by
  rw [iInter_inc]
  let j := Classical.arbitrary ι
  refine ⟨fun ⟨y, h⟩ i ↦ ⟨y, h i⟩, fun h ↦ ?_⟩
  obtain ⟨y, hy⟩ := h j
  use y, fun i ↦ hy.of_compatible (hG'.of_refl j i) (h i).edge_mem

lemma stronglyDisjoint_iff_disjoint_of_compatible (h : H₁.Compatible H₂) :
    StronglyDisjoint H₁ H₂ ↔ Disjoint H₁ H₂ := by
  rw [stronglyDisjoint_iff_vertexSet_disjoint_compatible, Set.disjoint_iff_inter_eq_empty,
    disjoint_iff, ← vertexSet_eq_empty_iff]
  simp [h]

end CompleteLattice

-- section Frame
-- variable [Order.Frame α] {G G₁ G₂ H H₁ H₂ : Graph α β} {Gs Hs G's H's : Set (Graph α β)}
--   {P Q : Partition α} {Gι Hι : ι → Graph α β} {Gι' Hι' : ι' → Graph α β}

-- lemma sUnion_powerset_pairwise_dup_agree (hs : Gs.Pairwise Dup_agree) :
--     (Graph.sUnion '' Gs.powerset).Pairwise Dup_agree := by
--   have hs' : (vertexPartition '' Gs).Pairwise Partition.Agree := by rwa [pairwise_image_of_refl]
--   rintro _ ⟨S, hS, rfl⟩ _ ⟨T, hT, rfl⟩ -
--   rw [mem_powerset_iff] at hS hT
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
--(hs' : Gs.Pairwise Dup_agree)
--     (hHs : Hs ⊆ Gs) (hH's : H's ⊆ Gs) : (Graph.sUnion Hs).Compatible (Graph.sUnion H's) := by
--   apply (sUnion_powerset_pairwise_compatible hs hs').of_refl
--   <;> exact mem_image_of_mem Graph.sUnion (by assumption)

-- lemma iInter_le_iUnion (hGι : Pairwise (Compatible on Gι)) (hG'ι : Pairwise (Dup_agree on Gι))
--     [Nonempty ι] : Graph.iInter Gι ≤ Graph.iUnion Gι :=
--   (Graph.iInter_le (Classical.arbitrary ι)).trans <| Graph.le_iUnion hGι hG'ι _

-- protected lemma inter_distrib_iUnion (hH : Pairwise (Compatible on Hι))
--     (hH' : Pairwise (Dup_agree on Hι)) :
--     G ∩ (Graph.iUnion Hι) = Graph.iUnion (fun i : ι ↦ G ∩ (Hι i)) := by
--   have hG : Pairwise (Compatible on fun i ↦ G ∩ Hι i) := by
--     exact fun i j hne ↦ hH.of_refl i j |>.mono Graph.inter_le_right Graph.inter_le_right
--   have hG' : Pairwise (Dup_agree on fun i ↦ G ∩ Hι i) := by
--     exact fun i j hne ↦ hH'.of_refl i j |>.mono Graph.inter_le_right Graph.inter_le_right
--   apply Graph.ext ?_ fun e x y ↦ ?_
--   · rw [iUnion_vertexSet hG', inter_vertexSet, iUnion_vertexSet hH', inter_comm, iUnion_inter]
--     simp_rw [inter_comm, inter_vertexSet]
--   rw [inter_isLink, iUnion_isLink hG hG']
--   simp only [Pi.inf_apply, inf_Prop_eq, inter_isLink, exists_and_left, and_congr_right_iff]
--   rintro he
--   rw [iUnion_isLink hH hH']

-- protected lemma inter_distrib_sUnion (hs : Gs.Pairwise Compatible)
--(hs' : Gs.Pairwise Dup_agree) :
--     G ∩ (Graph.sUnion Gs) = Graph.sUnion ((fun K ↦ G ∩ K) '' Gs) := by
--   have hG : ((fun K ↦ G ∩ K) '' Gs).Pairwise Compatible := by
--     rintro _ ⟨K₁, hK₁, rfl⟩ _ ⟨K₂, hK₂, rfl⟩ -
--     exact hs.of_refl hK₁ hK₂ |>.mono Graph.inter_le_right Graph.inter_le_right
--   have hG' : ((fun K ↦ G ∩ K) '' Gs).Pairwise Dup_agree := by
--     rintro _ ⟨K₁, hK₁, rfl⟩ _ ⟨K₂, hK₂, rfl⟩ -
--     exact hs'.of_refl hK₁ hK₂ |>.mono Graph.inter_le_right Graph.inter_le_right
--   apply Graph.ext ?_ fun e x y ↦ ?_
--   · rw [inter_vertexSet, sUnion_vertexSet hs', inter_comm]
--     simp_rw [sUnion_vertexSet hG', Set.iUnion₂_inter, inter_comm]
--     simp
--   rw [sUnion_isLink hG hG']
--   simp only [inter_isLink, Pi.inf_apply, sUnion_isLink hs hs', inf_Prop_eq, mem_image,
--     exists_exists_and_eq_and]
--   tauto

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

-- end Frame

section Subgraph

/-! ### Subgraphs -/

variable [CompleteLattice α] {G H H₁ H₂ : Graph α β} {Gs Hs G's H's : Set (Graph α β)}
  {P Q : Partition α} {Gι Hι : ι → Graph α β} {Gι' Hι' : ι' → Graph α β}

protected lemma iInter_le_of_forall_le [Nonempty ι] (h : ∀ i, Hι i ≤ G) : .iInter Hι ≤ G :=
  (Graph.iInter_le (Classical.arbitrary ι)).trans <| h _

protected lemma sInter_le_of_forall_le (h : ∀ ⦃H⦄, H ∈ Gs → H ≤ G) (hne : Gs.Nonempty) :
    .sInter Gs hne ≤ G :=
  have := hne.to_subtype
  Graph.iInter_le_of_forall_le (by simpa)

/-- A nonempty intersection of induced subgraphs `G` is an induced subgraph of `G`-/
lemma iInter_isInducedSubgraph [Nonempty ι] (h : ∀ i, Hι i ≤i G) : .iInter Hι ≤i G where
  le := Graph.iInter_le_of_forall_le fun i ↦ (h i).le
  isLink_of_mem_mem e x y hxy hx hy i := by
    simp only [iInter_vertexSet, mem_iInter] at hx hy
    exact (h i).isLink_of_mem_mem hxy (hx i) (hy i)

/-- A nonempty intersection of spanning subgraphs of `G` is a spanning subgraph of `G`.-/
lemma iInter_isSpanningSubgraph [Nonempty ι] (h : ∀ i, Hι i ≤s G) : .iInter Hι ≤s G where
  isLink_of_isLink := (Graph.iInter_le_of_forall_le fun i ↦ (h i).le).isLink_of_isLink
  vertexSet_eq := iInter_eq_const fun i ↦ (h i).vertexSet_eq

/-- A nonempty intersection of closed subgraphs `G` is an induced subgraph of `G`-/
lemma iInter_isClosedSubgraph [Nonempty ι] (h : ∀ i, Hι i ≤c G) : .iInter Hι ≤c G where
  toIsSubgraph := Graph.iInter_le_of_forall_le fun i ↦ (h i).le
  closed e x := by
    rw [iInter_vertexSet, mem_iInter]
    rintro ⟨y, hy⟩ hx
    use x, y, fun i ↦ by rwa [(h i).isLink_iff_of_mem (hx i)]

lemma sInter_isInducedSubgraph (hs : ∀ ⦃H⦄, H ∈ Gs → H ≤i G) (hne : Gs.Nonempty) :
    .sInter Gs hne ≤i G :=
  have := hne.to_subtype
  iInter_isInducedSubgraph <| by simpa

lemma sInter_isClosedSubgraph (hs : ∀ ⦃H⦄, H ∈ Gs → H ≤c G) (hne : Gs.Nonempty) :
    .sInter Gs hne ≤c G :=
  have := hne.to_subtype
  iInter_isClosedSubgraph <| by simpa

-- lemma isClosedSubgraph_iUnion_of_stronglyDisjoint (h : Pairwise (StronglyDisjoint on Hι))
--(i : ι) :
--     Hι i ≤c Graph.iUnion Hι where
--   le := Graph.le_iUnion sorry sorry i
--   closed e x he hx := by
--     obtain ⟨j, hj : (Hι j).Inc e x⟩ := (iUnion_inc_iff ..).1 he
--     obtain rfl | hne := eq_or_ne i j
--     · exact hj.edge_mem
--     exact False.elim <| (h hne).vertex.notMem_of_mem_left hx hj.vertex_mem

-- lemma isClosedSubgraph_sUnion_of_stronglyDisjoint (s : Set (Graph α β))
--     (hs : Gs.Pairwise StronglyDisjoint) (hG : G ∈ s) : G ≤c Graph.sUnion s :=
--   isClosedSubgraph_iUnion_of_stronglyDisjoint ((pairwise_subtype_iff_pairwise_set ..).2 hs)
--⟨G, hG⟩

-- lemma isClosedSubgraph_union_left_of_vertexSet_disjoint (h : Disjoint V(H₁) V(H₂)) :
--     H₁ ≤c H₁ ∪ H₂ := by
--   refine ⟨Graph.left_le_union H₁ H₂, fun e x hinc hx₁ => ?_⟩
--   have hninc : ¬ H₂.Inc e x := fun hinc ↦ h.notMem_of_mem_left hx₁ hinc.vertex_mem
--   simp only [union_inc_iff, hninc, false_and, or_false] at hinc
--   exact hinc.edge_mem

-- lemma Disjoint.isClosedSubgraph_union_left (h : Disjoint H₁ H₂) : H₁ ≤c H₁ ∪ H₂ :=
--   isClosedSubgraph_union_left_of_vertexSet_disjoint <| Disjoint.vertex_disjoint h

-- lemma StronglyDisjoint.isClosedSubgraph_union_left (h : StronglyDisjoint H₁ H₂) :
--     H₁ ≤c H₁ ∪ H₂ := by
--   rw [(stronglyDisjoint_le_compatible _ _ h).union_eq_sUnion]
--   exact isClosedSubgraph_sUnion_of_stronglyDisjoint _ (by simp [Set.Pairwise, h, h.symm])
--(by simp)

-- lemma StronglyDisjoint.isClosedSubgraph_union_right (h : StronglyDisjoint H₁ H₂) :
--     H₂ ≤c H₁ ∪ H₂ := by
--   rw [(stronglyDisjoint_le_compatible _ _ h).union_eq_sUnion]
--   exact isClosedSubgraph_sUnion_of_stronglyDisjoint _ (by simp [Set.Pairwise, h, h.symm])
--(by simp)

lemma IsInducedSubgraph.inter (h₁ : H₁ ≤i G) (h₂ : H₂ ≤i G) : H₁ ∩ H₂ ≤i G := by
  rw [inter_eq_iInter]
  exact iInter_isInducedSubgraph <| by simp [h₁,h₂]

lemma IsClosedSubgraph.inter (h₁ : H₁ ≤c G) (h₂ : H₂ ≤c G) : H₁ ∩ H₂ ≤c G := by
  rw [inter_eq_iInter]
  exact iInter_isClosedSubgraph <| by simp [h₁,h₂]

lemma IsClosedSubgraph.inter_le {K G H : Graph α β} (hKG : K ≤c G) (hle : H ≤ G) : K ∩ H ≤c H where
  toIsSubgraph := Graph.inter_le_right
  closed e x hex hx := by
    rw [inter_vertexSet] at hx
    have heK := ((hex.of_le hle).of_isClosedSubgraph_of_mem hKG hx.1).edge_mem
    rw [(compatible_of_le_le hKG.le hle).inter_edgeSet]
    exact ⟨heK, hex.edge_mem⟩

@[simp]
lemma le_bot_iff : G ≤ ⊥ ↔ G = ⊥ := _root_.le_bot_iff

@[simp]
lemma isClosedSubgraph_bot_iff : G ≤c ⊥ ↔ G = ⊥ :=
  ⟨fun h => le_bot_iff.mp h.le, fun h => h ▸ bot_isClosedSubgraph ⊥⟩

@[simp]
lemma isSpanningSubgraph_bot_iff : G ≤s ⊥ ↔ G = ⊥ := by
  refine ⟨fun h => le_bot_iff.mp h.le, fun h => ⟨?_, ?_⟩⟩ <;> simp [h]

@[simp]
lemma isInducedSubgraph_bot_iff : G ≤i ⊥ ↔ G = ⊥ :=
  ⟨fun h => le_bot_iff.mp h.le, fun h => h ▸ bot_isInducedSubgraph ⊥⟩

@[simp]
lemma induce_empty : G[⊥] = ⊥ := by
  rw [← vertexSet_eq_empty_iff]
  simp

end Subgraph

-- section SubgraphFrame
-- variable [Order.Frame α] {G H H₁ H₂ : Graph α β} {Gs Hs G's H's : Set (Graph α β)}
--   {P Q : Partition α} {Gι Hι : ι → Graph α β} {Gι' Hι' : ι' → Graph α β}

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

-- end SubgraphFrame
end Graph
