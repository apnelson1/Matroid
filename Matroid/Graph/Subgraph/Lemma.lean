import Matroid.Graph.Subgraph.Add
import Matroid.Graph.Subgraph.Inter

variable {α β ι ι' : Type*} {x y z u v w : Set α} {e f : β} {G G₁ G₂ H H₁ H₂ : Graph α β}
  {F F₁ F₂ : Set β} {X Y : Set (Set α)} {s t : Set (Graph α β)} {P Q : Partition (Set α)}
  [Nonempty ι] {Gι Hι : ι → Graph α β} {H'ι : ι' → Graph α β}

open Set Function

namespace Graph

lemma sUnion_powerset_pairwise_dup_agree (hs : s.Pairwise Dup_agree) :
    (Graph.sUnion '' s.powerset).Pairwise Dup_agree := by
  have hs' : (vertexPartition '' s).Pairwise Partition.Agree := by rwa [pairwise_image_of_refl]
  rintro _ ⟨S, hS, rfl⟩ _ ⟨T, hT, rfl⟩ -
  rw [mem_powerset_iff] at hS hT
  apply (Partition.powerset_sSup_pairwise_agree hs').of_refl
  <;> rw [sUnion_vertexPartition, ← sSup_image]
  <;> exact mem_image_of_mem sSup <| mem_powerset <| image_mono (by assumption)

lemma sUnion_dup_agree_sUnion_of_subset {S T : Set (Graph α β)} (hs : s.Pairwise Dup_agree)
    (hS : S ⊆ s) (hT : T ⊆ s) : (Graph.sUnion S).Dup_agree (Graph.sUnion T) := by
  apply (sUnion_powerset_pairwise_dup_agree hs).of_refl
  <;> exact mem_image_of_mem Graph.sUnion (by assumption)

lemma sUnion_powerset_pairwise_compatible (hs : s.Pairwise Compatible) (hs' : s.Pairwise Dup_agree):
    (Graph.sUnion '' s.powerset).Pairwise Compatible := by
  rintro _ ⟨S, hS, rfl⟩ _ ⟨T, hT, rfl⟩ - e ⟨heS, heT⟩
  rw [mem_powerset_iff] at hS hT
  ext u v
  simp only [hs.mono hS, sUnion_edgeSet, mem_iUnion, exists_prop, hs.mono hT] at heS heT
  obtain ⟨G, hGS, heG⟩ := heS
  obtain ⟨H, hHT, heH⟩ := heT
  rw [sUnion_isLink (hs.mono hS) (hs'.mono hS), sUnion_isLink (hs.mono hT) (hs'.mono hT)]
  refine ⟨fun ⟨G, hGS, heG⟩ => ⟨H, hHT, ?_⟩, fun ⟨H, hHT, heH⟩ => ⟨G, hGS, ?_⟩⟩
  · rwa [hs.of_refl (hT hHT) (hS hGS) ⟨heH, heG.edge_mem⟩]
  · rwa [hs.of_refl (hS hGS) (hT hHT) ⟨heG, heH.edge_mem⟩]

lemma sUnion_compatible_sUnion_of_subset {S T : Set (Graph α β)} (hs : s.Pairwise Compatible)
    (hs' : s.Pairwise Dup_agree) (hS : S ⊆ s) (hT : T ⊆ s) :
    (Graph.sUnion S).Compatible (Graph.sUnion T) := by
  apply (sUnion_powerset_pairwise_compatible hs hs').of_refl
  <;> exact mem_image_of_mem Graph.sUnion (by assumption)

lemma iInter_le_iUnion (hG : Pairwise (Compatible on Gι))
    (hG' : Pairwise (Dup_agree on Gι)) : Graph.iInter Gι ≤ Graph.iUnion Gι :=
  (Graph.iInter_le (Classical.arbitrary ι)).trans <| Graph.le_iUnion hG hG' _

@[simp↓]
lemma iInter_inc_of_compatible (hG' : Pairwise (Compatible on Gι)) :
    (Graph.iInter Gι).Inc e x ↔ ∀ i, (Gι i).Inc e x := by
  rw [iInter_inc]
  let j := Classical.arbitrary ι
  refine ⟨fun ⟨y, h⟩ i ↦ ⟨y, h i⟩, fun h ↦ ?_⟩
  obtain ⟨y, hy⟩ := h j
  use y, fun i ↦ hy.of_compatible (hG'.of_refl j i) (h i).edge_mem

lemma Compatible.inter_edgeSet (h : G.Compatible H) : E(G ∩ H) = E(G) ∩ E(H) := by
  rw [Graph.inter_edgeSet]
  exact le_antisymm (fun e he ↦ he.1) fun e he ↦ ⟨he, h he⟩

lemma stronglyDisjoint_iff_disjoint_of_compatible (h : H₁.Compatible H₂) :
    StronglyDisjoint H₁ H₂ ↔ Disjoint H₁ H₂ := by
  rw [stronglyDisjoint_iff_vertexSet_disjoint_compatible, Set.disjoint_iff_inter_eq_empty,
    disjoint_iff, ← vertexSet_eq_empty_iff]
  simp [h]

omit [Nonempty ι] in
protected lemma inter_distrib_iUnion (hH : Pairwise (Compatible on Hι))
    (hH' : Pairwise (Dup_agree on Hι)) :
    G ∩ (Graph.iUnion Hι) = Graph.iUnion (fun i : ι ↦ G ∩ (Hι i)) := by
  have hG : Pairwise (Compatible on fun i ↦ G ∩ Hι i) := by
    exact fun i j hne ↦ hH.of_refl i j |>.mono Graph.inter_le_right Graph.inter_le_right
  have hG' : Pairwise (Dup_agree on fun i ↦ G ∩ Hι i) := by
    exact fun i j hne ↦ hH'.of_refl i j |>.mono Graph.inter_le_right Graph.inter_le_right
  apply Graph.ext ?_ fun e x y ↦ ?_
  · rw [iUnion_vertexSet hG', inter_vertexSet, iUnion_vertexSet hH', inter_comm, iUnion_inter]
    simp_rw [inter_comm, inter_vertexSet]
  rw [inter_isLink, iUnion_isLink hG hG']
  simp only [Pi.inf_apply, inf_Prop_eq, inter_isLink, exists_and_left, and_congr_right_iff]
  rintro he
  rw [iUnion_isLink hH hH']

protected lemma inter_distrib_sUnion (hs : s.Pairwise Compatible) (hs' : s.Pairwise Dup_agree) :
    G ∩ (Graph.sUnion s) = Graph.sUnion ((fun K ↦ G ∩ K) '' s) := by
  have hG : ((fun K ↦ G ∩ K) '' s).Pairwise Compatible := by
    rintro _ ⟨K₁, hK₁, rfl⟩ _ ⟨K₂, hK₂, rfl⟩ -
    exact hs.of_refl hK₁ hK₂ |>.mono Graph.inter_le_right Graph.inter_le_right
  have hG' : ((fun K ↦ G ∩ K) '' s).Pairwise Dup_agree := by
    rintro _ ⟨K₁, hK₁, rfl⟩ _ ⟨K₂, hK₂, rfl⟩ -
    exact hs'.of_refl hK₁ hK₂ |>.mono Graph.inter_le_right Graph.inter_le_right
  apply Graph.ext ?_ fun e x y ↦ ?_
  · rw [inter_vertexSet, sUnion_vertexSet hs', inter_comm]
    simp_rw [sUnion_vertexSet hG', Set.iUnion₂_inter, inter_comm]
    simp
  rw [sUnion_isLink hG hG']
  simp only [inter_isLink, Pi.inf_apply, sUnion_isLink hs hs', inf_Prop_eq, mem_image,
    exists_exists_and_eq_and]
  tauto

lemma Pairwise.union_compatible (hst : (s ∪ t).Pairwise Compatible)
    (hst' : (s ∪ t).Pairwise Dup_agree): (Graph.sUnion s).Compatible (Graph.sUnion t) := by
  have hs : s.Pairwise Compatible := hst.mono subset_union_left
  have ht : t.Pairwise Compatible := hst.mono subset_union_right
  have hs' : s.Pairwise Dup_agree := hst'.mono subset_union_left
  have ht' : t.Pairwise Dup_agree := hst'.mono subset_union_right
  refine compatible_of_le_le (G := Graph.sUnion (s ∪ t)) ?_ ?_
  <;> rw [Graph.sUnion_le_iff (by assumption) (by assumption)]
  <;> exact fun G hG ↦ Graph.le_sUnion (by assumption) (by assumption) (by simp [hG])

lemma sUnion_union_sUnion (hst : (s ∪ t).Pairwise Compatible) (hst' : (s ∪ t).Pairwise Dup_agree) :
    Graph.sUnion s ∪ Graph.sUnion t = Graph.sUnion (s ∪ t) := by
  have hs : s.Pairwise Compatible := hst.mono subset_union_left
  have ht : t.Pairwise Compatible := hst.mono subset_union_right
  have hs' : s.Pairwise Dup_agree := hst'.mono subset_union_left
  have ht' : t.Pairwise Dup_agree := hst'.mono subset_union_right
  have hST : (Graph.sUnion s).Compatible (Graph.sUnion t) :=
    sUnion_compatible_sUnion_of_subset hst hst' subset_union_left subset_union_right
  have hST' : (Graph.sUnion s).Dup_agree (Graph.sUnion t) :=
    sUnion_dup_agree_sUnion_of_subset hst' subset_union_left subset_union_right
  refine Graph.ext ?_ fun e x y ↦ ?_
  · rw [sUnion_vertexSet hst', union_vertexSet hST', sUnion_vertexSet hs', sUnion_vertexSet ht']
    exact (biUnion_union s t vertexSet).symm
  rw [sUnion_isLink hst hst', hST.union_isLink hST', sUnion_isLink hs hs', sUnion_isLink ht ht']
  aesop

omit [Nonempty ι] in
lemma Compatible.sum_compatible (hGH : Pairwise (Compatible on (Sum.elim Gι H'ι)))
    (hGH' : Pairwise (Dup_agree on (Sum.elim Gι H'ι))) :
    (Graph.iUnion Gι).Compatible (Graph.iUnion H'ι) :=
  compatible_of_le_le (iUnion_left_le_iUnion_sum hGH hGH') <| iUnion_right_le_iUnion_sum hGH hGH'

protected lemma iUnion_sum (hGH : Pairwise (Compatible on (Sum.elim Gι H'ι)))
    (hGH' : Pairwise (Dup_agree on (Sum.elim Gι H'ι))) :
    Graph.iUnion (Sum.elim Gι H'ι) = (.iUnion Gι) ∪ (.iUnion H'ι) := by
  refine le_antisymm ?_ <| Graph.union_le (iUnion_left_le_iUnion_sum hGH hGH')
    (iUnion_right_le_iUnion_sum hGH hGH')
  rw [Graph.iUnion_le_iff hGH hGH']
  rintro (i | i) <;> simp only [Sum.elim_inl, Sum.elim_inr]
  · refine le_trans (Graph.le_iUnion hGH.sum_left hGH'.sum_left i) (Graph.left_le_union ?_)
    sorry
  · exact le_trans (Graph.le_iUnion hGH.sum_right hGH'.sum_right i)
      (Compatible.right_le_union (Compatible.sum_compatible hGH hGH') sorry)

section Subgraph

/-! ### Subgraphs -/

variable {H₁ H₂ : Graph α β}

omit [Nonempty ι] in
lemma pairwise_compatible_of_subgraph (h : ∀ i, Hι i ≤ G) :
    Pairwise (Compatible on Hι) :=
  fun i j _ ↦ compatible_of_le_le (h i) (h j)

lemma set_pairwise_compatible_of_subgraph (h : ∀ ⦃H⦄, H ∈ s → H ≤ G) :
    s.Pairwise Compatible :=
  fun _ hi _ hj _ ↦ compatible_of_le_le (h hi) (h hj)

omit [Nonempty ι] in
protected lemma iUnion_le_of_forall_le (h : ∀ i, Hι i ≤ G) : .iUnion Hι ≤ G := by
  rwa [Graph.iUnion_le_iff]
  · exact compatible_of_forall_map_le h
  · exact dup_agree_of_forall_map_le h

protected lemma sUnion_le_of_forall_le (h : ∀ ⦃H⦄, H ∈ s → H ≤ G) : .sUnion s ≤ G := by
  rwa [Graph.sUnion_le_iff]
  · exact compatible_of_forall_mem_le h
  · exact dup_agree_of_forall_mem_le h

protected lemma iInter_le_of_forall_le (h : ∀ i, Hι i ≤ G) : .iInter Hι ≤ G :=
  (Graph.iInter_le (Classical.arbitrary ι)).trans <| h _

protected lemma sInter_le_of_forall_le (h : ∀ ⦃H⦄, H ∈ s → H ≤ G) (hne : s.Nonempty) :
    .sInter s hne ≤ G :=
  have := hne.to_subtype
  Graph.iInter_le_of_forall_le (by simpa)

omit [Nonempty ι] in
/-- A union of closed subgraphs of `G` is a closed subgraph of `G`. -/
lemma iUnion_isClosedSubgraph (h : ∀ i, Hι i ≤c G) : .iUnion Hι ≤c G where
  le := Graph.iUnion_le_of_forall_le fun i ↦ (h i).le
  closed e x he := by
    rw [iUnion_vertexSet, iUnion_edgeSet]
    simp only [mem_iUnion, forall_exists_index]
    exact fun i hxi ↦ ⟨_, (he.of_isClosedSubgraph_of_mem (h i) hxi).edge_mem⟩
    · exact compatible_of_forall_map_le (fun a ↦ (h a).le)
    · exact dup_agree_of_forall_map_le (fun a ↦ (h a).le)

/-- A nonempty union of spanning subgraphs of `G` is a spanning subgraph of `G`. -/
lemma iUnion_isSpanningSubgraph (h : ∀ i, Hι i ≤s G) : .iUnion Hι ≤s G where
  vertexSet_eq := by
    rw [iUnion_vertexSet, iUnion_eq_const (fun i ↦ (h i).vertexSet_eq)]
    exact dup_agree_of_forall_map_le (fun a ↦ (h a).le)
  isLink_of_isLink := (Graph.iUnion_le_of_forall_le fun i ↦ (h i).le).isLink_of_isLink

-- A weakening of the previous lemma.
omit [Nonempty ι] in
lemma iUnion_isSpanningSubgraph_of_exists_isSpanningSubgraph_of_forall_le
    (h : ∀ i, Hι i ≤ G) (hH : ∃ i, Hι i ≤s G) : .iUnion Hι ≤s G where
  vertexSet_eq := by
    apply le_antisymm
    · simp only [iUnion_vertexSet (dup_agree_of_forall_map_le (fun a ↦ h a)), le_eq_subset,
        iUnion_subset_iff]
      exact fun i ↦ (h i).vertexSet_subset
    obtain ⟨i, hi⟩ := hH
    rw [← hi.vertexSet_eq, iUnion_vertexSet (dup_agree_of_forall_map_le (fun a ↦ h a))]
    exact subset_iUnion_of_subset i fun ⦃a⦄ a ↦ a
  isLink_of_isLink := (Graph.iUnion_le_of_forall_le h).isLink_of_isLink

/-- A nonempty intersection of induced subgraphs `G` is an induced subgraph of `G`-/
lemma iInter_isInducedSubgraph (h : ∀ i, Hι i ≤i G) : .iInter Hι ≤i G where
  le := Graph.iInter_le_of_forall_le fun i ↦ (h i).le
  isLink_of_mem_mem e x y hxy hx hy i := by
    simp only [iInter_vertexSet, mem_iInter] at hx hy
    exact (h i).isLink_of_mem_mem hxy (hx i) (hy i)

/-- A nonempty intersection of spanning subgraphs of `G` is a spanning subgraph of `G`.-/
lemma iInter_isSpanningSubgraph (h : ∀ i, Hι i ≤s G) : .iInter Hι ≤s G where
  isLink_of_isLink := (Graph.iInter_le_of_forall_le fun i ↦ (h i).le).isLink_of_isLink
  vertexSet_eq := iInter_eq_const fun i ↦ (h i).vertexSet_eq

/-- A nonempty intersection of closed subgraphs `G` is an induced subgraph of `G`-/
lemma iInter_isClosedSubgraph (h : ∀ i, Hι i ≤c G) : .iInter Hι ≤c G where
  le := Graph.iInter_le_of_forall_le fun i ↦ (h i).le
  closed e x := by
    rw [iInter_vertexSet, mem_iInter]
    rintro ⟨y, hy⟩ hx
    use x, y, fun i ↦ by rwa [(h i).isLink_iff_of_mem (hx i)]

lemma sUnion_isClosedSubgraph (hs : ∀ ⦃H⦄, H ∈ s → H ≤c G) : .sUnion s ≤c G where
  le := Graph.sUnion_le_of_forall_le fun i hi ↦ (hs hi).le
  closed e x := by
    rw [sUnion_vertexSet, sUnion_edgeSet]
    simp only [mem_iUnion, exists_prop, forall_exists_index, and_imp]
    rintro he H hHs hxH
    
    use x, y, fun i ↦ by rwa [(hs i).isLink_iff_of_mem (hx i)]


lemma sUnion_isSpanningSubgraph (hs : ∀ ⦃H⦄, H ∈ s → H ≤s G) (hne : s.Nonempty) : .sUnion s ≤s G :=
  have := hne.to_subtype
  iUnion_isSpanningSubgraph <| by simpa

lemma sInter_isInducedSubgraph (hs : ∀ ⦃H⦄, H ∈ s → H ≤i G) (hne : s.Nonempty) :
    Graph.sInter s hne ≤i G :=
  have := hne.to_subtype
  iInter_isInducedSubgraph <| by simpa

lemma sInter_isClosedSubgraph (hs : ∀ ⦃H⦄, H ∈ s → H ≤c G) (hne : s.Nonempty) :
    Graph.sInter s hne ≤c G :=
  have := hne.to_subtype
  iInter_isClosedSubgraph <| by simpa

lemma isClosedSubgraph_iUnion_of_stronglyDisjoint (h : Pairwise (StronglyDisjoint on H)) (i : ι) :
    H i ≤c Graph.iUnion H (h.mono fun _ _ ↦ StronglyDisjoint.compatible) where
  le := Graph.le_iUnion ..
  closed e x he hx := by
    obtain ⟨j, hj : (H j).Inc e x⟩ := (iUnion_inc_iff ..).1 he
    obtain rfl | hne := eq_or_ne i j
    · exact hj.edge_mem
    exact False.elim <| (h hne).vertex.notMem_of_mem_left hx hj.vertex_mem

lemma isClosedSubgraph_sUnion_of_stronglyDisjoint (s : Set (Graph α β))
    (hs : s.Pairwise StronglyDisjoint) (hG : G ∈ s) : G ≤c Graph.sUnion s (hs.mono' (by simp)) :=
  isClosedSubgraph_iUnion_of_stronglyDisjoint ((pairwise_subtype_iff_pairwise_set ..).2 hs) ⟨G, hG⟩

lemma isClosedSubgraph_union_left_of_vertexSet_disjoint (h : Disjoint V(H₁) V(H₂)) :
    H₁ ≤c H₁ ∪ H₂ := by
  refine ⟨Graph.left_le_union H₁ H₂, fun e x hinc hx₁ => ?_⟩
  have hninc : ¬ H₂.Inc e x := fun hinc ↦ h.notMem_of_mem_left hx₁ hinc.vertex_mem
  simp only [union_inc_iff, hninc, false_and, or_false] at hinc
  exact hinc.edge_mem

lemma Disjoint.isClosedSubgraph_union_left (h : Disjoint H₁ H₂) : H₁ ≤c H₁ ∪ H₂ :=
  isClosedSubgraph_union_left_of_vertexSet_disjoint <| Disjoint.vertex_disjoint h

lemma StronglyDisjoint.isClosedSubgraph_union_left (h : StronglyDisjoint H₁ H₂) :
    H₁ ≤c H₁ ∪ H₂ := by
  rw [(stronglyDisjoint_le_compatible _ _ h).union_eq_sUnion]
  exact isClosedSubgraph_sUnion_of_stronglyDisjoint _ (by simp [Set.Pairwise, h, h.symm]) (by simp)

lemma StronglyDisjoint.isClosedSubgraph_union_right (h : StronglyDisjoint H₁ H₂) :
    H₂ ≤c H₁ ∪ H₂ := by
  rw [(stronglyDisjoint_le_compatible _ _ h).union_eq_sUnion]
  exact isClosedSubgraph_sUnion_of_stronglyDisjoint _ (by simp [Set.Pairwise, h, h.symm]) (by simp)

lemma IsClosedSubgraph.union (h₁ : H₁ ≤c G) (h₂ : H₂ ≤c G) : H₁ ∪ H₂ ≤c G := by
  rw [(compatible_of_le_le h₁.le h₂.le).union_eq_iUnion]
  exact iUnion_isClosedSubgraph <| by simp [h₁,h₂]

lemma IsSpanningSubgraph.union (h₁ : H₁ ≤s G) (h₂ : H₂ ≤s G) : H₁ ∪ H₂ ≤s G := by
  rw [(compatible_of_le_le h₁.le h₂.le).union_eq_iUnion]
  exact iUnion_isSpanningSubgraph <| by simp [h₁,h₂]

lemma IsSpanningSubgraph.union_left (h₁ : H₁ ≤s G) (h₂ : H₂ ≤ G) : H₁ ∪ H₂ ≤s G := by
  rw [(compatible_of_le_le h₁.le h₂).union_eq_iUnion]
  exact iUnion_isSpanningSubgraph_of_exists_isSpanningSubgraph_of_forall_le (by simp [h₁.le, h₂])
    ⟨True, h₁⟩

lemma IsSpanningSubgraph.union_right (h₁ : H₁ ≤ G) (h₂ : H₂ ≤s G) : H₁ ∪ H₂ ≤s G := by
  rw [(compatible_of_le_le h₁ h₂.le).union_eq_iUnion]
  exact iUnion_isSpanningSubgraph_of_exists_isSpanningSubgraph_of_forall_le (by simp [h₁, h₂.le])
    ⟨False, h₂⟩

lemma IsInducedSubgraph.inter (h₁ : H₁ ≤i G) (h₂ : H₂ ≤i G) : H₁ ∩ H₂ ≤i G := by
  rw [inter_eq_iInter]
  exact iInter_isInducedSubgraph <| by simp [h₁,h₂]

lemma IsClosedSubgraph.inter (h₁ : H₁ ≤c G) (h₂ : H₂ ≤c G) : H₁ ∩ H₂ ≤c G := by
  rw [inter_eq_iInter]
  exact iInter_isClosedSubgraph <| by simp [h₁,h₂]

lemma IsClosedSubgraph.inter_le {K G H : Graph α β} (hKG : K ≤c G) (hle : H ≤ G) : K ∩ H ≤c H where
  le := Graph.inter_le_right
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
lemma isSpanningSubgraph_bot_iff : G ≤s ⊥ ↔ G = ⊥ :=
  ⟨fun h => le_bot_iff.mp h.le, fun h => h ▸ ⟨le_rfl, rfl⟩⟩

@[simp]
lemma isInducedSubgraph_bot_iff : G ≤i ⊥ ↔ G = ⊥ :=
  ⟨fun h => le_bot_iff.mp h.le, fun h => h ▸ bot_isInducedSubgraph ⊥⟩

@[simp]
lemma induce_empty : G[⊥] = ⊥ := by
  rw [← vertexSet_eq_empty_iff]
  simp

end Subgraph

end Graph
