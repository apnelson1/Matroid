import Matroid.Graph.Subgraph.Add

variable {α β ι ι' : Type*} {x y z u v w : α} {e f : β} {F F₁ F₂ : Set β} {X Y : Set α}

open Set Function

namespace Graph

section CompleteLattice

variable [CompleteLattice α] {P Q : Partition α} {Gs Hs : Set (Graph α β)}
  {G G₁ G₂ H H₁ H₂ : Graph α β} {Gι Hι : ι → Graph α β} {H'ι : ι' → Graph α β}

@[simp↓]
lemma iInter_inc_of_compatible [Nonempty ι] (hG' : Pairwise (Compatible on Gι)) :
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

lemma iInter_le_iUnion [Nonempty ι] (hGι : Agree (range Gι)) : Graph.iInter Gι ≤ Graph.iUnion Gι :=
  (Graph.iInter_le (Classical.arbitrary ι)).trans <| Graph.le_iUnion hGι _

protected lemma inter_distrib_sUnion (h : Agree Gs) :
    G ∩ (Graph.sUnion Gs) = Graph.sUnion ((fun K ↦ G ∩ K) '' Gs) := by
  have hG : Agree ((G ∩ ·) '' Gs) := h.mono fun H hH ↦  by
    obtain ⟨K, hK, rfl⟩ := hH
    exact ⟨K, hK, Graph.inter_le_right⟩
  apply Graph.ext ?_ fun e x y ↦ ?_
  · simp [hG, h, inter_iUnion]
  simp only [h, sUnion_eq_sUnion', inter_isLink, Pi.inf_apply, sUnion'_isLink, inf_Prop_eq, hG,
    mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, exists_exists_and_eq_and]
  tauto

protected lemma inter_distrib_iUnion (h : Agree (range Hι)) :
    G ∩ (Graph.iUnion Hι) = Graph.iUnion (fun i : ι ↦ G ∩ (Hι i)) := by
  rw [iUnion_eq_sUnion, iUnion_eq_sUnion, Graph.inter_distrib_sUnion h, ← range_comp]
  rfl

end CompleteLattice

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

protected lemma iUnion_le_of_forall_le (h : ∀ i, Hι i ≤ G) : .iUnion Hι ≤ G := by
  rwa [Graph.iUnion_le_iff]
  exact ⟨G, fun H ⟨i, hi⟩ ↦ hi ▸ (h i)⟩

protected lemma sUnion_le_of_forall_le (h : ∀ ⦃H⦄, H ∈ Gs → H ≤ G) : .sUnion Gs ≤ G := by
  rwa [Graph.sUnion_le_iff]
  exact ⟨G, fun H h' ↦ h h'⟩

/-- A union of closed subgraphs of `G` is a closed subgraph of `G`. -/
lemma iUnion_isClosedSubgraph (h : ∀ i, Hι i ≤c G) : .iUnion Hι ≤c G where
  toIsSubgraph := Graph.iUnion_le_of_forall_le fun i ↦ (h i).le
  closed e x he := by
    have h' : Agree (range Hι) := ⟨G, fun H ⟨i, hi⟩ ↦ hi ▸ (h i).le⟩
    rw [iUnion_vertexSet h', iUnion_edgeSet h']
    simp only [mem_iUnion, forall_exists_index]
    exact fun i hxi ↦ ⟨_, (he.of_isClosedSubgraph_of_mem (h i) hxi).edge_mem⟩

/-- A nonempty union of spanning subgraphs of `G` is a spanning subgraph of `G`. -/
lemma iUnion_isSpanningSubgraph [Nonempty ι] (h : ∀ i, Hι i ≤s G) : .iUnion Hι ≤s G where
  vertexSet_eq := by
    have h' : Agree (range Hι) := ⟨G, fun H ⟨i, hi⟩ ↦ hi ▸ (h i).le⟩
    rw [iUnion_vertexSet h', iUnion_eq_const (fun i ↦ (h i).vertexSet_eq)]
  isLink_of_isLink := (Graph.iUnion_le_of_forall_le fun i ↦ (h i).le).isLink_of_isLink

-- A weakening of the previous lemma.
lemma iUnion_isSpanningSubgraph_of_exists_isSpanningSubgraph_of_forall_le
    (h : ∀ i, Hι i ≤ G) (hH : ∃ i, Hι i ≤s G) : .iUnion Hι ≤s G where
  vertexSet_eq := by
    have h' : Agree (range Hι) := ⟨G, fun H ⟨i, hi⟩ ↦ hi ▸ (h i)⟩
    apply le_antisymm
    · simp only [iUnion_vertexSet h', le_eq_subset, iUnion_subset_iff]
      exact fun i ↦ (h i).vertexSet_subset
    obtain ⟨i, hi⟩ := hH
    rw [← hi.vertexSet_eq, iUnion_vertexSet h']
    exact subset_iUnion_of_subset i fun ⦃a⦄ a ↦ a
  isLink_of_isLink := (Graph.iUnion_le_of_forall_le h).isLink_of_isLink

lemma sUnion_isClosedSubgraph (hsc : ∀ ⦃H⦄, H ∈ Gs → H ≤c G) : .sUnion Gs ≤c G := by
  let f : Gs → Graph α β := Subtype.val
  have : .iUnion f ≤c G := iUnion_isClosedSubgraph <| by
    rintro ⟨H, hHs⟩
    simp [f, hsc hHs]
  convert this
  simp [f, Graph.iUnion_eq_sUnion]

lemma sUnion_isSpanningSubgraph (hs : ∀ ⦃H⦄, H ∈ Gs → H ≤s G) (hne : Gs.Nonempty) :
    .sUnion Gs ≤s G := by
  let f : Gs → Graph α β := Subtype.val
  have hne := hne.to_subtype
  have : .iUnion f ≤s G := iUnion_isSpanningSubgraph <| by
    rintro ⟨H, hHs⟩
    simp [f, hs hHs]
  convert this
  simp [f, Graph.iUnion_eq_sUnion]

lemma IsClosedSubgraph.union (h₁ : H₁ ≤c G) (h₂ : H₂ ≤c G) : H₁ ∪ H₂ ≤c G := by
  rw [union_eq_iUnion]
  exact iUnion_isClosedSubgraph <| by simp [h₁,h₂]

lemma IsSpanningSubgraph.union (h₁ : H₁ ≤s G) (h₂ : H₂ ≤s G) : H₁ ∪ H₂ ≤s G := by
  rw [union_eq_iUnion]
  exact iUnion_isSpanningSubgraph <| by simp [h₁,h₂]

lemma IsSpanningSubgraph.union_left (h₁ : H₁ ≤s G) (h₂ : H₂ ≤ G) : H₁ ∪ H₂ ≤s G := by
  rw [union_eq_iUnion]
  exact iUnion_isSpanningSubgraph_of_exists_isSpanningSubgraph_of_forall_le (by simp [h₁.le, h₂])
    ⟨True, h₁⟩

lemma IsSpanningSubgraph.union_right (h₁ : H₁ ≤ G) (h₂ : H₂ ≤s G) : H₁ ∪ H₂ ≤s G := by
  rw [union_eq_iUnion]
  exact iUnion_isSpanningSubgraph_of_exists_isSpanningSubgraph_of_forall_le (by simp [h₁, h₂.le])
    ⟨False, h₂⟩

end Subgraph
end Graph
