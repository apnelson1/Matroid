import Matroid.Graph.Subgraph.Add
import Matroid.Graph.Subgraph.Inter

variable {α β ι ι' : Type*} {x y z u v w : Set α} {e f : β} {G G₁ G₂ H H₁ H₂ : Graph α β}
  {F F₁ F₂ : Set β} {X Y : Set (Set α)} {s t : Set (Graph α β)} {P Q : Partition (Set α)}
  [Nonempty ι]

open Set Function

namespace Graph

lemma iInter_le_iUnion {G : ι → Graph α β} (hG : Pairwise (Compatible on G)) :
    Graph.iInter G ≤ Graph.iUnion G :=
  (Graph.iInter_le (Classical.arbitrary ι)).trans <| Graph.le_iUnion ..

@[simp↓]
lemma iInter_inc_of_compatible (hG : Pairwise (Dup_agree on G)) (hG' : Pairwise (Compatible on G)) :
    (Graph.iInter G).Inc e x ↔ ∀ i, (G i).Inc e x := by
  rw [iInter_inc hG]
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

protected lemma inter_distrib_iUnion {H : ι → Graph α β} (hH : Pairwise (Compatible on H)) :
    G ∩ (Graph.iUnion H hH) = Graph.iUnion (fun i ↦ G ∩ (H i))
      (fun _ _ hne ↦ (hH hne).mono Graph.inter_le_right Graph.inter_le_right) :=
  Graph.ext (by simp [inter_iUnion]) (by simp)

protected lemma inter_distrib_sUnion (hs : s.Pairwise Compatible) :
    G ∩ (Graph.sUnion s hs) = Graph.sUnion ((fun K ↦ G ∩ K) '' s) (by
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

lemma set_pairwise_compatible_of_subgraph (h : ∀ ⦃H⦄, H ∈ s → H ≤ G) :
    s.Pairwise Compatible :=
  fun _ hi _ hj _ ↦ compatible_of_le_le (h hi) (h hj)

-- protected lemma iUnion_le_of_forall_le (h : ∀ i, H i ≤ G) :
--     .iUnion H (pairwise_compatible_of_subgraph h) ≤ G := by
--   simpa

-- protected lemma sUnion_le_of_forall_le (h : ∀ ⦃H⦄, H ∈ s → H ≤ G) :
--     Graph.sUnion s (set_pairwise_compatible_of_subgraph h) ≤ G := by
--   simpa

-- protected lemma iInter_le_of_forall_le [Nonempty ι] (h : ∀ i, H i ≤ G) :
--     Graph.iInter H ≤ G :=
--   (Graph.iInter_le (Classical.arbitrary ι)).trans <| h _

-- protected lemma sInter_le_of_forall_le (h : ∀ ⦃H⦄, H ∈ s → H ≤ G) (hne : s.Nonempty) :
--     Graph.sInter s hne ≤ G :=
--   have := hne.to_subtype
--   Graph.iInter_le_of_forall_le (by simpa)

-- /-- A union of closed subgraphs of `G` is a closed subgraph of `G`. -/
-- lemma iUnion_isClosedSubgraph (h : ∀ i, H i ≤c G) :
--     Graph.iUnion H (pairwise_compatible_of_subgraph (fun i ↦ (h i).le)) ≤c G where
--   le := Graph.iUnion_le_of_forall_le fun i ↦ (h i).le
--   closed e x he := by
--     simp only [iUnion_vertexSet, mem_iUnion, iUnion_edgeSet, forall_exists_index]
--     exact fun i hxi ↦ ⟨_, (he.of_isClosedSubgraph_of_mem (h i) hxi).edge_mem⟩

-- /-- A nonempty union of spanning subgraphs of `G` is a spanning subgraph of `G`. -/
-- lemma iUnion_isSpanningSubgraph [Nonempty ι] (h : ∀ i, H i ≤s G) :
--     Graph.iUnion H (pairwise_compatible_of_subgraph (fun i ↦ (h i).le)) ≤s G where
--   le := Graph.iUnion_le_of_forall_le fun i ↦ (h i).le
--   vertexSet_eq := by simp [(h _).vertexSet_eq, iUnion_const]

-- -- A weakening of the previous lemma.
-- lemma iUnion_isSpanningSubgraph_of_exists_isSpanningSubgraph_of_forall_le [Nonempty ι]
--     (h : ∀ i, H i ≤ G) (hH : ∃ i, H i ≤s G) :
--     Graph.iUnion H (pairwise_compatible_of_subgraph h) ≤s G where
--   le := Graph.iUnion_le_of_forall_le h
--   vertexSet_eq := by
--     apply le_antisymm
--     · simp only [iUnion_vertexSet, le_eq_subset, iUnion_subset_iff]
--       exact fun i ↦ (h i).vertex_subset
--     obtain ⟨i, hi⟩ := hH
--     rw [← hi.vertexSet_eq]
--     exact subset_iUnion_of_subset i fun ⦃a⦄ a ↦ a

-- /-- A nonempty intersection of induced subgraphs `G` is an induced subgraph of `G`-/
-- lemma iInter_isInducedSubgraph [Nonempty ι] (h : ∀ i, H i ≤i G) :
--     Graph.iInter H ≤i G where
--   le := Graph.iInter_le_of_forall_le fun i ↦ (h i).le
--   isLink_of_mem_mem := by
--     simp only [iInter_vertexSet, mem_iInter, iInter_isLink]
--     exact fun e x y he hx hy i ↦ (h i).isLink_of_mem_mem he (hx i) (hy i)

-- /-- A nonempty intersection of spanning subgraphs of `G` is a spanning subgraph of `G`.-/
-- lemma iInter_isSpanningSubgraph [Nonempty ι] (h : ∀ i, H i ≤s G) :
--     Graph.iInter H ≤s G where
--   le := Graph.iInter_le_of_forall_le fun i ↦ (h i).le
--   vertexSet_eq := iInter_eq_const fun i ↦ (h i).vertexSet_eq

-- /-- A nonempty intersection of closed subgraphs `G` is an induced subgraph of `G`-/
-- lemma iInter_isClosedSubgraph [Nonempty ι] (h : ∀ i, H i ≤c G) :
--     Graph.iInter H ≤c G where
--   le := Graph.iInter_le_of_forall_le fun i ↦ (h i).le
--   closed e x he := by
--     simp only [iInter_vertexSet, mem_iInter, iInter_edgeSet, mem_setOf_eq]
--     rintro hx
--     obtain ⟨y, hy⟩ := he
--     use x, y, fun i ↦ by rwa [(h i).isLink_iff_of_mem (hx i)]

-- lemma sUnion_isClosedSubgraph (hs : ∀ ⦃H⦄, H ∈ s → H ≤c G) :
--     Graph.sUnion s (set_pairwise_compatible_of_subgraph (fun _ h ↦ (hs h).le)) ≤c G :=
--   iUnion_isClosedSubgraph <| by simpa

-- lemma sUnion_isSpanningSubgraph (hs : ∀ ⦃H⦄, H ∈ s → H ≤s G) (hne : s.Nonempty) :
--     Graph.sUnion s (set_pairwise_compatible_of_subgraph (fun _ h ↦ (hs h).le)) ≤s G :=
--   have := hne.to_subtype
--   iUnion_isSpanningSubgraph <| by simpa

-- lemma sInter_isInducedSubgraph (hs : ∀ ⦃H⦄, H ∈ s → H ≤i G) (hne : s.Nonempty) :
--     Graph.sInter s hne ≤i G :=
--   have := hne.to_subtype
--   iInter_isInducedSubgraph <| by simpa

-- lemma sInter_isClosedSubgraph (hs : ∀ ⦃H⦄, H ∈ s → H ≤c G) (hne : s.Nonempty) :
--     Graph.sInter s hne ≤c G :=
--   have := hne.to_subtype
--   iInter_isClosedSubgraph <| by simpa

-- lemma isClosedSubgraph_iUnion_of_stronglyDisjoint (h : Pairwise (StronglyDisjoint on H)) (i : ι) :
--     H i ≤c Graph.iUnion H (h.mono fun _ _ ↦ StronglyDisjoint.compatible) where
--   le := Graph.le_iUnion ..
--   closed e x he hx := by
--     obtain ⟨j, hj : (H j).Inc e x⟩ := (iUnion_inc_iff ..).1 he
--     obtain rfl | hne := eq_or_ne i j
--     · exact hj.edge_mem
--     exact False.elim <| (h hne).vertex.notMem_of_mem_left hx hj.vertex_mem

-- lemma isClosedSubgraph_sUnion_of_stronglyDisjoint (s : Set (Graph α β))
--     (hs : s.Pairwise StronglyDisjoint) (hG : G ∈ s) : G ≤c Graph.sUnion s (hs.mono' (by simp)) :=
--   isClosedSubgraph_iUnion_of_stronglyDisjoint ((pairwise_subtype_iff_pairwise_set ..).2 hs) ⟨G, hG⟩

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
--   exact isClosedSubgraph_sUnion_of_stronglyDisjoint _ (by simp [Set.Pairwise, h, h.symm]) (by simp)

-- lemma StronglyDisjoint.isClosedSubgraph_union_right (h : StronglyDisjoint H₁ H₂) :
--     H₂ ≤c H₁ ∪ H₂ := by
--   rw [(stronglyDisjoint_le_compatible _ _ h).union_eq_sUnion]
--   exact isClosedSubgraph_sUnion_of_stronglyDisjoint _ (by simp [Set.Pairwise, h, h.symm]) (by simp)

-- lemma IsClosedSubgraph.union (h₁ : H₁ ≤c G) (h₂ : H₂ ≤c G) : H₁ ∪ H₂ ≤c G := by
--   rw [(compatible_of_le_le h₁.le h₂.le).union_eq_iUnion]
--   exact iUnion_isClosedSubgraph <| by simp [h₁,h₂]

-- lemma IsSpanningSubgraph.union (h₁ : H₁ ≤s G) (h₂ : H₂ ≤s G) : H₁ ∪ H₂ ≤s G := by
--   rw [(compatible_of_le_le h₁.le h₂.le).union_eq_iUnion]
--   exact iUnion_isSpanningSubgraph <| by simp [h₁,h₂]

-- lemma IsSpanningSubgraph.union_left (h₁ : H₁ ≤s G) (h₂ : H₂ ≤ G) : H₁ ∪ H₂ ≤s G := by
--   rw [(compatible_of_le_le h₁.le h₂).union_eq_iUnion]
--   exact iUnion_isSpanningSubgraph_of_exists_isSpanningSubgraph_of_forall_le (by simp [h₁.le, h₂])
--     ⟨True, h₁⟩

-- lemma IsSpanningSubgraph.union_right (h₁ : H₁ ≤ G) (h₂ : H₂ ≤s G) : H₁ ∪ H₂ ≤s G := by
--   rw [(compatible_of_le_le h₁ h₂.le).union_eq_iUnion]
--   exact iUnion_isSpanningSubgraph_of_exists_isSpanningSubgraph_of_forall_le (by simp [h₁, h₂.le])
--     ⟨False, h₂⟩

-- lemma IsInducedSubgraph.inter (h₁ : H₁ ≤i G) (h₂ : H₂ ≤i G) : H₁ ∩ H₂ ≤i G := by
--   rw [inter_eq_iInter]
--   exact iInter_isInducedSubgraph <| by simp [h₁,h₂]

-- lemma IsClosedSubgraph.inter (h₁ : H₁ ≤c G) (h₂ : H₂ ≤c G) : H₁ ∩ H₂ ≤c G := by
--   rw [inter_eq_iInter]
--   exact iInter_isClosedSubgraph <| by simp [h₁,h₂]

-- lemma IsClosedSubgraph.inter_le {K G H : Graph α β} (hKG : K ≤c G) (hle : H ≤ G) : K ∩ H ≤c H where
--   le := Graph.inter_le_right
--   closed e x hex hx := by
--     rw [inter_vertexSet] at hx
--     have heK := ((hex.of_le hle).of_isClosedSubgraph_of_mem hKG hx.1).edge_mem
--     rw [(compatible_of_le_le hKG.le hle).inter_edgeSet]
--     exact ⟨heK, hex.edge_mem⟩

-- @[simp]
-- lemma le_bot_iff : G ≤ ⊥ ↔ G = ⊥ := _root_.le_bot_iff

-- @[simp]
-- lemma isClosedSubgraph_bot_iff : G ≤c ⊥ ↔ G = ⊥ :=
--   ⟨fun h => le_bot_iff.mp h.le, fun h => h ▸ bot_isClosedSubgraph ⊥⟩

-- @[simp]
-- lemma isSpanningSubgraph_bot_iff : G ≤s ⊥ ↔ G = ⊥ :=
--   ⟨fun h => le_bot_iff.mp h.le, fun h => h ▸ ⟨le_rfl, rfl⟩⟩

-- @[simp]
-- lemma isInducedSubgraph_bot_iff : G ≤i ⊥ ↔ G = ⊥ :=
--   ⟨fun h => le_bot_iff.mp h.le, fun h => h ▸ bot_isInducedSubgraph ⊥⟩

@[simp]
lemma induce_empty : G[∅] = ⊥ := by
  rw [← labelSet_eq_empty_iff]
  simp

end Subgraph

end Graph
