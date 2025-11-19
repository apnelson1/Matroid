import Matroid.Graph.Subgraph.Delete
import Matroid.Graph.Subgraph.Union
import Matroid.Graph.Subgraph.Inter

variable {α β ι ι' : Type*} {x y z u v w : α} {e f : β} {F F₁ F₂ : Set β} {X Y : Set α}
  {G G₁ G₂ H H₁ H₂ : Graph α β} {F F₁ F₂ : Set β} {X Y : Set α} {s t : Set (Graph α β)}
  {Gι Hι : ι → Graph α β} {Gι' Hι' : ι' → Graph α β}

open Set Function

namespace Graph

lemma stronglyDisjoint_iff_disjoint_of_compatible (h : H₁.Compatible H₂) :
    StronglyDisjoint H₁ H₂ ↔ Disjoint H₁ H₂ := by
  rw [stronglyDisjoint_iff_vertexSet_disjoint_compatible, Set.disjoint_iff_inter_eq_empty,
    disjoint_iff, ← vertexSet_eq_empty_iff]
  simp [h]

lemma iInter_option_eq_sInter_insert {G₁ : Graph α β} {G : ι → Graph α β} :
    Graph.iInter (Option.elim · G₁ G) = Graph.sInter (insert G₁ (range G)) (by simp) := by
  obtain hι | hι := isEmpty_or_nonempty ι
  · simp [range_eq_empty G]
  rw [Graph.sInter_insert _ (range_nonempty _), Graph.sInter_range, Graph.iInter_option]

lemma isClosedSubgraph_iUnion_of_stronglyDisjoint (h : Pairwise (StronglyDisjoint on Hι)) (i : ι) :
    Hι i ≤c Graph.iUnion Hι (h.mono fun _ _ ↦ StronglyDisjoint.compatible) where
  le := Graph.le_iUnion ..
  closed e x he hx := by
    obtain ⟨j, hj : (Hι j).Inc e x⟩ := (iUnion_inc_iff ..).1 he
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
  ⟨fun h => le_bot_iff.mp h.le, fun h => h ▸ ⟨rfl, (le_refl G).isLink_of_isLink⟩⟩

@[simp]
lemma isInducedSubgraph_bot_iff : G ≤i ⊥ ↔ G = ⊥ :=
  ⟨fun h => le_bot_iff.mp h.le, fun h => h ▸ bot_isInducedSubgraph ⊥⟩

/-! ### Adding one edge -/

lemma addEdge_deleteEdge (he : e ∉ E(G)) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    (G.addEdge e x y) ＼ {e} = G := by
  have hc : Compatible (Graph.singleEdge x y e) G := by simp [he]
  simp only [Graph.addEdge, Graph.ext_iff, edgeDelete_vertexSet, union_vertexSet,
    singleEdge_vertexSet, union_eq_right, insert_subset_iff, hx, singleton_subset_iff, hy, and_self,
    edgeDelete_isLink, hc.union_isLink_iff, singleEdge_isLink, mem_singleton_iff, true_and]
  intro f p q
  obtain rfl | hne := eq_or_ne f e
  · suffices ¬ G.IsLink f p q by simpa
    exact fun hf ↦ he hf.edge_mem
  simp [hne]

@[gcongr]
lemma addEdge_mono (hle : H ≤ G) : H.addEdge e x y ≤ G.addEdge e x y :=
  union_mono_right hle

lemma deleteEdge_le_addEdge : G ＼ {e} ≤ G.addEdge e x y := by
  rw [Graph.addEdge, union_eq_union_edgeDelete]
  simp only [singleEdge_edgeSet]
  exact Compatible.right_le_union <| by simp

lemma deleteEdge_addEdge : (G ＼ {e}).addEdge e x y = G.addEdge e x y := by
  refine le_antisymm (addEdge_mono edgeDelete_le) ?_
  unfold Graph.addEdge
  rw [union_le_iff]
  refine ⟨Graph.left_le_union (Graph.singleEdge x y e) (G ＼ {e}), Compatible.right_le_union ?_⟩
  simp

lemma isSpanningSubgraph_addEdge (he : e ∉ E(G)) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    G ≤s G.addEdge e x y := by
  nth_rw 1 [← addEdge_deleteEdge he hx hy]
  exact edgeDelete_isSpanningSubgraph

lemma IsLink.deleteEdge_addEdge (h : G.IsLink e x y) : (G ＼ {e}).addEdge e x y = G :=
  ext_of_le_le (addEdge_le (by simp) h) le_rfl (by simp [pair_subset_iff, h.left_mem, h.right_mem])
    <| by simp [h.edge_mem]

end Graph
