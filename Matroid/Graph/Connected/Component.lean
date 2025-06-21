import Matroid.Graph.Connected.Basic

open Set Function Nat WList

variable {α β : Type*} {G H : Graph α β} {u v x x₁ x₂ y y₁ y₂ z : α} {e e' f g : β}
  {U V S T : Set α} {F F' R R': Set β} {C W P Q : WList α β}



namespace Graph

/-! ### Components -/

/-- `H.IsComponent G` if `H` is a maximal connected subgraph of `G`. -/
def IsComponent (H G : Graph α β) := Maximal (fun H ↦ H.Connected ∧ H ≤ G) H

lemma IsComponent.le (h : H.IsComponent G) : H ≤ G :=
  h.prop.2

lemma IsComponent.connected (h : H.IsComponent G) : H.Connected :=
  h.prop.1

lemma IsComponent.isClosedSubgraph (h : H.IsComponent G) : H ≤c G where
  le := h.le
  closed := by
    refine fun e x ⟨y, hy⟩ hx ↦ by_contra fun hcon ↦ ?_
    rw [← h.eq_of_ge ⟨h.connected.addEdge_connected hx hcon y, addEdge_le h.le hy⟩
      (le_addEdge hcon)] at hcon
    simp at hcon

lemma IsComponent.isInducedSubgraph (h : H.IsComponent G) : H ≤i G :=
  h.isClosedSubgraph.isInducedSubgraph

lemma isComponent_iff_isClosedSubgraph_connected : H.IsComponent G ↔ H ≤c G ∧ H.Connected := by
  refine ⟨fun h ↦ ⟨h.isClosedSubgraph, h.connected⟩, fun ⟨hHG, hH⟩ ↦ ⟨⟨hH, hHG.le⟩, ?_⟩⟩
  refine fun K ⟨hK, hKG⟩ hHK ↦ hHK.eq_or_lt.elim (fun h ↦ h ▸ le_rfl) fun hlt ↦ False.elim ?_
  obtain ⟨e, x, hex, heH, hxH⟩ := hK.exists_inc_notMem_of_lt hlt hH.nonempty
  exact heH <| ((hex.of_le hKG).of_isClosedSubgraph_of_mem hHG hxH).edge_mem

lemma IsClosedSubgraph.isComponent_of_connected (h : H ≤c G) (hH : H.Connected) :
    H.IsComponent G := by
  refine isComponent_iff_isClosedSubgraph_connected.2 ⟨h, hH⟩

lemma Connected.isComponent_of_isClosedSubgraph (hH : H.Connected) (h : H ≤c G) :
    H.IsComponent G := by
  refine isComponent_iff_isClosedSubgraph_connected.2 ⟨h, hH⟩

/-- If `x` is a vertex of `G`, the set of vertices connected to `x` induces a component of `G`. -/
lemma induce_setOf_vertexConnected_isComponent (hx : x ∈ V(G)) :
    (G[{y | G.VertexConnected x y}]).IsComponent G := by
  refine ⟨⟨⟨⟨x, by simpa⟩, fun y y' h h' ↦ ?_⟩, ?_⟩, fun H' ⟨hc, hH'le⟩ hle ↦ ?_⟩
  · obtain ⟨W, hW, rfl, rfl⟩ := (VertexConnected.trans h.symm h').exists_isWalk
    refine (hW.induce fun y hy ↦ ?_).vertexConnected_first_last
    simp only [induce_vertexSet, mem_setOf_eq] at h h'
    exact h.trans <| hW.vertexConnected_of_mem_of_mem (by simp) hy
  · exact induce_le_iff.2 fun y hy ↦ VertexConnected.right_mem hy
  refine le_induce_of_le_of_subset hH'le fun z hz ↦ ?_
  exact (hc.vertexConnected (x := x) (vertexSet_mono hle (by simpa)) hz).of_le hH'le

lemma exists_isComponent (hG : V(G).Nonempty) : ∃ (H : Graph α β), H.IsComponent G :=
  ⟨_, induce_setOf_vertexConnected_isComponent hG.choose_spec⟩

/-- Every connected subgraph of `G` is a subgraph of a component of `G`. -/
lemma Connected.exists_component_ge (hH : H.Connected) (hle : H ≤ G) :
    ∃ G₁, G₁.IsComponent G ∧ H ≤ G₁ := by
  obtain ⟨x, hx⟩ := hH.nonempty
  refine ⟨_, induce_setOf_vertexConnected_isComponent (vertexSet_mono hle hx), ?_⟩
  exact le_induce_of_le_of_subset hle fun y hy ↦ (hH.vertexConnected hx hy).of_le hle

lemma exists_isComponent_vertex_mem (hx : x ∈ V(G)) :
    ∃ (H : Graph α β), H.IsComponent G ∧ x ∈ V(H) :=
  ⟨_, induce_setOf_vertexConnected_isComponent hx, by simpa⟩

lemma exists_isComponent_edge_mem (he : e ∈ E(G)) :
    ∃ (H : Graph α β), H.IsComponent G ∧ e ∈ E(H) := by
  obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet he
  obtain ⟨H, hH, hle⟩ := (singleEdge_connected e x y).exists_component_ge (G := G) (by simpa)
  simp only [singleEdge_le_iff] at hle
  exact ⟨H, hH, hle.edge_mem⟩

lemma IsWalk.exists_isComponent_isWalk (hW : G.IsWalk W) :
    ∃ (H : Graph α β), H.IsComponent G ∧ H.IsWalk W := by
  obtain ⟨H, hle, hWH⟩ := hW.toGraph_connected.exists_component_ge hW.toGraph_le
  exact ⟨H, hle, by rwa [← hW.wellFormed.toGraph_le_iff]⟩

/-- Distinct components are vertex-disjoint. -/
lemma IsComponent.disjoint_of_ne {H₁ H₂ : Graph α β}
    (hH₁ : H₁.IsComponent G) (hH₂ : H₂.IsComponent G) (hne : H₁ ≠ H₂) : H₁.Disjoint H₂ := by
  refine Compatible.disjoint_of_vertexSet_disjoint (G.compatible_of_le_le hH₁.le hH₂.le) ?_
  rw [disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty]
  contrapose! hne
  have hc : Compatible H₁ H₂ := compatible_of_le_le hH₁.le hH₂.le
  rw [← hH₁.eq_of_ge ⟨(hc.union_connected_of_nonempty_inter hH₁.connected hH₂.connected hne),
      (Graph.union_le hH₁.le hH₂.le)⟩ (Graph.left_le_union ..), hc.union_comm,
    hH₂.eq_of_ge ⟨(hc.symm.union_connected_of_nonempty_inter hH₂.connected hH₁.connected
      (by rwa [inter_comm])), (Graph.union_le hH₂.le hH₁.le)⟩ (Graph.left_le_union ..)]

lemma IsComponent.eq_of_mem_mem {H₁ H₂ : Graph α β} (hH₁ : H₁.IsComponent G)
    (hH₂ : H₂.IsComponent G) (hx₁ : x ∈ V(H₁)) (hx₂ : x ∈ V(H₂)) : H₁ = H₂ :=
  by_contra fun hne ↦ (hH₁.disjoint_of_ne hH₂ hne).vertex.notMem_of_mem_left hx₁ hx₂

lemma pairwiseDisjoint_components (G : Graph α β) :
    {H : Graph α β | H.IsComponent G}.Pairwise Graph.Disjoint :=
  fun _ hC _ hC' ↦ hC.disjoint_of_ne hC'

/-- A graph is connected if and only if it is a component of itself. -/
@[simp]
lemma isComponent_self_iff : G.IsComponent G ↔ G.Connected :=
  ⟨IsComponent.connected, fun h ↦ ⟨⟨h, le_rfl⟩, fun _ h _ ↦ h.2⟩⟩

lemma eq_sUnion_components (G : Graph α β) :
    G = Graph.sUnion {C | C.IsComponent G} (G.pairwiseDisjoint_components.mono' (by simp)) := by
  refine G.ext_of_le_le le_rfl ?_ ?_ ?_
  · simp +contextual [IsComponent.le]
  · refine subset_antisymm (fun v hv ↦ ?_) ?_
    · simpa using exists_isComponent_vertex_mem hv
    simpa using fun _ h ↦ (vertexSet_mono h.le)
  refine subset_antisymm (fun e he ↦ ?_) ?_
  · simpa using exists_isComponent_edge_mem he
  simpa using fun _ h ↦ (edgeSet_mono h.le)

/-- For a proper component `H`, the separation with parts `V(H)` and `V(G) \ V(H)`. -/
@[simps]
def IsComponent.separation_of_ne (h : H.IsComponent G) (hne : H ≠ G) : G.Separation where
  left := V(H)
  right := V(G) \ V(H)
  nonempty_left := h.connected.nonempty
  nonempty_right := diff_nonempty.2 fun hss ↦ hne <|
    h.isInducedSubgraph.eq_of_isSpanningSubgraph ⟨h.le, hss.antisymm' (vertexSet_mono h.le)⟩
  disjoint := disjoint_sdiff_right
  union_eq := by simp [vertexSet_mono h.le]
  not_adj x y hx hy hxy := hy.2 <| (h.isClosedSubgraph.adj_of_adj_of_mem hx hxy).right_mem

/-- If `H` is a connected subgraph of a disconnected graph `G`,
then there is a separation of `G` with `H` on the left. -/
lemma Connected.exists_separation_of_le (hH : H.Connected) (hG : ¬ G.Connected) (hle : H ≤ G) :
    ∃ S : G.Separation, H ≤ G[S.left] := by
  obtain ⟨H', hH'H, hle'⟩ := hH.exists_component_ge hle
  refine ⟨hH'H.separation_of_ne ?_, ?_⟩
  · rintro rfl
    exact hG hH'H.connected
  simp only [IsComponent.separation_of_ne_left]
  exact hle'.trans <| le_induce_self hH'H.le

/-- The components of the union of a set of disjoint connected graphs are the graphs themselves. -/
lemma isComponent_sUnion_iff {s : Set (Graph α β)} (h : s.Pairwise Graph.Disjoint)
    (hs : ∀ G ∈ s, G.Connected) :
    H.IsComponent (Graph.sUnion s (h.mono' (by simp))) ↔ H ∈ s := by
  suffices aux : ∀ ⦃H⦄, H ∈ s → H.IsComponent (Graph.sUnion s (h.mono' (by simp))) by
    refine ⟨fun hH ↦ ?_, fun hH ↦ aux hH⟩
    obtain ⟨x, hx⟩ := hH.connected.nonempty
    have hex : ∃ H ∈ s, x ∈ V(H) := by simpa using vertexSet_mono hH.le hx
    obtain ⟨H', hH', hxH'⟩ := hex
    rwa [← (aux hH').eq_of_mem_mem hH hxH' hx]
  exact fun H h' ↦ (isClosedSubgraph_sUnion_of_disjoint s h h').isComponent_of_connected (hs H h')

/-- If `H` is a nonempty subgraph of a connected graph `G`, and each vertex degree in `H`
is at least the corresponding degree in `G`, then `H = G`. -/
lemma Connected.eq_of_le_of_forall_degree_ge [G.LocallyFinite] (hG : G.Connected) (hle : H ≤ G)
    (hne : V(H).Nonempty) (hdeg : ∀ ⦃x⦄, x ∈ V(H) → G.degree x ≤ H.degree x) : H = G := by
  refine hle.eq_of_not_lt fun hlt ↦ ?_
  obtain ⟨e, x, hex, heH, hxH⟩ := hG.exists_inc_notMem_of_lt hlt hne
  have hle : H ≤ G ＼ {e} := by simp [heH, hle]
  exact hex.degree_delete_lt.not_le <| (hdeg hxH).trans (degree_mono hle x)

lemma regular_sUnion_iff {s : Set (Graph α β)} (hdj : s.Pairwise Graph.Disjoint) {d : ℕ} :
    (Graph.sUnion s (hdj.mono' (by simp))).Regular d ↔ ∀ G ∈ s, G.Regular d := by
  refine ⟨fun h G hGs v hv ↦ ?_, fun h v hv ↦ ?_⟩
  · rw [← h (v := v) (by simpa using ⟨G, hGs, hv⟩)]
    apply IsClosedSubgraph.eDegree_eq _ hv
    exact isClosedSubgraph_sUnion_of_disjoint s hdj hGs
  simp only [sUnion_vertexSet, mem_iUnion, exists_prop] at hv
  obtain ⟨G, hGs, hvG⟩ := hv
  rwa [← (isClosedSubgraph_sUnion_of_disjoint s hdj hGs).eDegree_eq hvG, h G hGs]

lemma regular_iff_forall_component {d : ℕ} :
    G.Regular d ↔ ∀ (H : Graph α β), H.IsComponent G → H.Regular d := by
  refine ⟨fun h H hle ↦ h.of_isClosedSubgraph hle.isClosedSubgraph, fun h ↦ ?_⟩
  rw [G.eq_sUnion_components, regular_sUnion_iff G.pairwiseDisjoint_components]
  simpa

lemma maxDegreeLE_iff_forall_component {d : ℕ} :
    G.MaxDegreeLE d ↔ ∀ (H : Graph α β), H.IsComponent G → H.MaxDegreeLE d := by
  refine ⟨fun h H hle ↦ h.mono hle.le, fun h ↦ ?_⟩
  rw [G.eq_sUnion_components, maxDegreeLE_iff']
  simp only [sUnion_vertexSet, mem_setOf_eq, mem_iUnion, exists_prop, forall_exists_index, and_imp]
  intro v H hH hvH
  rw [← G.eq_sUnion_components, ← hH.isClosedSubgraph.eDegree_eq hvH]
  exact h H hH v
