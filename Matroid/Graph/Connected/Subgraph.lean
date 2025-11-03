import Matroid.Graph.Connected.Defs
import Matroid.Graph.Walk.toGraph

open Set Function Nat WList

variable {α β : Type*} [CompleteLattice α] {G H : Graph α β} {u v x x₁ x₂ y y₁ y₂ z : α}
  {e e' f g : β} {U V S T : Set α} {F F' R R': Set β} {C W P Q : WList α β}

namespace Graph


/- ### Unions -/

lemma union_connected_of_forall (h : Agree {G, H}) (hG : G.Connected)
    (hH : ∀ x ∈ V(H), ∃ y ∈ V(G), H.VertexConnected x y) : (G ∪ H).Connected := by
  obtain ⟨v, hv⟩ := hG.nonempty
  refine connected_of_vertex (u := v) (by simp [hv, h]) ?_
  rw [union_vertexSet h]
  rintro y (hy | hy)
  · exact (hG.vertexConnected hy hv).of_le <| Graph.left_le_union h
  obtain ⟨z, hzG, hyz⟩ := hH _ hy
  exact (hyz.of_le <| Graph.right_le_union h).trans <| (hG.vertexConnected hzG hv).of_le <|
    Graph.left_le_union h

lemma union_connected_of_nonempty_inter (h : Agree {G, H}) (hG : G.Connected)
    (hH : H.Connected) (hne : (V(G) ∩ V(H)).Nonempty) : (G ∪ H).Connected :=
  let ⟨z, hzG, hzH⟩ := hne
  union_connected_of_forall h hG fun _ hx ↦ ⟨z, hzG, hH.vertexConnected hx hzH⟩

lemma IsWalk.exists_mem_mem_of_union (h : (G ∪ H).IsWalk W) (hxW : x ∈ V(W)) (hyW : y ∈ V(W))
    (hxG : x ∈ V(G)) (hyH : y ∈ V(H)) : ∃ x ∈ W, x ∈ V(G) ∧ x ∈ V(H) := by
  have hGH : Agree {G, H} := by
    rw [← union_ne_bot_iff <| Or.inl <| ne_bot_of_mem_vertexSet hxG]
    exact ne_bot_of_mem_vertexSet <| h.vertexSet_subset hxW
  by_cases hH' : y ∈ V(G)
  · exact ⟨y, hyW, hH', hyH⟩
  obtain ⟨e, x, y, hxy, hx, hy⟩ := W.exists_isLink_prop_not_prop hxW hxG hyW hH'
  obtain hxy' | hxy' := (union_isLink hGH).mp <| h.isLink_of_isLink hxy
  · exact False.elim <| hy <| hxy'.right_mem
  exact ⟨x, hxy.left_mem, hx, hxy'.left_mem⟩

lemma union_not_connected_of_disjoint_vertexSet (hV : Disjoint V(G) V(H)) (hG : V(G).Nonempty)
    (hH : V(H).Nonempty) : ¬ (G ∪ H).Connected := by
  obtain ⟨x, hx⟩ := hG
  obtain ⟨y, hy⟩ := hH
  intro h
  have := (union_ne_bot_iff <| Or.inl <| ne_bot_of_mem_vertexSet hx).mp h.ne_bot
  obtain ⟨W, hW, rfl, rfl⟩ :=
    (h.vertexConnected (x := x) (y := y) (by simp [hx, this]) (by simp [hy, this])).exists_isWalk
  obtain ⟨u, -, huG, huH⟩ := hW.exists_mem_mem_of_union first_mem last_mem hx hy
  exact hV.notMem_of_mem_left huG huH

/-! ### Cycles -/

/-- Two vertices of a cycle are connected after deleting any other vertex.  -/
lemma IsCycle.vertexConnected_deleteVertex_of_mem_of_mem (hC : G.IsCycle C) (x : α) (hy₁ : y₁ ∈ C)
    (hy₂ : y₂ ∈ C) (hne₁ : y₁ ≠ x) (hne₂ : y₂ ≠ x) : (G - ({x} : Set α)).VertexConnected y₁ y₂ := by
  obtain rfl | hne := eq_or_ne y₁ y₂
  · simpa [hC.vertexSet_subset hy₁]
  obtain ⟨u, e, rfl⟩ | hnt := hC.loop_or_nontrivial
  · simp_all
  by_cases hxC : x ∈ C
  · obtain ⟨P, hP, hP_eq⟩ := hC.exists_isPath_toGraph_eq_delete_vertex hnt hxC
    refine IsWalk.vertexConnected_of_mem_of_mem (W := P) ?_ ?_ ?_
    · simp [hP.isWalk, ← mem_vertexSet_iff, ← toGraph_vertexSet, hP_eq]
    all_goals simp_all [← mem_vertexSet_iff, ← toGraph_vertexSet, hP_eq]
  exact IsWalk.vertexConnected_of_mem_of_mem (W := C) (by simp [hxC, hC.isWalk]) hy₁ hy₂

/-- Two vertices of a cycle are connected after deleting any edge. -/
lemma IsCycle.vertexConnected_deleteEdge_of_mem_of_mem (hC : G.IsCycle C) (e : β)
    (hx₁ : x₁ ∈ C) (hx₂ : x₂ ∈ C) : (G ＼ {e}).VertexConnected x₁ x₂ := by
  obtain heC | heC := em' <| e ∈ C.edge
  · exact IsWalk.vertexConnected_of_mem_of_mem (by simp [hC.isWalk, heC]) hx₁ hx₂
  obtain ⟨P, hP, hP_eq⟩ := hC.exists_isPath_toGraph_eq_delete_edge heC
  apply IsWalk.vertexConnected_of_mem_of_mem (W := P)
    (by simp [hP.isWalk, ← toGraph_edgeSet, hP_eq])
  all_goals rwa [← mem_vertexSet_iff, ← toGraph_vertexSet, hP_eq, edgeDelete_vertexSet,
    toGraph_vertexSet, mem_vertexSet_iff]

/-- If two graphs intersect in at most one vertex,
then any cycle of their union is a cycle of one of the graphs. -/
lemma IsCycle.isCycle_or_isCycle_of_union_of_subsingleton_inter (hC : (G ∪ H).IsCycle C)
    (hi : (V(G) ∩ V(H)).Subsingleton) : G.IsCycle C ∨ H.IsCycle C := by
  wlog hcompat : Compatible G H generalizing H with aux
  · obtain (hG | hH) := aux (union_eq_union_edgeDelete .. ▸ hC) (hi.anti (by simp))
      (Compatible.of_disjoint_edgeSet disjoint_sdiff_right)
    · exact .inl hG
    exact .inr <| hH.isCycle_of_ge <| by simp
  -- If the cycle is a loop, this is easy.
  obtain ⟨x, e, rfl⟩ | hnt := hC.loop_or_nontrivial
  · obtain heG | heH := hC.isWalk.edge_mem_of_mem (e := e) (by simp)
    · exact .inl <| hC.isCycle_of_le (Graph.left_le_union ..) (by simpa)
    exact .inr <| hC.isCycle_of_le hcompat.right_le_union (by simpa)
  -- Every edge of `C` has distinct ends in `G` or in `H`.
  have aux1 (e) (he : e ∈ E(C)) :
      ∃ x y, x ≠ y ∧ x ∈ V(C) ∧ y ∈ V(C) ∧ (G.IsLink e x y ∨ H.IsLink e x y) := by
    obtain ⟨x, y, hxy⟩ := C.exists_isLink_of_mem_edge he
    exact ⟨x, y, hC.ne_of_isLink hnt hxy, hxy.left_mem, hxy.right_mem,
      by simpa [hcompat.union_isLink_iff] using hC.isWalk.isLink_of_isLink hxy ⟩
  -- If the vertices of `C` are contained in `G` or `H`, then `C` is contained in `G` or `H`.
  by_cases hCG : V(C) ⊆ V(G)
  · refine .inl <| hC.isCycle_of_le (Graph.left_le_union ..) fun e heC ↦ ?_
    obtain ⟨x, y, hne, hxC, hyC, hxy | hxy⟩ := aux1 e heC
    · exact hxy.edge_mem
    exact False.elim <| hne <| hi.elim ⟨hCG hxC, hxy.left_mem⟩ ⟨hCG hyC, hxy.right_mem⟩
  by_cases hCH : V(C) ⊆ V(H)
  · refine .inr <| hC.isCycle_of_le hcompat.right_le_union fun e heC ↦ ?_
    obtain ⟨x, y, hne, hxC, hyC, hxy | hxy⟩ := aux1 e heC
    · exact False.elim <| hne <| hi.elim ⟨hxy.left_mem, hCH hxC⟩ ⟨hxy.right_mem, hCH hyC⟩
    exact hxy.edge_mem
  -- Take a path from a vertex `x` of `C ∩ (G \ H)` to a vertex `y` of `C ∩ (H \ G)`.
  -- This path must intersect `V(G) ∩ V(H)` in a vertex `a`.
  obtain ⟨x, hxC, hxH⟩ := not_subset.1 hCH
  obtain ⟨y, hyC, hyG⟩ := not_subset.1 hCG
  have hxG : x ∈ V(G) := by simpa [hxH] using hC.vertexSet_subset hxC
  have hyH : y ∈ V(H) := by simpa [hyG] using hC.vertexSet_subset hyC
  obtain ⟨W, hW, rfl, rfl⟩ := (hC.isWalk.vertexConnected_of_mem_of_mem hxC hyC).exists_isWalk
  obtain ⟨a, -, haG, haH⟩ := hW.exists_mem_mem_of_union first_mem last_mem hxG hyH
  have hxa : W.first ≠ a := by rintro rfl; contradiction
  have hya : W.last ≠ a := by rintro rfl; contradiction
  -- Now take an `xy`-path in `C` that doesn't use `a`. This must intersect `V(G) ∩ V(H)`
  -- in another vertex `b`, contradicting the fact that the intersection is a subsingleton.
  obtain ⟨w', hW', h1', h2'⟩ :=
    (hC.vertexConnected_deleteVertex_of_mem_of_mem a hxC hyC hxa hya).exists_isWalk
  rw [hcompat.vertexDelete_union] at hW'
  obtain ⟨b, -, hbG, hbH⟩ :=
    hW'.exists_mem_mem_of_union first_mem last_mem (by simp [h1', hxG, hxa])
      (by simp [h2', hyH, hya])
  rw [vertexDelete_vertexSet, mem_diff, mem_singleton_iff] at hbG hbH
  refine False.elim <| hbG.2 (hi.elim ?_ ?_) <;> simp_all

lemma Compatible.isCycle_union_iff_of_subsingleton_inter (hcompat : G.Compatible H)
    (hi : (V(G) ∩ V(H)).Subsingleton) : (G ∪ H).IsCycle C ↔ G.IsCycle C ∨ H.IsCycle C :=
  ⟨fun h ↦ h.isCycle_or_isCycle_of_union_of_subsingleton_inter hi,
    fun h ↦ h.elim (fun h' ↦ h'.isCycle_of_ge (Graph.left_le_union ..))
    (fun h' ↦ h'.isCycle_of_ge hcompat.right_le_union)⟩



/-- Every connected subgraph of `G` is a subgraph of a component of `G`. -/
lemma Connected.exists_component_ge (hH : H.Connected) (hle : H ≤ G) :
    ∃ G₁, G₁.IsCompOf G ∧ H ≤ G₁ := by
  obtain ⟨x, hx⟩ := hH.nonempty
  refine ⟨_, walkable_isCompOf (vertexSet_mono hle hx), ?_⟩
  rw [walkable_eq_induce_setOf_vertexConnected]
  refine le_induce_of_le_of_subset hle fun y hy ↦ (hH.vertexConnected hx hy).of_le hle

lemma exists_IsCompOf_edge_mem (he : e ∈ E(G)) :
    ∃ (H : Graph α β), H.IsCompOf G ∧ e ∈ E(H) := by
  obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet he
  obtain ⟨H, hH, hle⟩ := (connected_singleEdge x y e).exists_component_ge (G := G) (by simpa)
  simp only [singleEdge_le_iff] at hle
  exact ⟨H, hH, hle.edge_mem⟩

lemma IsWalk.exists_IsCompOf_isWalk (hW : G.IsWalk W) :
    ∃ (H : Graph α β), H.IsCompOf G ∧ H.IsWalk W := by
  obtain ⟨H, hle, hWH⟩ := hW.toGraph_connected.exists_component_ge hW.toGraph_le
  exact ⟨H, hle, by rwa [← hW.wellFormed.toGraph_le_iff]⟩

lemma IsCompOf_iff_isClosedSubgraph_connected : H.IsCompOf G ↔ H ≤c G ∧ H.Connected := by
  refine ⟨fun h ↦ ⟨h.isClosedSubgraph, h.connected⟩, fun ⟨hHG, hH⟩ ↦ ⟨⟨hHG, hH.nonempty⟩, ?_⟩⟩
  refine fun K ⟨hK, hKG⟩ hHK ↦ hHK.eq_or_lt.elim (fun h ↦ h ▸ le_rfl) fun hlt ↦ False.elim ?_
  obtain ⟨e, x, hex, heH, hxH⟩ := hH.exists_inc_notMem_of_lt hlt hKG
  exact heH <| ((hex.of_le hHG.le).of_isClosedSubgraph_of_mem hK hxH).edge_mem

lemma IsClosedSubgraph.IsCompOf_of_connected (h : H ≤c G) (hH : H.Connected) :
    H.IsCompOf G := by
  refine IsCompOf_iff_isClosedSubgraph_connected.2 ⟨h, hH⟩

lemma Connected.IsCompOf_of_isClosedSubgraph (hH : H.Connected) (h : H ≤c G) :
    H.IsCompOf G := by
  refine IsCompOf_iff_isClosedSubgraph_connected.2 ⟨h, hH⟩

/-- For a proper component `H`, the separation with parts `V(H)` and `V(G) \ V(H)`. -/
@[simps]
def IsCompOf.separation_of_ne (h : H.IsCompOf G) (hne : H ≠ G) : G.Separation where
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
  simp only [IsCompOf.separation_of_ne_left]
  exact hle'.trans <| le_induce_self hH'H.le

/-- The components of the union of a set of disjoint connected graphs are the graphs themselves. -/
lemma IsCompOf_sUnion_iff {s : Set (Graph α β)} (h : s.Pairwise Graph.StronglyDisjoint)
    (hs : ∀ G ∈ s, G.Connected) :
    H.IsCompOf (Graph.sUnion s (h.mono' (by simp))) ↔ H ∈ s := by
  suffices aux : ∀ ⦃H⦄, H ∈ s → H.IsCompOf (Graph.sUnion s (h.mono' (by simp))) by
    refine ⟨fun hH ↦ ?_, fun hH ↦ aux hH⟩
    obtain ⟨x, hx⟩ := hH.connected.nonempty
    have hex : ∃ H ∈ s, x ∈ V(H) := by simpa using vertexSet_mono hH.le hx
    obtain ⟨H', hH', hxH'⟩ := hex
    rwa [← (aux hH').eq_of_mem_mem hH hxH' hx]
  exact fun H h' ↦ (isClosedSubgraph_sUnion_of_stronglyDisjoint s h h').IsCompOf_of_connected
    (hs H h')

/-- If `H` is a nonempty subgraph of a connected graph `G`, and each vertex degree in `H`
is at least the corresponding degree in `G`, then `H = G`. -/
lemma Connected.eq_of_le_of_forall_degree_ge [G.LocallyFinite] (hG : G.Connected) (hle : H ≤ G)
    (hne : V(H).Nonempty) (hdeg : ∀ ⦃x⦄, x ∈ V(H) → G.degree x ≤ H.degree x) : H = G := by
  refine hle.eq_of_not_lt fun hlt ↦ ?_
  obtain ⟨e, x, hex, heH, hxH⟩ := hG.exists_inc_notMem_of_lt hlt hne
  have hle : H ≤ G ＼ {e} := by simp [heH, hle]
  exact hex.degree_delete_lt.not_ge <| (hdeg hxH).trans (degree_mono hle x)

lemma regular_sUnion_iff {s : Set (Graph α β)} (hdj : s.Pairwise Graph.StronglyDisjoint) {d : ℕ} :
    (Graph.sUnion s (hdj.mono' (by simp))).Regular d ↔ ∀ G ∈ s, G.Regular d := by
  refine ⟨fun h G hGs v hv ↦ ?_, fun h v hv ↦ ?_⟩
  · rw [← h (v := v) (by simpa using ⟨G, hGs, hv⟩)]
    apply IsClosedSubgraph.eDegree_eq _ hv
    exact isClosedSubgraph_sUnion_of_stronglyDisjoint s hdj hGs
  simp only [sUnion_vertexSet, mem_iUnion, exists_prop] at hv
  obtain ⟨G, hGs, hvG⟩ := hv
  rwa [← (isClosedSubgraph_sUnion_of_stronglyDisjoint s hdj hGs).eDegree_eq hvG, h G hGs]

lemma regular_iff_forall_component {d : ℕ} :
    G.Regular d ↔ ∀ (H : Graph α β), H.IsCompOf G → H.Regular d := by
  refine ⟨fun h H hle ↦ h.of_isClosedSubgraph hle.isClosedSubgraph, fun h ↦ ?_⟩
  rw [G.eq_sUnion_components, regular_sUnion_iff G.components_pairwise_stronglyDisjoint]
  simpa

lemma maxDegreeLE_iff_forall_component {d : ℕ} :
    G.MaxDegreeLE d ↔ ∀ (H : Graph α β), H.IsCompOf G → H.MaxDegreeLE d := by
  refine ⟨fun h H hle ↦ h.mono hle.le, fun h ↦ ?_⟩
  rw [G.eq_sUnion_components, maxDegreeLE_iff']
  simp only [sUnion_vertexSet, mem_setOf_eq, mem_iUnion, exists_prop, forall_exists_index, and_imp]
  intro v H hH hvH
  rw [← G.eq_sUnion_components, ← hH.isClosedSubgraph.eDegree_eq hvH]
  exact h H hH v


/-! ### Bridges -/

/-- A bridge is an edge in no cycle-/
@[mk_iff]
structure IsBridge (G : Graph α β) (e : β) : Prop where
  mem_edgeSet : e ∈ E(G)
  notMem_cycle : ∀ ⦃C⦄, G.IsCycle C → e ∉ C.edge

lemma not_isBridge (he : e ∈ E(G)) : ¬ G.IsBridge e ↔ ∃ C, G.IsCycle C ∧ e ∈ C.edge := by
  simp [isBridge_iff, he]

lemma IsCycle.not_isBridge_of_mem (hC : G.IsCycle C) (heC : e ∈ C.edge) : ¬ G.IsBridge e := by
  rw [not_isBridge (hC.isWalk.edgeSet_subset heC)]
  exact ⟨C, hC, heC⟩

lemma IsLink.isBridge_iff_not_vertexConnected (he : G.IsLink e x y) :
    G.IsBridge e ↔ ¬ (G ＼ {e}).VertexConnected x y := by
  refine ⟨fun h hconn ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨P, hP, rfl, rfl⟩ := hconn.exists_isPath
    simp only [isPath_edgeDelete_iff, disjoint_singleton_right, mem_edgeSet_iff] at hP
    exact (hP.1.cons_isCycle he hP.2).not_isBridge_of_mem (by simp) h
  contrapose! h
  obtain ⟨C, hC, heC⟩ := (not_isBridge he.edge_mem).1 h
  rw [← hC.isWalk.isLink_iff_isLink_of_mem heC] at he
  exact hC.vertexConnected_deleteEdge_of_mem_of_mem _ he.left_mem he.right_mem

lemma Connected.edgeDelete_singleton_connected (hG : G.Connected) (he : ¬ G.IsBridge e) :
    (G ＼ {e}).Connected := by
  obtain heE | heE := em' <| e ∈ E(G)
  · rwa [edgeDelete_eq_self _ (by simpa)]
  obtain ⟨C, hC, heC⟩ := (not_isBridge heE).1 he
  rw [← (G ＼ {e}).induce_union_edgeDelete (X := V(C))]
  refine Compatible.union_connected_of_forall (G.compatible_of_le_le ?_ (by simp)) ?_ ?_
  · exact le_trans (induce_le) edgeDelete_le
  · obtain ⟨P, hP, hPC⟩ := hC.exists_isPath_toGraph_eq_delete_edge heC
    refine (hP.isWalk.toGraph_connected.of_isSpanningSubgraph ⟨?_, ?_⟩)
    · rw [hPC, edgeDelete_induce, hC.isWalk.toGraph_eq_induce_restrict]
      exact edgeDelete_mono_left (by simp)
    rw [hPC]
    simp
  simp only [edgeDelete_induce, edgeDelete_edgeSet, edgeDelete_edgeDelete, union_diff_self,
    singleton_union, edgeDelete_vertexSet, induce_vertexSet, mem_vertexSet_iff]
  intro x hx
  obtain ⟨y, hy, hconn⟩ := hG.exists_vertexConnected_deleteEdge_set (X := V(C))
    (by simp [inter_eq_self_of_subset_left hC.vertexSet_subset]) hx
  refine ⟨y, hy, ?_⟩
  rwa [insert_eq_of_mem (hC.isWalk.edgeSet_subset_induce_edgeSet heC )]

lemma Connected.edgeDelete_singleton_connected_iff (hG : G.Connected) :
    (G ＼ {e}).Connected ↔ ¬ G.IsBridge e := by
  obtain heE | heE := em' <| e ∈ E(G)
  · simp [edgeDelete_eq_self G (F := {e}) (by simpa), hG, isBridge_iff, heE]
  refine ⟨fun h hbr ↦ ?_, hG.edgeDelete_singleton_connected⟩
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet heE
  obtain ⟨P, hP, rfl, rfl⟩ := (h.vertexConnected hxy.left_mem hxy.right_mem).exists_isPath
  simp only [isPath_edgeDelete_iff, disjoint_singleton_right, mem_edgeSet_iff] at hP
  simpa using hbr.notMem_cycle <| hP.1.cons_isCycle hxy hP.2

lemma Connected.isBridge_iff (hG : G.Connected) : G.IsBridge e ↔ ¬ (G ＼ {e}).Connected := by
  rw [hG.edgeDelete_singleton_connected_iff, not_not]

/-- Every edge of a path is a bridge -/
lemma IsPath.isBridge_of_mem (hP : G.IsPath P) (heP : e ∈ P.edge) : P.toGraph.IsBridge e := by
  rw [hP.isWalk.toGraph_connected.isBridge_iff, hP.isWalk.toGraph_eq_induce_restrict]
  obtain ⟨P₁, P₂, hP₁, hP₂, heP₁, heP₂, hdj, hedj, rfl⟩ := hP.eq_append_cons_of_edge_mem heP
  rw [append_vertexSet (by simp)]
  suffices ¬(G[V(P₁) ∪ V(P₂)] ↾ (E(P₁) ∪ E(P₂)) \ {e}).Connected by simpa
  rw [diff_singleton_eq_self (by simp [heP₁, heP₂]), ← edgeRestrict_induce, induce_union,
    edgeRestrict_induce, edgeRestrict_induce]
  · exact union_not_connected_of_disjoint_vertexSet
      (by simpa [vertexSet_disjoint_iff]) (by simp) (by simp)
  rintro x hx y hy ⟨f, hf⟩
  simp only [edgeRestrict_isLink, mem_union, mem_edgeSet_iff] at hf
  obtain ⟨(hf | hf), hfxy⟩ := hf
  · rw [← hP₁.isWalk.isLink_iff_isLink_of_mem hf] at hfxy
    exact List.disjoint_right.1 hdj hy hfxy.right_mem
  rw [← hP₂.isWalk.isLink_iff_isLink_of_mem hf] at hfxy
  exact List.disjoint_left.1 hdj hx hfxy.left_mem


/-! ### Staying Connected -/

/-- A leaf vertex in a trail is either the first or last vertex of the trail -/
lemma IsLeaf.eq_first_or_eq_last_of_mem_trail {P : WList α β} (hx : G.IsLeaf x)
    (hP : G.IsTrail P) (hxP : x ∈ P) : x = P.first ∨ x = P.last := by
  induction P with
  | nil => simpa using hxP
  | cons u e P ih =>
    simp only [cons_isTrail_iff] at hP
    obtain (rfl : x = u) | (hxP : x ∈ P) := by simpa using hxP
    · simp
    obtain rfl | rfl := (ih hP.1 hxP).symm
    · simp
    obtain v | ⟨v, f, P⟩ := P
    · simp
    simp only [cons_isTrail_iff, first_cons, cons_edge, List.mem_cons, not_or] at hP
    simp [hx.dup_of_inc_inc hP.1.2.1.inc_left hP.2.1.inc_right] at hP

lemma IsLeaf.eq_first_or_eq_last_of_mem_path {P : WList α β} (hx : G.IsLeaf x)
    (hP : G.IsPath P) (hxP : x ∈ P) : x = P.first ∨ x = P.last :=
  hx.eq_first_or_eq_last_of_mem_trail hP.isTrail hxP

lemma IsLeaf.delete_connected (hx : G.IsLeaf x) (hG : G.Connected) : (G - {x}).Connected := by
  obtain ⟨y, hy : G.Adj x y, hu⟩ := hx.exists_unique_adj
  refine connected_of_vertex ⟨hy.right_mem, fun h : y = x ↦ hx.not_adj_self (h ▸ hy)⟩ fun z hz ↦ ?_
  obtain ⟨P, hP, rfl, rfl⟩ := (hG.vertexConnected hz.1 hy.right_mem).exists_isPath
  refine IsWalk.vertexConnected_first_last <| isWalk_vertexDelete_iff.2 ⟨hP.isWalk, ?_⟩
  simp only [disjoint_singleton_right, mem_vertexSet_iff]
  intro hxP
  obtain rfl | rfl := hx.eq_first_or_eq_last_of_mem_path hP hxP
  · simp at hz
  exact hx.not_adj_self hy

/-- Deleting the first vertex of a maximal path of a connected graph gives a connected graph. -/
lemma Connected.delete_first_connected_of_maximal_isPath (hG : G.Connected) (hnt : V(G).Nontrivial)
    (hP : Maximal (fun P ↦ G.IsPath P) P) : (G - {P.first}).Connected := by
  cases P with
  | nil u =>
    obtain ⟨e, y, huy, hne⟩ := hG.exists_isLink_of_mem hnt (x := u) (by simpa using hP.prop)
    exact False.elim <| hne.symm <| by
      simpa [huy, huy.right_mem] using hP.eq_of_ge (y := cons u e (nil y))
  | cons u e P =>
    have ⟨hP', he, huP⟩ : G.IsPath P ∧ G.IsLink e u P.first ∧ u ∉ P := by simpa using hP.prop
    by_contra hcon
    simp only [first_cons] at hcon
    have hP'' : (G - {u}).IsPath P := by simp [isPath_vertexDelete_iff, huP, hP']
    obtain ⟨S, hS⟩ :=
      hP''.isWalk.toGraph_connected.exists_separation_of_le hcon hP''.isWalk.toGraph_le
    have hPS : V(P) ⊆ S.left := by simpa using vertexSet_mono hS
    have huleft : u ∉ S.left := fun huS ↦ by simpa using S.left_subset huS
    have huright : u ∉ S.right := fun huS ↦ by simpa using S.right_subset huS
    suffices hu : ∀ x ∈ S.right, ¬ G.Adj u x by
      refine Separation.not_connected
        ⟨insert u S.left, S.right, by simp, S.nonempty_right, ?_, ?_, ?_⟩ hG
      · simp [S.disjoint, huright]
      · simpa [insert_union, S.union_eq] using he.left_mem
      rintro x y (rfl | hxS) hyS ⟨e, hxy⟩
      · exact hu y hyS hxy.adj
      refine S.not_adj hxS hyS ⟨e, ?_⟩
      simp only [vertexDelete_isLink_iff, hxy, mem_singleton_iff, true_and]
      constructor <;> (rintro rfl; contradiction)
    rintro x hx ⟨f, hux⟩
    have hne : u ≠ x := by rintro rfl; contradiction
    refine S.disjoint.notMem_of_mem_left (hPS ?_) hx
    simpa [hne.symm] using mem_of_adj_first_of_maximal_isPath hP hux.symm.adj

/-- Deleting the last vertex of a maximal path of a connected graph gives a connected graph. -/
lemma Connected.delete_last_connected_of_maximal_isPath (hG : G.Connected) (hnt : V(G).Nontrivial)
    (hP : Maximal (fun P ↦ G.IsPath P) P) : (G - {P.last}).Connected := by
  suffices aux : Maximal (fun P ↦ G.IsPath P) P.reverse by
    simpa using hG.delete_first_connected_of_maximal_isPath hnt aux
  refine ⟨by simpa using hP.prop, fun Q hQ hPQ ↦ ?_⟩
  simp [hP.eq_of_le (y := Q.reverse) (by simpa) (by simpa using IsSublist.reverse hPQ)]

/-- Every finite connected graph on at least two vertices has a vertex whose deletion
preserves its connectedness.
(This requires a finite graph, since otherwise an infinite path is a counterexample.) -/
lemma Connected.exists_delete_vertex_connected [G.Finite] (hG : G.Connected)
    (hnt : V(G).Nontrivial) : ∃ x ∈ V(G), (G - {x}).Connected := by
  obtain ⟨x, hx⟩ := hG.nonempty
  obtain ⟨P, hP⟩ := Finite.exists_maximal G.isPath_finite ⟨nil x, by simpa⟩
  exact ⟨_, hP.prop.isWalk.first_mem, hG.delete_first_connected_of_maximal_isPath hnt hP⟩
