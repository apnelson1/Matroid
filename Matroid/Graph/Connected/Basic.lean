import Matroid.Graph.Connected.Defs

open Set Function Nat WList

variable {α β : Type*} {G H K : Graph α β} {u v x x₁ x₂ y y₁ y₂ z : α} {e e' f g : β}
  {U V S T : Set α} {F F' R R': Set β} {C W P Q : WList α β} {n m : ℕ}

namespace Graph

lemma IsCompOf.connected (h : H.IsCompOf G) : H.Connected :=
  h.of_le_le le_rfl h.le

lemma walkable_connected (hx : x ∈ V(G)) : (G.walkable x).Connected :=
  (walkable_isCompOf hx).connected

lemma Connected.components_subsingleton (hG : G.Connected) : G.Components.Subsingleton := by
  rintro H₁ hH₁ H₂ hH₂
  rw [mem_components_iff_isCompOf] at hH₁ hH₂
  have hH₁bot := hH₁.ne_bot
  have hH₂bot := hH₂.ne_bot
  by_cases hGbot : G = ⊥
  · subst G
    simp at hG
  have := hG.isSimpleOrder hGbot
  let H₁' : G.ClosedSubgraph := ⟨H₁, hH₁.isClosedSubgraph⟩
  let H₂' : G.ClosedSubgraph := ⟨H₂, hH₂.isClosedSubgraph⟩
  change H₁'.val = H₂'.val
  rw [eq_bot_or_eq_top H₁' |>.resolve_left ?_, eq_bot_or_eq_top H₂' |>.resolve_left ?_] <;>
    rwa [← Subtype.coe_inj]

lemma IsClosedSubgraph.isCompOf_of_isCompOf_compl (h : H ≤c G) (hK : K.IsCompOf G) :
    K.IsCompOf H ∨ K.IsCompOf (G - V(H)) := by
  refine (h.disjoint_or_subset_of_isCompOf hK).elim .inl fun hdj ↦ .inr <| hK.of_le_le ?_ (by simp)
  simp [hK.le, le_vertexDelete_iff, hdj.vertex]

lemma Connected.exists_isCompOf_ge (h : H.Connected) (hle : H ≤ G) :
    ∃ G₁, H ≤ G₁ ∧ G₁.IsCompOf G := by
  set s := {G' | G' ≤c G ∧ H ≤ G'} with hs_def
  have hne : s.Nonempty := ⟨G, by simpa [s]⟩
  let G₁ := Graph.sInter s hne
  have hHG₁ : H ≤ G₁ := (Graph.le_sInter_iff ..).2 fun K hK ↦ hK.2
  have hG₁G : G₁ ≤c G := sInter_isClosedSubgraph (fun _ hK ↦ hK.1) _
  refine ⟨G₁, hHG₁, ⟨hG₁G, h.nonempty.mono (vertexSet_mono hHG₁)⟩, fun K ⟨hKG, hKne⟩ hKG₁ ↦ ?_⟩
  refine Graph.sInter_le ?_
  simp only [mem_setOf_eq, hKG, true_and, s]
  obtain hdj | hne := disjoint_or_nonempty_inter V(K) V(H)
  · have hKG₁' : K ≤c G₁ := hKG.of_le_of_le hKG₁ hG₁G.le
    simp only [Graph.le_sInter_iff, mem_setOf_eq, and_imp, G₁, s] at hKG₁
    simpa [hHG₁, hdj.symm, hKne.ne_empty] using hKG₁ _ (hKG₁'.compl.trans hG₁G)
  rw [← h.eq_of_isClosedSubgraph (hKG.inter_le hle) (by simpa)]
  exact Graph.inter_le_left

lemma Connected.le_or_le_compl (h : H.Connected) (hle : H ≤ G) (hK : K ≤c G) :
    H ≤ K ∨ H ≤ G - V(K) := by
  obtain ⟨G', hHG', hG'G⟩ := h.exists_isCompOf_ge hle
  obtain hc | hc := hK.isCompOf_of_isCompOf_compl hG'G
  · exact .inl (hHG'.trans hc.le)
  refine .inr <| le_vertexDelete_iff.2 ⟨hle, ?_⟩
  obtain ⟨hG'G, hdj : Disjoint V(G') V(K)⟩ := by simpa using hc.le
  exact hdj.mono_left <| vertexSet_mono hHG'

lemma Connected.le_of_nonempty_inter (h : H.Connected) (hle : H ≤ G) (hK : K ≤c G)
    (hne : (V(H) ∩ V(K)).Nonempty) : H ≤ K :=
  (h.le_or_le_compl hle hK).elim id fun hle' ↦
    by simp [disjoint_iff_inter_eq_empty, hne.ne_empty] at hle'

lemma isCompOf_iff_maximal : H.IsCompOf G ↔ Maximal (fun K ↦ K.Connected ∧ K ≤ G) H := by
  refine ⟨fun h ↦ ⟨⟨h.connected, h.le⟩, fun K ⟨hK, hKG⟩ hHK ↦ ?_⟩, fun h ↦ ?_⟩
  · obtain ⟨G₁, hKG₁, hG₁⟩ := hK.exists_isCompOf_ge hKG
    refine hKG₁.trans (hG₁.connected.le_of_nonempty_inter hG₁.le h.isClosedSubgraph ?_)
    rw [inter_eq_self_of_subset_right (vertexSet_mono (hHK.trans hKG₁))]
    exact h.nonempty
  obtain ⟨K, hHK, hKG⟩ := h.prop.1.exists_isCompOf_ge h.prop.2
  rwa [← h.eq_of_ge ⟨hKG.connected, hKG.le⟩ hHK]

lemma Connected.union (hG : G.Connected) (hH : H.Connected) (hcompat : G.Compatible H)
    (hi : (V(H) ∩ V(G)).Nonempty) : (G ∪ H).Connected := by
  rw [connected_iff_forall_closed (hi.mono (inter_subset_left.trans (by simp)))]
  refine fun K hK hKne ↦ ?_
  have hGle : G ≤ K ∨ Disjoint V(G) V(K) := by simpa using hG.le_or_le_compl (G.left_le_union H) hK
  have hHle := hH.le_or_le_compl hcompat.right_le_union hK
  simp only [le_vertexDelete_iff, hcompat.right_le_union, true_and] at hHle
  obtain hGK | hGK := disjoint_or_nonempty_inter V(G) V(K)
  · obtain hHK | hHK := disjoint_or_nonempty_inter V(H) V(K)
    · simpa [union_vertexSet, ← inter_eq_right, union_inter_distrib_right, hGK.inter_eq,
        hHK.inter_eq, hKne.ne_empty.symm] using vertexSet_mono hK.le
    rw [or_iff_left (not_disjoint_iff_nonempty_inter.2 hHK)] at hHle
    simpa [hGK.symm.inter_eq] using hi.mono (inter_subset_inter_left _ (vertexSet_mono hHle))
  rw [or_iff_left (not_disjoint_iff_nonempty_inter.2 hGK)] at hGle
  have hne := hi.mono (inter_subset_inter_right _ (vertexSet_mono hGle))
  rw [or_iff_left (not_disjoint_iff_nonempty_inter.2 hne)] at hHle
  exact hK.le.antisymm (Graph.union_le hGle hHle)

lemma Connected.exists_inc_notMem_of_lt (hG : G.Connected) (hlt : H < G) (hne : V(H).Nonempty) :
    ∃ e x, G.Inc e x ∧ e ∉ E(H) ∧ x ∈ V(H) := by
  refine by_contra fun hcon ↦ hlt.ne <| hG.eq_of_isClosedSubgraph ⟨hlt.le, fun e x hex hx ↦ ?_⟩ hne
  simp only [not_exists, not_and, not_imp_not] at hcon
  exact hcon _ _ hex hx

lemma Connected.of_isSpanningSubgraph (hH : H.Connected) (hle : H ≤s G) : G.Connected := by
  rw [connected_iff_forall_closed (hH.nonempty.mono (vertexSet_mono hle.le))]
  refine fun K hKG hKne ↦ hKG.isInducedSubgraph.eq_of_isSpanningSubgraph <|
    hle.of_isSpanningSubgraph_right ?_ hKG.le
  exact hH.le_of_nonempty_inter hle.le hKG
    (by rwa [hle.vertexSet_eq, inter_eq_self_of_subset_right (vertexSet_mono hKG.le)])

@[simp]
lemma connected_bouquet (v : α) (F : Set β) : (bouquet v F).Connected := by
  suffices aux : (bouquet v (∅ : Set β)).Connected from
    aux.of_isSpanningSubgraph <| bouquet_mono _ (empty_subset F)
  rw [connected_iff_forall_closed_ge (by simp)]
  refine fun H hle hne ↦ ⟨?_, by simp⟩
  simp only [bouquet_vertexSet, singleton_subset_iff]
  obtain ⟨x, hx⟩ := hne
  obtain rfl := by simpa using vertexSet_mono hle.le hx
  exact hx

@[simp]
lemma connected_banana (x y : α) (hF : F.Nonempty) : (banana x y F).Connected := by
  simp only [banana_vertexSet, insert_nonempty, connected_iff_forall_closed_ge]
  refine fun H hle hne ↦ ?_
  have hmem : ∀ z ∈ V(H), z = x ∨ z = y := by simpa [subset_pair_iff] using vertexSet_mono hle.le
  wlog hx : x ∈ V(H) generalizing x y with aux
  · rw [banana_comm]
    refine aux y x (by rwa [banana_comm]) (fun z hz ↦ (hmem z hz).symm) ?_
    obtain ⟨z, hz⟩ := hne
    obtain rfl | rfl := hmem _ hz
    · contradiction
    assumption
  have hl (e) (he : e ∈ F) : H.IsLink e x y := IsLink.of_isClosedSubgraph_of_mem (by simpa) hle hx
  refine ⟨by simp [pair_subset_iff, hx, (hl _ hF.some_mem).right_mem], fun e z w he ↦ ?_⟩
  simp only [banana_isLink] at he
  obtain ⟨hef, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := he
  · exact hl e hef
  exact (hl e hef).symm

@[simp]
lemma connected_singleEdge (x y : α) (e : β) : (Graph.singleEdge x y e).Connected := by
  rw [← banana_singleton]
  exact connected_banana x y (by simp)

-- @[simp]
-- lemma connected_noEdge_singleton (v : α) : (Graph.noEdge {v} β).Connected := by
--   refine ⟨by simp, fun H ⟨_, hne⟩ hle ↦ ?_⟩
--   simp at hle

lemma Connected.addEdge_connected (hG : G.Connected) (hx : x ∈ V(G)) (he : e ∉ E(G)) (y : α) :
    (G.addEdge e x y).Connected := by
  unfold Graph.addEdge
  refine (connected_singleEdge x y e).union hG (by simp [he]) ?_
  rw [singleEdge_vertexSet]
  exact ⟨x, hx, by simp⟩

lemma walkable_eq_induce_setOf_connectedBetween :
    G.walkable x = G[{y | G.ConnectedBetween x y}] := by
  rw [walkable_isClosedSubgraph.eq_induce]
  congr

lemma singleVertex_connected (hG : V(G) = {x}) : G.Connected := by
  simp [connected_iff, hG, preconnected_of_vertexSet_subsingleton]

lemma exists_of_not_connected (h : ¬ G.Connected) (hne : V(G).Nonempty) :
    ∃ X ⊂ V(G), X.Nonempty ∧ ∀ ⦃u v⦄, u ∈ X → G.Adj u v → v ∈ X := by
  simp only [connected_iff, hne, Preconnected, true_and, not_forall, exists_prop,
    exists_and_left] at h
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  refine ⟨{z | G.ConnectedBetween x z}, ?_, ⟨x, by simpa⟩,
    fun u v (h : G.ConnectedBetween x u) huv ↦ h.trans huv.connectedBetween⟩
  exact HasSubset.Subset.ssubset_of_mem_notMem (fun z hz ↦ hz.right_mem) hy (by simpa)

lemma connected_iff_forall_exists_adj (hne : V(G).Nonempty) :
    G.Connected ↔ ∀ X ⊂ V(G), X.Nonempty → ∃ x ∈ X, ∃ y ∈ V(G) \ X, G.Adj x y := by
  refine ⟨fun h X hXV hXnem ↦ ?_, fun h ↦ by_contra fun hnc ↦ ?_⟩
  · by_contra! hnadj
    have hGXcl : G[X] ≤c G := ⟨induce_le hXV.subset, fun e x ⟨y, hexy⟩ hxX =>
      ⟨x, y, hexy, hxX, by_contra fun hyX => hnadj x hxX y ⟨hexy.right_mem, hyX⟩ ⟨e, hexy⟩⟩⟩
    rw [← le_antisymm hGXcl.le <| h.2 ⟨hGXcl, by simpa⟩ hGXcl.le, induce_vertexSet] at hXV
    exact (and_not_self_iff (X ⊆ X)).mp hXV
  obtain ⟨X, hXV, hXne, h'⟩ := exists_of_not_connected hnc hne
  obtain ⟨x, hX, y, hy, hxy⟩ := h X hXV hXne
  exact hy.2 <| h' hX hxy


/-- A `WList` that is `WellFormed` produces a connected graph. -/
lemma _root_.WList.WellFormed.toGraph_connected (hW : W.WellFormed) : W.toGraph.Connected := by
  rw [connected_iff, Preconnected]
  exact ⟨by simp, fun x y hx hy ↦ hW.isWalk_toGraph.connectedBetween_of_mem_of_mem
    (by simpa using hx) (by simpa using hy)⟩

lemma IsWalk.toGraph_connected (hW : G.IsWalk W) : W.toGraph.Connected :=
  hW.wellFormed.toGraph_connected

lemma Connected.exists_connectedBetween_deleteEdge_set {X : Set α} (hG : G.Connected)
    (hX : (X ∩ V(G)).Nonempty) (hu : u ∈ V(G)) : ∃ x ∈ X, (G ＼ E(G[X])).ConnectedBetween u x := by
  obtain ⟨x', hx'X, hx'V⟩ := hX
  obtain ⟨W, hW, hu, rfl⟩ := (hG.connectedBetween hu hx'V)
  induction hW generalizing u with
  | nil => exact ⟨_, hx'X, by simp_all⟩
  | @cons x e W hW h ih =>
    obtain rfl : x = u := hu
    by_cases hmem : e ∈ E(G ＼ E(G[X]))
    · obtain ⟨x', hx', hWx'⟩ := ih (u := W.first) (hW.vertex_mem_of_mem (by simp)) rfl
        (by simpa using hx'X) (by simpa using hx'V)
      have hconn := (h.of_le_of_mem edgeDelete_le hmem).connectedBetween
      exact ⟨x', hx', hconn.trans hWx'⟩
    rw [edgeDelete_edgeSet, mem_diff, and_iff_right h.edge_mem, h.mem_induce_iff, not_not] at hmem
    exact ⟨x, hmem.1, by simpa⟩

lemma Connected.exists_isPathFrom (hG : G.Connected) (hS : (S ∩ V(G)).Nonempty)
    (hT : (T ∩ V(G)).Nonempty) : ∃ P, G.IsPathFrom S T P := by
  obtain ⟨x, hxS, hx⟩ := hS
  obtain ⟨y, hyT, hy⟩ := hT
  obtain ⟨W, hW, rfl, rfl⟩ := (hG.connectedBetween hx hy)
  clear hx hy
  induction hW generalizing S with
  | @nil x hx => exact ⟨nil x, by simp_all⟩
  | @cons x e P hP h ih =>
    simp_all only [first_cons, last_cons, forall_const]
    by_cases hPS : P.first ∈ S
    · apply ih hPS
    obtain ⟨P₀, hP₀⟩ := ih (mem_insert P.first S)
    obtain (hP₀S | h_eq) := hP₀.first_mem.symm
    · exact ⟨P₀, hP₀.subset_left (by simp) hP₀S⟩
    by_cases hxT : x ∈ T
    · exact ⟨nil x, by simp [hxS, hxT, h.left_mem]⟩
    use cons x e P₀
    simp only [isPathFrom_iff, cons_isPath_iff, first_cons, last_cons]
    refine ⟨⟨hP₀.isPath, by rwa [h_eq], fun hxP₀ ↦ hPS ?_⟩, hxS, hP₀.last_mem, ?_, ?_⟩
    · rwa [← h_eq, ← hP₀.eq_first_of_mem hxP₀ (by simp [hxS])]
    · simp only [mem_cons_iff, forall_eq_or_imp, implies_true, true_and]
      exact fun a haP haS ↦ hPS.elim <| by rwa [← h_eq, ← hP₀.eq_first_of_mem haP (by simp [haS])]
    simp only [mem_cons_iff, forall_eq_or_imp, hxT, IsEmpty.forall_iff, true_and]
    exact fun a haP₀ haT ↦ hP₀.eq_last_of_mem haP₀ haT

lemma Connected.exists_connectedBetween_deleteEdge_set_set (hG : G.Connected)
    (hS : (S ∩ V(G)).Nonempty) (hT : (T ∩ V(G)).Nonempty) :
    ∃ x ∈ S, ∃ y ∈ T, (G ＼ (E(G[S]) ∪ E(G[T]))).ConnectedBetween x y := by
  obtain ⟨P, hP⟩ := hG.exists_isPathFrom hS hT
  have h0 : P.first ∈ V(G ＼ (E(G[S]) ∪ E(G[T]))) := by
    simpa using hP.isWalk.vertex_mem_of_mem (by simp)
  refine ⟨_, hP.first_mem, _, hP.last_mem,
    (hP.isPathFrom_le (by simp) (fun e heP ↦ ?_) h0).isWalk.connectedBetween_first_last⟩
  obtain ⟨x, y, hxy⟩ := exists_dInc_of_mem_edge heP
  have hxy' := hP.isWalk.isLink_of_dInc hxy
  rw [edgeDelete_edgeSet, mem_diff, mem_union, hxy'.mem_induce_iff,
    hxy'.mem_induce_iff, and_iff_right hxy'.edge_mem]
  simp [hP.notMem_left_of_dInc hxy, hP.notMem_right_of_dInc hxy]

lemma Connected.exists_isLink_of_mem (hG : G.Connected) (hV : V(G).Nontrivial) (hx : x ∈ V(G)) :
    ∃ e y, G.IsLink e x y ∧ y ≠ x := by
  obtain ⟨z, hz, hne⟩ := hV.exists_ne x
  obtain ⟨P, hP, rfl, rfl⟩ := (hG.connectedBetween hx hz).exists_isPath
  rw [ne_comm, first_ne_last_iff hP.nodup] at hne
  obtain ⟨x, e, P⟩ := hne
  simp only [cons_isPath_iff] at hP
  exact ⟨e, P.first, hP.2.1, mt (by simp +contextual [eq_comm]) hP.2.2⟩

lemma Isolated.not_connected (hx : G.Isolated x) (hnt : V(G).Nontrivial) : ¬ G.Connected :=
  fun h ↦ by simpa [hx.not_isLink] using h.exists_isLink_of_mem hnt hx.mem

lemma Connected.degreePos (h : G.Connected) (hnt : V(G).Nontrivial) : G.DegreePos := by
  intro x hx
  obtain ⟨e, y, h, -⟩ := h.exists_isLink_of_mem hnt hx
  exact ⟨e, h.inc_left⟩

lemma Connected.edgeSet_nonempty (h : G.Connected) (hnt : V(G).Nontrivial) : E(G).Nonempty := by
  obtain ⟨x, hx⟩ := hnt.nonempty
  obtain ⟨e, y, he, -⟩ := h.exists_isLink_of_mem hnt hx
  exact ⟨e, he.edge_mem⟩

/-- If `G` is connected but its restriction to some set `F` of edges is not,
then there is an edge of `G` joining two vertices that are not connected in the restriction. -/
lemma Connected.exists_of_edgeRestrict_not_connected (hG : G.Connected)
    (hF : ¬ (G.edgeRestrict F).Connected) :
    ∃ (S : (G.edgeRestrict F).Separation) (e : β) (x : α) (y : α),
    e ∉ F ∧ x ∈ S.left ∧ y ∈ S.right ∧ G.IsLink e x y := by
  obtain ⟨S⟩ := nonempty_separation_of_not_connected (by simpa using hG.nonempty) hF
  obtain ⟨x₀, hx₀⟩ := S.nonempty_left
  obtain ⟨y₀, hy₀⟩ := S.nonempty_right
  obtain ⟨W, hW, rfl, rfl⟩ :=
    (hG.connectedBetween (S.left_subset hx₀) (S.right_subset hy₀))
  rw [← S.not_left_mem_iff (S.right_subset hy₀)] at hy₀
  obtain ⟨e, x, y, hexy, hx, hy⟩ := W.exists_dInc_prop_not_prop hx₀ hy₀
  have h' := hW.isLink_of_dInc hexy
  rw [S.not_left_mem_iff h'.right_mem] at hy
  refine ⟨S, e, x, y, fun heF ↦ ?_, hx, hy, h'⟩
  exact S.not_adj hx hy <| IsLink.adj <| h'.of_le_of_mem (by simp) <| by simpa [h'.edge_mem]

/- ### Unions -/

lemma Compatible.union_connected_of_forall (h : G.Compatible H) (hG : G.Connected)
    (hH : ∀ x ∈ V(H), ∃ y ∈ V(G), H.ConnectedBetween x y) : (G ∪ H).Connected := by
  obtain ⟨v, hv⟩ := hG.nonempty
  refine connected_of_vertex (u := v) (by simp [hv]) ?_
  rintro y (hy | hy)
  · exact (hG.connectedBetween hy hv).of_le <| Graph.left_le_union ..
  obtain ⟨z, hzG, hyz⟩ := hH _ hy
  exact (hyz.of_le h.right_le_union).trans <| (hG.connectedBetween hzG hv).of_le <|
    Graph.left_le_union ..

lemma Compatible.union_connected_of_nonempty_inter (h : Compatible G H) (hG : G.Connected)
    (hH : H.Connected) (hne : (V(G) ∩ V(H)).Nonempty) : (G ∪ H).Connected :=
  let ⟨z, hzG, hzH⟩ := hne
  h.union_connected_of_forall hG fun _ hx ↦ ⟨z, hzG, hH.connectedBetween hx hzH⟩

lemma IsWalk.exists_mem_mem_of_union (h : (G ∪ H).IsWalk W) (hxW : x ∈ V(W)) (hyW : y ∈ V(W))
    (hxG : x ∈ V(G)) (hyH : y ∈ V(H)) : ∃ x ∈ W, x ∈ V(G) ∧ x ∈ V(H) := by
  by_cases hH' : y ∈ V(G)
  · exact ⟨y, hyW, hH', hyH⟩
  obtain ⟨e, x, y, hxy, hx, hy⟩ := W.exists_isLink_prop_not_prop hxW hxG hyW hH'
  obtain hxy' | hxy' := isLink_or_isLink_of_union <| h.isLink_of_isLink hxy
  · exact False.elim <| hy <| hxy'.right_mem
  exact ⟨x, hxy.left_mem, hx, hxy'.left_mem⟩

lemma union_not_connected_of_disjoint_vertexSet (hV : Disjoint V(G) V(H)) (hG : V(G).Nonempty)
    (hH : V(H).Nonempty) : ¬ (G ∪ H).Connected := by
  obtain ⟨x, hx⟩ := hG
  obtain ⟨y, hy⟩ := hH
  intro h
  obtain ⟨W, hW, rfl, rfl⟩ := (h.connectedBetween (x := x) (y := y) (by simp [hx]) (by simp [hy]))
  obtain ⟨u, -, huG, huH⟩ := hW.exists_mem_mem_of_union first_mem last_mem hx hy
  exact hV.notMem_of_mem_left huG huH

/-! ### Cycles -/

/-- Two vertices of a cycle are connected after deleting any other vertex.  -/
lemma IsCycle.connectedBetween_deleteVertex_of_mem_of_mem (hC : G.IsCycle C) (x : α) (hy₁ : y₁ ∈ C)
    (hy₂ : y₂ ∈ C) (hne₁ : y₁ ≠ x) (hne₂ : y₂ ≠ x) :
    (G - ({x} : Set α)).ConnectedBetween y₁ y₂ := by
  obtain rfl | hne := eq_or_ne y₁ y₂
  · simpa [hC.vertexSet_subset hy₁]
  obtain ⟨u, e, rfl⟩ | hnt := hC.loop_or_nontrivial
  · simp_all
  by_cases hxC : x ∈ C
  · obtain ⟨P, hP, hP_eq⟩ := hC.exists_isPath_toGraph_eq_delete_vertex hnt hxC
    refine IsWalk.connectedBetween_of_mem_of_mem (W := P) ?_ ?_ ?_
    · simp [hP.isWalk, ← toGraph_vertexSet, hP_eq]
    all_goals simp_all [← mem_vertexSet_iff, ← toGraph_vertexSet]
  exact IsWalk.connectedBetween_of_mem_of_mem (W := C) (by simp [hxC, hC.isWalk]) hy₁ hy₂

/-- Two vertices of a cycle are connected after deleting any edge. -/
lemma IsCycle.connectedBetween_deleteEdge_of_mem_of_mem (hC : G.IsCycle C) (e : β)
    (hx₁ : x₁ ∈ C) (hx₂ : x₂ ∈ C) : (G ＼ {e}).ConnectedBetween x₁ x₂ := by
  obtain heC | heC := em' <| e ∈ C.edge
  · exact IsWalk.connectedBetween_of_mem_of_mem (by simp [hC.isWalk, heC]) hx₁ hx₂
  obtain ⟨P, hP, hP_eq⟩ := hC.exists_isPath_toGraph_eq_delete_edge heC
  apply IsWalk.connectedBetween_of_mem_of_mem (W := P)
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
  obtain ⟨W, hW, rfl, rfl⟩ := (hC.isWalk.connectedBetween_of_mem_of_mem hxC hyC)
  obtain ⟨a, -, haG, haH⟩ := hW.exists_mem_mem_of_union first_mem last_mem hxG hyH
  have hxa : W.first ≠ a := by rintro rfl; contradiction
  have hya : W.last ≠ a := by rintro rfl; contradiction
  -- Now take an `xy`-path in `C` that doesn't use `a`. This must intersect `V(G) ∩ V(H)`
  -- in another vertex `b`, contradicting the fact that the intersection is a subsingleton.
  obtain ⟨w', hW', h1', h2'⟩ :=
    (hC.connectedBetween_deleteVertex_of_mem_of_mem a hxC hyC hxa hya)
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
  rw [walkable_eq_induce_setOf_connectedBetween]
  refine le_induce_of_le_of_subset hle fun y hy ↦ (hH.connectedBetween hx hy).of_le hle

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
  simp only [sUnion_vertexSet, mem_iUnion, exists_prop, forall_exists_index, and_imp]
  intro v H hH hvH
  rw [← G.eq_sUnion_components, ← hH.isClosedSubgraph.eDegree_eq hvH]
  exact h H hH v
