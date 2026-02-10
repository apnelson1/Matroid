import Matroid.Graph.Connected.Defs
import Matroid.Graph.Degree.Constructions
import Matroid.ForMathlib.Data.Set.Subsingleton

open Set Function Nat WList

variable {α β : Type*} {G H H₁ H₂ K : Graph α β} {u v x x₁ x₂ y y₁ y₂ z : α} {e e' f g : β}
  {U V S T : Set α} {F F' R R': Set β} {C W P Q : WList α β} {n m : ℕ}

namespace Graph

lemma IsCompOf.connected (h : H.IsCompOf G) : H.Connected :=
  h.of_le_le le_rfl h.le

lemma IsCompOf.preconnected (h : H.IsCompOf G) : H.Preconnected :=
  h.connected.pre

lemma walkable_connected (hx : x ∈ V(G)) : (G.walkable x).Connected :=
  (walkable_isCompOf hx).connected

lemma Preconnected.components_subsingleton (h : G.Preconnected) : G.Components.Subsingleton := by
  intro H₁ hH₁ H₂ hH₂
  obtain ⟨x, hx, rfl⟩ := hH₁.exists_walkable
  obtain ⟨y, hy, rfl⟩ := hH₂.exists_walkable
  exact walkable_eq_walkable_of_mem <| h y x (hH₂.subset hy) (hH₁.subset hx)

lemma components_subsingleton_iff : G.Components.Subsingleton ↔ G.Preconnected := by
  refine ⟨fun h x y hx hy ↦ ?_, Preconnected.components_subsingleton⟩
  rw [connBetween_iff_mem_walkable_of_mem, h (G.walkable_isCompOf hx) (G.walkable_isCompOf hy)]
  exact mem_walkable_self_iff.mpr hy

lemma Connected.components_subsingleton (hG : G.Connected) : G.Components.Subsingleton :=
  hG.pre.components_subsingleton

@[simp]
lemma connPartition_rel_iff (G : Graph α β) (x y : α): G.connPartition x y ↔ G.ConnBetween x y := by
  simp only [connPartition, Partition.rel_iff_exists]
  refine ⟨fun ⟨S, ⟨H, hH, hSeq⟩, hx, hy⟩ => ?_, fun h =>
    ⟨V(G.walkable x), (by use G.walkable x, walkable_isCompOf h.left_mem), by simp [h.left_mem], h⟩⟩
  subst S
  exact hH.preconnected x y hx hy |>.mono hH.le

lemma components_eq_singleton_iff : (∃ H, G.Components = {H}) ↔ G.Connected := by
  refine ⟨?_, ?_⟩
  · intro ⟨H, hH⟩
    have := G.eq_sUnion_components
    simp only [hH, Graph.sUnion_singleton] at this
    subst G
    change H.IsCompOf H
    rw [←mem_components_iff_isCompOf]
    simp_all only [mem_singleton_iff]
  intro hyp
  obtain ⟨x, hx⟩ := hyp.nonempty
  refine ⟨G.walkable x, ?_⟩
  have h₁ := hyp.components_subsingleton
  have h₂ : G.walkable x ∈ G.Components := walkable_isCompOf hx
  rwa [subsingleton_iff_singleton h₂] at h₁

lemma components_subsingleton_iff_connected : G.Components.Subsingleton ↔ G = ⊥ ∨ G.Connected := by
  rw [components_subsingleton_iff, preconnected_iff]

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

lemma walkable_eq_induce_setOf_connBetween : G.walkable x = G[{y | G.ConnBetween x y}] := by
  rw [walkable_isClosedSubgraph.eq_induce]
  congr

lemma walkable_mono (hle : G ≤ H) (x : α) : G.walkable x ≤ H.walkable x := by
  obtain hxG | hxG := (em <| x ∈ V(G)).symm
  · simp [hxG]
  have := (walkable_isCompOf <| vertexSet_mono hle hxG).isInducedSubgraph
  apply this.le_of_le_subset (walkable_isCompOf hxG |>.le.trans hle)
  intro v hv
  exact ConnBetween.mono hv hle

lemma IsCompOf.of_vertexDelete (hH : H.IsCompOf G) (hS : Disjoint V(H) S) : H.IsCompOf (G - S) := by
  refine ⟨⟨hH.isClosedSubgraph.vertexDelete_of_disjoint hS, hH.1.2⟩, ?_⟩
  rintro K ⟨hKcS, ⟨v, hvK⟩⟩ hKH
  obtain rfl := hH.eq_walkable_of_mem_walkable (vertexSet_mono hKH hvK)
  have hKG := hKcS.isInducedSubgraph.trans <| G.vertexDelete_isInducedSubgraph _
  apply hKG.le_of_le_subset hH.le
  rintro u ⟨w, hw, rfl, rfl⟩
  have hwW : (G.walkable w.first).IsWalk w :=
    hw.isWalk_isClosedSubgraph_of_first_mem G.walkable_isClosedSubgraph (by simp [hw.first_mem])
  have hwS : (G - S).IsWalk w := by
    simp only [isWalk_vertexDelete_iff, hw, true_and]
    exact hS.mono_left hwW.vertexSet_subset
  exact hwS.isWalk_isClosedSubgraph_of_first_mem hKcS hvK |>.last_mem

lemma singleVertex_connected (hG : V(G) = {x}) : G.Connected := by
  simp [connected_iff, hG, preconnected_of_vertexSet_subsingleton]

lemma exists_of_not_connected (h : ¬ G.Connected) (hne : V(G).Nonempty) :
    ∃ X ⊂ V(G), X.Nonempty ∧ ∀ ⦃u v⦄, u ∈ X → G.Adj u v → v ∈ X := by
  simp only [connected_iff, hne, Preconnected, true_and, not_forall, exists_prop,
    exists_and_left] at h
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  refine ⟨{z | G.ConnBetween x z}, ?_, ⟨x, by simpa⟩,
    fun u v (h : G.ConnBetween x u) huv ↦ h.trans huv.connBetween⟩
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
  exact ⟨by simp, fun x y hx hy ↦ hW.isWalk_toGraph.connBetween_of_mem_of_mem
    (by simpa using hx) (by simpa using hy)⟩

lemma IsWalk.toGraph_connected (hW : G.IsWalk W) : W.toGraph.Connected :=
  hW.wellFormed.toGraph_connected

lemma Preconnected.exists_connBetween_deleteEdge_set {X : Set α} (hG : G.Preconnected)
    (hX : (X ∩ V(G)).Nonempty) (hu : u ∈ V(G)) : ∃ x ∈ X, (G ＼ E(G[X])).ConnBetween u x := by
  obtain ⟨x', hx'X, hx'V⟩ := hX
  obtain ⟨W, hW, hu, rfl⟩ := (hG _ _ hu hx'V)
  induction hW generalizing u with
  | nil => exact ⟨_, hx'X, by simp_all⟩
  | @cons x e W hW h ih =>
    obtain rfl : x = u := hu
    by_cases hmem : e ∈ E(G ＼ E(G[X]))
    · obtain ⟨x', hx', hWx'⟩ := ih (u := W.first) (hW.vertex_mem_of_mem (by simp)) rfl
        (by simpa using hx'X) (by simpa using hx'V)
      have hconn := (h.of_le_of_mem edgeDelete_le hmem).connBetween
      exact ⟨x', hx', hconn.trans hWx'⟩
    rw [edgeDelete_edgeSet, mem_diff, and_iff_right h.edge_mem, h.mem_induce_iff, not_not] at hmem
    exact ⟨x, hmem.1, by simpa⟩

lemma Preconnected.exists_isPathFrom (hG : G.Preconnected) (hS : (S ∩ V(G)).Nonempty)
    (hT : (T ∩ V(G)).Nonempty) : ∃ P, G.IsPathFrom S T P := by
  obtain ⟨x, hxS, hx⟩ := hS
  obtain ⟨y, hyT, hy⟩ := hT
  obtain ⟨W, hW, rfl, rfl⟩ := (hG _ _ hx hy)
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
    refine ⟨⟨by rwa [h_eq], hP₀.isPath, fun hxP₀ ↦ hPS ?_⟩, hxS, hP₀.last_mem, ?_, ?_⟩
    · rwa [← h_eq, ← hP₀.eq_first_of_mem hxP₀ (by simp [hxS])]
    · simp only [mem_cons_iff, forall_eq_or_imp, implies_true, true_and]
      exact fun a haP haS ↦ hPS.elim <| by rwa [← h_eq, ← hP₀.eq_first_of_mem haP (by simp [haS])]
    simp only [mem_cons_iff, forall_eq_or_imp, hxT, IsEmpty.forall_iff, true_and]
    exact fun a haP₀ haT ↦ hP₀.eq_last_of_mem haP₀ haT

lemma Preconnected.exists_connBetween_deleteEdge_set_set (hG : G.Preconnected)
    (hS : (S ∩ V(G)).Nonempty) (hT : (T ∩ V(G)).Nonempty) :
    ∃ x ∈ S, ∃ y ∈ T, (G ＼ (E(G[S]) ∪ E(G[T]))).ConnBetween x y := by
  obtain ⟨P, hP⟩ := hG.exists_isPathFrom hS hT
  have h0 : P.first ∈ V(G ＼ (E(G[S]) ∪ E(G[T]))) := by
    simpa using hP.isWalk.vertex_mem_of_mem (by simp)
  refine ⟨_, hP.first_mem, _, hP.last_mem,
    (hP.isPathFrom_le (by simp) (fun e heP ↦ ?_) h0).isWalk.connBetween_first_last⟩
  obtain ⟨x, y, hxy⟩ := exists_dInc_of_mem_edge heP
  have hxy' := hP.isWalk.isLink_of_dInc hxy
  rw [edgeDelete_edgeSet, mem_diff, mem_union, hxy'.mem_induce_iff,
    hxy'.mem_induce_iff, and_iff_right hxy'.edge_mem]
  simp [hP.notMem_left_of_dInc hxy, hP.notMem_right_of_dInc hxy]

lemma loopRemove_preconnected_iff (G : Graph α β) :
    (G.loopRemove).Preconnected ↔ G.Preconnected := by
  refine ⟨fun h s t hs ht ↦ h s t hs ht |>.mono G.loopRemove_le, fun h s t hs ht ↦ ?_⟩
  obtain ⟨P, hP, rfl, rfl⟩ := h s t hs ht |>.exists_isPath
  use P, hP.loopRemove.isWalk

lemma loopRemove_connected_iff (G : Graph α β) : (G.loopRemove).Connected ↔ G.Connected := by
  rw [connected_iff, connected_iff, loopRemove_preconnected_iff]
  simp

lemma edgeDelete_connected_iff_of_forall_isLoopAt (hF : ∀ e ∈ F, ∃ x, G.IsLoopAt e x) :
    (G ＼ F).Connected ↔ G.Connected := by
  refine ⟨fun h ↦ h.of_isSpanningSubgraph <| G.edgeDelete_isSpanningSubgraph, fun h ↦ ?_⟩
  rw [← loopRemove_connected_iff, loopRemove] at h
  rw [edgeDelete_eq_edgeRestrict]
  refine h.of_isSpanningSubgraph ?_
  apply edgeRestrict_isSpanningSubgraph_edgeRestrict
  intro e ⟨he, hel⟩
  have := by simpa using mt (hF e)
  use he, he, this hel

lemma edgeDelete_isLoopAt_isSep_iff (C) : (G ＼ E(G, u, u)).IsSep C ↔ G.IsSep C := by
  refine ⟨fun h ↦ ⟨h.subset_vx, fun hc ↦ ?_⟩, fun h ↦ ⟨h.subset_vx, fun hc ↦ ?_⟩⟩
  swap
  · rw [edgeDelete_vertexDelete] at hc
    exact h.not_connected <| hc.of_isSpanningSubgraph <| edgeDelete_isSpanningSubgraph ..
  have := h.not_connected
  by_cases huC : u ∈ C
  · rw [edgeDelete_vertexDelete, edgeDelete_eq_of_disjoint] at this
    exact this hc
    rw [vertexDelete_edgeSet_diff]
    exact disjoint_sdiff_left.mono_right
    <| G.linkEdges_subset_incEdges_left u u |>.trans <| G.incEdge_subset_setIncEdges huC
  rw [edgeDelete_vertexDelete, edgeDelete_connected_iff_of_forall_isLoopAt] at this
  exact this hc
  intro e he
  use u, by simpa
  simp [he.left_mem, huC]

lemma Preconnected.edgeDelete_linkEdges_connBetween_or (hG : G.Preconnected) (hx : x ∈ V(G))
    (hu : u ∈ V(G)) (hv : v ∈ V(G)) :
    (G ＼ E(G, u, v)).ConnBetween x u ∨ (G ＼ E(G, u, v)).ConnBetween x v := by
  obtain ⟨w, (rfl | rfl), hw⟩ := hG.exists_connBetween_deleteEdge_set (X := {u, v})
    ⟨u, by simp, hu⟩ hx
  <;> replace hw := hw.mono <| G.edgeDelete_anti_right <| G.induce_pair_edgeSet _ _ <;> tauto

lemma Preconnected.edgeDelete_linkEdges_not_connBetween (hG : G.Preconnected)
    (h' : ¬ (G ＼ E(G, u, v)).Preconnected) : ¬ (G ＼ E(G, u, v)).ConnBetween u v := by
  contrapose! h'
  apply preconnected_of_exists_connBetween
  use u
  intro x hx
  simp only [edgeDelete_vertexSet] at hx
  obtain hw | hw := hG.edgeDelete_linkEdges_connBetween_or hx h'.left_mem h'.right_mem
  · exact hw.symm
  exact .trans h' hw.symm

lemma Preconnected.edgeDelete_linkEdges_components (hG : G.Preconnected) (hu : u ∈ V(G))
    (hv : v ∈ V(G)) :
    (G ＼ E(G, u, v)).Components = {(G ＼ E(G, u, v)).walkable u, (G ＼ E(G, u, v)).walkable v} := by
  rw [components_eq_walkable_image]
  ext H
  simp only [edgeDelete_vertexSet, mem_image, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply (hG.edgeDelete_linkEdges_connBetween_or hx hu hv).imp <;> intro h <;> grw [h]
  · rintro (rfl | rfl)
    · use u
    · use v

lemma Preconnected.walkable_singleton_left_of_vertexDelete_connected (hG : G.Preconnected)
    (h : ¬ (G ＼ E(G, u, v)).Connected) (huconn : (G - u).Connected) :
    V((G ＼ E(G, u, v)).walkable u) = {u} := by
  rw [connected_iff, not_and_or, edgeDelete_vertexSet, vertexSet_not_nonempty_iff] at h
  obtain rfl | h := h
  · simp at huconn
  have hu : u ∈ V(G) := by
    by_contra! hu
    simp [hu, hG] at h
  have hv : v ∈ V(G) := by
    by_contra! hv
    simp [hv, hG] at h
  have hne : u ≠ v := by
    by_contra huv
    rw [← loopRemove_preconnected_iff] at hG
    subst v
    simp only [linkEdges_self] at h
    exact h <| hG.isSpanningSubgraph <| G.loopRemove_isSpanningSubgraph_edgeDelete_isLoopAt u
  refine subset_antisymm ?_ (by simpa)
  have := (G ＼ E(G, u, v)).walkable_isClosedSubgraph (u := u) |>.vertexDelete {u}
  rw [edgeDelete_vertexDelete, ← vertexDelete_singleton, ← vertexDelete_singleton,
    (G - u).edgeDelete_eq ?_] at this
  have := mt (huconn.eq_of_isClosedSubgraph this) ?_
  simpa [vertexDelete_vertexSet, not_nonempty_iff_eq_empty, diff_eq_empty] using this
  · apply_fun vertexSet
    intro heq
    have : v ∈ V(G - u) := by simp [hne.symm, hv]
    rw [← heq] at this
    simp only [vertexDelete_singleton, vertexDelete_vertexSet, mem_diff,
      ← connBetween_iff_mem_walkable_of_mem, mem_singleton_iff, hne.symm, not_false_eq_true,
      and_true] at this
    exact hG.edgeDelete_linkEdges_not_connBetween h this
  · rw [disjoint_iff_forall_notMem, vertexDelete_singleton, vertexDelete_edgeSet_diff,
      setIncEdges_singleton]
    intro e ⟨he, heu⟩
    contrapose! heu
    exact G.linkEdges_subset_incEdges_left u v heu

lemma Preconnected.walkable_singleton_right_of_vertexDelete_connected (hG : G.Preconnected)
    (h : ¬ (G ＼ E(G, u, v)).Connected) (hvconn : (G - v).Connected) :
    V((G ＼ E(G, u, v)).walkable v) = {v} := by
  rw [linkEdges_comm] at h ⊢
  exact hG.walkable_singleton_left_of_vertexDelete_connected h hvconn

lemma not_connected_or_singleton_isSep_or_pair (h : ¬ (G ＼ E(G, u, v)).Connected) :
    ¬ G.Connected ∨ G.IsSep {u} ∨ G.IsSep {v} ∨ V(G) = {u, v} := by
  simp only [or_iff_not_imp_left, not_not]
  intro hG husep hvsep
  have hu : u ∈ V(G) := by
    by_contra! hu
    simp [hu, hG] at h
  have hv : v ∈ V(G) := by
    by_contra! hv
    simp [hv, hG] at h
  simp only [isSep_iff, singleton_subset_iff, hu, hv, true_and, not_not] at husep hvsep
  have hcomp := (G ＼ E(G, u, v)).eq_sUnion_components
  apply_fun vertexSet at hcomp
  simp only [edgeDelete_vertexSet, (hG.pre.edgeDelete_linkEdges_components hu hv), sUnion_vertexSet,
    mem_insert_iff, mem_singleton_iff, iUnion_iUnion_eq_or_left, iUnion_iUnion_eq_left] at hcomp
  rw [hcomp, hG.pre.walkable_singleton_left_of_vertexDelete_connected h husep,
    hG.pre.walkable_singleton_right_of_vertexDelete_connected h hvsep, pair_comm]
  simp

lemma not_preconnected_or_singleton_isSep_or_pair (h : ¬ (G ＼ E(G, u, v)).Preconnected) :
    ¬ G.Preconnected ∨ G.IsSep {u} ∨ G.IsSep {v} ∨ V(G) = {u, v} := by
  refine not_connected_or_singleton_isSep_or_pair (mt Connected.pre h) |>.imp (mt ?_) id
  simp_all only [preconnected_iff, ← vertexSet_not_nonempty_iff, edgeDelete_vertexSet, not_or,
    not_not, not_true_eq_false, false_or, implies_true]

lemma IsSep.of_edgeDelete_linkEdges (h : (G ＼ E(G, u, v)).IsSep S) :
    G.IsSep S ∨ G.IsSep (insert u S) ∨ G.IsSep (insert v S) ∨ V(G) = {u, v} ∪ S := by
  obtain huS | huS := em (u ∈ S)
  · refine Or.inl ⟨by simpa using h.subset_vx, ?_⟩
    have := h.not_connected
    rwa [edgeDelete_vertexDelete, edgeDelete_eq_of_disjoint] at this
    apply Disjoint.mono_right <| (G.linkEdges_subset_incEdges_left u v).trans
    <| G.incEdge_subset_setIncEdges huS
    rw [vertexDelete_edgeSet_diff]
    exact disjoint_sdiff_left
  obtain hvS | hvS := em (v ∈ S)
  · refine Or.inl ⟨by simpa using h.subset_vx, ?_⟩
    have := h.not_connected
    rwa [edgeDelete_vertexDelete, edgeDelete_eq_of_disjoint] at this
    apply Disjoint.mono_right <| (G.linkEdges_subset_incEdges_right u v).trans
    <| G.incEdge_subset_setIncEdges hvS
    rw [vertexDelete_edgeSet_diff]
    exact disjoint_sdiff_left

  have : ¬((G - S) ＼ E(G - S, u, v)).Connected := by
    have := h.not_connected
    rw [edgeDelete_vertexDelete] at this
    exact mt (Connected.of_isSpanningSubgraph ·
    <| (G - S).edgeDelete_isSpanningSubgraph_anti_right <| by simp [huS, hvS]) this
  obtain hnconn | hsepu | hsepv | hpair := (G - S).not_connected_or_singleton_isSep_or_pair
    this
  · exact Or.inl ⟨by simpa using h.subset_vx, hnconn⟩
  · refine Or.inr (Or.inl ⟨?_, ?_⟩)
    · have := by simpa using hsepu.subset_vx
      simpa [insert_subset_iff, this] using h.subset_vx
    · rw [← union_singleton, ← vertexDelete_vertexDelete]
      exact hsepu.not_connected
  · refine Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩))
    · have := by simpa using hsepv.subset_vx
      simpa [insert_subset_iff, this] using h.subset_vx
    · rw [← union_singleton, ← vertexDelete_vertexDelete]
      exact hsepv.not_connected
  · refine Or.inr (Or.inr (Or.inr ?_))
    simp only [vertexDelete_vertexSet] at hpair
    rw [← hpair, diff_union_self, eq_comm, union_eq_left]
    simpa using h.subset_vx

lemma ConnGE.edgeDelete_linkEdges (h : G.ConnGE (n + 1)) (u v : α) :
    (G ＼ E(G, u, v)).ConnGE n where
  le_cut C hC := by
    by_contra! hcd
    obtain h1 | h2 | h3 | h4 := hC.of_edgeDelete_linkEdges
    · have := hcd.trans_le' (h.le_cut h1)
      norm_cast at this
      simp at this
    · simpa [hcd.not_ge] using h.le_cut h2 |>.trans <| encard_insert_le ..
    · simpa [hcd.not_ge] using h.le_cut h3 |>.trans <| encard_insert_le ..
    obtain h | hss := h.le_card.symm
    · grw [h4, insert_union, singleton_union, encard_insert_le, encard_insert_le] at h
      enat_to_nat!
      omega
    obtain hne | rfl := eq_or_ne u v |>.symm
    · apply hss.not_nontrivial
      use u, (by simp [h4]), v, (by simp [h4])
    rw [edgeDelete_isLoopAt_isSep_iff] at hC
    have := h.le_cut ⟨hC.subset_vx, hC.not_connected⟩
    enat_to_nat!
    omega
  le_card := by
    simp only [edgeDelete_vertexSet]
    refine h.le_card.imp id (fun h ↦ ?_)
    enat_to_nat!
    omega

lemma Preconnected.exists_isLink_of_mem (h : G.Preconnected) (hV : V(G).Nontrivial) (hx : x ∈ V(G)):
    ∃ e y, G.IsLink e x y ∧ y ≠ x := by
  obtain ⟨z, hz, hne⟩ := hV.exists_ne x
  obtain ⟨P, hP, rfl, rfl⟩ := (h _ _ hx hz).exists_isPath
  rw [ne_comm, first_ne_last_iff hP.nodup] at hne
  obtain ⟨x, e, P⟩ := hne
  simp only [cons_isPath_iff] at hP
  exact ⟨e, P.first, hP.1, mt (by simp +contextual [eq_comm]) hP.2.2⟩

lemma Connected.exists_isLink_of_mem (hG : G.Connected) (hV : V(G).Nontrivial) (hx : x ∈ V(G)) :
    ∃ e y, G.IsLink e x y ∧ y ≠ x := hG.pre.exists_isLink_of_mem hV hx

lemma Isolated.not_preconnected (hx : G.Isolated x) (hnt : V(G).Nontrivial) : ¬ G.Preconnected :=
  fun h ↦ by simpa [hx.not_isLink] using h.exists_isLink_of_mem hnt hx.mem

lemma Isolated.not_connected (hx : G.Isolated x) (hnt : V(G).Nontrivial) : ¬ G.Connected :=
  fun h ↦ by simpa [hx.not_isLink] using h.exists_isLink_of_mem hnt hx.mem

lemma Preconnected.degreePos (h : G.Preconnected) (hnt : V(G).Nontrivial) : G.DegreePos := by
  intro x hx
  obtain ⟨e, y, h, -⟩ := h.exists_isLink_of_mem hnt hx
  exact ⟨e, h.inc_left⟩

lemma Connected.degreePos (h : G.Connected) (hnt : V(G).Nontrivial) : G.DegreePos :=
  h.pre.degreePos hnt

lemma Connected.edgeSet_nonempty (h : G.Connected) (hnt : V(G).Nontrivial) : E(G).Nonempty := by
  obtain ⟨x, hx⟩ := hnt.nonempty
  obtain ⟨e, y, he, -⟩ := h.exists_isLink_of_mem hnt hx
  exact ⟨e, he.edge_mem⟩

lemma Preconnected.finite [G.EdgeFinite] (h : G.Preconnected) : G.Finite where
  vertexSet_finite := by
    obtain hss | hnt := V(G).subsingleton_or_nontrivial
    · exact hss.finite
    have : V(G, E(G)) = V(G) := by
      ext x
      refine ⟨fun ⟨e, he, hex⟩ ↦ hex.vertex_mem, fun hx ↦ ?_⟩
      obtain ⟨e, y, h, -⟩ := h.exists_isLink_of_mem hnt hx
      exact ⟨e, h.edge_mem, h.inc_left⟩
    rw [← this, ← encard_lt_top_iff]
    exact lt_of_le_of_lt (endSetSet_encard_le G E(G))
    <| WithTop.mul_lt_top (compareOfLessAndEq_eq_lt.mp rfl) (encard_lt_top_iff.mpr G.edgeSet_finite)

lemma Connected.finite [G.EdgeFinite] (h : G.Connected) : G.Finite := h.pre.finite

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
    (hG.connBetween (S.left_subset hx₀) (S.right_subset hy₀))
  rw [← S.not_left_mem_iff (S.right_subset hy₀)] at hy₀
  obtain ⟨e, x, y, hexy, hx, hy⟩ := W.exists_dInc_prop_not_prop hx₀ hy₀
  have h' := hW.isLink_of_dInc hexy
  rw [S.not_left_mem_iff h'.right_mem] at hy
  refine ⟨S, e, x, y, fun heF ↦ ?_, hx, hy, h'⟩
  exact S.not_adj hx hy <| IsLink.adj <| h'.of_le_of_mem (by simp) <| by simpa [h'.edge_mem]

lemma IsSep.exists_adj_of_isCompOf_vertexDelete (hM : IsSep G S) (hG : G.Connected)
    (hH : H.IsCompOf (G - S)) : ∃ x ∈ S, ∃ y ∈ V(H), G.Adj x y := by
  by_contra! hno
  have hHcl' : H ≤c G - S := hH.1.1
  have hHcl : H ≤c G := by
    refine ⟨hHcl'.le.trans vertexDelete_le, fun e x ⟨y, hxy⟩ hxH ↦ hHcl'.closed ?_ hxH⟩
    refine ((G.vertexDelete_isLink_iff S).2 ⟨hxy, ?_, ?_⟩).inc_left
    · simpa using (vertexSet_mono hHcl'.le hxH).2
    exact (hno y · x hxH <| by simpa [adj_comm] using hxy.adj)
  obtain rfl : H = G := hG.eq_of_isClosedSubgraph hHcl hH.1.2
  obtain ⟨x, hxS⟩ := hM.nonempty_of_connected hG
  have := by simpa [disjoint_iff_forall_notMem] using hHcl'.le
  exact this (hM.subset_vx hxS) hxS

/-- Every vertex in a mininum cardinality separator has an edge to components of the vertex-deleted
graph. This lemma requires the separator to be finite because `IsMinSep` uses `encard` for
cardinality comparison and cannot tell the size difference of infinite sets. -/
lemma IsMinSep.exists_adj_of_isCompOf_vertexDelete (hM : IsMinSep G S) (hH : H.IsCompOf (G - S))
    (hx : x ∈ S) (hfin : S.Finite) : ∃ y ∈ V(H), G.Adj x y := by
  by_contra! hno
  have hHcl : H ≤c G - S := hH.1.1
  refine hM.not_isSep_of_encard_lt (hfin.diff.encard_lt_encard (by simpa : S \ {x} ⊂ _)) ?_
  refine ⟨diff_subset.trans hM.subset_vx, fun hcon ↦ ?_⟩
  have hHclS' : H ≤c (G - (S \ {x})) := by
    refine ⟨hHcl.le.trans (by grw [diff_subset]), fun e u ⟨v, huv⟩ huH ↦ hHcl.closed ⟨v, ?_⟩ huH⟩
    simp only [vertexDelete_isLink_iff, huv.of_le vertexDelete_le, vertexSet_mono hHcl.le huH |>.2,
      not_false_eq_true, true_and]
    obtain rfl | hvne := eq_or_ne v x
    · exact hno u huH (huv.symm.of_le vertexDelete_le).adj |>.elim
    simpa [hvne] using huv.right_mem.2
  obtain rfl : H = G - (S \ {x}) := hcon.eq_of_isClosedSubgraph hHclS' hH.1.2
  have hxnotH : x ∉ V(G - (S \ {x})) := (vertexSet_mono hHcl.le · |>.2 hx)
  exact hxnotH <| by simp [hM.toIsSep.subset_vx hx]

lemma ConnGE.connected {n : ℕ} (hG : G.ConnGE n) (hn : 1 ≤ n) : G.Connected := by
  have h1 : G.ConnGE 1 := hG.anti_right hn
  simpa [connGE_one_iff] using h1

lemma Preconnected.exists_isNonloopAt_of_nontrivial (hG : G.Preconnected)
    (hnt : V(G).Nontrivial) : ∃ e x, G.IsNonloopAt e x := by
  obtain ⟨x, hx⟩ := hnt.nonempty
  obtain ⟨e, y, hxy, hne⟩ := hG.exists_isLink_of_mem hnt hx
  exact ⟨e, x, ⟨y, hne, hxy⟩⟩

lemma ConnGE.exists_isNonloopAt {k : ℕ} (hG : G.ConnGE k) (hk : 2 ≤ k) :
    ∃ e x, G.IsNonloopAt e x := by
  have hconn : G.Connected := hG.connected (show 1 ≤ k from (by decide : 1 ≤ 2).trans hk)
  have hle : (k : ℕ∞) ≤ V(G).encard := by simpa using hG.le_cut vertexSet_isSep
  have hnt : V(G).Nontrivial := by
    exact two_le_encard_iff_nontrivial.mp <| (by norm_cast : (2 : ℕ∞) ≤ k).trans hle
  obtain ⟨x, hx⟩ := hconn.nonempty
  obtain ⟨e, y, hxy, hne⟩ := hconn.exists_isLink_of_mem hnt hx
  exact ⟨e, x, ⟨y, hne, hxy⟩⟩

/- ### Unions -/

lemma Compatible.union_connected_of_forall (h : G.Compatible H) (hG : G.Connected)
    (hH : ∀ x ∈ V(H), ∃ y ∈ V(G), H.ConnBetween x y) : (G ∪ H).Connected := by
  obtain ⟨v, hv⟩ := hG.nonempty
  refine connected_of_vertex (u := v) (by simp [hv]) ?_
  rintro y (hy | hy)
  · exact (hG.connBetween hy hv).mono <| Graph.left_le_union ..
  obtain ⟨z, hzG, hyz⟩ := hH _ hy
  exact (hyz.mono h.right_le_union).trans <| (hG.connBetween hzG hv).mono <|
    Graph.left_le_union ..

lemma Compatible.union_connected_of_nonempty_inter (h : Compatible G H) (hG : G.Connected)
    (hH : H.Connected) (hne : (V(G) ∩ V(H)).Nonempty) : (G ∪ H).Connected :=
  let ⟨z, hzG, hzH⟩ := hne
  h.union_connected_of_forall hG fun _ hx ↦ ⟨z, hzG, hH.connBetween hx hzH⟩

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
  obtain ⟨W, hW, rfl, rfl⟩ := (h.connBetween (x := x) (y := y) (by simp [hx]) (by simp [hy]))
  obtain ⟨u, -, huG, huH⟩ := hW.exists_mem_mem_of_union first_mem last_mem hx hy
  exact hV.notMem_of_mem_left huG huH

lemma IsPath.isPath_of_union_of_subsingleton_inter (hP : (G ∪ H).IsPath P)
    (hi : (V(G) ∩ V(H)).Subsingleton) (hf : P.first ∈ V(G)) (hl : P.last ∈ V(G)) :
    G.IsPath P := by
  wlog hc : Compatible G H generalizing H with aux
  · exact aux (union_eq_union_edgeDelete .. ▸ hP) (hi.anti (by simp))
      (Compatible.of_disjoint_edgeSet disjoint_sdiff_right)
  induction P with
  | nil u => simpa [hf]
  | cons u e w ih =>
    obtain ⟨heuwf, hw, huw⟩ := cons_isPath_iff.mp hP
    obtain heG | heH := by simpa using heuwf.edge_mem
    · replace heuwf : G.IsLink e u w.first := heuwf.of_le_of_mem (Graph.left_le_union ..) heG
      simp [ih heuwf.right_mem hl hw, heuwf, huw]
    replace heH : H.IsLink e u w.first := heuwf.of_le_of_mem (hc.right_le_union ..) heH
    rw [hc.union_comm] at hw
    obtain ⟨z, hz, hzH, hzG⟩ := hw.isWalk.exists_mem_mem_of_union first_mem last_mem heH.right_mem
      hl
    obtain rfl := hi ⟨hf, heH.left_mem⟩ ⟨hzG, hzH⟩
    exact huw hz |>.elim

/-! ### Cycles -/

/-- Two vertices of a cycle are connected after deleting any other vertex.  -/
lemma IsCyclicWalk.connBetween_deleteVertex_of_mem_of_mem (hC : G.IsCyclicWalk C) (x : α)
    (hy₁ : y₁ ∈ C) (hy₂ : y₂ ∈ C) (hne₁ : y₁ ≠ x) (hne₂ : y₂ ≠ x) :
    (G - ({x} : Set α)).ConnBetween y₁ y₂ := by
  obtain rfl | hne := eq_or_ne y₁ y₂
  · simpa [hC.vertexSet_subset hy₁]
  obtain ⟨u, e, rfl⟩ | hnt := hC.loop_or_nontrivial
  · simp_all
  by_cases hxC : x ∈ C
  · obtain ⟨P, hP, hP_eq⟩ := hC.exists_isPath_toGraph_eq_delete_vertex hnt hxC
    refine IsWalk.connBetween_of_mem_of_mem (W := P) ?_ ?_ ?_
    · simp [hP.isWalk, ← toGraph_vertexSet, hP_eq]
    all_goals simp_all [← mem_vertexSet_iff, ← toGraph_vertexSet]
  exact IsWalk.connBetween_of_mem_of_mem (W := C) (by simp [hxC, hC.isWalk]) hy₁ hy₂

/-- Two vertices of a cycle are connected after deleting any edge. -/
lemma IsCyclicWalk.connBetween_deleteEdge_of_mem_of_mem (hC : G.IsCyclicWalk C) (e : β)
    (hx₁ : x₁ ∈ C) (hx₂ : x₂ ∈ C) : (G ＼ {e}).ConnBetween x₁ x₂ := by
  obtain heC | heC := em' <| e ∈ C.edge
  · exact IsWalk.connBetween_of_mem_of_mem (by simp [hC.isWalk, heC]) hx₁ hx₂
  obtain ⟨P, hP, hP_eq⟩ := hC.exists_isPath_toGraph_eq_delete_edge heC
  apply IsWalk.connBetween_of_mem_of_mem (W := P)
    (by simp [hP.isWalk, ← toGraph_edgeSet, hP_eq])
  all_goals rwa [← mem_vertexSet_iff, ← toGraph_vertexSet, hP_eq, edgeDelete_vertexSet,
    toGraph_vertexSet, mem_vertexSet_iff]

/-- If two graphs intersect in at most one vertex,
then any cycle of their union is a cycle of one of the graphs. -/
lemma IsCyclicWalk.isCyclicWalk_or_isCyclicWalk_of_union_of_subsingleton_inter
    (hC : (G ∪ H).IsCyclicWalk C) (hi : (V(G) ∩ V(H)).Subsingleton) :
    G.IsCyclicWalk C ∨ H.IsCyclicWalk C := by
  wlog hc : Compatible G H generalizing H with aux
  · obtain (hG | hH) := aux (union_eq_union_edgeDelete .. ▸ hC) (hi.anti (by simp))
      (Compatible.of_disjoint_edgeSet disjoint_sdiff_right)
    · exact .inl hG
    exact .inr <| hH.of_le <| by simp
  obtain ⟨u, e, w⟩ := hC.nonempty
  wlog heG : e ∈ E(G) generalizing G H with aux
  · obtain heH := by simpa using hC.isWalk.edge_mem_of_mem (e := e) (by simp) |>.resolve_left heG
    rw [inter_comm] at hi
    rw [hc.union_comm] at hC
    exact aux hi hc.symm hC heH |>.symm
  left
  obtain rfl := by simpa using hC.isClosed
  have he := cons_isWalk_iff.mp hC.isWalk |>.1
  have hw := by simpa using hC.tail_isPath
  refine hC.isCycle_of_le (Graph.left_le_union ..) ?_
  replace he : G.IsLink e w.last w.first := he.of_le_of_mem (Graph.left_le_union ..) heG
  replace hw : G.IsPath w := hw.isPath_of_union_of_subsingleton_inter hi he.right_mem he.left_mem
  simp [he.edge_mem, insert_subset_iff, hw.isWalk.edgeSet_subset]

lemma Compatible.isCyclicWalk_union_iff_of_subsingleton_inter (hcompat : G.Compatible H)
    (hi : (V(G) ∩ V(H)).Subsingleton) :
    (G ∪ H).IsCyclicWalk C ↔ G.IsCyclicWalk C ∨ H.IsCyclicWalk C :=
  ⟨fun h ↦ h.isCyclicWalk_or_isCyclicWalk_of_union_of_subsingleton_inter hi,
    fun h ↦ h.elim (fun h' ↦ h'.of_le (Graph.left_le_union ..))
    (fun h' ↦ h'.of_le hcompat.right_le_union)⟩


/-- Every connected subgraph of `G` is a subgraph of a component of `G`. -/
lemma Connected.exists_component_ge (hH : H.Connected) (hle : H ≤ G) :
    ∃ G₁, G₁.IsCompOf G ∧ H ≤ G₁ := by
  obtain ⟨x, hx⟩ := hH.nonempty
  refine ⟨_, walkable_isCompOf (vertexSet_mono hle hx), ?_⟩
  rw [walkable_eq_induce_setOf_connBetween]
  refine le_induce_of_le_of_subset hle fun y hy ↦ (hH.connBetween hx hy).mono hle

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

lemma IsClosedSubgraph.isCompOf_of_connected (h : H ≤c G) (hH : H.Connected) :
    H.IsCompOf G := by
  refine IsCompOf_iff_isClosedSubgraph_connected.2 ⟨h, hH⟩

lemma Connected.IsCompOf_of_isClosedSubgraph (hH : H.Connected) (h : H ≤c G) :
    H.IsCompOf G := by
  refine IsCompOf_iff_isClosedSubgraph_connected.2 ⟨h, hH⟩

/-- For a proper component `H`, the separation with parts `V(H)` and `V(G) \ V(H)`. -/
@[simps (attr := grind =)]
def IsCompOf.separation_of_ne (h : H.IsCompOf G) (hne : H ≠ G) : G.Separation where
  left := V(H)
  right := V(G) \ V(H)
  nonempty_left := h.connected.nonempty
  nonempty_right := diff_nonempty.2 fun hss ↦ hne <| h.isInducedSubgraph.eq_of_isSpanningSubgraph
    ⟨hss.antisymm' (vertexSet_mono h.le), h.le.isLink_of_isLink⟩
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
  exact fun H h' ↦ (isClosedSubgraph_sUnion_of_stronglyDisjoint s h h').isCompOf_of_connected
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
