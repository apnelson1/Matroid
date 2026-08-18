module

public import Matroid.Graph.Connected.Defs
public import Matroid.Graph.Degree.Constructions
public import Matroid.ForMathlib.Data.Set.Subsingleton
import all Mathlib.Combinatorics.Graph.Delete
public import Mathlib.Combinatorics.Graph.Delete


@[expose] public section

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

@[simp]
lemma walkable_disjoint_iff : Disjoint V(G.walkable x) V(G.walkable y) ↔ ¬ G.ConnBetween x y := by
  wlog hx : x ∈ V(G)
  · simp [hx]
  wlog hy : y ∈ V(G)
  · simp [hy]
  rw [(walkable_isCompOf hx).not_disjoint_iff (walkable_isCompOf hy) |>.not_right,
    walkable_eq_walkable_iff_mem hx, mem_walkable_iff, connBetween_comm]

-- @[simp]
lemma IsCompOf.eq_of_connBetween (hH₁ : H₁.IsCompOf G) (hH₂ : H₂.IsCompOf G)
    (hxy : G.ConnBetween x y) (hx : x ∈ V(H₁)) (hy : y ∈ V(H₂)) : H₁ = H₂ := by
  obtain rfl := hH₁.eq_walkable_of_mem_walkable hx
  obtain rfl := hH₂.eq_walkable_of_mem_walkable hy
  exact hxy.walkable_eq_walkable

lemma Preconnected.components_subsingleton (h : G.Preconnected) : G.Components.Subsingleton := by
  intro H₁ hH₁ H₂ hH₂
  obtain ⟨x, hx, rfl⟩ := hH₁.exists_walkable
  obtain ⟨y, hy, rfl⟩ := hH₂.exists_walkable
  exact walkable_eq_walkable_of_mem <| h y x (hH₂.subset hy) (hH₁.subset hx)

lemma components_subsingleton_iff : G.Components.Subsingleton ↔ G.Preconnected := by
  refine ⟨fun h x y hx hy ↦ ?_, Preconnected.components_subsingleton⟩
  rw [connBetween_iff_mem_walkable_of_mem, h (G.walkable_isCompOf hx) (G.walkable_isCompOf hy)]
  exact mem_walkable_self_iff.mpr hy

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
  have h₁ := hyp.pre.components_subsingleton
  have h₂ : G.walkable x ∈ G.Components := walkable_isCompOf hx
  rwa [subsingleton_iff_singleton h₂] at h₁

@[simp]
lemma numberOfComponents_eq_one_iff : c(G) = 1 ↔ G.Connected := by
  rw [NumberOfComponents, encard_eq_one, components_eq_singleton_iff]
alias ⟨_, Connected.numberOfComponents⟩ := numberOfComponents_eq_one_iff

lemma components_subsingleton_iff_connected : G.Components.Subsingleton ↔ G = ⊥ ∨ G.Connected := by
  rw [components_subsingleton_iff, preconnected_iff]

lemma finite_components_of_finite [G.Finite] : G.Components.Finite :=
  G.vertexSet_finite.finite_of_encard_le G.components_encard_le

lemma ge_two_components_of_not_connected (hNeBot : V(G).Nonempty) (h : ¬ G.Connected) :
    2 ≤ G.Components.encard := by
  by_contra! hcon
  rw [ENat.lt_two_iff, encard_le_one_iff_subsingleton,
    components_subsingleton_iff_connected] at hcon
  grind [ne_bot_iff]

lemma not_connected_of_nontrivial_components (h : G.Components.Nontrivial) : ¬ G.Connected := by
  rw [← numberOfComponents_eq_one_iff, NumberOfComponents]
  rw [← one_lt_encard_iff_nontrivial] at h
  exact h.ne'

lemma components_nontrivial_of_not_connected (hNeBot : V(G).Nonempty) (h : ¬ G.Connected) :
    G.Components.Nontrivial := by
  rw [← two_le_encard_iff_nontrivial]
  exact ge_two_components_of_not_connected hNeBot h

protected lemma Connected.components_eq_singleton_self (h : G.Connected) : G.Components = {G} :=
  (components_subsingleton_iff_connected.mpr (Or.inr h)).eq_singleton_of_mem h

lemma components_eq_singleton_self (h : G.Connected) : G.Components = {G} :=
  h.components_eq_singleton_self

lemma components_eq_singleton_self_iff : H.Components = {H} ↔ H.Connected :=
  ⟨fun h ↦ components_eq_singleton_iff.mp ⟨_, h⟩, fun h ↦ h.connected.components_eq_singleton_self⟩

lemma eq_iff_components_eq_components : G = H ↔ G.Components = H.Components := by
  refine ⟨fun heq ↦ heq ▸ rfl, fun hyp ↦ ?_⟩
  rw [G.eq_sUnion_components, H.eq_sUnion_components]
  simp_all only

lemma IsCompOf.eq_of_connected (hH : H.IsCompOf G) (hG : G.Connected) : H = G := by
  obtain ⟨x, hx⟩ := hH.nonempty
  exact hH.eq_of_mem_mem hG.connected hx (hH.subset hx)

lemma IsClosedSubgraph.isCompOf_of_isCompOf_compl (h : H ≤c G) (hK : K.IsCompOf G) :
    K.IsCompOf H ∨ K.IsCompOf (G - V(H)) := by
  refine (h.disjoint_or_subset_of_isCompOf hK).elim .inl fun hdj ↦ .inr <| hK.of_le_le ?_ (by simp)
  simp [hK.le, le_deleteVerts_iff, hdj.vertex]

lemma Connected.exists_isCompOf_ge (h : H.Connected) (hle : H ≤ G) :
    ∃ G₁, H ≤ G₁ ∧ G₁.IsCompOf G := by
  set s := {G' | G' ≤c G ∧ H ≤ G'} with hs_def
  have hne : s.Nonempty := ⟨G, by simpa [s]⟩
  let G₁ := Graph.sInter s hne
  have hHG₁ : H ≤ G₁ := (Graph.le_sInter_iff ..).2 fun K hK ↦ hK.2
  have hG₁G : G₁ ≤c G := sInter_isClosedSubgraph (fun _ hK ↦ hK.1) _
  refine ⟨G₁, hHG₁, ⟨hG₁G, h.nonempty.mono (vertexSet_mono hHG₁)⟩, fun K ⟨hKG, hKne⟩ hKG₁ ↦ ?_⟩
  refine Graph.sInter_le ?_
  simp only [mem_ofPred_eq, hKG, true_and, s]
  obtain hdj | hne := disjoint_or_nonempty_inter V(K) V(H)
  · have hKG₁' : K ≤c G₁ := hKG.anti_right hKG₁ hG₁G.le
    simp only [Graph.le_sInter_iff, mem_ofPred_eq, and_imp, G₁, s] at hKG₁
    simpa [hHG₁, hdj.symm, hKne.ne_empty] using hKG₁ _ (hKG₁'.compl.trans hG₁G)
  rw [← h.eq_of_isClosedSubgraph (hKG.inter_le hle) (by simpa)]
  exact Graph.inter_le_left

lemma Connected.le_or_le_compl (h : H.Connected) (hle : H ≤ G) (hK : K ≤c G) :
    H ≤ K ∨ H ≤ G - V(K) := by
  obtain ⟨G', hHG', hG'G⟩ := h.exists_isCompOf_ge hle
  obtain hc | hc := hK.isCompOf_of_isCompOf_compl hG'G
  · exact .inl (hHG'.trans hc.le)
  refine .inr <| le_deleteVerts_iff.2 ⟨hle, ?_⟩
  obtain ⟨hG'G, hdj⟩ := by simpa only [le_deleteVerts_iff] using hc.le
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
  simp only [le_deleteVerts_iff, hcompat.right_le_union, true_and] at hHle
  obtain hGK | hGK := disjoint_or_nonempty_inter V(G) V(K)
  · obtain hHK | hHK := disjoint_or_nonempty_inter V(H) V(K)
    · simpa [vertexSet_union, ← inter_eq_right, union_inter_distrib_right, hGK.inter_eq,
        hHK.inter_eq, hKne.ne_empty.symm] using vertexSet_mono hK.le
    rw [or_iff_left (not_disjoint_iff_nonempty_inter.2 hHK)] at hHle
    simpa [hGK.symm.inter_eq] using hi.mono (inter_subset_inter_left _ (vertexSet_mono hHle))
  rw [or_iff_left (not_disjoint_iff_nonempty_inter.2 hGK)] at hGle
  have hne := hi.mono (inter_subset_inter_right _ (vertexSet_mono hGle))
  rw [or_iff_left (not_disjoint_iff_nonempty_inter.2 hne)] at hHle
  exact hK.le.antisymm (Graph.union_le hGle hHle)

lemma connected_union_iff_of_disjoint (hV : Disjoint V(G) V(H)) :
    (G ∪ H).Connected ↔ (G = ⊥ ∧ H.Connected) ∨ (G.Connected ∧ H = ⊥) := by
  obtain rfl | hG := eq_or_ne G ⊥
  · simp
  obtain rfl | hH := eq_or_ne H ⊥
  · simp
  suffices ¬ (G ∪ H).Connected by simpa [hG, hH]
  let s : (G ∪ H).Separation := by
    refine ⟨V(G), V(H), by simpa using hG, by simpa using hH, hV, by simp,
      fun x y hx hy ⟨e, he⟩ ↦ ?_⟩
    rw [union_isLink_iff] at he
    exact he.elim (fun h ↦ hV.notMem_of_mem_left h.right_mem hy) fun ⟨h, _⟩ ↦
      hV.notMem_of_mem_right h.left_mem hx
  exact (not_connected_iff_nonempty_separation.2 ⟨s⟩).2

lemma preconnected_union_iff_of_disjoint (hV : Disjoint V(G) V(H)) :
    (G ∪ H).Preconnected ↔ (G = ⊥ ∧ H.Preconnected) ∨ (G.Preconnected ∧ H = ⊥) := by
  simp [preconnected_iff, connected_union_iff_of_disjoint hV, union_eq_bot]
  tauto

lemma Connected.exists_inc_notMem_of_lt (hG : G.Connected) (hlt : H < G) (hne : V(H).Nonempty) :
    ∃ e x, G.Inc e x ∧ e ∉ E(H) ∧ x ∈ V(H) := by
  refine by_contra fun hcon ↦ hlt.ne <| hG.eq_of_isClosedSubgraph
    (IsClosedSubgraph.mk' hlt.le (fun e x hex hx ↦ ?_)) hne
  simp only [not_exists, not_and, not_imp_not] at hcon
  exact hcon _ _ hex hx

@[simp]
lemma connected_bouquet (v : α) (F : Set β) : (bouquet v F).Connected := by
  suffices aux : (bouquet v (∅ : Set β)).Connected from
    aux.of_isSpanningSubgraph <| IsSpanningSubgraph.banana_mono (empty_subset F)
  rw [connected_iff_forall_closed_ge (by simp)]
  refine fun H hle hne ↦ ⟨?_, by simp⟩
  simp only [vertexSet_bouquet, singleton_subset_iff]
  obtain ⟨x, hx⟩ := hne
  obtain rfl := by simpa only [vertexSet_bouquet, mem_singleton_iff] using vertexSet_mono hle.le hx
  exact hx

@[simp]
lemma connected_banana (x y : α) (hF : F.Nonempty) : (banana x y F).Connected := by
  simp only [vertexSet_banana, insert_nonempty, connected_iff_forall_closed_ge]
  refine fun H hle hne ↦ ?_
  have hmem : ∀ z ∈ V(H), z = x ∨ z = y := by simpa [subset_pair_iff] using vertexSet_mono hle.le
  wlog hx : x ∈ V(H) generalizing x y with aux
  · rw [banana_comm]
    refine aux y x (by rwa [banana_comm]) (fun z hz ↦ (hmem z hz).symm) ?_
    obtain ⟨z, hz⟩ := hne
    obtain rfl | rfl := hmem _ hz
    · contradiction
    assumption
  have hl (e) (he : e ∈ F) : H.IsLink e x y := (hle.isLink_congr hx).mpr (by simpa)
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
  rw [vertexSet_singleEdge]
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
  exact hv.mono hle

lemma IsCompOf.of_deleteVerts (hH : H.IsCompOf G) (hS : Disjoint V(H) S) : H.IsCompOf (G - S) := by
  refine ⟨⟨hH.isClosedSubgraph.deleteVerts_of_disjoint hS, hH.1.2⟩, ?_⟩
  rintro K ⟨hKcS, ⟨v, hvK⟩⟩ hKH
  obtain rfl := hH.eq_walkable_of_mem_walkable (vertexSet_mono hKH hvK)
  have hKG := hKcS.isInducedSubgraph.trans <| G.deleteVerts_isInducedSubgraph _
  apply hKG.le_of_le_subset hH.le
  rintro u ⟨w, hw, rfl, rfl⟩
  have hwW : (G.walkable w.first).IsWalk w :=
    hw.isWalk_isClosedSubgraph_of_first_mem G.walkable_isClosedSubgraph (by simp [hw.first_mem])
  have hwS : (G - S).IsWalk w := by
    simp only [isWalk_deleteVerts_iff, hw, true_and]
    exact hS.mono_left hwW.vertexSet_subset
  exact hwS.isWalk_isClosedSubgraph_of_first_mem hKcS hvK |>.last_mem

lemma IsClosedSubgraph.vertexDelete_components_eq (hH : H ≤c G) :
    (G - V(H)).Components = G.Components \ H.Components := by
  ext C
  simp only [mem_components_iff_isCompOf, mem_sdiff]
  refine ⟨fun hC ↦ ⟨hC.of_isClosedSubgraph hH.compl, fun bad ↦ ?_⟩,
    fun hC ↦ (hH.isCompOf_of_isCompOf_compl hC.1).elim (hC.2 · |>.elim) id⟩
  have solver := ((le_deleteVerts_iff.mp hC.le).2.eq_bot_of_le bad.subset) ▸ hC.nonempty
  simp at solver

lemma IsClosedSubgraph.vertexDelete_components_encard_eq (hH : H ≤c G) :
    (G - V(H)).Components.encard + H.Components.encard = G.Components.encard := by
  rw [hH.vertexDelete_components_eq, encard_sdiff_add_encard,
    union_eq_left.mpr hH.components_subset_components]

lemma IsCompOf.vertexDelete_components_eq (hH : H.IsCompOf G) :
    (G - V(H)).Components = G.Components \ {H} := by
  rw [hH.isClosedSubgraph.vertexDelete_components_eq]
  suffices H.Components = {H} by rw [this]
  exact hH.connected.components_eq_singleton_self

lemma IsCompOf.vertexDelete_components_encard_eq (hH : H.IsCompOf G) :
    (G - V(H)).Components.encard + 1 = G.Components.encard := by
  rw [← encard_singleton H, ← hH.connected.components_eq_singleton_self]
  exact hH.isClosedSubgraph.vertexDelete_components_encard_eq

lemma IsCompOf.isSepSet_of_three_le_components_encard
    (hH : H.IsCompOf G) (hG : 3 ≤ G.Components.encard) : G.IsSep V(H) := by
  refine ⟨hH.subset, not_connected_of_nontrivial_components ?_⟩
  rw [← two_le_encard_iff_nontrivial]
  suffices h : 3 ≤ 1 + (G - V(H)).Components.encard from
    ENat.one_add_le_one_add_iff.mp h
  rwa [add_comm, hH.vertexDelete_components_encard_eq]

lemma IsCompOf.isSepSet_of_not_connected_of_ssubset
    (hH : H.IsCompOf G) (hG : ¬ G.Connected) (hssub : S ⊂ V(H)) : G.IsSep S := by
  refine ⟨hssub.le.trans hH.subset, ?_⟩
  obtain ⟨hSH, x, hxH, hxnS⟩ := ssubset_iff_exists.mp hssub
  have hxHS : x ∈ V(H - S) := by
    simp only [deleteVerts_vertexSet, mem_sdiff]
    exact ⟨hxH, hxnS⟩
  obtain ⟨Cx, hCx_ge, hCx_isCompOf⟩ := (walkable_connected hxHS).exists_isCompOf_ge <|
    walkable_isClosedSubgraph.le.trans <| deleteVerts_mono_left hH.le _
  obtain ⟨K, K_isCompOf_G, hne⟩ :=
    (components_nontrivial_of_not_connected (hH.nonempty.mono hH.subset) hG).exists_ne H
  have K_isCompOf_GS : K.IsCompOf (G - S) :=
    K_isCompOf_G.of_deleteVerts <| by
      contrapose! hne
      obtain ⟨y, hyK, hyS⟩ := Set.not_disjoint_iff.mp hne
      exact K_isCompOf_G.eq_of_mem_mem hH hyK (hSH hyS)
  refine not_connected_of_nontrivial_components ⟨K, K_isCompOf_GS, Cx, hCx_isCompOf, ?_⟩
  contrapose hne
  exact K_isCompOf_G.eq_of_mem_mem hH
    (hne ▸ vertexSet_mono hCx_ge <| mem_walkable_self_iff.mpr hxHS) hxHS.1

lemma exists_isSepSet_with_encard_lt_components_encard (hG : 3 ≤ V(G).encard)
    (hConn : ¬ G.Connected) {n} (hn : n + 2 ≤ V(G).encard) : ∃ S, G.IsSep S ∧ S.encard = n := by
  have hNeBot : V(G).Nonempty := by
    rw [← encard_pos]
    suffices aux : (0 : ℕ∞) < 3 from aux.trans_le hG
    eomega
  obtain ⟨H, hH⟩ := exists_isCompOf hNeBot
  obtain ⟨K, hK, hHK⟩ := (components_nontrivial_of_not_connected hNeBot hConn).exists_ne H
  obtain ⟨x, hx⟩ := hH.nonempty
  obtain ⟨y, hy⟩ := hK.nonempty
  have hxV : x ∈ V(G) := hH.subset hx
  have hyV : y ∈ V(G) := hK.subset hy
  have hxy : x ≠ y := by
    rintro rfl
    exact hHK (hH.eq_of_mem_mem hK hx hy).symm
  have hn' : n ≤ (V(G) \ {x, y}).encard := by
    have hcard : (V(G) \ {x, y}).encard + 2 = V(G).encard := by
      rw [← encard_pair hxy, encard_sdiff_add_encard_of_subset (pair_subset_iff.mpr ⟨hxV, hyV⟩)]
    rwa [← hcard, ENat.add_le_add_iff_right (by decide)] at hn
  obtain ⟨S, hSsub, hSenc⟩ := (V(G) \ {x, y}).exists_subset_encard_eq hn'
  refine ⟨S, ⟨hSsub.trans sdiff_subset, fun hconn ↦ ?_⟩, hSenc⟩
  have hx_not_S : x ∉ S := fun h ↦ (hSsub h).2 (Or.inl rfl)
  have hy_not_S : y ∉ S := fun h ↦ (hSsub h).2 (Or.inr rfl)
  have hxS : x ∈ V(G - S) := by simp [hxV, hx_not_S]
  have hyS : y ∈ V(G - S) := by simp [hyV, hy_not_S]
  have hwalk : y ∈ V(G.walkable x) := (hconn.connBetween hxS hyS).mono deleteVerts_le
  refine hHK ?_
  exact (hK.eq_of_mem_mem (walkable_isCompOf hxV) hy hwalk).trans
    (hH.eq_of_mem_mem (walkable_isCompOf hxV) hx (mem_walkable_self_iff.mpr hxV)).symm

lemma exists_isSepSet_size_one_of_not_connected (hG : 3 ≤ V(G).encard) (h : ¬ G.Connected) :
    ∃ S, G.IsSep S ∧ S.encard = 1 :=
  exists_isSepSet_with_encard_lt_components_encard hG h (show (1 : ℕ∞) + 2 ≤ _ from hG)

lemma singleVertex_connected (hG : V(G) = {x}) : G.Connected := by
  simp [connected_iff, hG, preconnected_of_vertexSet_subsingleton]

lemma exists_of_not_connected (h : ¬ G.Connected) (hne : V(G).Nonempty) :
    ∃ X ⊂ V(G), X.Nonempty ∧ ∀ ⦃u v⦄, u ∈ X → G.Adj u v → v ∈ X := by
  simp only [connected_iff, hne, Preconnected, true_and, not_forall, exists_prop,
    exists_and_left] at h
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  refine ⟨{z | G.ConnBetween x z}, ?_, ⟨x, by simpa⟩,
    fun u v (h : G.ConnBetween x u) huv ↦ h.trans huv.connBetween⟩
  exact LE.le.ssubset_of_mem_notMem (fun z hz ↦ hz.right_mem) hy (by simpa)

lemma connected_iff_forall_exists_adj (hne : V(G).Nonempty) :
    G.Connected ↔ ∀ X ⊂ V(G), X.Nonempty → ∃ x ∈ X, ∃ y ∈ V(G) \ X, G.Adj x y := by
  refine ⟨fun h X hXV hXnem ↦ ?_, fun h ↦ by_contra fun hnc ↦ ?_⟩
  · by_contra! hnadj
    have hGXcl : G[X] ≤c G := IsClosedSubgraph.mk' (induce_le hXV.subset) fun e x ⟨y, hexy⟩ hxX =>
      ⟨x, y, hexy, hxX, by_contra fun hyX => hnadj x hxX y ⟨hexy.right_mem, hyX⟩ ⟨e, hexy⟩⟩
    rw [← le_antisymm hGXcl.le <| h.2 ⟨hGXcl, by simpa⟩ hGXcl.le, vertexSet_induce] at hXV
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

lemma _root_.WList.WellFormed.toGraph_deleteVerts_singleton_connBetween_first_or_last
    [DecidableEq α] (hQ : Q.WellFormed) (hQnd : Q.vertex.count x ≤ 1) (hv : v ∈ Q) (hne : v ≠ x) :
    (Q.toGraph - ({x} : Set α)).ConnBetween v Q.first ∨
    (Q.toGraph - ({x} : Set α)).ConnBetween v Q.last := by
  obtain h0 | h1 := Nat.le_one_iff_eq_zero_or_eq_one.mp hQnd
  · rw [List.count_eq_zero, mem_vertex] at h0
    rw [Q.toGraph.deleteVerts_eq_self_iff {x} |>.mpr (by grind)]
    exact Or.inl <| hQ.toGraph_connected.connBetween (by grind) (by grind)
  have hx : x ∈ Q := List.one_le_count_iff.mp h1.ge
  have hQwalk := hQ.isWalk_toGraph
  have hPre := hQwalk.prefix (Q.prefixUntilVertex_isPrefix x)
  have hSuf := hQwalk.suffix (Q.suffixFromVertex_isSuffix x)
  have hvsplit : v ∈ Q.prefixUntilVertex x ∨ v ∈ Q.suffixFromVertex x := by
    rw [← prefixUntilVertex_append_suffixFromVertex Q x] at hv
    exact mem_of_mem_append hv
  refine hvsplit.imp (fun hvPre ↦ ?_) (fun hvSuf ↦ ?_)
  · have hPre_ne : (Q.prefixUntilVertex x).Nonempty :=
      (Q.prefixUntilVertex x).nil_or_nonempty.resolve_left fun hnil ↦ hne <|
        nil_last.symm.trans <| hnil.eq_nil_of_mem hvPre ▸ prefixUntilVertex_last hx
    have hx_not : x ∉ (Q.prefixUntilVertex x).dropLast := by
      refine fun hxdl ↦ (Q.prefixUntil_vertex_dropLast_not_prop (P := (· = x)) ?_ rfl)
      simpa [prefixUntilVertex] using (show x ∈ (Q.prefixUntilVertex x).vertex.dropLast by
        rwa [← hPre_ne.vertex_dropLast, mem_vertex])
    refine isWalk_deleteVerts_iff.mpr ⟨hPre.dropLast, disjoint_singleton_right.mpr hx_not⟩
      |>.connBetween_of_mem_of_mem ?_ ?_
    · refine (mem_iff_eq_mem_dropLast_or_eq_last.mp hvPre).resolve_right ?_
      rwa [prefixUntilVertex_last hx]
    simpa using (Q.prefixUntilVertex x).dropLast.first_mem
  have hSuf_ne : (Q.suffixFromVertex x).Nonempty :=
    (Q.suffixFromVertex x).nil_or_nonempty.resolve_left fun hnil ↦ hne
      <| nil_first.symm.trans <| hnil.eq_nil_of_mem hvSuf ▸ suffixFromVertex_first hx
  have hsuf0 : x ∉ (Q.suffixFromVertex x).tail := by
    rw [← mem_vertex, hSuf_ne.vertex_tail, ← List.count_eq_zero, suffixFromVertex]
    have ht := Q.prefixUntil_vertex_append_suffixFrom_tail_vertex (· = x) ▸ hQnd
    rw [List.count_append] at ht
    have hpre1 := List.one_le_count_iff.mpr (show _ ∈ Q.prefixUntilVertex x from WList.last_mem)
    rw [Q.prefixUntilVertex_last hx, prefixUntilVertex] at hpre1
    omega
  refine isWalk_deleteVerts_iff.mpr ⟨hSuf.tail, disjoint_singleton_right.2 hsuf0⟩
    |>.connBetween_of_mem_of_mem ?_ ?_
  · refine (mem_iff_eq_first_or_mem_tail.mp hvSuf).resolve_left ?_
    rwa [suffixFromVertex_first hx]
  simpa using (Q.suffixFromVertex x).tail.last_mem

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
      have hconn := (h.of_le_of_mem deleteEdges_le hmem).connBetween
      exact ⟨x', hx', hconn.trans hWx'⟩
    rw [edgeSet_deleteEdges, mem_sdiff, and_iff_right h.edge_mem, h.mem_induce_iff, not_not] at hmem
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
  rw [edgeSet_deleteEdges, mem_sdiff, mem_union, hxy'.mem_induce_iff,
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

lemma deleteEdges_connected_iff_of_forall_isLoopAt (hF : ∀ e ∈ F, ∃ x, G.IsLoopAt e x) :
    (G ＼ F).Connected ↔ G.Connected := by
  refine ⟨fun h ↦ h.of_isSpanningSubgraph <| G.deleteEdges_isSpanningSubgraph, fun h ↦ ?_⟩
  rw [← loopRemove_connected_iff, loopRemove] at h
  rw [← restrict_edgeSet_sdiff_eq_deleteEdges]
  refine h.of_isSpanningSubgraph ?_
  apply restrict_isSpanningSubgraph_restrict
  intro e ⟨he, hel⟩
  have : (∀ (x : α), ¬G.IsLoopAt e x) → e ∉ F := by simpa only [not_exists] using mt (hF e)
  use he, he, this hel

lemma deleteEdges_isLoopAt_isSep_iff (C) : (G ＼ E(G, u, u)).IsSep C ↔ G.IsSep C := by
  refine ⟨fun h ↦ ⟨h.subset_vx, fun hc ↦ ?_⟩, fun h ↦ ⟨h.subset_vx, fun hc ↦ ?_⟩⟩
  swap
  · rw [deleteEdges_deleteVerts] at hc
    exact h.not_connected <| hc.of_isSpanningSubgraph <| deleteEdges_isSpanningSubgraph ..
  have := h.not_connected
  by_cases huC : u ∈ C
  · rw [deleteEdges_deleteVerts, deleteEdges_eq_of_disjoint] at this
    exact this hc
    rw [deleteVerts_edgeSet_diff]
    exact disjoint_sdiff_left.mono_right
    <| G.linkEdges_subset_incEdges_left u u |>.trans <| G.incEdge_subset_setIncEdges huC
  rw [deleteEdges_deleteVerts, deleteEdges_connected_iff_of_forall_isLoopAt] at this
  exact this hc
  intro e he
  use u, by simpa
  simp [he.left_mem, huC]

lemma Preconnected.deleteEdges_linkEdges_connBetween_or (hG : G.Preconnected) (hx : x ∈ V(G))
    (hu : u ∈ V(G)) (hv : v ∈ V(G)) :
    (G ＼ E(G, u, v)).ConnBetween x u ∨ (G ＼ E(G, u, v)).ConnBetween x v := by
  obtain ⟨w, (rfl | rfl), hw⟩ := hG.exists_connBetween_deleteEdge_set (X := {u, v})
    ⟨u, by simp, hu⟩ hx
  <;> replace hw := hw.mono <| G.deleteEdges_anti_right <| G.induce_pair_edgeSet _ _ <;> tauto

lemma Preconnected.deleteEdges_linkEdges_not_connBetween (hG : G.Preconnected)
    (h' : ¬ (G ＼ E(G, u, v)).Preconnected) : ¬ (G ＼ E(G, u, v)).ConnBetween u v := by
  contrapose! h'
  apply preconnected_of_exists_connBetween
  use u
  intro x hx
  simp only [vertexSet_deleteEdges] at hx
  obtain hw | hw := hG.deleteEdges_linkEdges_connBetween_or hx h'.left_mem h'.right_mem
  · exact hw.symm
  exact .trans h' hw.symm

lemma Preconnected.deleteEdges_linkEdges_components (hG : G.Preconnected) (hu : u ∈ V(G))
    (hv : v ∈ V(G)) :
    (G ＼ E(G, u, v)).Components = {(G ＼ E(G, u, v)).walkable u, (G ＼ E(G, u, v)).walkable v} := by
  rw [components_eq_walkable_image]
  ext H
  simp only [vertexSet_deleteEdges, mem_image, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply (hG.deleteEdges_linkEdges_connBetween_or hx hu hv).imp <;> intro h <;> grw [h]
  · rintro (rfl | rfl)
    · use u
    · use v

lemma Preconnected.walkable_singleton_left_of_deleteVerts_connected (hG : G.Preconnected)
    (h : ¬ (G ＼ E(G, u, v)).Connected) (huconn : (G - {u}).Connected) :
    V((G ＼ E(G, u, v)).walkable u) = {u} := by
  rw [connected_iff, not_and_or, vertexSet_deleteEdges, vertexSet_not_nonempty_iff] at h
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
    exact h <| hG.isSpanningSubgraph <| G.loopRemove_isSpanningSubgraph_deleteEdges_isLoopAt u
  refine subset_antisymm ?_ (by simpa)
  have := (G ＼ E(G, u, v)).walkable_isClosedSubgraph (u := u) |>.deleteVerts {u}
  rw [deleteEdges_deleteVerts, (G - {u}).deleteEdges_eq ?_] at this
  have := mt (huconn.eq_of_isClosedSubgraph this) ?_
  simpa [vertexSet_deleteVerts, not_nonempty_iff_eq_empty, sdiff_eq_empty] using this
  · apply_fun vertexSet
    intro heq
    have : v ∈ V(G - {u}) := by simp [hne.symm, hv]
    rw [← heq] at this
    simp only [vertexSet_deleteVerts, mem_sdiff,
      ← connBetween_iff_mem_walkable_of_mem, mem_singleton_iff, hne.symm, not_false_eq_true,
      and_true] at this
    exact hG.deleteEdges_linkEdges_not_connBetween h this
  · rw [disjoint_iff_forall_notMem, deleteVerts_edgeSet_diff, setIncEdges_singleton]
    intro e ⟨he, heu⟩
    contrapose! heu
    exact G.linkEdges_subset_incEdges_left u v heu

lemma Preconnected.walkable_singleton_right_of_deleteVerts_connected (hG : G.Preconnected)
    (h : ¬ (G ＼ E(G, u, v)).Connected) (hvconn : (G - {v}).Connected) :
    V((G ＼ E(G, u, v)).walkable v) = {v} := by
  rw [linkEdges_comm] at h ⊢
  exact hG.walkable_singleton_left_of_deleteVerts_connected h hvconn

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
  simp only [vertexSet_deleteEdges, (hG.pre.deleteEdges_linkEdges_components hu hv),
    vertexSet_sUnion, mem_insert_iff, mem_singleton_iff, iUnion_iUnion_eq_or_left,
    iUnion_iUnion_eq_left] at hcomp
  rw [hcomp, hG.pre.walkable_singleton_left_of_deleteVerts_connected h husep,
    hG.pre.walkable_singleton_right_of_deleteVerts_connected h hvsep, pair_comm]
  simp

lemma not_preconnected_or_singleton_isSep_or_pair (h : ¬ (G ＼ E(G, u, v)).Preconnected) :
    ¬ G.Preconnected ∨ G.IsSep {u} ∨ G.IsSep {v} ∨ V(G) = {u, v} := by
  refine not_connected_or_singleton_isSep_or_pair (mt Connected.pre h) |>.imp (mt ?_) id
  simp_all only [preconnected_iff, ← vertexSet_not_nonempty_iff, vertexSet_deleteEdges, not_or,
    not_not, not_true_eq_false, false_or, implies_true]

lemma IsSep.of_deleteEdges_linkEdges (h : (G ＼ E(G, u, v)).IsSep S) :
    G.IsSep S ∨ G.IsSep (insert u S) ∨ G.IsSep (insert v S) ∨ V(G) = {u, v} ∪ S := by
  obtain huS | huS := em (u ∈ S)
  · refine Or.inl ⟨by simpa using h.subset_vx, ?_⟩
    have := h.not_connected
    rwa [deleteEdges_deleteVerts, deleteEdges_eq_of_disjoint] at this
    apply Disjoint.mono_right <| (G.linkEdges_subset_incEdges_left u v).trans
    <| G.incEdge_subset_setIncEdges huS
    rw [deleteVerts_edgeSet_diff]
    exact disjoint_sdiff_left
  obtain hvS | hvS := em (v ∈ S)
  · refine Or.inl ⟨by simpa using h.subset_vx, ?_⟩
    have := h.not_connected
    rwa [deleteEdges_deleteVerts, deleteEdges_eq_of_disjoint] at this
    apply Disjoint.mono_right <| (G.linkEdges_subset_incEdges_right u v).trans
    <| G.incEdge_subset_setIncEdges hvS
    rw [deleteVerts_edgeSet_diff]
    exact disjoint_sdiff_left

  have : ¬((G - S) ＼ E(G - S, u, v)).Connected := by
    have := h.not_connected
    rw [deleteEdges_deleteVerts] at this
    exact mt (Connected.of_isSpanningSubgraph ·
    <| (G - S).deleteEdges_isSpanningSubgraph_anti_right <| by grind) this
  obtain hnconn | hsepu | hsepv | hpair := (G - S).not_connected_or_singleton_isSep_or_pair
    this
  · exact Or.inl ⟨by simpa using h.subset_vx, hnconn⟩
  · refine Or.inr (Or.inl ⟨?_, ?_⟩)
    · have : u ∈ V(G) ∧ u ∉ S := by simpa using hsepu.subset_vx
      simpa [insert_subset_iff, this] using h.subset_vx
    · rw [← union_singleton, ← deleteVerts_deleteVerts]
      exact hsepu.not_connected
  · refine Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩))
    · have : v ∈ V(G) ∧ v ∉ S := by simpa using hsepv.subset_vx
      simpa [insert_subset_iff, this] using h.subset_vx
    · rw [← union_singleton, ← deleteVerts_deleteVerts]
      exact hsepv.not_connected
  · refine Or.inr (Or.inr (Or.inr ?_))
    simp only [vertexSet_deleteVerts] at hpair
    rw [← hpair, sdiff_union_self, eq_comm, union_eq_left]
    simpa using h.subset_vx

lemma ConnGE.deleteEdges_linkEdges (h : G.ConnGE (n + 1)) (u v : α) :
    (G ＼ E(G, u, v)).ConnGE n where
  le_cut C hC := by
    by_contra! hcd
    obtain h1 | h2 | h3 | h4 := hC.of_deleteEdges_linkEdges
    · simpa using ENat.natCast_lt_natCast.1 <| hcd.trans_le' (h.le_cut h1)
    · simpa [hcd.not_ge] using h.le_cut h2 |>.trans <| encard_insert_le ..
    · simpa [hcd.not_ge] using h.le_cut h3 |>.trans <| encard_insert_le ..
    obtain h | hss := h.le_card.symm
    · grw [h4, insert_union, singleton_union, encard_insert_le, encard_insert_le] at h
      enat_to_nat!
      omega
    obtain hne | rfl := eq_or_ne u v |>.symm
    · apply hss.not_nontrivial
      use u, (by simp [h4]), v, (by simp [h4])
    rw [deleteEdges_isLoopAt_isSep_iff] at hC
    have := h.le_cut ⟨hC.subset_vx, hC.not_connected⟩
    enat_to_nat!
    omega
  le_card := by
    simp only [vertexSet_deleteEdges]
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
    exact lt_of_le_of_lt (incVertexSet_encard_le G E(G))
    <| WithTop.mul_lt_top (compareOfLessAndEq_eq_lt.mp rfl) (encard_lt_top_iff.mpr G.edgeSet_finite)

lemma Connected.finite [G.EdgeFinite] (h : G.Connected) : G.Finite := h.pre.finite

/-- If `G` is connected but its restriction to some set `F` of edges is not,
then there is an edge of `G` joining two vertices that are not connected in the restriction. -/
lemma Connected.exists_of_restrict_not_connected (hG : G.Connected)
    (hF : ¬ (G.restrict F).Connected) :
    ∃ (S : (G.restrict F).Separation) (e : β) (x : α) (y : α),
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

lemma IsSep.exists_adj_of_isCompOf_deleteVerts (hM : IsSep G S) (hG : G.Connected)
    (hH : H.IsCompOf (G - S)) : ∃ x ∈ S, ∃ y ∈ V(H), G.Adj x y := by
  by_contra! hno
  have hHcl' : H ≤c G - S := hH.1.1
  have hHcl : H ≤c G := by
    refine IsClosedSubgraph.mk' (hHcl'.le.trans deleteVerts_le)
      fun e x ⟨y, hxy⟩ hxH ↦ hHcl'.closed ?_ hxH
    refine ((G.deleteVerts_isLink_iff S).2 ⟨hxy, ?_, ?_⟩).inc_left
    · simpa using (vertexSet_mono hHcl'.le hxH).2
    exact (hno y · x hxH <| by simpa [adj_comm] using hxy.adj)
  obtain rfl : H = G := hG.eq_of_isClosedSubgraph hHcl hH.1.2
  obtain ⟨x, hxS⟩ := hM.nonempty_of_connected hG
  have : ∀ ⦃x : α⦄, x ∈ V(H) → x ∉ S := by simpa [disjoint_iff_forall_notMem] using hHcl'.le
  exact this (hM.subset_vx hxS) hxS

/-- Every vertex in a mininum cardinality separator has an edge to components of the vertex-deleted
graph. This lemma requires the separator to be finite because `IsMinSep` uses `encard` for
cardinality comparison and cannot tell the size difference of infinite sets. -/
lemma IsMinSep.exists_adj_of_isCompOf_deleteVerts (hM : IsMinSep G S) (hH : H.IsCompOf (G - S))
    (hx : x ∈ S) (hfin : S.Finite) : ∃ y ∈ V(H), G.Adj x y := by
  by_contra! hno
  have hHcl : H ≤c G - S := hH.1.1
  refine hM.not_isSep_of_encard_lt (hfin.sdiff.encard_lt_encard (by simpa : S \ {x} ⊂ _)) ?_
  refine ⟨sdiff_subset.trans hM.subset_vx, fun hcon ↦ ?_⟩
  have hHclS' : H ≤c (G - (S \ {x})) := by
    refine IsClosedSubgraph.mk' (hHcl.le'.trans (by grw [sdiff_subset]))
      fun e u ⟨v, huv⟩ huH ↦ hHcl.closed ⟨v, ?_⟩ huH
    simp only [deleteVerts_isLink_iff, huv.of_le deleteVerts_le, vertexSet_mono hHcl.le huH |>.2,
      not_false_eq_true, true_and]
    obtain rfl | hvne := eq_or_ne v x
    · exact hno u huH (huv.symm.of_le deleteVerts_le).adj |>.elim
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
    exact two_le_encard_iff_nontrivial.mp <| (by simpa : (2 : ℕ∞) ≤ k).trans hle
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
  obtain hxy' | hxy' := isLink_or_isLink_of_union <| h.isLink_mono hxy
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
  · exact aux (union_eq_union_deleteEdges .. ▸ hP) (hi.anti (by simp))
      (Compatible.of_disjoint_edgeSet disjoint_sdiff_right)
  induction P with
  | nil u => simpa [hf]
  | cons u e w ih =>
    obtain ⟨heuwf, hw, huw⟩ := cons_isPath_iff.mp hP
    obtain heG | heH := by simpa only [edgeSet_union, mem_union] using heuwf.edge_mem
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
  all_goals rwa [← mem_vertexSet_iff, ← toGraph_vertexSet, hP_eq, vertexSet_deleteEdges,
    toGraph_vertexSet, mem_vertexSet_iff]

/-- If two graphs intersect in at most one vertex,
then any cycle of their union is a cycle of one of the graphs. -/
lemma IsCyclicWalk.isCyclicWalk_or_isCyclicWalk_of_union_of_subsingleton_inter
    (hC : (G ∪ H).IsCyclicWalk C) (hi : (V(G) ∩ V(H)).Subsingleton) :
    G.IsCyclicWalk C ∨ H.IsCyclicWalk C := by
  wlog hc : Compatible G H generalizing H with aux
  · obtain (hG | hH) := aux (union_eq_union_deleteEdges .. ▸ hC) (hi.anti (by simp))
      (Compatible.of_disjoint_edgeSet disjoint_sdiff_right)
    · exact .inl hG
    exact .inr <| hH.of_le <| by simp
  obtain ⟨u, e, w⟩ := hC.nonempty
  wlog heG : e ∈ E(G) generalizing G H with aux
  · obtain heH := by simpa only using hC.isWalk.edge_mem_of_mem (by simp) |>.resolve_left heG
    rw [inter_comm] at hi
    rw [hc.union_comm] at hC
    exact aux hi hc.symm hC heH |>.symm
  left
  obtain rfl := by simpa only [cons_isClosed_iff] using hC.isClosed
  have he := cons_isWalk_iff.mp hC.isWalk |>.1
  have hw := by simpa only [tail_cons] using hC.tail_isPath
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
  exact heH <| (hK.inc_congr hxH).mpr (hex.of_le hHG.le) |>.edge_mem

lemma IsClosedSubgraph.isCompOf_of_connected (h : H ≤c G) (hH : H.Connected) :
    H.IsCompOf G := by
  refine IsCompOf_iff_isClosedSubgraph_connected.2 ⟨h, hH⟩

lemma Connected.isCompOf_of_isClosedSubgraph (hH : H.Connected) (h : H ≤c G) :
    H.IsCompOf G := by
  refine IsCompOf_iff_isClosedSubgraph_connected.2 ⟨h, hH⟩

/-- For a proper component `H`, the separation with parts `V(H)` and `V(G) \ V(H)`. -/
@[simps (attr := grind =)]
def IsCompOf.separation_of_ne (h : H.IsCompOf G) (hne : H ≠ G) : G.Separation where
  left := V(H)
  right := V(G) \ V(H)
  nonempty_left := h.connected.nonempty
  nonempty_right := sdiff_nonempty.2 fun hss ↦ hne <| h.isInducedSubgraph.eq_of_isSpanningSubgraph
    <| IsSpanningSubgraph.mk' (hss.antisymm' h.le.vertexSet_mono) h.le.isLink_mono
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
  simp only [vertexSet_sUnion, mem_iUnion, exists_prop] at hv
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
  simp only [vertexSet_sUnion, mem_iUnion, exists_prop, forall_exists_index, and_imp]
  intro v H hH hvH
  rw [← G.eq_sUnion_components, ← hH.isClosedSubgraph.eDegree_eq hvH]
  exact h H hH v

section NoEdge

variable {X Y : Set α}

@[simp]
lemma noEdge_isComplete_iff : (Graph.noEdge X β).IsComplete ↔ X.Subsingleton := by
  refine ⟨fun h x hx y hy => ?_, fun h x hx y hy hne => (hne <| h hx hy).elim⟩
  by_contra! hne
  obtain ⟨e, he⟩ := h x hx y hy hne
  simpa using he.edge_mem

@[simp]
lemma IsWalk.nil_of_noEdge (h : (Graph.noEdge X β).IsWalk W) : W.Nil := by
  match W with
  | .nil u => simp
  | .cons u e w => simp at h

@[simp]
lemma connBetween_noEdge_iff : (Graph.noEdge X β).ConnBetween x y ↔ x = y ∧ x ∈ X := by
  refine ⟨?_, ?_⟩
  · rintro ⟨w, hw, rfl, rfl⟩
    match hw.nil_of_noEdge with | .nil x => simp_all
  rintro ⟨rfl, hx⟩
  simpa

@[simp]
lemma noEdge_preconnected_iff : (Graph.noEdge X β).Preconnected ↔ X.Subsingleton := by
  refine ⟨fun h => ?_, fun h x y hx hy => ?_⟩
  · by_contra! ht
    obtain ⟨x, hx, y, hy, hne⟩ := ht
    simpa [hne] using h x y hx hy
  simp only [vertexSet_noEdge] at hx hy
  obtain rfl := h hx hy
  simpa

@[simp]
lemma noEdge_connected_iff : (Graph.noEdge X β).Connected ↔ ∃ v, X = {v} := by
  rw [connected_iff, noEdge_preconnected_iff, vertexSet_noEdge]
  simp only [exists_eq_singleton_iff_nonempty_subsingleton]

@[simp]
lemma IsSepBetween.ne_of_noEdge (h : (Graph.noEdge X β).IsSepBetween x y Y) (hx : x ∈ X) :
    x ≠ y := by
  rintro rfl
  simpa [hx, h.left_not_mem] using h.not_connBetween

lemma isSepBetween_noEdge_of_ne (hne : x ≠ y) (hY : Y ⊆ X \ {x, y}) :
    (Graph.noEdge X β).IsSepBetween x y Y where
  subset := subset_sdiff.mp hY |>.1
  left_not_mem := (disjoint_iff_forall_notMem ..).mp (subset_sdiff.mp hY).2.symm (by simp)
  right_not_mem := (disjoint_iff_forall_notMem ..).mp (subset_sdiff.mp hY).2.symm (by simp)
  not_connBetween := by
    rintro ⟨W, hW, rfl, rfl⟩
    rw [isWalk_deleteVerts_iff] at hW
    exact hne hW.1.nil_of_noEdge.first_eq_last

@[simp]
lemma isEdgeSep_noEdge_iff : (Graph.noEdge X β).IsEdgeSep F ↔ F = ∅ ∧ X.encard ≠ 1 := by
  refine ⟨fun ⟨hF, h⟩ => ?_, ?_⟩
  · obtain rfl : F = ∅ := by simpa using hF
    simpa [encard_eq_one] using h
  rintro ⟨rfl, hne⟩
  simpa [encard_eq_one] using hne

@[simp]
lemma isEdgeSep_bot_iff : (⊥ : Graph α β).IsEdgeSep F ↔ F = ∅ := by
  rw [← noEdge_empty, isEdgeSep_noEdge_iff]
  simp

@[simp]
lemma noEdge_connBetweenGE_iff (n : ℕ) : (Graph.noEdge X β).ConnBetweenGE x y n ↔
    n = 0 ∨ (x = y ∧ x ∈ X) := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [or_iff_not_imp_right, not_and']
    rintro hne
    by_cases hxX : x ∈ X
    · simpa using h (isSepBetween_noEdge_of_ne (hne hxX) (empty_subset _))
    simpa [hxX] using h.left_mem
  rintro (rfl | ⟨rfl, hx⟩)
  · simp
  exact connBetweenGE_self hx n

@[simp]
lemma noEdge_preconnGE_iff (n : ℕ) : (Graph.noEdge X β).PreconnGE n ↔ n = 0 ∨ X.Subsingleton := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [or_iff_not_imp_right, not_subsingleton_iff]
    rintro ⟨x, hx, y, hy, hne⟩
    simpa using h hx hy (isSepBetween_noEdge_of_ne hne (empty_subset _))
  rintro (rfl | hss) u v hu hv C hC
  · simp
  obtain rfl := hss hu hv
  exact (hC.ne_of_noEdge hu rfl).elim

@[simp]
lemma noEdge_ConnGE_iff (n : ℕ) : (Graph.noEdge X β).ConnGE n ↔ n = 0 ∨ (n = 1 ∧ ∃ x, X = {x}):= by
  obtain hc | hc := em ((Graph.noEdge X β).IsComplete) |>.symm
  · rw [← preconnGE_iff_connGE_of_not_isComplete (fun _ ↦ hc), noEdge_preconnGE_iff]
    constructor
    · rintro (rfl | hss)
      · tauto
      simp [hss] at hc
    rintro (rfl | ⟨rfl, x, rfl⟩) <;> simp
  rw [hc.connGE_iff]
  rw [noEdge_isComplete_iff] at hc
  simp only [vertexSet_noEdge, hc, true_and]
  obtain (rfl | ⟨x, rfl⟩) := hc.eq_empty_or_singleton
  · simp
  simp only [encard_singleton, singleton_eq_singleton_iff, exists_eq', and_true,
    Nat.cast_le_one, Nat.cast_lt_one]
  lia

end NoEdge
