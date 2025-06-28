import Matroid.Graph.Lattice
import Matroid.Graph.Finite
import Matroid.Graph.Degree.Defs
import Matroid.Graph.Degree.Constructions
import Mathlib.Data.Set.Insert
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Real.Basic

open Set Function Nat WList

variable {α β : Type*} {G H K : Graph α β} {u v x x₁ x₂ y y₁ y₂ z : α} {e e' f g : β}
  {U V S T : Set α} {F F' R R': Set β} {C W P Q : WList α β}

namespace Graph

/-- A graph is connected if it is a minimal closed subgraph of itself -/
protected def Connected (G : Graph α β) : Prop := G.IsCompOf G

lemma Connected.nonempty (hG : G.Connected) : V(G).Nonempty := by
  rw [Graph.Connected, IsCompOf] at hG
  exact hG.prop.2

lemma connected_iff_forall_closed (hG : V(G).Nonempty) :
    G.Connected ↔ ∀ ⦃H⦄, H ≤c G → V(H).Nonempty → H = G := by
  refine ⟨fun h H hHG hHne ↦ ?_, fun h ↦ ⟨by simpa [-vertexSet_nonempty_iff],
    fun H ⟨hle, hH⟩ _ ↦ (h hle hH).symm.le⟩⟩
  rw [Graph.Connected, IsCompOf] at h
  exact h.eq_of_le ⟨hHG, hHne⟩ hHG.le

lemma connected_iff_forall_closed_ge (hG : V(G).Nonempty) :
    G.Connected ↔ ∀ ⦃H⦄, H ≤c G → V(H).Nonempty → G ≤ H := by
  rw [connected_iff_forall_closed hG]
  exact ⟨fun h H hle hne ↦ (h hle hne).symm.le, fun h H hle hne ↦ (h hle hne).antisymm' hle.le⟩

lemma Connected.eq_of_isClosedSubgraph (hG : G.Connected) (hH : H ≤c G) (hne : V(H).Nonempty) :
    H = G := by
  rw [connected_iff_forall_closed (hne.mono (vertexSet_mono hH.le))] at hG
  exact hG hH hne

lemma IsClosedSubgraph.disjoint_or_subset_of_isCompOf (h : H ≤c G) (hK : K.IsCompOf G) :
    K.IsCompOf H ∨ K.Disjoint H := by
  rw [or_iff_not_imp_right, Graph.disjoint_iff_of_le_le hK.le h.le,
    not_disjoint_iff_nonempty_inter, inter_comm]
  intro hne
  have h_eq := hK.eq_of_le ⟨h.inter hK.isClosedSubgraph, by simpa⟩ Graph.inter_le_right
  rw [← h_eq] at hK ⊢
  refine ⟨⟨hK.isClosedSubgraph.of_le_of_le Graph.inter_le_left h.le, by simpa⟩, ?_⟩
  intro P ⟨hPH, hP⟩ hle
  rw [hK.eq_of_le ⟨?_, hP⟩ hle]
  exact (hPH.of_le_of_le hle Graph.inter_le_left).trans hK.isClosedSubgraph

lemma IsCompOf.of_le_le (h : K.IsCompOf G) (hKH : K ≤ H) (hHG : H ≤ G) : K.IsCompOf H := by
  refine ⟨⟨h.isClosedSubgraph.of_le_of_le hKH hHG, h.nonempty⟩, fun K' ⟨hK'H, hK'ne⟩ hK'K ↦ ?_⟩
  exact h.le_of_le ⟨(hK'H.of_le_of_le hK'K hKH).trans h.isClosedSubgraph, hK'ne⟩ hK'K

lemma IsCompOf.connected (h : H.IsCompOf G) : H.Connected :=
  h.of_le_le le_rfl h.le

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
    aux.of_isSpanningSubgraph <| bouquet_mono _ (by simp)
  simp only [bouquet_vertexSet, singleton_nonempty, connected_iff_forall_closed_ge]
  refine fun H hle hne ↦ ⟨?_, by simp⟩
  simp only [bouquet_vertexSet, singleton_subset_iff]
  obtain ⟨x, hx⟩ := hne
  rwa [← show x = v from vertexSet_mono hle.le hx]

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




-- @[simp]
-- lemma connected_noEdge_singleton (v : α) : (Graph.noEdge {v} β).Connected := by
--   refine ⟨by simp, fun H ⟨_, hne⟩ hle ↦ ?_⟩
--   simp at hle




-- lemma Connected.addEdge_connected (hG : G.Connected) (hx : x ∈ V(G)) (he : e ∉ E(G)) (y : α) :
--     (G.addEdge e x y).Connected := by
--   Connected.union hG (by simp [he]) (by simp) hG <|
--     by simp [hx, insert_inter_of_mem hx]

-- lemma union_not_connected_of_disjoint_vertexSet (hV : Disjoint V(G) V(H)) (hG : V(G).Nonempty)
--     (hH : V(H).Nonempty) : ¬ (G ∪ H).Connected := by
--   _
--   intro
  -- obtain ⟨x, hx⟩ := hG
  -- obtain ⟨y, hy⟩ := hH
  -- intro h
  -- obtain ⟨W, hW, rfl, rfl⟩ :=
  --   (h.vertexConnected (x := x) (y := y) (by simp [hx]) (by simp [hy])).exists_isWalk
  -- obtain ⟨u, -, huG, huH⟩ := hW.exists_mem_mem_of_union hx hy
  -- exact hV.notMem_of_mem_left huG huH


  -- have := hG.eq_of_isClosedSubgraph


def VertexConnected (G : Graph α β) (x y : α) : Prop :=
  ∃ H ∈ G.Components, x ∈ V(H.val) ∧ y ∈ V(H.val)

lemma VertexConnected.refl (hx : x ∈ V(G)) : G.VertexConnected x x :=
  ⟨foo G x, foo_mem_components hx, mem_foo hx, mem_foo hx⟩

lemma VertexConnected.symm (h : G.VertexConnected x y) : G.VertexConnected y x := by
  obtain ⟨H, hH, hx, hy⟩ := h
  exact ⟨H, hH, hy, hx⟩

instance : IsSymm _ G.VertexConnected where
  symm _ _ := VertexConnected.symm

lemma VertexConnected_comm : G.VertexConnected x y ↔ G.VertexConnected y x :=
  ⟨VertexConnected.symm, VertexConnected.symm⟩

lemma VertexConnected.left_mem (hxy : G.VertexConnected x y) : x ∈ V(G) :=
  let ⟨H, _, hx, _⟩ := hxy
  vertexSet_mono H.prop.le hx

lemma VertexConnected.right_mem (hxy : G.VertexConnected x y) : y ∈ V(G) :=
  hxy.symm.left_mem

lemma VertexConnected.trans (hxy : G.VertexConnected x y) (hyz : G.VertexConnected y z) :
    G.VertexConnected x z := by
  obtain ⟨H₁, hH₁, hx, hy₁⟩ := hxy
  obtain ⟨H₂, hH₂, hy₂, hz⟩ := hyz
  obtain rfl := H₁.eq_of_mem_component_of_mem_mem hH₁ hH₂ hy₁ hy₂
  exact ⟨H₁, hH₁, hx, hz⟩

instance : IsTrans _ G.VertexConnected where
  trans _ _ _ := VertexConnected.trans

lemma VertexConnected.mem_vertexSet_iff (H : G.ClosedSubgraph) :
    ∀ {x y : α}, G.VertexConnected x y → (x ∈ V(H.val) ↔ y ∈ V(H.val)) := by
  suffices ∀ x y, G.VertexConnected x y → x ∈ V(H.val) → y ∈ V(H.val) by
    exact fun x y h => ⟨fun hx => this x y h hx, fun hy => this y x h.symm hy⟩
  exact fun x y ⟨H', hH', hx', hy'⟩ hx ↦
    vertexSet_mono (H'.le_of_mem_component_of_mem_mem hH' hx' hx) hy'

@[simp]
lemma vertexConnected_self : G.VertexConnected x x ↔ x ∈ V(G) :=
  ⟨VertexConnected.left_mem, VertexConnected.refl⟩

lemma VertexConnected.mem_foo (h : G.VertexConnected x y) : y ∈ V((foo G x).val) :=
  let ⟨H, hH, hx, hy⟩ := h
  vertexSet_mono (H.le_of_mem_component_of_mem_mem hH hx (Graph.mem_foo h.left_mem)) hy

lemma vertexConnected_iff_mem_foo_of_mem (hx : x ∈ V(G)) :
    G.VertexConnected x y ↔ y ∈ V((foo G x).val) :=
  ⟨fun h => h.mem_foo, fun hy ↦ ⟨foo G x, foo_mem_components hx, mem_foo hx, hy⟩⟩

lemma Adj.vertexConnected (h : G.Adj x y) : G.VertexConnected x y :=
  ⟨foo G x, foo_mem_components h.left_mem, Graph.mem_foo h.left_mem, h.mem_foo⟩

lemma IsLink.vertexConnected (h : G.IsLink e x y) : G.VertexConnected x y :=
  h.adj.vertexConnected

lemma IsWalk.vertexConnected_of_mem_of_mem (hW : G.IsWalk W) (hx : x ∈ W) (hy : y ∈ W) :
    G.VertexConnected x y := by
  suffices aux : ∀ ⦃z⦄, z ∈ W → G.VertexConnected z W.last from (aux hx).trans (aux hy).symm
  clear hx hy
  intro z hz
  induction hW generalizing z with
  | nil => simp_all
  | cons hW h ih =>
    obtain rfl | hz := by simpa using hz
    · exact h.vertexConnected.trans <| by simpa only [last_cons] using ih <| by simp
    simpa using ih hz

lemma IsWalk.vertexConnected_first_last (hW : G.IsWalk W) : G.VertexConnected W.first W.last :=
  hW.vertexConnected_of_mem_of_mem (by simp) <| by simp

lemma VertexConnected.of_le (h : H.VertexConnected x y) (hle : H ≤ G) : G.VertexConnected x y := by
  rw [vertexConnected_iff_mem_foo_of_mem <| vertexSet_mono hle h.left_mem]
  exact vertexSet_mono (foo_le_foo_of_le h.left_mem hle) h.mem_foo

-- Not true anymore because of infinite graphs
-- lemma VertexConnected.exists_isWalk (h : G.VertexConnected x y) :
--     ∃ W, G.IsWalk W ∧ W.first = x ∧ W.last = y := by
--   rw [VertexConnected] at h
--   induction h using Relation.TransGen.head_induction_on with
--   | @base a h =>
--     obtain ⟨e, he⟩ | ⟨rfl, h⟩ := h
--     · exact ⟨he.walk, by simp⟩
--     exact ⟨.nil a, by simp [h]⟩
--   | @ih u v h₁ h₂ h₃ =>
--     obtain ⟨W, hW, rfl, rfl⟩ := h₃
--     obtain ⟨e, he⟩ | ⟨rfl, h⟩ := h₁
--     · exact ⟨.cons u e W, by simp [he, hW]⟩
--     exact ⟨W, hW, rfl, rfl⟩

-- lemma vertexConnected_iff_exists_walk :
--     G.VertexConnected x y ↔ ∃ W, G.IsWalk W ∧ W.first = x ∧ W.last = y := by
--   refine ⟨VertexConnected.exists_isWalk, ?_⟩
--   rintro ⟨W, hW, rfl, rfl⟩
--   exact hW.vertexConnected_first_last

-- lemma VertexConnected.exists_isPath (h : G.VertexConnected x y) :
--     ∃ P, G.IsPath P ∧ P.first = x ∧ P.last = y := by
--   classical
--   obtain ⟨W, hW, rfl, rfl⟩ := h.exists_isWalk
--   exact ⟨W.dedup, by simp [hW.dedup_isPath]⟩

-- lemma vertexConnected_induce_iff {X : Set α} (hx : x ∈ V(G)) :
--     G[X].VertexConnected x y ↔ ∃ P, G.IsPath P ∧ P.first = x ∧ P.last = y ∧ V(P) ⊆ X := by
--   refine ⟨fun h ↦ ?_, ?_⟩
--   · obtain ⟨P, hP, rfl, rfl⟩ := h.exists_isPath
--     refine ⟨P, ?_, rfl, rfl, hP.vertexSet_subset⟩
--     cases P with
--     | nil => simpa
--     | cons u e W =>
--       rw [isPath_induce_iff' (by simp)] at hP
--       exact hP.1
--   rintro ⟨P, h, rfl, rfl, hPX⟩
--   cases P with
--   | nil => simpa using hPX
--   | cons u e W =>
--     apply IsWalk.vertexConnected_first_last
--     rw [isWalk_induce_iff' (by simp)]
--     simp_all only [cons_isPath_iff, first_cons, cons_vertexSet, cons_isWalk_iff, true_and, and_true]
--     exact h.1.isWalk
