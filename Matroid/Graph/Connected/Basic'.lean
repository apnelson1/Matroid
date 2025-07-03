import Matroid.Graph.Lattice
import Matroid.Graph.Finite
import Matroid.Graph.Degree.Defs
import Matroid.Graph.Degree.Constructions
import Mathlib.Data.Set.Insert
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Real.Basic
import Matroid.ForMathlib.Set

open Set Function Nat WList

variable {α β : Type*} {G H K : Graph α β} {u v x x₁ x₂ y y₁ y₂ z : α} {e e' f g : β}
  {U V S T : Set α} {F F' R R': Set β} {C W P Q : WList α β}

namespace Graph

/-- A graph is connected if it is a minimal closed subgraph of itself -/
protected def Connected (G : Graph α β) : Prop := G.IsCompOf G

lemma Connected.nonempty (hG : G.Connected) : V(G).Nonempty := by
  rw [Graph.Connected, IsCompOf] at hG
  exact hG.prop.2

@[simp]
lemma bot_not_connected : ¬ (⊥ : Graph α β).Connected := by
  unfold Graph.Connected
  simp

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

lemma Connected.isSimpleOrder (hG : G.Connected) (hnonempty : G ≠ ⊥) :
    IsSimpleOrder G.ClosedSubgraph where
  exists_pair_ne := by
    use ⊥, ⊤
    apply_fun Subtype.val
    exact hnonempty.symm
  eq_bot_or_eq_top H := by
    refine (eq_empty_or_nonempty V(H.val)).imp (by simp) ?_
    convert hG.eq_of_isClosedSubgraph H.prop
    exact Iff.symm (StrictMono.apply_eq_top_iff fun ⦃a b⦄ a ↦ a)

lemma IsClosedSubgraph.disjoint_or_subset_of_isCompOf (h : H ≤c G) (hK : K.IsCompOf G) :
    K.IsCompOf H ∨ K.StronglyDisjoint H := by
  rw [or_iff_not_imp_right, StronglyDisjoint_iff_of_le_le hK.le h.le,
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

lemma CompWith_connected (hx : x ∈ V(G)) : (CompWith G x).val.Connected :=
  (compWith_isCompOf hx).connected

lemma Connected.components_subsingleton (hG : G.Connected) : G.Components.Subsingleton := by
  rintro H₁ hH₁ H₂ hH₂
  rw [components_isCompOf_iff] at hH₁ hH₂
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
  ∃ H : Graph α β, H.IsCompOf G ∧ x ∈ V(H) ∧ y ∈ V(H)

lemma VertexConnected.refl (hx : x ∈ V(G)) : G.VertexConnected x x :=
  ⟨CompWith G x, compWith_isCompOf hx, mem_compWith hx, mem_compWith hx⟩

lemma VertexConnected.symm (h : G.VertexConnected x y) : G.VertexConnected y x := by
  obtain ⟨H, hH, hx, hy⟩ := h
  exact ⟨H, hH, hy, hx⟩

instance : IsSymm _ G.VertexConnected where
  symm _ _ := VertexConnected.symm

lemma VertexConnected_comm : G.VertexConnected x y ↔ G.VertexConnected y x :=
  ⟨VertexConnected.symm, VertexConnected.symm⟩

lemma VertexConnected.left_mem (hxy : G.VertexConnected x y) : x ∈ V(G) :=
  let ⟨_, hHco, hx, _⟩ := hxy
  vertexSet_mono hHco.le hx

lemma VertexConnected.right_mem (hxy : G.VertexConnected x y) : y ∈ V(G) :=
  hxy.symm.left_mem

lemma VertexConnected.trans (hxy : G.VertexConnected x y) (hyz : G.VertexConnected y z) :
    G.VertexConnected x z := by
  obtain ⟨H₁, hH₁, hx, hy₁⟩ := hxy
  obtain ⟨H₂, hH₂, hy₂, hz⟩ := hyz
  obtain rfl := G.eq_of_mem_component_of_mem_mem hH₁ hH₂ hy₁ hy₂
  exact ⟨H₁, hH₁, hx, hz⟩

instance : IsTrans _ G.VertexConnected where
  trans _ _ _ := VertexConnected.trans

lemma VertexConnected.mem_vertexSet_iff (H : G.ClosedSubgraph) :
    ∀ {x y : α}, G.VertexConnected x y → (x ∈ V(H.val) ↔ y ∈ V(H.val)) := by
  suffices ∀ x y, G.VertexConnected x y → x ∈ V(H.val) → y ∈ V(H.val) by
    exact fun x y h => ⟨fun hx => this x y h hx, fun hy => this y x h.symm hy⟩
  exact fun x y ⟨H', hH', hx', hy'⟩ hx ↦
    vertexSet_mono (hH'.le_of_mem_mem H.prop hx' hx) hy'

@[simp]
lemma vertexConnected_self : G.VertexConnected x x ↔ x ∈ V(G) :=
  ⟨VertexConnected.left_mem, VertexConnected.refl⟩

lemma VertexConnected.mem_CompWith (h : G.VertexConnected x y) : y ∈ V((CompWith G x).val) :=
  let ⟨_, hH, hx, hy⟩ := h
  vertexSet_mono (hH.le_of_mem_mem (G.CompWith x).prop hx <|
    mem_compWith <| vertexSet_mono hH.le hx) hy

lemma vertexConnected_iff_mem_CompWith_of_mem (hx : x ∈ V(G)) :
    G.VertexConnected x y ↔ y ∈ V((CompWith G x).val) :=
  ⟨fun h => h.mem_CompWith, fun hy ↦ ⟨CompWith G x, compWith_isCompOf hx, mem_compWith hx, hy⟩⟩

lemma Adj.vertexConnected (h : G.Adj x y) : G.VertexConnected x y :=
  ⟨CompWith G x, compWith_isCompOf h.left_mem, mem_compWith h.left_mem, h.mem_CompWith⟩

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

lemma IsWalk.isWalk_or_isWalk_compl_of_closedSubgraph (H : G.ClosedSubgraph) (hW : G.IsWalk W) :
    H.val.IsWalk W ∨ Hᶜ.val.IsWalk W := by
  by_cases hx : W.first ∈ V(H.val)
  · exact .inl <| hW.isWalk_isClosedSubgraph H.prop hx
  exact .inr <| hW.isWalk_isClosedSubgraph Hᶜ.prop <| by simp [hx, hW.first_mem]

lemma IsWalk.isWalk_or_isWalk_of_union_of_disjoint (h : G.StronglyDisjoint H)
    (hW : (G ∪ H).IsWalk W) : G.IsWalk W ∨ H.IsWalk W := by
  obtain hCG | hCH := hW.isWalk_or_isWalk_compl_of_closedSubgraph ⟨G, h.isClosedSubgraph_union_left⟩
  · exact .inl hCG
  rw [ClosedSubgraph.compl_eq_of_stronglyDisjoint_union h] at hCH
  exact .inr hCH

lemma IsWalk.vertexConnected_first_last (hW : G.IsWalk W) : G.VertexConnected W.first W.last :=
  hW.vertexConnected_of_mem_of_mem (by simp) <| by simp

lemma VertexConnected.of_le (h : H.VertexConnected x y) (hle : H ≤ G) : G.VertexConnected x y := by
  rw [vertexConnected_iff_mem_CompWith_of_mem <| vertexSet_mono hle h.left_mem]
  exact vertexSet_mono (compWith_le_compWith_of_le h.left_mem hle) h.mem_CompWith


/-- If `G` has one vertex connected to all others, then `G` is connected. -/
lemma connected_of_vertex (hu : u ∈ V(G)) (h : ∀ y ∈ V(G), G.VertexConnected y u) :
    G.Connected := by
  have hco := compWith_isCompOf hu
  rwa [(CompWith G u).eq_ambient_of_subset_vertexSet (h · · |>.symm.mem_CompWith)] at hco

lemma Connected.vertexConnected (h : G.Connected) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    G.VertexConnected x y := ⟨G, h, hx, hy⟩

lemma connected_iff : G.Connected ↔ V(G).Nonempty ∧ ∀ x y, x ∈ V(G) → y ∈ V(G) →
    G.VertexConnected x y :=
  ⟨fun h => ⟨h.nonempty, fun _ _ => h.vertexConnected⟩,
    fun ⟨hne, h⟩ => connected_of_vertex hne.some_mem (h · _ · hne.some_mem)⟩

lemma singleVertex_connected (hG : V(G) = {x}) : G.Connected := by
  simp [connected_iff, hG]

@[simp]
lemma singleEdge_connected (e : β) (x y : α) : (Graph.singleEdge x y e).Connected := by
  refine connected_of_vertex (u := x) (by simp) ?_
  simp only [singleEdge_vertexSet, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp,
    vertexConnected_self, true_or, forall_eq, true_and]
  exact Adj.vertexConnected <| by simp [Adj]

lemma exists_of_not_connected (h : ¬ G.Connected) (hne : V(G).Nonempty) :
    ∃ X ⊂ V(G), X.Nonempty ∧ ∀ ⦃u v⦄, u ∈ X → G.Adj u v → v ∈ X := by
  simp only [connected_iff, hne, true_and, not_forall, Classical.not_imp,
    exists_prop, exists_and_left] at h
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  refine ⟨{z | G.VertexConnected x z}, ?_, ⟨x, by simpa⟩,
    fun u v (h : G.VertexConnected x u) huv ↦ ?_⟩
  · exact HasSubset.Subset.ssubset_of_mem_notMem
      (fun z hz ↦ VertexConnected.right_mem hz) hy (by simpa)
  exact h.trans huv.vertexConnected

lemma connected_iff_forall_exists_adj (hne : V(G).Nonempty) :
    G.Connected ↔ ∀ X ⊂ V(G), X.Nonempty → ∃ x ∈ X, ∃ y ∈ V(G) \ X, G.Adj x y := by
  refine ⟨fun h X hXV hXnem ↦ ?_, fun h ↦ by_contra fun hnc ↦ ?_⟩
  · by_contra! hnadj
    have hGXcl : G[X] ≤c G := ⟨induce_le hXV.subset, fun e x ⟨y, hexy⟩ hxX =>
      ⟨x, y, hexy, hxX, by_contra fun hyX => hnadj x hxX y ⟨hexy.right_mem, hyX⟩ ⟨e, hexy⟩⟩⟩
    rw [← le_antisymm hGXcl.le <| h.2 ⟨hGXcl, hXnem⟩ hGXcl.le, induce_vertexSet] at hXV
    exact (and_not_self_iff (X ⊆ X)).mp hXV
  obtain ⟨X, hXV, hXne, h'⟩ := exists_of_not_connected hnc hne
  obtain ⟨x, hX, y, hy, hxy⟩ := h X hXV hXne
  exact hy.2 <| h' hX hxy

/-- A `WList` that is `WellFormed` produces a connected graph. -/
lemma _root_.WList.WellFormed.toGraph_connected (hW : W.WellFormed) : W.toGraph.Connected :=
  connected_iff.mpr ⟨by simp, fun x y hx hy ↦
    hW.isWalk_toGraph.vertexConnected_of_mem_of_mem (by simpa using hx) (by simpa using hy)⟩

lemma IsWalk.toGraph_connected (hW : G.IsWalk W) : W.toGraph.Connected :=
  hW.wellFormed.toGraph_connected

lemma Connected.exists_vertexConnected_deleteEdge_set {X : Set α} (hG : G.Connected)
    (hX : (X ∩ V(G)).Nonempty) (hu : u ∈ V(G)) : ∃ x ∈ X, (G ＼ E(G[X])).VertexConnected u x := by
  by_contra! h
  simp_rw [(G ＼ E(G[X])).vertexConnected_iff_mem_CompWith_of_mem hu] at h
  let H := CompWith (G ＼ E(G[X])) u
  have hHX : Disjoint V(H.val) X := by
    rw [Set.disjoint_left]
    exact fun ⦃a⦄ a_1 a_2 ↦ h a a_2 a_1
  clear h
  have hHleG := H.prop.le.trans edgeDelete_le
  have hHssub : V(H.val) ⊂ V(G) := Set.ssubset_iff_subset_ne.mpr ⟨vertexSet_mono hHleG,
    ne_comm.mp <| ne_of_mem_of_not_mem' hX.some_mem.2 <| hHX.notMem_of_mem_right hX.some_mem.1⟩
  obtain ⟨x, hxH, y, hy, e, hadj⟩ := connected_iff_forall_exists_adj hG.nonempty
    |>.mp hG V(H.val) hHssub (nonempty_of_mem <| mem_compWith hu)
  have hxnX : x ∉ X := hHX.notMem_of_mem_left hxH
  have hedel : e ∈ E(G ＼ E(G[X])) := by simp [hadj.edge_mem, hadj.symm.mem_induce_iff,hxnX]
  have heH := H.prop.closed (Inc.of_le_of_mem (⟨y, hadj⟩ : G.Inc e x) edgeDelete_le hedel) hxH
  exact hy.2 <| hadj.of_le_of_mem hHleG heH |>.right_mem

lemma Connected.exists_vertexConnected_deleteEdge_set_set (hG : G.Connected)
    (hS : (S ∩ V(G)).Nonempty) (hT : (T ∩ V(G)).Nonempty) :
    ∃ x ∈ S, ∃ y ∈ T, (G ＼ (E(G[S]) ∪ E(G[T]))).VertexConnected x y := by
  obtain ⟨s, hs, hsconn⟩ := hG.exists_vertexConnected_deleteEdge_set hS hT.some_mem.2
  let G₁ := CompWith (G ＼ E(G[S])) s
  have hG₁leG : G₁.val ≤ G := G₁.prop.le.trans edgeDelete_le
  have hG₁ : G₁.val.Connected := CompWith_connected hsconn.right_mem
  have hT₁ : (T ∩ V(G₁.val)).Nonempty := by
    refine ⟨hT.some, hT.some_mem.1, ?_⟩
    rwa [← vertexConnected_iff_mem_CompWith_of_mem hsconn.right_mem, VertexConnected_comm]
  have hs₁ : s ∈ V(G₁.val) := mem_compWith hsconn.right_mem
  obtain ⟨t, ht, htconn⟩ := hG₁.exists_vertexConnected_deleteEdge_set hT₁ hs₁
  refine ⟨s, hs, t, ht, htconn.of_le ?_⟩
  have hh : G₁.val ＼ E((G₁.val)[T]) = G₁.val ＼ E(G[T]) := by
    rw [eq_comm, ← edgeDelete_inter_edgeSet, inter_comm,
      edgeSet_induce_inter_eq_edgeSet_induce_of_le hG₁leG]
  rw [hh, ← edgeDelete_edgeDelete]
  exact edgeDelete_mono_left G₁.prop.le

lemma Connected.exists_isLink_of_mem (hG : G.Connected) (hV : V(G).Nontrivial) (hx : x ∈ V(G)) :
    ∃ e y, G.IsLink e x y ∧ y ≠ x := by
  have hinduce : ¬ G[({x} : Set α)] ≤c G := by
    rintro hinduce
    rw [← hG.eq_of_isClosedSubgraph hinduce (by simp)] at hV
    simp at hV
  rw [not_isClosedSubgraph_iff_of_IsInducedSubgraph (by simpa)] at hinduce
  obtain ⟨u, v, ⟨e, hl⟩, hu, hv⟩ := hinduce
  simp only [induce_vertexSet, mem_singleton_iff] at hu hv
  use e, v, hu ▸ hl, hv

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

/- ### Unions -/

lemma Compatible.union_connected_of_forall (h : G.Compatible H) (hG : G.Connected)
    (hH : ∀ x ∈ V(H), ∃ y ∈ V(G), H.VertexConnected x y) : (G ∪ H).Connected := by
  obtain ⟨v, hv⟩ := hG.nonempty
  refine connected_of_vertex (u := v) (by simp [hv]) ?_
  rintro y (hy | hy)
  · exact (hG.vertexConnected hy hv).of_le <| Graph.left_le_union ..
  obtain ⟨z, hzG, hyz⟩ := hH _ hy
  exact (hyz.of_le h.right_le_union).trans <| (hG.vertexConnected hzG hv).of_le <|
    Graph.left_le_union ..

lemma Compatible.union_connected_of_nonempty_inter (h : Compatible G H) (hG : G.Connected)
    (hH : H.Connected) (hne : (V(G) ∩ V(H)).Nonempty) : (G ∪ H).Connected :=
  let ⟨z, hzG, hzH⟩ := hne
  h.union_connected_of_forall hG fun _ hx ↦ ⟨z, hzG, hH.vertexConnected hx hzH⟩

lemma IsWalk.exists_mem_mem_of_union (h : (G ∪ H).IsWalk W) (hxW : x ∈ V(W)) (hyW : y ∈ V(W))
    (hxG : x ∈ V(G)) (hyH : y ∈ V(H)) : ∃ x ∈ W, x ∈ V(G) ∧ x ∈ V(H) := by
  by_cases hH' : y ∈ V(G)
  · exact ⟨y, hyW, hH', hyH⟩
  obtain ⟨e, x, y, hxy, hx, hy⟩ := W.exists_isLink_prop_not_prop hxW hxG hyW hH'
  obtain hxy' | hxy' := isLink_or_isLink_of_union <| h.isLink_of_isLink hxy
  · exact False.elim <| hy <| hxy'.right_mem
  exact ⟨x, hxy.left_mem, hx, hxy'.left_mem⟩

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
  -- Suppose `G` and `H` are disjoint. Then any walk in `G ∪ H` has a walk in `G` or `H`.
  obtain hempty | ⟨v, hv⟩ := hi.eq_empty_or_singleton
  · have hdisj : Graph.StronglyDisjoint G H := by
      rw [Graph.stronglyDisjoint_iff_vertexSet_disjoint_compatible]
      use disjoint_iff_inter_eq_empty.mpr hempty
    clear hempty
    obtain hCG | hCH := hC.isWalk.isWalk_or_isWalk_of_union_of_disjoint hdisj
    · exact .inl ⟨⟨hCG, hC.edge_nodup⟩, hC.nonempty, hC.isClosed, hC.nodup⟩
    · exact .inr ⟨⟨hCH, hC.edge_nodup⟩, hC.nonempty, hC.isClosed, hC.nodup⟩
  -- Otherwise, `G` and `H` intersect in a vertex `v`.
  -- Every edge of `C` has distinct ends in `G` or in `H`.
  have aux1 (e : β) (he : e ∈ E(C)) :
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
  -- Then, `C - v` is a path in two disjoint graphs, `G - v` and `H - v`.
  obtain ⟨x, hxC, hxH⟩ := not_subset.1 hCH
  obtain ⟨y, hyC, hyG⟩ := not_subset.1 hCG
  have hxv : x ≠ v := fun hxv => have : x ∈ V(G) ∩ V(H) := hv ▸ hxv; hxH this.2
  have hyv : y ≠ v := fun hyv => have : y ∈ V(G) ∩ V(H) := hv ▸ hyv; hyG this.1
  have hvC : v ∈ V(C) :=
    let ⟨u, huC, huG, huH⟩ := hC.isWalk.exists_mem_mem_of_union hxC hyC
      (by simpa [hxH] using hC.vertexSet_subset hxC) <| by simpa [hyG] using hC.vertexSet_subset hyC
    (hv ▸ (mem_inter huG huH)) ▸ huC
  exfalso
  -- A walk `C - v` is a walk in `G - v` or `H - v` yet it has vertices `x` and `y` in `G` and `H`.
  have hGHv : (G ∪ H) - {v} = G - {v} ∪ H - {v} := hcompat.vertexDelete_union {v}
  have hcompatv : (G - {v}).Compatible H - {v} := hcompat.mono vertexDelete_le vertexDelete_le
  have hdisjv : Graph.StronglyDisjoint (G - {v}) (H - {v}) := by
    rw [Graph.stronglyDisjoint_iff_vertexSet_disjoint_compatible, disjoint_iff_inter_eq_empty]
    simp [hv, hcompatv]
  obtain ⟨P, hP, hPeq⟩ := hC.exists_isPath_toGraph_eq_delete_vertex hnt hvC
  apply_fun Graph.vertexSet at hPeq
  simp only [toGraph_vertexSet, vertexDelete_vertexSet] at hPeq
  have hxP : x ∈ V(P) := by simp [hPeq, hxC, hxv]
  have hyP : y ∈ V(P) := by simp [hPeq, hyC, hyv]
  have hPv : (G - {v} ∪ H - {v}).IsPath P :=
    hGHv ▸ isPath_vertexDelete_iff.mpr ⟨hP, by simp [disjoint_singleton_right, hPeq]⟩

  obtain hPG | hPH := hPv.isWalk.isWalk_or_isWalk_of_union_of_disjoint hdisjv
  · exact hyG <| (hPG.of_le vertexDelete_le).vertex_mem_of_mem hyP
  · exact hxH <| (hPH.of_le vertexDelete_le).vertex_mem_of_mem hxP

#print axioms IsCycle.isCycle_or_isCycle_of_union_of_subsingleton_inter

lemma Compatible.isCycle_union_iff_of_subsingleton_inter (hcompat : G.Compatible H)
    (hi : (V(G) ∩ V(H)).Subsingleton) : (G ∪ H).IsCycle C ↔ G.IsCycle C ∨ H.IsCycle C :=
  ⟨fun h ↦ h.isCycle_or_isCycle_of_union_of_subsingleton_inter hi,
    fun h ↦ h.elim (fun h' ↦ h'.isCycle_of_ge (Graph.left_le_union ..))
    (fun h' ↦ h'.isCycle_of_ge hcompat.right_le_union)⟩
