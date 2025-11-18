import Matroid.Graph.Connected.Component
import Mathlib.Data.Set.Insert
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Real.Basic
import Matroid.ForMathlib.Set

open Set Function Nat WList

variable {α β : Type*} [CompleteLattice α] {G H K : Graph α β} {u v x x₁ x₂ y y₁ y₂ z : α}
  {e e' f g : β} {U V S T X Y : Set α} {F F' R R': Set β} {C W P Q : WList α β}

namespace Graph

/- ### Separations -/

/-- A partition of `G.V` into two parts with no edge between them. -/
structure Separation (G : Graph α β) where
  left : Set α
  right : Set α
  nonempty_left : left.Nonempty
  nonempty_right : right.Nonempty
  disjoint : Disjoint left right
  union_eq : left ∪ right = V(G)
  not_adj : ∀ ⦃x y⦄, x ∈ left → y ∈ right → ¬ G.Adj x y

namespace Separation

variable {S : G.Separation}

lemma left_subset (S : G.Separation) : S.left ⊆ V(G) := by
  simp [← S.union_eq]

lemma right_subset (S : G.Separation) : S.right ⊆ V(G) := by
  simp [← S.union_eq]

@[simps]
def symm (S : G.Separation) : G.Separation where
  left := S.right
  right := S.left
  nonempty_left := S.nonempty_right
  nonempty_right := S.nonempty_left
  disjoint := S.disjoint.symm
  union_eq := by rw [← S.union_eq, union_comm]
  not_adj x y hx hy := by simpa [adj_comm] using S.not_adj hy hx

lemma not_left_mem_iff (S : G.Separation) (hxV : x ∈ V(G)) : x ∉ S.left ↔ x ∈ S.right := by
  rw [← S.union_eq, mem_union] at hxV
  have := S.disjoint.notMem_of_mem_left (a := x)
  tauto

lemma not_right_mem_iff (S : G.Separation) (hxV : x ∈ V(G)) : x ∉ S.right ↔ x ∈ S.left := by
  simpa using S.symm.not_left_mem_iff hxV

lemma left_mem_of_adj (hx : x ∈ S.left) (hxy : G.Adj x y) : y ∈ S.left := by
  rw [← S.not_right_mem_iff hxy.right_mem]
  exact fun hy ↦ S.not_adj hx hy hxy

lemma right_mem_of_adj (hx : x ∈ S.right) (hxy : G.Adj x y) : y ∈ S.right :=
  S.symm.left_mem_of_adj hx (y := y) hxy

lemma mem_or_mem (S : G.Separation) (hxV : x ∈ V(G)) : x ∈ S.left ∨ x ∈ S.right := by
  rwa [← mem_union, S.union_eq]

lemma edge_induce_disjoint (S : G.Separation) : Disjoint E(G[S.left]) E(G[S.right]) := by
  refine disjoint_left.2 fun e he he' ↦ ?_
  simp only [induce_edgeSet, mem_setOf_eq] at he he'
  obtain ⟨x, y, hexy, hx, hy⟩ := he
  obtain ⟨x', y', hexy', hx', hy'⟩ := he'
  obtain rfl | rfl := hexy.left_eq_or_eq hexy'
  · exact S.disjoint.notMem_of_mem_left hx hx'
  exact S.disjoint.notMem_of_mem_left hx hy'

lemma eq_union (S : G.Separation) : G = G[S.left] ∪ G[S.right] := by
  have : Agree {G[S.left], G[S.right]} := by use G, by simp
  refine Graph.ext ?_ fun e x y ↦ ?_
  · simp [← S.union_eq, inter_eq_right.mpr, this]
  rw [union_isLink this]
  simp +contextual only [induce_isLink, ← and_or_left, iff_def, true_and, implies_true, and_true]
  exact fun he ↦ (S.mem_or_mem he.left_mem).imp (fun hx ↦ ⟨hx, S.left_mem_of_adj hx he.adj⟩)
    (fun hx ↦ ⟨hx, S.right_mem_of_adj hx he.adj⟩)

lemma vertexSet_nontrivial (S : G.Separation) : V(G).Nontrivial :=
  ⟨_, S.left_subset S.nonempty_left.some_mem, _, S.right_subset S.nonempty_right.some_mem,
    S.disjoint.ne_of_mem S.nonempty_left.some_mem S.nonempty_right.some_mem⟩

end Separation


/- ### Preconnectedness -/

variable {n m : ℕ}

/-- A graph is preconnected if the graph has no separation. -/
def Preconnected (G : Graph α β) : Prop := IsEmpty G.Separation

/-- A graph has preconnectivityGe n, if for every n-vertex subset of the graph, `X`, there is no
    separation in `G - X`. -/
def PreconnectivityGe (G : Graph α β) (n : ℕ) : Prop :=
    ∀ X : Set α, X.encard < ↑n → (G - X).Preconnected

lemma PreconnectivityGe.preconnected (h : G.PreconnectivityGe n) (hn : n ≠ 0) : G.Preconnected := by
  simpa using (h ∅ (by simp; omega))

lemma PreconnectivityGe.anti_right (hle : n ≤ m) (h : G.PreconnectivityGe m) :
    G.PreconnectivityGe n := by
  intro X hX
  have : X.encard < (m : ℕ∞) := lt_of_lt_of_le hX <| by exact_mod_cast hle
  exact h X this

@[simp]
lemma preconnectivityGe_zero : G.PreconnectivityGe 1 ↔ G.Preconnected := by
  refine ⟨fun h => by simpa using (h ∅ (by simp)), fun h X hX => ?_⟩
  rw [cast_one, ENat.lt_one_iff_eq_zero, encard_eq_zero] at hX
  simpa [hX]

lemma vertexDelete_isPreconnected_iff (h : G.PreconnectivityGe (V(G) ∩ X).ncard.succ)
    (hX : (V(G) ∩ X).Finite) : (G - X).Preconnected := by
  rw [← vertexDelete_vertexSet_inter]
  apply h
  simpa [ENat.lt_add_one_iff, encard_le_coe_iff_finite_ncard_le]

lemma preconnected_of_vertexSet_subsingleton (hV : V(G).Subsingleton) : G.Preconnected := by
  contrapose! hV
  obtain ⟨S⟩ := by simpa only [Preconnected, not_isEmpty_iff] using hV
  exact S.vertexSet_nontrivial

/- ### Connectedness -/

/-- A graph is connected if it is a minimal closed subgraph of itself -/
protected def Connected (G : Graph α β) : Prop := G.IsCompOf G

lemma Connected.nonempty (hG : G.Connected) : V(G).Nonempty := by
  rw [Graph.Connected, IsCompOf] at hG
  exact hG.prop.2

@[simp]
lemma bot_not_connected : ¬ (⊥ : Graph α β).Connected := by
  unfold Graph.Connected
  simp

lemma Connected.ne_bot (hG : G.Connected) : G ≠ ⊥ := by
  rintro rfl
  exact bot_not_connected hG

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

lemma Connected.union (hG : G.Connected) (hH : H.Connected) (hcompat : Agree {G, H})
    (hi : (V(H) ∩ V(G)).Nonempty) : (G ∪ H).Connected := by
  rw [connected_iff_forall_closed (hi.mono (inter_subset_left.trans (by simp [hcompat])))]
  refine fun K hK hKne ↦ ?_
  have hGle : G ≤ K ∨ Disjoint V(G) V(K) := by
    simpa [Graph.left_le_union hcompat] using hG.le_or_le_compl (Graph.left_le_union hcompat) hK
  have hHle := hH.le_or_le_compl (Graph.right_le_union hcompat) hK
  simp only [le_vertexDelete_iff, Graph.right_le_union hcompat, true_and] at hHle
  obtain hGK | hGK := disjoint_or_nonempty_inter V(G) V(K)
  · obtain hHK | hHK := disjoint_or_nonempty_inter V(H) V(K)
    · simpa [union_vertexSet hcompat, ← inter_eq_right, union_inter_distrib_right, hGK.inter_eq,
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
lemma connected_bouquet (v : α) (hv : v ≠ ⊥) (F : Set β) : (bouquet v F).Connected := by
  suffices aux : (bouquet v (∅ : Set β)).Connected from
    aux.of_isSpanningSubgraph <| bouquet_mono (empty_subset F)
  rw [connected_iff_forall_closed_ge (by simp [hv])]
  refine fun H hle hne ↦ ⟨?_, by simp⟩
  simp only [bouquet_vertexSet, ne_eq, hv, not_false_eq_true, Partition.indiscrete'_eq_of_ne_bot,
    Partition.indiscrete_parts, singleton_subset_iff]
  obtain ⟨x, hx⟩ := hne
  obtain rfl := by simpa [hv] using vertexSet_mono hle.le hx
  exact hx

def ConnectivityGe (G : Graph α β) (n : ℕ) : Prop :=
  ∀ X : Set α, X.encard < ↑n → (G - X).Connected


/-- Vertices `x` and `y` are connected if they belong to the same component. -/
def VertexConnected (G : Graph α β) (x y : α) : Prop :=
  ∃ H : Graph α β, H.IsCompOf G ∧ x ∈ V(H) ∧ y ∈ V(H)

lemma VertexConnected.refl (hx : x ∈ V(G)) : G.VertexConnected x x :=
  ⟨G.walkable x, walkable_isCompOf hx, mem_walkable hx, mem_walkable hx⟩

@[symm]
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
  obtain rfl := hH₁.eq_of_mem_mem hH₂ hy₁ hy₂
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

lemma VertexConnected.mem_walkable (h : G.VertexConnected x y) : y ∈ V(G.walkable x) :=
  let ⟨_, hH, hx, hy⟩ := h
  vertexSet_mono (hH.le_of_mem_mem walkable_isClosedSubgraph hx <|
    Graph.mem_walkable <| vertexSet_mono hH.le hx) hy

lemma vertexConnected_iff_mem_walkable_of_mem (hx : x ∈ V(G)) :
    G.VertexConnected x y ↔ y ∈ V(G.walkable x) :=
  ⟨fun h => h.mem_walkable, fun hy ↦ ⟨G.walkable x, walkable_isCompOf hx, mem_walkable hx, hy⟩⟩

@[simp]
lemma not_vertexConnected_of_left_not_mem (hx : x ∉ V(G)) : ¬ G.VertexConnected x y := by
  rintro h
  exact hx h.left_mem

@[simp]
lemma not_vertexConnected_of_right_not_mem (hy : y ∉ V(G)) : ¬ G.VertexConnected x y := by
  rintro h
  exact hy h.right_mem

lemma walkable_eq_induce_setOf_vertexConnected :
    G.walkable x = G.induce {y | G.VertexConnected x y} := by
  obtain hx | hx := em (x ∈ V(G)) |>.symm
  · simp [hx]
  rw [walkable_isClosedSubgraph.eq_induce]
  congr
  ext y
  rw [mem_setOf_eq, vertexConnected_iff_mem_walkable_of_mem hx]

lemma Adj.vertexConnected (h : G.Adj x y) : G.VertexConnected x y :=
  ⟨G.walkable x, walkable_isCompOf h.left_mem, Graph.mem_walkable h.left_mem, h.mem_walkable⟩

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

lemma IsWalk.vertexConnected_first_last (hW : G.IsWalk W) : G.VertexConnected W.first W.last :=
  hW.vertexConnected_of_mem_of_mem (by simp) <| by simp

lemma VertexConnected.exists_isWalk (h : G.VertexConnected x y) :
    ∃ W, G.IsWalk W ∧ W.first = x ∧ W.last = y := by
  obtain ⟨H, hH, hx, hy⟩ := h
  obtain ⟨x, _, rfl⟩ := isCompOf_iff_exists_walkable.mp hH
  exact exists_isWalk_of_mem_mem hx hy

lemma vertexConnected_iff_exists_walk :
    G.VertexConnected x y ↔ ∃ W, G.IsWalk W ∧ W.first = x ∧ W.last = y := by
  refine ⟨VertexConnected.exists_isWalk, ?_⟩
  rintro ⟨W, hW, rfl, rfl⟩
  exact hW.vertexConnected_first_last

lemma VertexConnected.exists_isPath (h : G.VertexConnected x y) :
    ∃ P, G.IsPath P ∧ P.first = x ∧ P.last = y := by
  classical
  obtain ⟨W, hW, rfl, rfl⟩ := h.exists_isWalk
  exact ⟨W.dedup, by simp [hW.dedup_isPath]⟩

lemma VertexConnected.of_le (h : H.VertexConnected x y) (hle : H ≤ G) : G.VertexConnected x y := by
  rw [vertexConnected_iff_exists_walk] at h ⊢
  obtain ⟨W, hW, rfl, rfl⟩ := h
  use W, hW.of_le hle

lemma vertexConnected_induce_iff {X : Set α} (hx : x ∈ V(G)) :
    G[X].VertexConnected x y ↔ ∃ P, G.IsPath P ∧ P.first = x ∧ P.last = y ∧ V(P) ⊆ X := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨P, hP, rfl, rfl⟩ := h.exists_isPath
    refine ⟨P, ?_, rfl, rfl, hP.vertexSet_subset.trans inter_subset_right⟩
    cases P with
    | nil => simpa
    | cons u e W =>
      rw [isPath_induce_iff' (by simp)] at hP
      exact hP.1
  rintro ⟨P, h, rfl, rfl, hPX⟩
  cases P with
  | nil => simp_all
  | cons u e W =>
    apply IsWalk.vertexConnected_first_last
    rw [isWalk_induce_iff' (by simp)]
    simp_all only [cons_isPath_iff, first_cons, cons_vertexSet, cons_isWalk_iff, true_and, and_true]
    exact h.1.isWalk

/-- If `G` has one vertex connected to all others, then `G` is connected. -/
lemma connected_of_vertex (hu : u ∈ V(G)) (h : ∀ y ∈ V(G), G.VertexConnected y u) :
    G.Connected := by
  have hco := walkable_isCompOf hu
  rwa [walkable_isClosedSubgraph.eq_ambient_of_subset_vertexSet (h · · |>.symm.mem_walkable)] at hco

lemma Connected.vertexConnected (h : G.Connected) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    G.VertexConnected x y := ⟨G, h, hx, hy⟩

lemma connected_iff : G.Connected ↔ V(G).Nonempty ∧ ∀ x y, x ∈ V(G) → y ∈ V(G) →
    G.VertexConnected x y :=
  ⟨fun h => ⟨h.nonempty, fun _ _ => h.vertexConnected⟩,
    fun ⟨hne, h⟩ => connected_of_vertex hne.some_mem (h · _ · hne.some_mem)⟩

lemma singleVertex_connected (hG : V(G) = {x}) : G.Connected := by
  simp [connected_iff, hG]

lemma exists_of_not_connected (h : ¬ G.Connected) (hne : V(G).Nonempty) :
    ∃ X ⊂ V(G), X.Nonempty ∧ ∀ ⦃u v⦄, u ∈ X → G.Adj u v → v ∈ X := by
  simp only [connected_iff, hne, true_and, not_forall, exists_prop, exists_and_left] at h
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  refine ⟨{z | G.VertexConnected x z}, ?_, ⟨x, by simpa⟩,
    fun u v (h : G.VertexConnected x u) huv ↦ h.trans huv.vertexConnected⟩
  exact HasSubset.Subset.ssubset_of_mem_notMem (fun z hz ↦ hz.right_mem) hy (by simpa)

lemma connected_iff_forall_exists_adj (hne : V(G).Nonempty) :
    G.Connected ↔ ∀ X ⊂ V(G), X.Nonempty → ∃ x ∈ X, ∃ y ∈ V(G) \ X, G.Adj x y := by
  refine ⟨fun h X hXV hXnem ↦ ?_, fun h ↦ by_contra fun hnc ↦ ?_⟩
  · by_contra! hnadj
    have hGXcl : G[X] ≤c G := ⟨induce_le, fun e x ⟨y, hexy⟩ hxX =>
      ⟨x, y, hexy, hxX.2, by_contra fun hyX => hnadj x hxX.2 y ⟨hexy.right_mem, hyX⟩ ⟨e, hexy⟩⟩⟩
    have : V(G) ∩ X = X := by rw [inter_eq_right.mpr hXV.subset]
    rw [← le_antisymm hGXcl.le <| h.2 ⟨hGXcl, by simpa [this]⟩ hGXcl.le, induce_vertexSet,
      this] at hXV
    exact (and_not_self_iff (X ⊆ X)).mp hXV
  obtain ⟨X, hXV, hXne, h'⟩ := exists_of_not_connected hnc hne
  obtain ⟨x, hX, y, hy, hxy⟩ := h X hXV hXne
  exact hy.2 <| h' hX hxy

lemma Separation.not_vertexConnected (S : G.Separation) (hx : x ∈ S.left) (hy : y ∈ S.right) :
    ¬ G.VertexConnected x y := by
  intro h
  obtain ⟨W, hW, rfl, rfl⟩ := h.exists_isWalk
  rw [← S.not_left_mem_iff (S.right_subset hy)] at hy
  obtain ⟨e, x, y, hinc, hx, hy⟩ := exists_dInc_prop_not_prop hx hy
  exact hy <| S.left_mem_of_adj hx (hW.isLink_of_dInc hinc).adj

lemma Separation.not_connected (S : G.Separation) : ¬ G.Connected := by
  obtain ⟨x, hx⟩ := S.nonempty_left
  obtain ⟨y, hy⟩ := S.nonempty_right
  exact fun h ↦ S.not_vertexConnected hx hy <| h.vertexConnected (S.left_subset hx)
    (S.right_subset hy)

lemma Connected.isEmpty_separation (hG : G.Connected) : IsEmpty G.Separation :=
  isEmpty_iff.2 fun S ↦ S.not_connected hG

lemma exists_separation_of_not_vertexConnected (hxV : x ∈ V(G)) (hyV : y ∈ V(G))
    (hxy : ¬ G.VertexConnected x y) : ∃ S : G.Separation, x ∈ S.left ∧ y ∈ S.right :=
  ⟨⟨{w ∈ V(G) | G.VertexConnected x w}, {w ∈ V(G) | ¬ G.VertexConnected x w}, ⟨x, by simpa⟩,
    ⟨y, by aesop⟩, by simp +contextual [disjoint_left],
    by simp [Set.ext_iff, ← and_or_left, or_not],
    fun x' y' ⟨_, hx'⟩ ⟨_, hy'⟩ hxy' ↦  hy' <| hx'.trans hxy'.vertexConnected⟩, by simp_all⟩

lemma preconnected_iff_forall_vertexConnected :
    G.Preconnected ↔ ∀ x y, x ∈ V(G) → y ∈ V(G) → G.VertexConnected x y := by
  rw [← not_iff_not]
  simp only [Preconnected, not_isEmpty_iff, not_forall]
  refine ⟨fun ⟨S⟩ => ?_, fun ⟨x, y, hx, hy, h⟩ => ?_⟩
  · use S.nonempty_left.some, S.nonempty_right.some, S.left_subset S.nonempty_left.some_mem,
      S.right_subset S.nonempty_right.some_mem, S.not_vertexConnected S.nonempty_left.some_mem
      S.nonempty_right.some_mem
  obtain ⟨S, hxL, hyR⟩ := exists_separation_of_not_vertexConnected hx hy h
  exact ⟨S⟩

lemma nonempty_separation_of_not_connected (hne : V(G).Nonempty) (hG : ¬ G.Connected) :
    Nonempty G.Separation := by
  simp only [connected_iff, hne, true_and, not_forall] at hG
  obtain ⟨x, y, hx, hy, hxy⟩ := hG
  exact ⟨(exists_separation_of_not_vertexConnected hx hy hxy).choose⟩

-- /-- A `WList` that is `WellFormed` produces a connected graph. -/
-- lemma _root_.WList.WellFormed.toGraph_connected (hW : W.WellFormed) : W.toGraph.Connected :=
--   connected_iff.mpr ⟨by simp, fun x y hx hy ↦
--     hW.isWalk_toGraph.vertexConnected_of_mem_of_mem (by simpa using hx) (by simpa using hy)⟩

-- lemma IsWalk.toGraph_connected (hW : G.IsWalk W) : W.toGraph.Connected :=
--   hW.wellFormed.toGraph_connected

lemma Connected.exists_vertexConnected_deleteEdge_set {X : Set α} (hG : G.Connected)
    (hX : (X ∩ V(G)).Nonempty) (hu : u ∈ V(G)) : ∃ x ∈ X, (G ＼ E(G[X])).VertexConnected u x := by
  obtain ⟨x', hx'X, hx'V⟩ := hX
  obtain ⟨W, hW, hu, rfl⟩ := (hG.vertexConnected hu hx'V).exists_isWalk
  induction hW generalizing u with
  | nil => exact ⟨_, hx'X, by simp_all⟩
  | @cons x e W hW h ih =>
    obtain rfl : x = u := hu
    by_cases hmem : e ∈ E(G ＼ E(G[X]))
    · obtain ⟨x', hx', hWx'⟩ := ih (u := W.first) (hW.vertex_mem_of_mem (by simp)) rfl
        (by simpa using hx'X) (by simpa using hx'V)
      have hconn := (h.of_le_of_mem edgeDelete_le hmem).vertexConnected
      exact ⟨x', hx', hconn.trans hWx'⟩
    rw [edgeDelete_edgeSet, mem_diff, and_iff_right h.edge_mem, h.mem_induce_iff, not_not] at hmem
    exact ⟨x, hmem.1, by simpa⟩

lemma Connected.exists_isPathFrom (hG : G.Connected) (hS : (S ∩ V(G)).Nonempty)
    (hT : (T ∩ V(G)).Nonempty) : ∃ P, G.IsPathFrom S T P := by
  obtain ⟨x, hxS, hx⟩ := hS
  obtain ⟨y, hyT, hy⟩ := hT
  obtain ⟨W, hW, rfl, rfl⟩ := (hG.vertexConnected hx hy).exists_isWalk
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

lemma Connected.exists_vertexConnected_deleteEdge_set_set (hG : G.Connected)
    (hS : (S ∩ V(G)).Nonempty) (hT : (T ∩ V(G)).Nonempty) :
    ∃ x ∈ S, ∃ y ∈ T, (G ＼ (E(G[S]) ∪ E(G[T]))).VertexConnected x y := by
  obtain ⟨P, hP⟩ := hG.exists_isPathFrom hS hT
  have h0 : P.first ∈ V(G ＼ (E(G[S]) ∪ E(G[T]))) := by
    simpa using hP.isWalk.vertex_mem_of_mem (by simp)
  refine ⟨_, hP.first_mem, _, hP.last_mem,
    (hP.isPathFrom_le (by simp) (fun e heP ↦ ?_) h0).isWalk.vertexConnected_first_last⟩
  obtain ⟨x, y, hxy⟩ := exists_dInc_of_mem_edge heP
  have hxy' := hP.isWalk.isLink_of_dInc hxy
  rw [edgeDelete_edgeSet, mem_diff, mem_union, hxy'.mem_induce_iff,
    hxy'.mem_induce_iff, and_iff_right hxy'.edge_mem]
  simp [hP.notMem_left_of_dInc hxy, hP.notMem_right_of_dInc hxy]

lemma Connected.exists_isLink_of_mem (hG : G.Connected) (hV : V(G).Nontrivial) (hx : x ∈ V(G)) :
    ∃ e y, G.IsLink e x y ∧ y ≠ x := by
  obtain ⟨z, hz, hne⟩ := hV.exists_ne x
  obtain ⟨P, hP, rfl, rfl⟩ := (hG.vertexConnected hx hz).exists_isPath
  rw [ne_comm, first_ne_last_iff hP.nodup] at hne
  obtain ⟨x, e, P⟩ := hne
  simp only [cons_isPath_iff] at hP
  exact ⟨e, P.first, hP.2.1, mt (by simp +contextual [eq_comm]) hP.2.2⟩

-- lemma Isolated.not_connected (hx : G.Isolated x) (hnt : V(G).Nontrivial) : ¬ G.Connected :=
--   fun h ↦ by simpa [hx.not_isLink] using h.exists_isLink_of_mem hnt hx.mem

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
    (hG.vertexConnected (S.left_subset hx₀) (S.right_subset hy₀)).exists_isWalk
  rw [← S.not_left_mem_iff (S.right_subset hy₀)] at hy₀
  obtain ⟨e, x, y, hexy, hx, hy⟩ := W.exists_dInc_prop_not_prop hx₀ hy₀
  have h' := hW.isLink_of_dInc hexy
  rw [S.not_left_mem_iff h'.right_mem] at hy
  refine ⟨S, e, x, y, fun heF ↦ ?_, hx, hy, h'⟩
  exact S.not_adj hx hy <| IsLink.adj <| h'.of_le_of_mem (by simp) <| by simpa [h'.edge_mem]
