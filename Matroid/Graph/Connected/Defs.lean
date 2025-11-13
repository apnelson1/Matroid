import Matroid.Graph.Connected.Component
import Matroid.Graph.Connected.Set.Defs

open Set Function Nat WList

variable {α β : Type*} {G H K : Graph α β} {s t u v x x₁ x₂ y y₁ y₂ z : α} {n m : ℕ}
  {e e' f g : β} {U V S S' T T' X Y : Set α} {F F' R R': Set β} {C W P Q : WList α β}

@[simp]
lemma isLeast_empty {α : Type*} [LE α] {m : α} : ¬ IsLeast ∅ m := by
  simp [IsLeast]

namespace Graph

/-! ### Connectivity on a graph -/

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
  refine Graph.ext (by simp [← S.union_eq]) fun e x y ↦ ?_
  rw [Compatible.union_isLink_iff (by simp)]
  simp +contextual only [induce_isLink_iff, iff_def, true_and]
  exact ⟨fun he ↦ (S.mem_or_mem he.left_mem).imp (fun hx ↦ ⟨hx, S.left_mem_of_adj hx he.adj⟩)
    (fun hx ↦ ⟨hx, S.right_mem_of_adj hx he.adj⟩), by tauto⟩

lemma edge_mem_or_mem (S : G.Separation) (he : e ∈ E(G)) :
    e ∈ E(G[S.left]) ∨ e ∈ E(G[S.right]) := by
  have := S.eq_union
  apply_fun edgeSet at this
  rwa [this, union_edgeSet] at he

lemma vertexSet_nontrivial (S : G.Separation) : V(G).Nontrivial :=
  ⟨_, S.left_subset S.nonempty_left.some_mem, _, S.right_subset S.nonempty_right.some_mem,
    S.disjoint.ne_of_mem S.nonempty_left.some_mem S.nonempty_right.some_mem⟩

lemma induce_left_isClosedSubgraph (S : G.Separation) : G[S.left].IsClosedSubgraph G where
  le := by simp [S.left_subset]
  closed e x hex hx := by
    contrapose! hx
    have := hex.of_le_of_mem (by simp [S.right_subset])
      (S.edge_mem_or_mem hex.edge_mem |>.resolve_left hx) |>.vertex_mem
    simp only [induce_vertexSet] at this ⊢
    rwa [S.not_left_mem_iff hex.vertex_mem]

def of_not_connectedBetween (h : ¬ G.ConnectedBetween x y) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    G.Separation where
  left := {y ∈ V(G) | G.ConnectedBetween x y}
  right := {y ∈ V(G) | ¬ G.ConnectedBetween x y}
  nonempty_left := ⟨x, by simpa⟩
  nonempty_right := ⟨y, by simpa [h]⟩
  disjoint := by
    rw [disjoint_iff_forall_notMem]
    rintro z ⟨hz, hxz⟩ ⟨_, hyz⟩
    exact hyz hxz
  union_eq := by
    ext z
    by_cases hz : G.ConnectedBetween x z <;> simp [hz]
  not_adj a b ha hb hab := by
    simp only [mem_setOf_eq] at ha hb
    exact hb.2 <| ha.2.trans hab.connectedBetween

end Separation

/-- A graph is preconnected if the graph has no separation. -/
def Preconnected (G : Graph α β) : Prop := IsEmpty G.Separation

lemma preconnected_of_vertexSet_subsingleton (hV : V(G).Subsingleton) : G.Preconnected := by
  contrapose! hV
  obtain ⟨S⟩ := by simpa only [Preconnected, not_isEmpty_iff] using hV
  exact S.vertexSet_nontrivial

lemma Separation.not_connectedBetween (S : G.Separation) (hx : x ∈ S.left) (hy : y ∈ S.right) :
    ¬ G.ConnectedBetween x y := by
  intro h
  obtain ⟨W, hW, rfl, rfl⟩ := h
  rw [← S.not_left_mem_iff (S.right_subset hy)] at hy
  obtain ⟨e, x, y, hinc, hx, hy⟩ := exists_dInc_prop_not_prop hx hy
  exact hy <| S.left_mem_of_adj hx (hW.isLink_of_dInc hinc).adj

lemma exists_separation_of_not_connectedBetween (hxV : x ∈ V(G)) (hyV : y ∈ V(G))
    (hxy : ¬ G.ConnectedBetween x y) : ∃ S : G.Separation, x ∈ S.left ∧ y ∈ S.right :=
  ⟨⟨{w ∈ V(G) | G.ConnectedBetween x w}, {w ∈ V(G) | ¬ G.ConnectedBetween x w}, ⟨x, by simpa⟩,
    ⟨y, by aesop⟩, by simp +contextual [disjoint_left],
    by simp [Set.ext_iff, ← and_or_left, or_not],
    fun x' y' ⟨_, hx'⟩ ⟨_, hy'⟩ hxy' ↦  hy' <| hx'.trans hxy'.connectedBetween⟩, by simp_all⟩

lemma preconnected_iff_forall_connectedBetween :
    G.Preconnected ↔ ∀ {x y}, x ∈ V(G) → y ∈ V(G) → G.ConnectedBetween x y := by
  rw [← not_iff_not]
  simp only [Preconnected, not_isEmpty_iff, not_forall]
  refine ⟨fun ⟨S⟩ => ?_, fun ⟨x, y, hx, hy, h⟩ => ?_⟩
  · use S.nonempty_left.some, S.nonempty_right.some, S.left_subset S.nonempty_left.some_mem,
      S.right_subset S.nonempty_right.some_mem, S.not_connectedBetween S.nonempty_left.some_mem
      S.nonempty_right.some_mem
  obtain ⟨S, hxL, hyR⟩ := exists_separation_of_not_connectedBetween hx hy h
  exact ⟨S⟩

/- ### Connectedness -/

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

lemma ConnectedBetween.mem_walkable (h : G.ConnectedBetween x y) : y ∈ V(G.walkable x) := h

/-- If `G` has one vertex connected to all others, then `G` is connected. -/
lemma connected_of_vertex (hu : u ∈ V(G)) (h : ∀ y ∈ V(G), G.ConnectedBetween y u) :
    G.Connected := by
  have hco := walkable_isCompOf hu
  rwa [walkable_isClosedSubgraph.eq_ambient_of_subset_vertexSet (h · · |>.symm)] at hco

lemma connectedBetween_iff_mem_walkable_of_mem :
    G.ConnectedBetween x y ↔ y ∈ V(G.walkable x) := Iff.rfl

lemma Connected.connectedBetween (h : G.Connected) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    G.ConnectedBetween x y := by
  rwa [connectedBetween_iff_mem_walkable_of_mem, ← h.eq_walkable_of_mem_walkable hx]

lemma connected_iff : G.Connected ↔ V(G).Nonempty ∧ G.Preconnected := by
  rw [preconnected_iff_forall_connectedBetween]
  exact ⟨fun h => ⟨h.nonempty, h.connectedBetween⟩,
    fun ⟨hne, h⟩ => connected_of_vertex hne.some_mem (fun a b => h b hne.some_mem)⟩

/-- A graph has `PreconnectivityGe n`, if for every pair of vertices `s` and `t`, there is no
    `n`-vertex cut between them. -/
def PreconnectivityGe (G : Graph α β) (n : ℕ) : Prop :=
  ∀ {s t}, s ∈ V(G) → t ∈ V(G) → G.ConnectivityBetweenGe s t n

def ConnectivityGe (G : Graph α β) (n : ℕ) : Prop :=
  ∀ {X}, X.encard < ↑n → (G - X).Connected

def EdgeConnectivityGe (G : Graph α β) (n : ℕ) : Prop :=
  ∀ {s t}, s ∈ V(G) → t ∈ V(G) → G.EdgeConnectivityBetweenGe s t n

@[simp]
lemma PreconnectivityGe_zero : G.PreconnectivityGe 0 := by
  simp [PreconnectivityGe]

lemma PreconnectivityGe.anti_right (hle : n ≤ m) (h : G.PreconnectivityGe m) :
    G.PreconnectivityGe n := by
  intro s t hs ht
  exact h hs ht |>.anti_right hle

@[simp]
lemma preconnectivityGe_one_iff : G.PreconnectivityGe 1 ↔ G.Preconnected := by
  simp [preconnected_iff_forall_connectedBetween, PreconnectivityGe, connectivityBetweenGe_one_iff]

@[simp]
lemma ConnectivityGe_zero : G.ConnectivityGe 0 := by
  simp [ConnectivityGe]

lemma ConnectivityGe.anti_right (hle : n ≤ m) (h : G.ConnectivityGe m) : G.ConnectivityGe n :=
  (h <| lt_of_lt_of_le · (by norm_cast))

@[simp]
lemma connectivityGe_one_iff : G.ConnectivityGe 1 ↔ G.Connected := by
  simp [ConnectivityGe, cast_one, ENat.lt_one_iff_eq_zero]

@[simp]
lemma EdgeConnectivityGe_zero : G.EdgeConnectivityGe 0 := by
  simp [EdgeConnectivityGe]

lemma EdgeConnectivityGe.anti_right (hle : n ≤ m) (h : G.EdgeConnectivityGe m) :
    G.EdgeConnectivityGe n := by
  intro s t hs ht
  exact h hs ht |>.anti_right hle

@[simp]
lemma edgeConnectivityGe_one_iff : G.EdgeConnectivityGe 1 ↔ G.Preconnected := by
  simp [EdgeConnectivityGe, edgeConnectivityBetweenGe_one_iff,
    preconnected_iff_forall_connectedBetween]

end Graph
