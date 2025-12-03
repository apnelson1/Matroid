import Matroid.Graph.Connected.Component
import Matroid.Graph.Connected.Set.Defs

open Set Function Nat WList

variable {α β : Type*} {G H K : Graph α β} {s t u v x x₁ x₂ y y₁ y₂ z : α} {n m : ℕ}
  {e e' f g : β} {U V S S' T T' X Y : Set α} {F F' R R': Set β} {C W P Q : WList α β}

@[simp]
lemma isLeast_empty {α : Type*} [LE α] {m : α} : ¬ IsLeast ∅ m := by
  simp [IsLeast]

theorem diff_nonempty_of_encard_lt_encard {s t : Set α} (h : s.encard < t.encard) :
    (t \ s).Nonempty := by
  rw [Set.nonempty_iff_ne_empty, Ne, diff_eq_empty]
  exact fun h' ↦ h.not_ge (encard_le_encard h')

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
  simp +contextual only [induce_isLink, iff_def, true_and]
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

lemma not_connectedBetween (S : G.Separation) (hx : x ∈ S.left) (hy : y ∈ S.right) :
    ¬ G.ConnectedBetween x y := by
  rintro ⟨W, hW, rfl, rfl⟩
  rw [← S.not_left_mem_iff (S.right_subset hy)] at hy
  obtain ⟨e, x, y, hinc, hx, hy⟩ := exists_dInc_prop_not_prop hx hy
  exact hy <| S.left_mem_of_adj hx (hW.isLink_of_dInc hinc).adj

def cutBetween_of_vertexDelete (S : (G - X).Separation) (hx : x ∈ S.left)
    (hy : y ∈ S.right) : G.CutBetween x y where
  carrier := V(G) ∩ X
  carrier_subset := inter_subset_left
  left_not_mem := by simp [(S.left_subset hx).2]
  right_not_mem := by simp [(S.right_subset hy).2]
  not_connectedBetween' := by
    rw [vertexDelete_vertexSet_inter]
    exact S.not_connectedBetween hx hy

@[simp]
lemma cutBetween_of_vertexDelete_coe (S : (G - X).Separation) (hx : x ∈ S.left)
    (hy : y ∈ S.right) : (S.cutBetween_of_vertexDelete hx hy : Set α) = V(G) ∩ X := rfl

end Separation

/-- A graph is preconnected if for every pair of vertices, there is a path between them. -/
def Preconnected (G : Graph α β) : Prop :=
  ∀ x y, x ∈ V(G) → y ∈ V(G) → G.ConnectedBetween x y

lemma exists_separation_of_not_connectedBetween (hxV : x ∈ V(G)) (hyV : y ∈ V(G))
    (hxy : ¬ G.ConnectedBetween x y) : ∃ S : G.Separation, x ∈ S.left ∧ y ∈ S.right :=
  ⟨⟨{w ∈ V(G) | G.ConnectedBetween x w}, {w ∈ V(G) | ¬ G.ConnectedBetween x w}, ⟨x, by simpa⟩,
    ⟨y, by aesop⟩, by simp +contextual [disjoint_left],
    by simp [Set.ext_iff, ← and_or_left, or_not],
    fun x' y' ⟨_, hx'⟩ ⟨_, hy'⟩ hxy' ↦  hy' <| hx'.trans hxy'.connectedBetween⟩, by simp_all⟩

lemma preconnected_iff_isEmpty_separation : G.Preconnected ↔ IsEmpty G.Separation := by
  rw [← not_iff_not]
  simp only [Preconnected, not_isEmpty_iff, not_forall]
  refine ⟨fun ⟨x, y, hx, hy, h⟩ => ?_, fun ⟨S⟩ => ?_⟩
  · obtain ⟨S, hxL, hyR⟩ := exists_separation_of_not_connectedBetween hx hy h
    exact ⟨S⟩
  use S.nonempty_left.some, S.nonempty_right.some, S.left_subset S.nonempty_left.some_mem,
    S.right_subset S.nonempty_right.some_mem, S.not_connectedBetween S.nonempty_left.some_mem
    S.nonempty_right.some_mem
alias ⟨Preconnected.separation_isEmpty, _⟩ := preconnected_iff_isEmpty_separation

lemma preconnected_of_vertexSet_subsingleton (hV : V(G).Subsingleton) : G.Preconnected := by
  rw [preconnected_iff_isEmpty_separation]
  contrapose! hV
  obtain ⟨S⟩ := by simpa only [Preconnected, not_isEmpty_iff] using hV
  exact S.vertexSet_nontrivial

lemma Preconnected.isSpanningSubgraph (h : H.Preconnected) (hsle : H ≤s G) : G.Preconnected :=
  fun s t hs ht ↦ (h s t (hsle.vertexSet_eq ▸ hs) (hsle.vertexSet_eq ▸ ht)).of_le hsle.le

@[simp]
lemma IsComplete.preconnected (h : G.IsComplete) : G.Preconnected := by
  intro s t hs ht
  obtain rfl | hne := eq_or_ne s t
  · simpa
  exact h s hs t ht hne |>.connectedBetween

/- ### Connectedness -/

/-- A graph is connected if it is a minimal closed subgraph of itself -/
protected def Connected (G : Graph α β) : Prop := G.IsCompOf G

lemma Connected.nonempty (hG : G.Connected) : V(G).Nonempty := by
  rw [Graph.Connected, IsCompOf] at hG
  exact hG.prop.2

@[simp]
lemma bot_not_connected : ¬ (⊥ : Graph α β).Connected := by
  rintro h
  simpa using h.nonempty

lemma Connected.ne_bot (hG : G.Connected) : G ≠ ⊥ := by
  rintro rfl
  exact bot_not_connected hG

lemma connected_iff_forall_closed (hG : V(G).Nonempty) :
    G.Connected ↔ ∀ ⦃H⦄, H ≤c G → V(H).Nonempty → H = G := by
  refine ⟨fun h H hHG hHne ↦ ?_, fun h ↦ ⟨by simpa, fun H ⟨hle, hH⟩ _ ↦ (h hle hH).symm.le⟩⟩
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

lemma Connected.pre (h : G.Connected) : G.Preconnected :=
  fun _ _ ↦ h.connectedBetween

lemma Separation.not_connected (S : G.Separation) : ¬ G.Connected := by
  obtain ⟨x, hx⟩ := S.nonempty_left
  obtain ⟨y, hy⟩ := S.nonempty_right
  exact fun h ↦ S.not_connectedBetween hx hy <| h.connectedBetween (S.left_subset hx)
    (S.right_subset hy)

lemma Connected.isEmpty_separation (hG : G.Connected) : IsEmpty G.Separation :=
  isEmpty_iff.2 fun S ↦ S.not_connected hG

lemma connected_iff : G.Connected ↔ V(G).Nonempty ∧ G.Preconnected :=
  ⟨fun h => ⟨h.nonempty, h.pre⟩,
    fun ⟨hne, h⟩ => connected_of_vertex hne.some_mem (fun _ b => h _ _ b hne.some_mem)⟩

lemma preconnected_iff : G.Preconnected ↔ G = ⊥ ∨ G.Connected := by
  rw [connected_iff]
  obtain h | h := G.eq_bot_or_vertexSet_nonempty <;> simp [h, G.ne_bot_iff]

lemma nonempty_separation_of_not_connected (hne : V(G).Nonempty) (hG : ¬ G.Connected) :
    Nonempty G.Separation := by
  obtain ⟨x, y, hx, hy, hxy⟩ := by simpa only [Preconnected, hne,
    connected_iff, true_and, not_forall] using hG
  exact ⟨(exists_separation_of_not_connectedBetween hx hy hxy).choose⟩

lemma Connected.isSpanningSubgraph (h : H.Connected) (hsle : H ≤s G) : G.Connected := by
  rw [connected_iff] at h ⊢
  exact ⟨hsle.vertexSet_eq ▸ h.1, h.2.isSpanningSubgraph hsle⟩

@[simp]
lemma IsComplete.connected_iff (h : G.IsComplete) : G.Connected ↔ V(G).Nonempty := by
  simp [h, Graph.connected_iff]

/-! ### Cut -/

structure Cut (G : Graph α β) where
  carrier : Set α
  carrier_subset : carrier ⊆ V(G)
  not_connected' : ¬ (G - carrier).Connected

instance : SetLike (G.Cut) α where
  coe := (·.carrier)
  coe_injective' C1 C2 h := by rwa [Cut.mk.injEq]

@[simp]
lemma Cut.coe_subset (C : G.Cut) : (C : Set α) ⊆ V(G) := C.carrier_subset

@[simp]
lemma Cut.not_connected (C : G.Cut) : ¬ (G - C).Connected := C.not_connected'

def cut_empty (h : ¬ G.Connected) : G.Cut where
  carrier := ∅
  carrier_subset := empty_subset _
  not_connected' := by simpa

@[simp]
lemma cut_empty_coe (h : ¬ G.Connected) : (cut_empty h : Set α) = ∅ := rfl

def cut_vertexSet : G.Cut where
  carrier := V(G)
  carrier_subset := refl _
  not_connected' := by simp

@[simp]
lemma cut_vertexSet_coe : (G.cut_vertexSet : Set α) = V(G) := rfl

def Cut.of_not_connected (h : ¬ (G - X).Connected) : G.Cut where
  carrier := V(G) ∩ X
  carrier_subset := inter_subset_left
  not_connected' := by rwa [vertexDelete_vertexSet_inter]

@[simp]
lemma Cut.of_not_connected_coe (h : ¬ (G - X).Connected) :
    (Cut.of_not_connected h : Set α) = V(G) ∩ X := rfl

def Cut.of_vertexDelete (C : (G - X).Cut) : G.Cut where
  carrier := C ∪ (V(G) ∩ X)
  carrier_subset := by
    have := by simpa [subset_diff] using C.coe_subset
    simp [this.1]
  not_connected' := by
    rw [union_comm, ← vertexDelete_vertexDelete, vertexDelete_vertexSet_inter]
    exact C.not_connected

@[simp]
lemma Cut.of_vertexDelete_coe (C : (G - X).Cut) :
    (Cut.of_vertexDelete C : Set α) = ↑C ∪ (V(G) ∩ X) := rfl

def Cut.of_isSpanningSubgraph (hsle : H ≤s G) (C : G.Cut) : H.Cut where
  carrier := C
  carrier_subset := by simp [hsle.vertexSet_eq]
  not_connected' h := C.not_connected (h.isSpanningSubgraph <| by gcongr)

@[mk_iff]
structure IsSepSet (G : Graph α β) (S : Set α) : Prop where
  subset_vx : S ⊆ V(G)
  not_connected : ¬ (G - S).Connected

@[mk_iff]
structure IsMinSepSet (G : Graph α β) (S : Set α) : Prop extends IsSepSet G S where
  minimal : ∀ A, IsSepSet G A → S.encard ≤ A.encard

lemma IsMinSepSet.not_isSepSet_of_encard_lt (hM : IsMinSepSet G S) (hSS' : S'.encard < S.encard) :
    ¬ IsSepSet G S' := by
  by_contra hc
  grw [hM.2 S' hc, lt_self_iff_false S'.encard] at hSS'
  exact hSS'

lemma connected_of_not_isSepSet (hV : S ⊆ V(G)) (hS : ¬ IsSepSet G S) : (G - S).Connected := by
  by_contra hc
  exact hS ⟨hV, hc⟩

structure Sep (G : Graph α β) where
  left : Set α
  right : Set α
  carrier : Set α
  nonempty_left : left.Nonempty
  nonempty_right : right.Nonempty
  disjoint_left_right : Disjoint left right
  disjoint_left_carrier : Disjoint left carrier
  disjoint_right_carrier : Disjoint right carrier
  union_eq : left ∪ carrier ∪ right = V(G)
  not_adj : ∀ ⦃x y⦄, x ∈ left → y ∈ right → ¬ G.Adj x y

@[simps]
def IsClosedSubgraph.Sep (hH : H ≤c (G - S)) (hVH : V(H).Nonempty) (huV : u ∈ V(G))
    (hu : u ∉ S ∪ V(H)) : G.Sep where
  left := V(H)
  right := V(G - S) \ V(H)
  carrier := V(G) ∩ S
  nonempty_left := hVH
  nonempty_right := ⟨u, by simpa [huV] using hu⟩
  disjoint_left_right := disjoint_sdiff_right
  disjoint_left_carrier := by
    have := by simpa [subset_diff] using hH.vertexSet_mono
    exact this.2.mono_right inter_subset_right
  disjoint_right_carrier := by
    simp only [vertexDelete_vertexSet]
    exact disjoint_sdiff_inter.mono_left diff_subset
  union_eq := by
    ext x
    simp only [vertexDelete_vertexSet, mem_union, mem_inter_iff, mem_diff, iff_def]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ((h | h) | h) := h
      · exact hH.vertexSet_mono h |>.1
      all_goals simp_all only
    by_cases hx : x ∈ S <;> simp_all [em (x ∈ V(H))]
  not_adj x y hx hy hadj := by
    have hadj' := G.vertexDelete_isInducedSubgraph S |>.adj_of_adj hadj (hH.vertexSet_mono hx) hy.1
    rw [hH.mem_iff_mem_of_adj hadj'] at hx
    exact hy.2 hx

@[simps!]
def IsCompOf.Sep (hH : H.IsCompOf (G - S)) (huV : u ∈ V(G)) (hu : u ∉ S ∪ V(H)) : G.Sep :=
  hH.isClosedSubgraph.Sep hH.nonempty huV hu

structure EdgeCut (G : Graph α β) where
  carrier : Set β
  carrier_subset : carrier ⊆ E(G)
  not_connected' : ¬ (G ＼ carrier).Connected

instance : SetLike (G.EdgeCut) β where
  coe := (·.carrier)
  coe_injective' C1 C2 h := by rwa [EdgeCut.mk.injEq]

@[simp]
lemma EdgeCut.coe_subset (C : G.EdgeCut) : (C : Set β) ⊆ E(G) := C.carrier_subset

@[simp]
lemma EdgeCut.not_connected (C : G.EdgeCut) : ¬ (G ＼ C).Connected := C.not_connected'

def edgeCut_empty (h : ¬ G.Connected) : G.EdgeCut where
  carrier := ∅
  carrier_subset := empty_subset _
  not_connected' := by simpa

@[simp]
lemma edgeCut_empty_coe (h : ¬ G.Connected) : (edgeCut_empty h : Set β) = ∅ := rfl

structure MixedCut (G : Graph α β) where
  vertexSet : Set α
  edgeSet : Set β
  vertexSet_subset : vertexSet ⊆ V(G)
  edgeSet_subset : edgeSet ⊆ E(G)
  not_conn' : ¬ ((G ＼ edgeSet)- vertexSet).Connected

@[simps]
def mixedCut_of_cut (C : G.Cut) : G.MixedCut where
  vertexSet := ↑C
  edgeSet := ∅
  vertexSet_subset := C.coe_subset
  edgeSet_subset := empty_subset _
  not_conn' := by simp

@[simps]
def mixedCut_of_edgeCut (F : G.EdgeCut) : G.MixedCut where
  vertexSet := ∅
  edgeSet := F
  vertexSet_subset := empty_subset _
  edgeSet_subset := F.coe_subset
  not_conn' := by simp

@[simps]
def MixedCut.of_isSpanningSubgraph (C : G.MixedCut) (hle : H ≤s G) : H.MixedCut where
  vertexSet := V(H) ∩ C.vertexSet
  edgeSet := E(H) ∩ C.edgeSet
  vertexSet_subset := inter_subset_left
  edgeSet_subset := inter_subset_left
  not_conn' := by
    rw [edgeDelete_edgeSet_inter, ← edgeDelete_vertexSet, vertexDelete_vertexSet_inter]
    have := C.not_conn'
    contrapose! this
    apply this.isSpanningSubgraph
    gcongr

/-- A graph has `PreconnGe n`, if for every pair of vertices `s` and `t`, there is no
    `n`-vertex cut between them.
    In the case of complete graphs, K_n, ∀ κ, K_n.PreconnGe κ. -/
def PreconnGe (G : Graph α β) (n : ℕ) : Prop :=
  ∀ ⦃s t⦄, s ∈ V(G) → t ∈ V(G) → G.ConnBetweenGe s t n

/-- A graph has `ConnGe n`, if mixed cut, the size of the cut is at least `n`. In the case of
    complete graphs, K_n, K_n.ConnGe n. -/
def ConnGe (G : Graph α β) (n : ℕ) : Prop :=
  ∀ C : G.MixedCut, n ≤ C.vertexSet.encard + C.edgeSet.encard

/-- A graph has `EdgeConnGe n`, if for every pair of vertices `s` and `t`, there is no
    `n`-edge cut between them. -/
def EdgeConnGe (G : Graph α β) (n : ℕ) : Prop :=
  ∀ ⦃s t⦄, s ∈ V(G) → t ∈ V(G) → G.EdgeConnBetweenGe s t n

@[simp]
lemma PreconnGe_zero : G.PreconnGe 0 := by
  simp [PreconnGe]

lemma PreconnGe.anti_right (hle : n ≤ m) (h : G.PreconnGe m) :
    G.PreconnGe n := by
  intro s t hs ht
  exact h hs ht |>.anti_right hle

@[simp]
lemma preconnGe_one_iff : G.PreconnGe 1 ↔ G.Preconnected := by
  simp [PreconnGe, connBetweenGe_one_iff, Preconnected]

lemma preconnGe_iff_forall_connBetweenGe :
    G.PreconnGe n ↔ ∀ ⦃s t⦄, s ∈ V(G) → t ∈ V(G) → G.ConnBetweenGe s t n := Iff.rfl

lemma preconnGe_iff_forall_preconnected :
    G.PreconnGe n ↔ ∀ ⦃X⦄, X.encard < ↑n → (G - X).Preconnected := by
  refine ⟨fun h X hX => ?_, fun h s t hs ht C => ?_⟩
  · rw [preconnected_iff_isEmpty_separation]
    by_contra! hS
    obtain ⟨S⟩ := hS
    have := h (diff_subset <| S.left_subset S.nonempty_left.some_mem)
      (diff_subset <| S.right_subset S.nonempty_right.some_mem)
      <| S.cutBetween_of_vertexDelete S.nonempty_left.some_mem S.nonempty_right.some_mem
    simp only [Separation.cutBetween_of_vertexDelete_coe] at this
    exact this.trans (encard_le_encard inter_subset_right) |>.not_gt hX
  · by_contra! hC
    exact C.not_connectedBetween' <| h hC _ _ (by simpa) (by simpa)

lemma preconnGe_iff_forall_setConnGe : G.PreconnGe n ↔ ∀ S T : Set α, S ⊆ V(G) → T ⊆ V(G) →
    G.SetConnGe S T (min ↑n (min S.encard T.encard)).toNat := by
  refine ⟨fun h S T hS hT C hC ↦ ?_, fun h s t hs ht C ↦ ?_⟩
  · rw [ENat.coe_toNat (by simp)]
    by_contra! hCcd
    obtain ⟨hCn, hCS, hCT⟩ := (by simpa using hCcd); clear hCcd
    obtain ⟨s, hs, hsC⟩ := diff_nonempty_of_encard_lt_encard hCS
    obtain ⟨t, ht, htC⟩ := diff_nonempty_of_encard_lt_encard hCT
    have := by simpa [SetConnected] using hC.ST_disconnects
    exact hCn.not_ge <| h (hS hs) (hT ht) ⟨C, hC.subset_vertexSet, hsC, htC, this s hs t ht⟩
  obtain hCinfty | hCFin := eq_or_ne (C : Set α).encard ⊤
  · exact StrictMono.maximal_preimage_top (fun ⦃a b⦄ a_1 ↦ a_1) hCinfty ↑n
  simp only [ne_eq, encard_eq_top_iff, not_infinite] at hCFin
  have hsC : (C : Set α).encard < Set.encard (insert s C) :=
    hCFin.encard_lt_encard (ssubset_insert C.left_notMem)
  have htC : (C : Set α).encard < Set.encard (insert t C) :=
    hCFin.encard_lt_encard (ssubset_insert C.right_notMem)
  have hcd := h _ _ (by simpa [insert_subset_iff]) (by simpa [insert_subset_iff]) C.isSetCut
  rw [ENat.coe_toNat (by simp)] at hcd
  simpa [hsC.not_ge, htC.not_ge] using hcd

lemma PreconnGe.isSpanningSubgraph (hconn : H.PreconnGe n) (hsle : H ≤s G) :
    G.PreconnGe n :=
  fun _ _ hs ht C ↦ hconn (hsle.vertexSet_eq ▸ hs) (hsle.vertexSet_eq ▸ ht) |>.of_le hsle.le C

@[simp]
lemma IsComplete.preconnGe (h : G.IsComplete) (n : ℕ) : G.PreconnGe n :=
  fun _ _ hs ht ↦ h.connBetweenGe hs ht n

-- lemma PreconnGe.edgeDelete_singleton_of_not_isComplete (h : G.PreconnGe n)
--     (hne : ¬ G.IsComplete) (e : β) : (G ＼ {e}).PreconnGe (n - 1) := by
--   obtain he | he := (em <| e ∈ E(G)).symm
--   · rw [edgeDelete_eq_self _ (by simpa)]
--     exact h.anti_right (by omega)
--   rintro s t hs ht


@[simp]
lemma ConnGe_zero : G.ConnGe 0 := by
  simp [ConnGe]

lemma ConnGe.anti_right (hle : n ≤ m) (h : G.ConnGe m) : G.ConnGe n :=
  fun C ↦ (by norm_cast : (n : ℕ∞) ≤ ↑m).trans (h C)

@[simp]
lemma connGe_one_iff : G.ConnGe 1 ↔ G.Connected := by
  refine ⟨fun h ↦ ?_, fun h C ↦ ?_⟩
  · by_contra! hc
    simpa using h <| mixedCut_of_cut <| cut_empty hc
  by_contra! hCcd
  simp only [cast_one, ENat.lt_one_iff_eq_zero, add_eq_zero, encard_eq_zero] at hCcd
  simpa [hCcd.1, hCcd.2, h] using C.not_conn'

lemma ConnGe.pre (h : G.ConnGe n) : G.PreconnGe n := by
  rw [preconnGe_iff_forall_preconnected]
  intro X hX
  by_contra! hc
  have := mt Connected.pre hc
  have := by simpa using h ⟨V(G) ∩ X, ∅, inter_subset_left, empty_subset _, by simpa⟩
  exact hX.not_ge <| this.trans <| encard_le_encard inter_subset_right

lemma ConnGe.le_card (h : G.ConnGe n) : n ≤ ENat.card V(G) := by
  simpa using h <| mixedCut_of_cut <| G.cut_vertexSet

-- lemma preconnGe_iff_connGe_of_not_isComplete (h : ¬ G.IsComplete) (n : ℕ) :
--     G.PreconnGe n ↔ G.ConnGe n := by
--   refine ⟨fun hn C ↦ ?_, fun hn ↦ hn.pre⟩

--   sorry

lemma ConnGe.isSpanningSubgraph (h : H.ConnGe n) (hsle : H ≤s G) : G.ConnGe n := by
  intro C
  have := by simpa using h <| C.of_isSpanningSubgraph hsle
  exact this.trans <| add_le_add (encard_le_encard inter_subset_right)
    (encard_le_encard inter_subset_right)

lemma ConnGe.of_edgeDelete (h : (G ＼ F).ConnGe n) : G.ConnGe n :=
  h.isSpanningSubgraph edgeDelete_isSpanningSubgraph

-- lemma ConnGe.mt (h : G.ConnGe n) (hconn : ¬ (G - X).Connected) :
--     n ≤ X.encard := by
--   by_contra! hcd
--   rw [connGe_iff_forall_connected] at h
--   exact hconn (h hcd)

-- lemma ConnGe.vertexDelete (h : G.ConnGe n) (X : Set α) :
--     (G - X).ConnGe (n - (V(G) ∩ X).encard).toNat := by
--   rw [connGe_iff_forall_connected] at h ⊢
--   rintro C hC
--   rw [ENat.coe_toNat (by simp), lt_tsub_iff_right] at hC
--   rw [← G.vertexDelete_vertexSet_inter X, vertexDelete_vertexDelete, union_comm]
--   exact h <| lt_of_le_of_lt (encard_union_le _ _) hC

@[simp]
lemma EdgeConnGe_zero : G.EdgeConnGe 0 := by
  simp [EdgeConnGe]

lemma EdgeConnGe.anti_right (hle : n ≤ m) (h : G.EdgeConnGe m) : G.EdgeConnGe n := by
  intro s t hs ht
  exact h hs ht |>.anti_right hle

@[simp]
lemma edgeConnGe_one_iff : G.EdgeConnGe 1 ↔ G.Preconnected := by
  simp [EdgeConnGe, edgeConnBetweenGe_one_iff, Preconnected]

end Graph
