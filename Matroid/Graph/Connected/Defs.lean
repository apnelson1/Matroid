module

public import Matroid.ForMathlib.Tactic.ENatToNat
public import Matroid.Graph.Connected.Component
public import Matroid.Graph.Map
public import Matroid.Graph.Connected.Set.Defs
public import Mathlib.Combinatorics.Graph.Delete
public import Matroid.Graph.Connected.Vertex.Basic

@[expose] public section

open Set Function Nat WList
variable {α β : Type*} {G H K : Graph α β} {s t u v x x₁ x₂ y y₁ y₂ z : α} {n m : ℕ}
  {e e' f g : β} {U V S S' T T' X Y : Set α} {F F' R R': Set β} {C W P Q : WList α β}

@[simp]
lemma isLeast_empty {α : Type*} [LE α] {m : α} : ¬ IsLeast ∅ m := by
  simp [IsLeast]

theorem diff_nonempty_of_encard_lt_encard {s t : Set α} (h : s.encard < t.encard) :
    (t \ s).Nonempty := by
  rw [Set.nonempty_iff_ne_empty, Ne, sdiff_eq_empty]
  exact fun h' ↦ h.not_ge (encard_le_encard h')

namespace Graph

@[gcongr]
lemma ConnBetween.walkable_eq_walkable (h : G.ConnBetween x y) : G.walkable x = G.walkable y :=
  walkable_eq_walkable_of_mem h.symm

/-! ### Connectivity on a graph -/

/-- A graph is preconnected if for every pair of vertices, there is a path between them. -/
def Preconnected (G : Graph α β) : Prop :=
  ∀ x y, x ∈ V(G) → y ∈ V(G) → G.ConnBetween x y

lemma Preconnected.isSpanningSubgraph (h : H.Preconnected) (hsle : H ≤s G) : G.Preconnected :=
  fun s t hs ht ↦ (h s t (hsle.vertexSet_eq ▸ hs) (hsle.vertexSet_eq ▸ ht)).mono hsle.le

@[simp]
lemma IsComplete.preconnected (h : G.IsComplete) : G.Preconnected := by
  intro s t hs ht
  obtain rfl | hne := eq_or_ne s t
  · simpa
  exact h s hs t ht hne |>.connBetween

lemma preconnected_bot : Preconnected (⊥ : Graph α β) :=
  bot_isComplete.preconnected

lemma preconnected_of_exists_connBetween (h : ∃ x, ∀ y ∈ V(G), G.ConnBetween x y) :
    G.Preconnected := by
  obtain ⟨x, hx⟩ := h
  exact fun s t hs ht ↦ (hx s hs).symm.trans <| hx t ht

lemma preconnected_iff_exists_connBetween (hx : x ∈ V(G)) :
    G.Preconnected ↔ ∀ y ∈ V(G), G.ConnBetween x y := by
  refine ⟨fun h => fun y hy ↦ h x y hx hy, fun hx => ?_⟩
  exact fun s t hs ht ↦ (hx s hs).symm.trans <| hx t ht

@[simp]
lemma preconnected_edgeMap_iff {β' : Type*} {φ : β → β'} {hφ} :
    (G.edgeMap φ hφ).Preconnected ↔ G.Preconnected := by
  simp [Preconnected]

lemma preconnected_map_iff_of_injOn {α' : Type*} {φ : α → α'} (hφ : InjOn φ V(G)) :
    (φ ''ᴳ G).Preconnected ↔ G.Preconnected := by
  simp only [Preconnected, vertexSet_map, mem_image, forall_exists_index, and_imp]
  refine ⟨fun h x y hx hy ↦ ?_, ?_⟩
  · exact (connBetween_map_iff_of_injOn hφ hx hy).1 <| h _ _ _ hx rfl _ hy rfl
  rintro h _ _ x hx rfl y hy rfl
  rw [connBetween_map_iff_of_injOn hφ hx hy]
  exact h x y hx hy

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
  refine ⟨⟨hK.isClosedSubgraph.anti_right Graph.inter_le_left h.le, by simpa⟩, ?_⟩
  intro P ⟨hPH, hP⟩ hle
  rw [hK.eq_of_le ⟨?_, hP⟩ hle]
  exact (hPH.anti_right hle Graph.inter_le_left).trans hK.isClosedSubgraph

lemma IsCompOf.of_le_le (h : K.IsCompOf G) (hKH : K ≤ H) (hHG : H ≤ G) : K.IsCompOf H := by
  refine ⟨⟨h.isClosedSubgraph.anti_right hKH hHG, h.nonempty⟩, fun K' ⟨hK'H, hK'ne⟩ hK'K ↦ ?_⟩
  exact h.le_of_le ⟨(hK'H.anti_right hK'K hKH).trans h.isClosedSubgraph, hK'ne⟩ hK'K

lemma ConnBetween.mem_walkable (h : G.ConnBetween x y) : y ∈ V(G.walkable x) := h

/-- If `G` has one vertex connected to all others, then `G` is connected. -/
lemma connected_of_vertex (hu : u ∈ V(G)) (h : ∀ y ∈ V(G), G.ConnBetween y u) :
    G.Connected := by
  have hco := walkable_isCompOf hu
  rwa [walkable_isClosedSubgraph.eq_ambient_of_subset_vertexSet (h · · |>.symm)] at hco

lemma connBetween_iff_mem_walkable_of_mem :
    G.ConnBetween x y ↔ y ∈ V(G.walkable x) := Iff.rfl

lemma Connected.connBetween (h : G.Connected) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    G.ConnBetween x y := by
  rwa [connBetween_iff_mem_walkable_of_mem, ← h.eq_walkable_of_mem_walkable hx]

lemma Connected.pre (h : G.Connected) : G.Preconnected :=
  fun _ _ ↦ h.connBetween

lemma connected_iff : G.Connected ↔ V(G).Nonempty ∧ G.Preconnected :=
  ⟨fun h => ⟨h.nonempty, h.pre⟩,
    fun ⟨hne, h⟩ => connected_of_vertex hne.some_mem (fun _ b => h _ _ b hne.some_mem)⟩

lemma connected_map_iff_of_injOn {α' : Type*} {φ : α → α'} (hφ : InjOn φ V(G)) :
    (φ ''ᴳ G).Connected ↔ G.Connected := by
  rw [connected_iff, preconnected_map_iff_of_injOn hφ, connected_iff]
  simp

@[simp]
lemma connected_edgeMap_iff {β' : Type*} {φ : β → β'} {hφ} :
    (G.edgeMap φ hφ).Connected ↔ G.Connected := by
  simp [connected_iff]

lemma preconnected_iff : G.Preconnected ↔ G = ⊥ ∨ G.Connected := by
  rw [connected_iff]
  obtain h | h := G.eq_bot_or_vertexSet_nonempty <;> simp [h, G.ne_bot_iff]

lemma preconnected_iff_of_mem (hx : x ∈ V(G)) : G.Preconnected ↔ G.Connected := by
  simp [connected_iff, (show V(G).Nonempty from ⟨x, hx⟩)]

lemma connected_of_exists_connBetween (h : ∃ x ∈ V(G), ∀ y ∈ V(G), G.ConnBetween x y) :
    G.Connected := by
  obtain ⟨x, hx, h⟩ := h
  rw [connected_iff]
  exact ⟨⟨x, hx⟩, preconnected_of_exists_connBetween ⟨x, h⟩⟩

lemma connected_iff_exists_connBetween (hx : x ∈ V(G)) :
    G.Connected ↔ ∀ y ∈ V(G), G.ConnBetween x y := by
  rw [← preconnected_iff_of_mem hx, preconnected_iff_exists_connBetween hx]

lemma exists_not_connBetween_of_not_connected (h : ¬ G.Connected) (hx : x ∈ V(G)) :
    ∃ y ∈ V(G), ¬ G.ConnBetween x y := by
  simpa [connected_iff_exists_connBetween hx, not_forall] using h

lemma Connected.of_isSpanningSubgraph (h : H.Connected) (hsle : H ≤s G) : G.Connected := by
  rw [connected_iff] at h ⊢
  exact ⟨hsle.vertexSet_eq ▸ h.1, h.2.isSpanningSubgraph hsle⟩

lemma Preconnected.of_isSpanningSubgraph (h : H.Preconnected) (hsle : H ≤s G) : G.Preconnected := by
  rw [preconnected_iff] at *
  refine Or.imp ?_ (fun h ↦ h.of_isSpanningSubgraph hsle) h
  rintro rfl
  simpa using hsle

@[simp]
lemma IsComplete.connected_iff (h : G.IsComplete) : G.Connected ↔ V(G).Nonempty := by
  simp [h, Graph.connected_iff]

lemma Preconnected.eq_of_isClosedSubgraph (hG : G.Preconnected) (hH : H ≤c G) (hne : V(H).Nonempty):
    H = G := by
  refine Connected.eq_of_isClosedSubgraph ?_ hH hne
  rw [connected_iff]
  use (by use hne.some, hH.vertexSet_mono hne.some_mem)

lemma not_preconnected_of_ne_of_isClosedSubgraph {H₁ H₂ : Graph α β} (h₁ : H₁ ≤c G)
    (hV₁ : V(H₁).Nonempty) (h₂ : H₂ ≤c G) (hV₂ : V(H₂).Nonempty) (hdj : H₁ ≠ H₂) :
    ¬ G.Preconnected := by
  contrapose! hdj
  obtain rfl := hdj.eq_of_isClosedSubgraph h₂ hV₂
  exact hdj.eq_of_isClosedSubgraph h₁ hV₁

/-! ### Cut -/

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

@[simps (attr := grind =)]
def symm (S : G.Separation) : G.Separation where
  left := S.right
  right := S.left
  nonempty_left := S.nonempty_right
  nonempty_right := S.nonempty_left
  disjoint := S.disjoint.symm
  union_eq := by rw [← S.union_eq, union_comm]
  not_adj x y hx hy := by simpa [adj_comm] using S.not_adj hy hx

@[simp, grind .]
lemma left_ssubset (S : G.Separation) : S.left ⊂ V(G) := by
  obtain ⟨x, hx⟩ := S.nonempty_right
  exact ⟨S.left_subset, by grind [S.disjoint, S.union_eq]⟩

@[simp, grind .] lemma right_ssubset (S : G.Separation) : S.right ⊂ V(G) := S.symm.left_ssubset

@[simp] lemma symm_symm (S : G.Separation) : S.symm.symm = S := rfl

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
  simp only [edgeSet_induce, mem_ofPred_eq] at he he'
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
  rwa [this, edgeSet_union] at he

lemma vertexSet_nontrivial (S : G.Separation) : V(G).Nontrivial :=
  ⟨_, S.left_subset S.nonempty_left.some_mem, _, S.right_subset S.nonempty_right.some_mem,
    S.disjoint.ne_of_mem S.nonempty_left.some_mem S.nonempty_right.some_mem⟩

lemma induce_left_isClosedSubgraph (S : G.Separation) : G[S.left].IsClosedSubgraph G :=
  IsClosedSubgraph.mk' (by simp [S.left_subset]) fun e x hex hx => by
    contrapose! hx
    have := hex.of_le_of_mem (by simp [S.right_subset])
      (S.edge_mem_or_mem hex.edge_mem |>.resolve_left hx) |>.vertex_mem
    simp only [vertexSet_induce] at this ⊢
    rwa [S.not_left_mem_iff hex.vertex_mem]

lemma induce_right_isClosedSubgraph (S : G.Separation)  : G[S.right] ≤c G :=
  S.symm.induce_left_isClosedSubgraph

def of_not_connBetween (h : ¬ G.ConnBetween x y) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    G.Separation where
  left := {y ∈ V(G) | G.ConnBetween x y}
  right := {y ∈ V(G) | ¬ G.ConnBetween x y}
  nonempty_left := ⟨x, by simpa⟩
  nonempty_right := ⟨y, by simpa [h]⟩
  disjoint := by
    rw [disjoint_iff_forall_notMem]
    rintro z ⟨hz, hxz⟩ ⟨_, hyz⟩
    exact hyz hxz
  union_eq := by
    ext z
    by_cases hz : G.ConnBetween x z <;> simp [hz]
  not_adj a b ha hb hab := by
    simp only [mem_ofPred_eq] at ha hb
    exact hb.2 <| ha.2.trans hab.connBetween

lemma not_connBetween (S : G.Separation) (hx : x ∈ S.left) (hy : y ∈ S.right) :
    ¬ G.ConnBetween x y := by
  rintro ⟨W, hW, rfl, rfl⟩
  rw [← S.not_left_mem_iff (S.right_subset hy)] at hy
  obtain ⟨e, x, y, hinc, hx, hy⟩ := exists_dInc_prop_not_prop hx hy
  exact hy <| S.left_mem_of_adj hx (hW.isLink_of_dInc hinc).adj

theorem isSepBetween_of_deleteVerts (S : (G - X).Separation) (hx : x ∈ S.left)
    (hy : y ∈ S.right) : G.IsSepBetween x y (V(G) ∩ X) := by
  refine ⟨inter_subset_left, ?_, ?_, ?_⟩
  · simp [deleteVerts_vertexSet .. ▸ (S.left_subset hx) |>.2]
  · simp [deleteVerts_vertexSet .. ▸ (S.right_subset hy) |>.2]
  · simpa [deleteVerts_vertexSet_inter] using S.not_connBetween hx hy

lemma induce_stronglyDisjoint (S : G.Separation) : G[S.left].StronglyDisjoint G[S.right] where
  vertex := by simp only [vertexSet_induce, S.disjoint]
  edge := S.edge_induce_disjoint

lemma induce_left_lt (S : G.Separation) : G[S.left] < G :=
  lt_of_le_of_ne (S.induce_left_isClosedSubgraph.le) fun bad ↦ by grind [S.left_ssubset]

lemma induce_right_lt (S : G.Separation) : G[S.right] < G := S.symm.induce_left_lt

end Separation

lemma exists_mem_left_of_nonempty_separation (h : Nonempty G.Separation) (hx : x ∈ V(G)) :
    ∃ S : G.Separation, x ∈ S.left := by
  obtain ⟨S⟩ := h
  obtain hxS | hxS := S.mem_or_mem hx
  · exact ⟨S, hxS⟩
  · exact ⟨S.symm, by simpa using hxS⟩

lemma exists_separation_of_not_connBetween (hxV : x ∈ V(G)) (hyV : y ∈ V(G))
    (hxy : ¬ G.ConnBetween x y) : ∃ S : G.Separation, x ∈ S.left ∧ y ∈ S.right :=
  ⟨⟨{w ∈ V(G) | G.ConnBetween x w}, {w ∈ V(G) | ¬ G.ConnBetween x w}, ⟨x, by simpa⟩,
    ⟨y, by aesop⟩, by simp +contextual [disjoint_left],
    by simp [Set.ext_iff, ← and_or_left, or_not],
    fun x' y' ⟨_, hx'⟩ ⟨_, hy'⟩ hxy' ↦  hy' <| hx'.trans hxy'.connBetween⟩, by simp_all⟩

lemma preconnected_iff_isEmpty_separation : G.Preconnected ↔ IsEmpty G.Separation := by
  rw [← not_iff_not]
  simp only [Preconnected, not_isEmpty_iff, not_forall]
  refine ⟨fun ⟨x, y, hx, hy, h⟩ => ?_, fun ⟨S⟩ => ?_⟩
  · obtain ⟨S, hxL, hyR⟩ := exists_separation_of_not_connBetween hx hy h
    exact ⟨S⟩
  use S.nonempty_left.some, S.nonempty_right.some, S.left_subset S.nonempty_left.some_mem,
    S.right_subset S.nonempty_right.some_mem, S.not_connBetween S.nonempty_left.some_mem
    S.nonempty_right.some_mem
alias ⟨Preconnected.separation_isEmpty, _⟩ := preconnected_iff_isEmpty_separation

lemma preconnected_of_vertexSet_subsingleton (hV : V(G).Subsingleton) : G.Preconnected := by
  rw [preconnected_iff_isEmpty_separation]
  contrapose! hV
  obtain ⟨S⟩ := by simpa only [Preconnected, not_isEmpty_iff] using hV
  exact S.vertexSet_nontrivial

lemma Separation.not_connected (S : G.Separation) : ¬ G.Connected := by
  obtain ⟨x, hx⟩ := S.nonempty_left
  obtain ⟨y, hy⟩ := S.nonempty_right
  exact fun h ↦ S.not_connBetween hx hy <| h.connBetween (S.left_subset hx)
    (S.right_subset hy)

lemma Connected.isEmpty_separation (hG : G.Connected) : IsEmpty G.Separation :=
  isEmpty_iff.2 fun S ↦ S.not_connected hG

lemma nonempty_separation_of_not_connected (hne : V(G).Nonempty) (hG : ¬ G.Connected) :
    Nonempty G.Separation := by
  obtain ⟨x, y, hx, hy, hxy⟩ := by simpa only [Preconnected, hne,
    connected_iff, true_and, not_forall] using hG
  exact ⟨(exists_separation_of_not_connBetween hx hy hxy).choose⟩

lemma not_connected_iff_nonempty_separation :
    V(G).Nonempty ∧ ¬ G.Connected ↔ Nonempty G.Separation :=
  ⟨fun ⟨hV, hconn⟩ ↦ nonempty_separation_of_not_connected hV hconn,
  fun ⟨S⟩ => ⟨S.vertexSet_nontrivial.nonempty, S.not_connected⟩⟩

/-- `G`.IsSep `S` means that `S` is a subset of the vertices whose deletion leaves a
disconnected graph -/
@[mk_iff]
structure IsSep (G : Graph α β) (S : Set α) : Prop where
  subset_vx : S ⊆ V(G)
  not_connected : ¬ (G - S).Connected

@[mk_iff]
structure IsMinSep (G : Graph α β) (S : Set α) : Prop extends IsSep G S where
  minimal : ∀ A, IsSep G A → S.encard ≤ A.encard

lemma IsMinSep.encard_le_of_isSep (hS : G.IsMinSep S) (hT : G.IsSep T) :
    S.encard ≤ T.encard := hS.minimal T hT

lemma IsMinSep.not_isSep_of_encard_lt (hM : IsMinSep G S) (hSS' : S'.encard < S.encard) :
    ¬ IsSep G S' := by
  by_contra hc
  grw [hM.minimal S' hc, lt_self_iff_false S'.encard] at hSS'
  exact hSS'

lemma connected_of_not_isSep (hV : S ⊆ V(G)) (hS : ¬ IsSep G S) : (G - S).Connected := by
  by_contra hc
  exact hS ⟨hV, hc⟩

@[simp]
lemma empty_isSep_iff : G.IsSep ∅ ↔ ¬ G.Connected :=
  ⟨fun h ↦ by simpa using h.not_connected, fun h ↦ ⟨empty_subset _, by simpa⟩⟩

lemma empty_isSep (h : ¬ G.Connected) : G.IsSep ∅ :=
  empty_isSep_iff.mpr h

lemma IsSep.not_connected_of_empty (h : G.IsSep ∅) : ¬ G.Connected :=
  empty_isSep_iff.mp h

@[simp]
lemma IsMinSep.eq_empty_iff (hS : G.IsMinSep S) : S = ∅ ↔ ¬ G.Connected := by
  refine ⟨fun h ↦ (h ▸ hS).toIsSep.not_connected_of_empty, ?_⟩
  by_contra! hcon
  obtain ⟨hG, hSne⟩ := hcon
  obtain rfl := by simpa using hS.minimal ∅ <| empty_isSep hG
  simp at hSne

@[simp]
lemma empty_isMinSep_iff : G.IsMinSep ∅ ↔ ¬ G.Connected :=
  ⟨fun h ↦ h.toIsSep.not_connected_of_empty, fun h ↦ ⟨empty_isSep h, by simp⟩⟩

lemma IsMinSep.connected_iff (hS : G.IsMinSep S) : G.Connected ↔ S.Nonempty := by
  simpa [nonempty_iff_ne_empty] using hS.eq_empty_iff.not.symm

lemma IsMinSep.encard_eq_encard_of_isMinSep (hS : G.IsMinSep S) (hT : G.IsMinSep T) :
    S.encard = T.encard := by
  have h₁ := hS.minimal _ hT.toIsSep
  have h₂ := hT.minimal _ hS.toIsSep
  exact h₁.antisymm h₂

lemma isSep_empty_iff_isMinSep_empty : G.IsSep ∅ ↔ G.IsMinSep ∅ :=
  ⟨fun hyp ↦ ⟨hyp, by simp⟩, fun h ↦ h.toIsSep⟩

lemma conn_iff_forall_isSep : G.Connected ↔ ∀ ⦃S⦄, IsSep G S → S.Nonempty := by
  refine ⟨fun h S hS => ?_, fun h => ?_⟩ <;> by_contra! hC
  · simpa [hC, h] using hS.not_connected
  simpa using h (empty_isSep_iff.mpr hC)

lemma IsSep.nonempty_of_connected (hG : G.Connected) (hS : G.IsSep S) : S.Nonempty :=
  conn_iff_forall_isSep.mp hG hS

lemma IsMinSep.nonempty_of_connected (hG : G.Connected) (hM : G.IsMinSep S) : S.Nonempty :=
  hM.toIsSep.nonempty_of_connected hG

lemma vertexSet_isSep : G.IsSep V(G) := ⟨refl _, by simp⟩

lemma isSep_of_not_connected (h : ¬ (G - S).Connected) : G.IsSep (V(G) ∩ S) :=
  ⟨inter_subset_left, by simpa⟩

lemma IsSep.of_deleteVerts (h : (G - X).IsSep S) : G.IsSep (S ∪ (V(G) ∩ X)) where
  subset_vx := by
    have : S ⊆ V(G) ∧ Disjoint S X := by simpa [subset_sdiff] using h.subset_vx
    simp [this.1]
  not_connected := by
    rw [union_comm, ← deleteVerts_deleteVerts, deleteVerts_vertexSet_inter]
    exact h.not_connected

lemma IsSep.of_isSpanningSubgraph (h : G.IsSep S) (hsle : H ≤s G) : H.IsSep S where
  subset_vx := by simp [hsle.vertexSet_eq, h.subset_vx]
  not_connected h' := h.not_connected (h'.of_isSpanningSubgraph <| by gcongr)

lemma IsComplete.isInducedSubgraph (hG : G.IsComplete) (hH : H ≤i G) : H.IsComplete := by
  rintro x hx y hy hne
  exact hH.adj_congr hx hy |>.mpr (hG x (hH.vertexSet_mono hx) y (hH.vertexSet_mono hy) hne)

@[simp]
lemma IsComplete.isSep_iff_subset (h : G.IsComplete) : G.IsSep S ↔ S = V(G) := by
  refine ⟨fun hS => hS.subset_vx.antisymm ?_, ?_⟩
  · have := h.isInducedSubgraph (G.deleteVerts_isInducedSubgraph S)
    |>.connected_iff.not.mp hS.not_connected
    simpa only [vertexSet_deleteVerts, not_nonempty_iff_eq_empty, sdiff_eq_empty] using this
  rintro rfl
  exact vertexSet_isSep

@[mk_iff isEdgeSep_iff]
structure IsEdgeSep (G : Graph α β) (S : Set β) : Prop where
  subset_edgeSet : S ⊆ E(G)
  not_connected : ¬ (G ＼ S).Connected

@[mk_iff]
structure IsMinEdgeSep (G : Graph α β) (S : Set β) : Prop extends IsEdgeSep G S where
  minimal : ∀ A, IsEdgeSep G A → S.encard ≤ A.encard

lemma IsMinEdgeSep.isEdgeSep (hM : IsMinEdgeSep G (S := F)) : IsEdgeSep G F :=
  hM.toIsEdgeSep

lemma IsMinEdgeSep.encard_le_of_isEdgeSep (hF : G.IsMinEdgeSep F) (hF' : G.IsEdgeSep F') :
    F.encard ≤ F'.encard := hF.minimal F' hF'

@[simp]
lemma empty_isEdgeSep_iff : G.IsEdgeSep ∅ ↔ ¬ G.Connected := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa using h.not_connected
  exact ⟨empty_subset _, by simpa⟩

-- lemma not_connBetween_of_linkEdges_isEdgeSep (hc : G.Preconnected)
--     (h : G.IsEdgeSep E(G, u, v)) : ¬ (G ＼ E(G, u, v)).ConnBetween u v := by
--   obtain hu | hu := em (u ∈ V(G)) |>.symm
--   · simp [linkEdges_eq_empty_of_left_not_mem hu v, mt ConnBetween.left_mem hu]

--   obtain ⟨S, hxS⟩ := exists_mem_left_of_nonempty_separation (nonempty_separation_of_not_connected
--     (by use u; simpa) h.not_connected) hu

@[mk_iff isMixedSep_iff]
structure IsMixedSep (G : Graph α β) (S : Set α) (F : Set β) : Prop where
  subset_vertexSet : S ⊆ V(G)
  subset_edgeSet : F ⊆ E(G)
  not_connected : ¬ ((G ＼ F) - S).Connected

noncomputable def IsMixedSep.size (S : Set α) (F : Set β) : ℕ∞ := S.encard + F.encard

@[mk_iff]
structure IsMinMixedSep (G : Graph α β) (S : Set α) (F : Set β) : Prop
    extends IsMixedSep G S F where
  minimal : ∀ S' F', IsMixedSep G S' F' →
    IsMixedSep.size (α := α) (β := β) S F ≤ IsMixedSep.size (α := α) (β := β) S' F'

lemma IsMinMixedSep.isMixedSep (hM : IsMinMixedSep G S F) : IsMixedSep G S F :=
  hM.toIsMixedSep

lemma IsMinMixedSep.size_le_of_isMixedSep (hM : G.IsMinMixedSep S F) (h : G.IsMixedSep S' F') :
    IsMixedSep.size (α := α) (β := β) S F ≤ IsMixedSep.size (α := α) (β := β) S' F' :=
  hM.minimal S' F' h

lemma IsEdgeSep.toIsMixedSep (h : G.IsEdgeSep F) : G.IsMixedSep ∅ F :=
  ⟨empty_subset _, h.subset_edgeSet, by simpa using h.not_connected⟩

lemma IsMixedSep.of_isSpanningSubgraph (h : G.IsMixedSep S F) (hsle : H ≤s G) :
    H.IsMixedSep S (E(H) ∩ F) where
  subset_vertexSet := hsle.vertexSet_eq ▸ h.subset_vertexSet
  subset_edgeSet := inter_subset_left
  not_connected hc := by
    rw [edgeSet_deleteEdges_inter] at hc
    exact h.not_connected <| hc.of_isSpanningSubgraph (by gcongr)

/-- A graph has `PreconnGE n`, if for every pair of vertices `s` and `t`, there is no
    `n`-vertex cut between them.
    In the case of complete graphs, K_n, ∀ κ, K_n.PreconnGE κ. -/
def PreconnGE (G : Graph α β) (n : ℕ) : Prop :=
  ∀ ⦃s t⦄, s ∈ V(G) → t ∈ V(G) → G.ConnBetweenGE s t n

/-- A graph has `ConnGE n`, if every cut has size at least `n` and the number of vertices is at
  least `n + 1`. -/
@[mk_iff]
structure ConnGE (G : Graph α β) (n : ℕ) : Prop where
  le_cut : ∀ ⦃C⦄, G.IsSep C → n ≤ C.encard
  le_card : V(G).Subsingleton ∨ n < V(G).encard

lemma exists_isSepSet_encard_lt_of_not_connGE (hnV : n < V(G).encard) (h : ¬ G.ConnGE n) :
    ∃ C, G.IsSep C ∧ C.encard < n := by
  by_contra! hno
  exact h ⟨hno, Or.inr hnV⟩

lemma exists_isSepSet_encard_le_of_not_connGE (hnV : n + 1 < V(G).encard) (h : ¬ G.ConnGE (n+1)) :
    ∃ C, G.IsSep C ∧ C.encard ≤ n := by
  obtain ⟨C, hC, hlt⟩ := exists_isSepSet_encard_lt_of_not_connGE (G := G) (n := n+1) hnV h
  use C, hC, by enat_to_nat! <;> omega

/-- A graph has `EdgeConnGE n`, if for every pair of vertices `s` and `t`, there is no
    `n`-edge cut between them. -/
def EdgeConnGE (G : Graph α β) (n : ℕ) : Prop :=
  ∀ ⦃s t⦄, s ∈ V(G) → t ∈ V(G) → G.EdgeConnBetweenGE s t n

@[simp]
lemma PreconnGE_zero : G.PreconnGE 0 := by
  simp [PreconnGE]

@[gcongr]
lemma PreconnGE.anti_right (hle : n ≤ m) (h : G.PreconnGE m) : G.PreconnGE n := by
  intro s t hs ht
  exact h hs ht |>.anti_right hle

@[simp]
lemma preconnGE_one_iff : G.PreconnGE 1 ↔ G.Preconnected := by
  simp [PreconnGE, connBetweenGE_one_iff, Preconnected]

lemma preconnGE_iff_forall_connBetweenGE :
    G.PreconnGE n ↔ ∀ ⦃s t⦄, s ∈ V(G) → t ∈ V(G) → G.ConnBetweenGE s t n := Iff.rfl

lemma preconnGE_iff_forall_preconnected :
    G.PreconnGE n ↔ ∀ X ⊆ V(G), X.encard < ↑n → (G - X).Preconnected := by
  refine ⟨fun h X hXV hX => ?_, fun h s t hs ht C hC => ?_⟩
  · rw [preconnected_iff_isEmpty_separation]
    by_contra! hS
    obtain ⟨S⟩ := hS
    have hcut :=
      h (sdiff_subset <| deleteVerts_vertexSet .. ▸ S.left_subset S.nonempty_left.some_mem)
        (sdiff_subset <| deleteVerts_vertexSet .. ▸ S.right_subset S.nonempty_right.some_mem)
        (S.isSepBetween_of_deleteVerts (X := X) S.nonempty_left.some_mem S.nonempty_right.some_mem)
    exact hcut.trans (encard_le_encard inter_subset_right) |>.not_gt hX
  by_contra! hCn
  have hpre : (G - C).Preconnected := h (X := C) hC.subset hCn
  have hs' : s ∈ V(G - C) := by simp [hs, hC.left_not_mem]
  have ht' : t ∈ V(G - C) := by simp [ht, hC.right_not_mem]
  exact hC.not_connBetween <| hpre s t hs' ht'

lemma preconnGE_map_iff_of_injOn {α' : Type*} {φ : α → α'} (hφ : InjOn φ V(G)) :
    (φ ''ᴳ G).PreconnGE n ↔ G.PreconnGE n := by
  simp only [preconnGE_iff_forall_preconnected, vertexSet_map, forall_subset_image_iff]
  refine ⟨fun h X hX hXn ↦ ?_, fun h X hX hXn ↦ ?_⟩
  · specialize h X hX (by rwa [(hφ.mono hX).encard_image])
    rwa [← map_deleteVerts_of_injOn hφ hX,
      preconnected_map_iff_of_injOn (hφ.mono (deleteVerts_vertexSet .. ▸ sdiff_subset))] at h
  rw [← map_deleteVerts_of_injOn hφ hX, preconnected_map_iff_of_injOn
    (hφ.mono (deleteVerts_vertexSet .. ▸ sdiff_subset))]
  exact h X hX <| by rwa [← (hφ.mono hX).encard_image]

@[simp]
lemma preconnGE_edgeMap_iff {β' : Type*} {φ : β → β'} {hφ} :
    (G.edgeMap φ hφ).PreconnGE n ↔ G.PreconnGE n := by
  simp [preconnGE_iff_forall_preconnected, ← edgeMap_deleteVerts]

lemma PreconnGE.preconnected_deleteVerts (hG : G.PreconnGE n) (hX : X.encard < n) :
    (G - X).Preconnected := by
  rw [← deleteVerts_vertexSet_inter]
  exact (preconnGE_iff_forall_preconnected.1 hG) (V(G) ∩ X) inter_subset_left
    (by grw [inter_subset_right, hX])

lemma PreconnGE.encard_ge (hG : G.PreconnGE n) (hX : ¬ (G - X).Preconnected) : n ≤ X.encard := by
  contrapose! hX
  exact hG.preconnected_deleteVerts hX

lemma PreconnGE_two_iff : G.PreconnGE 2 ↔ G.Preconnected ∧ ∀ x ∈ V(G), (G - {x}).Preconnected := by
  refine ⟨fun h ↦ ⟨by simpa using h.preconnected_deleteVerts (X := ∅),
    fun x hx ↦ h.preconnected_deleteVerts (by simp)⟩,
    fun h ↦ preconnGE_iff_forall_preconnected.2 fun X hX hX2 ↦ ?_⟩
  obtain (rfl | ⟨x, rfl⟩) : X = ∅ ∨ ∃ x, X = {x} := by
    simpa [encard_le_one_iff_subsingleton, subsingleton_iff_eq_empty_or_singleton] using hX2
  · simpa using h.1
  exact h.2 x (by simpa using hX)

lemma preconnGE_iff_forall_setConnGE : G.PreconnGE n ↔ ∀ S T : Set α, S ⊆ V(G) → T ⊆ V(G) →
    G.SetConnGE S T (min ↑n (min S.encard T.encard)).toNat := by
  refine ⟨fun h S T hS hT C hC ↦ ?_, fun h s t hs ht C hC ↦ ?_⟩
  · rw [ENat.natCast_toNat (by simp)]
    by_contra! hCcd
    obtain ⟨hCn, hCS, hCT⟩ := (by simpa using hCcd); clear hCcd
    obtain ⟨s, hs, hsC⟩ := diff_nonempty_of_encard_lt_encard hCS
    obtain ⟨t, ht, htC⟩ := diff_nonempty_of_encard_lt_encard hCT
    have := by simpa only [SetConnected, not_exists, not_and] using hC.ST_disconnects
    have hSep : G.IsSepBetween s t C :=
      ⟨hC.subset_vertexSet, hsC, htC, this s hs t ht⟩
    exact hCn.not_ge <| h (hS hs) (hT ht) hSep
  obtain hCinfty | hCFin := eq_or_ne C.encard ⊤
  · exact StrictMono.maximal_preimage_top (fun ⦃a b⦄ a_1 ↦ a_1) hCinfty ↑n
  simp only [ne_eq, encard_eq_top_iff, not_infinite] at hCFin
  have hsC : C.encard < Set.encard (insert s C) :=
    hCFin.encard_lt_encard (ssubset_insert hC.left_not_mem)
  have htC : C.encard < Set.encard (insert t C) :=
    hCFin.encard_lt_encard (ssubset_insert hC.right_not_mem)
  have hSC : insert s C ⊆ V(G) := by
    simpa [insert_subset_iff] using And.intro hs hC.subset
  have hTC : insert t C ⊆ V(G) := by
    simpa [insert_subset_iff] using And.intro ht hC.subset
  have hcd := h _ _ hSC hTC hC.isSetCut
  rw [ENat.natCast_toNat (by simp)] at hcd
  simpa [hsC.not_ge, htC.not_ge] using hcd

/-- Minimum `C.encard` over vertex cuts `C` of `G`, as an `ℕ∞`. -/
noncomputable def sepConnectivity (G : Graph α β) : ℕ∞ :=
  ⨅ C : {C : Set α // G.IsSep C}, (C.val : Set α).encard

open Classical in
/-- Upper bound on connectivity from the vertex count: `⊤` if `V(G)` is a subsingleton, else
`|V(G)| - 1` in `ℕ∞`. -/
noncomputable def cardConnectivityBound (G : Graph α β) : ℕ∞ :=
  if _ : V(G).Subsingleton then ⊤ else V(G).encard - 1

/-- Global vertex connectivity as an `ℕ∞`: minimum of separator connectivity and the
cardinality bound that appears in `ConnGE`. -/
noncomputable def connectivity (G : Graph α β) : ℕ∞ :=
  min G.sepConnectivity G.cardConnectivityBound

notation "κ(" G ")" => Graph.connectivity G

/-- Minimum pairwise `connBetweenConnectivity` over ordered pairs of vertices in `V(G)`. -/
noncomputable def preconnectivity (G : Graph α β) : ℕ∞ :=
  ⨅ s : V(G), ⨅ t : V(G), connectivityBetween G s t

notation "κ'(" G ")" => Graph.preconnectivity G

/-- Minimum pairwise `edgeConnBetweenConnectivity` over ordered pairs of vertices in `V(G)`. -/
noncomputable def edgeConnectivity (G : Graph α β) : ℕ∞ :=
    (⨅ s : V(G), ⨅ t : V(G), edgeConnectivityBetween G s t)

notation "κₑ(" G ")" => Graph.edgeConnectivity G

lemma le_sepConnectivity_iff {k : ℕ∞} :
    k ≤ G.sepConnectivity ↔ ∀ ⦃C : Set α⦄, G.IsSep C → k ≤ C.encard := by
  simp [sepConnectivity, le_iInf_iff, Subtype.forall]

lemma nat_le_cardConnectivityBound_iff (n : ℕ) :
    n ≤ G.cardConnectivityBound ↔ V(G).Subsingleton ∨ n < V(G).encard := by
  unfold cardConnectivityBound
  split_ifs with hV
  · refine ⟨fun _ => Or.inl hV, fun _ => le_top⟩
  refine ⟨fun hn => Or.inr ?_, by simp only [hV, false_or]; eomega⟩
  rw [not_subsingleton_iff, ← one_lt_encard_iff_nontrivial] at hV
  eomega

lemma connGE_iff_le_connectivity (n : ℕ) : G.ConnGE n ↔ n ≤ κ(G) := by
  rw [connectivity, le_min_iff, connGE_iff, le_sepConnectivity_iff,
    nat_le_cardConnectivityBound_iff n]

lemma le_preconnectivity_iff {k : ℕ∞} : k ≤ κ'(G) ↔ ∀ ⦃s t : α⦄, s ∈ V(G) → t ∈ V(G) →
    k ≤ connectivityBetween G s t := by
  rw [preconnectivity, le_iInf_iff]
  exact ⟨fun h s t hs ht ↦ (le_iInf_iff.mp (h ⟨s, hs⟩)) ⟨t, ht⟩,
    fun h ⟨s, hs⟩ ↦ le_iInf_iff.mpr fun ⟨t, ht⟩ ↦ h hs ht⟩

lemma preconnGE_iff_le_preconnectivity (n : ℕ) : G.PreconnGE n ↔ n ≤ κ'(G) := by
  rw [preconnGE_iff_forall_connBetweenGE, le_preconnectivity_iff]
  exact forall₄_congr fun s t _ _ ↦ by simpa using connBetweenGE_iff_le_connectivityBetween s t n

lemma le_edgeConnectivity_iff {k : ℕ∞} : k ≤ κₑ(G) ↔
    ∀ ⦃s t : α⦄, s ∈ V(G) → t ∈ V(G) → k ≤ edgeConnectivityBetween G s t := by
  rw [edgeConnectivity, le_iInf_iff]
  exact ⟨fun h s t hs ht ↦ (le_iInf_iff.mp (h ⟨s, hs⟩)) ⟨t, ht⟩,
    fun h ⟨s, hs⟩ ↦ le_iInf_iff.mpr fun ⟨t, ht⟩ ↦ h hs ht⟩

lemma connectivity_simplify (h : G.IsSimpleficationOf H) : κ(G) = κ(H) := by
  have hsle := h.isSpanningSubgraph
  have hsep {C} : G.IsSep C ↔ H.IsSep C := by
    refine ⟨fun hC ↦ ⟨hsle.vertexSet_eq ▸ hC.subset_vx, fun hHconn ↦ hC.not_connected ?_⟩,
      fun hC ↦ hC.of_isSpanningSubgraph hsle⟩
    have hVG : V(G - C) = V(H - C) := by simp [hsle.vertexSet_eq]
    rw [connected_iff] at hHconn ⊢
    refine ⟨hVG ▸ hHconn.1, fun s t hs ht ↦ ?_⟩
    rw [h.deleteVerts C |>.connBetween_iff]
    exact hHconn.2 s t (hVG ▸ hs) (hVG ▸ ht)
  unfold connectivity cardConnectivityBound
  congr 1
  · refine le_antisymm ?_ ?_ <;> rw [le_sepConnectivity_iff]
    · exact fun _ hC ↦ (le_sepConnectivity_iff.1 le_rfl) (hsep.mpr hC)
    · exact fun _ hC ↦ (le_sepConnectivity_iff.1 le_rfl) (hsep.mp hC)
  rw [hsle.vertexSet_eq]

lemma edgeConnGE_iff_le_edgeConnectivity (n : ℕ) : G.EdgeConnGE n ↔ n ≤ κₑ(G) := by
  rw [EdgeConnGE, le_edgeConnectivity_iff]
  refine forall₄_congr fun s t hs ht ↦ ?_
  simpa using (edgeConnBetweenGE_iff_le_edgeConnectivityBetween s t n)

lemma PreconnGE.isSpanningSubgraph (hconn : H.PreconnGE n) (hsle : H ≤s G) : G.PreconnGE n :=
  fun _ _ hs ht => hconn (hsle.vertexSet_eq ▸ hs) (hsle.vertexSet_eq ▸ ht) |>.of_le hsle.le

@[simp]
lemma IsComplete.preconnGE (h : G.IsComplete) (n : ℕ) : G.PreconnGE n :=
  fun _ _ hs ht ↦ h.connBetweenGE hs ht n

lemma encard_le_preconnGE_of_not_isComplete (h : ¬ G.IsComplete) (hn : G.PreconnGE n) :
    n ≤ V(G).encard := by
  obtain ⟨x, hx, y, hy, hne, hxy⟩ := by simpa [IsComplete] using h
  exact connBetweenGE_le_encard (hn hx hy) hne hxy

lemma preconnGE_add_two_le_encard_of_not_isComplete (h : ¬ G.IsComplete) (hn : G.PreconnGE n) :
    n + 2 ≤ V(G).encard := by
  obtain ⟨x, hx, y, hy, hne, hxy⟩ := by simpa [IsComplete] using h
  exact connBetweenGE_add_two_le_encard (hn hx hy) hx hy hne hxy

@[simp]
lemma connGE_zero : G.ConnGE 0 := by
  obtain h | h := V(G).eq_empty_or_nonempty <;> simp [connGE_iff, h]

@[gcongr]
lemma ConnGE.anti_right (hle : n ≤ m) (h : G.ConnGE m) : G.ConnGE n where
  le_cut C hC := (by simpa : (n : ℕ∞) ≤ ↑m).trans (h.le_cut hC)
  le_card := h.le_card.imp id (fun h ↦ by enat_to_nat!; omega)

@[simp]
lemma connGE_one_iff : G.ConnGE 1 ↔ G.Connected := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_contra! hc
    simpa using h.le_cut <| empty_isSep_iff.mpr hc
  by_contra! hCcd
  simp [connGE_iff, one_lt_encard_iff_nontrivial, V(G).subsingleton_or_nontrivial,
    Set.not_nonempty_iff_eq_empty, h] at hCcd

@[simp]
lemma connGE_bot : (⊥ : Graph α β).ConnGE n ↔ n = 0 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · simpa using h.le_cut <| (isSep_of_not_connected (S := ∅) (by simp))
  rintro rfl
  simp

@[simp]
lemma bouquet_deleteVerts : (bouquet v F) - {v} = ⊥ :=
  (deleteVerts_eq_bot_iff (bouquet v F) {v}).mpr <| by simp

@[simp]
lemma connGE_bouquet_iff (n : ℕ) : (bouquet v F).ConnGE n ↔ n ≤ 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ConnGE.anti_right h <| by simp⟩
  simpa using h.le_cut (C := {v}) (by simp)

lemma connGE_iff_of_vertexSet_singleton (h : V(G) = {x}) : G.ConnGE n ↔ n ≤ 1 := by
  rw [eq_bouquet_iff.mpr h, connGE_bouquet_iff]

lemma connGE_iff_of_vertexSet_subsingleton (hss : V(G).Subsingleton) :
    G.ConnGE n ↔ n ≤ V(G).encard := by
  obtain he | ⟨x, hx⟩ := hss.eq_empty_or_singleton
  · simp only [vertexSet_eq_empty_iff] at he
    simp [he]
  simp [connGE_iff_of_vertexSet_singleton, hx]

lemma ConnGE.pre (h : G.ConnGE n) : G.PreconnGE n := by
  rw [preconnGE_iff_forall_preconnected]
  intro X hXV hX
  by_contra! hc
  have := mt Connected.pre hc
  have : ↑n ≤ (V(G) ∩ X).encard := by simpa using h.le_cut (isSep_of_not_connected this)
  exact hX.not_ge <| this.trans <| encard_le_encard inter_subset_right

/-- `G.PreconnGE n` and `G.ConnGE n` agree except on complete graphs on more than `n` vertices. -/
lemma preconnGE_iff_connGE_of_not_isComplete (h' : V(G).encard ≤ n → ¬ G.IsComplete) :
    G.PreconnGE n ↔ G.ConnGE n := by
  refine ⟨fun h ↦ ?_, ConnGE.pre⟩
  obtain hle | hgt := le_or_gt V(G).encard n
  · grw [← preconnGE_add_two_le_encard_of_not_isComplete (h' hle) h] at hle
    simp at hle
  refine ⟨fun C hC ↦ ?_, .inr hgt⟩
  have hconn := hC.not_connected
  rw [connected_iff, not_and_or, not_nonempty_iff_eq_empty, vertexSet_deleteVerts,
    sdiff_eq_empty] at hconn
  obtain hss | hnC := hconn
  · grw [← hss, ← hgt]
  exact h.encard_ge hnC

lemma connGE_iff_preconnGE (hnt : V(G).Nontrivial) :
    G.ConnGE n ↔ G.PreconnGE n ∧ n < V(G).encard := by
  obtain hle | hgt := le_or_gt V(G).encard n
  · exact iff_of_false (fun hc ↦ hc.2.elim hnt.not_subsingleton hle.not_gt) (by simp [hle.not_gt])
  rw [preconnGE_iff_connGE_of_not_isComplete (by simp [hgt.not_ge]), and_iff_left hgt]

lemma preconnGE_iff_connGE : G.PreconnGE n ↔ G.ConnGE n ∨ (V(G).encard ≤ n ∧ G.IsComplete) := by
  obtain hle | hgt := le_or_gt V(G).encard n
  · by_cases hcomp : G.IsComplete
    · exact iff_of_true (hcomp.preconnGE n) <| .inr ⟨hle, hcomp⟩
    rw [or_iff_left (by simp [hcomp]), preconnGE_iff_connGE_of_not_isComplete (fun _ ↦ hcomp)]
  rw [preconnGE_iff_connGE_of_not_isComplete, or_iff_left (by simp [hgt.not_ge])]
  simp [hgt.not_ge]

lemma connGE_iff_forall_connected (h' : V(G).encard = n → ¬ G.IsComplete) :
    G.ConnGE n ↔ ∀ X ⊆ V(G), X.encard < n → (G - X).Connected := by
  obtain hlt | hge := lt_or_ge V(G).encard n
  · refine iff_of_false (fun hGE ↦ ?_) fun h ↦ by simpa using h V(G) subset_rfl hlt
    obtain hss | hcard := hGE.2
    · rw [connGE_iff_of_vertexSet_subsingleton hss] at hGE
      exact hlt.not_ge hGE
    exact hlt.le.not_gt hcard
  rw [le_antisymm_iff, and_iff_left hge] at h'
  refine ⟨fun h X hX hXn ↦ connected_iff.2 ⟨?_, h.pre.preconnected_deleteVerts hXn⟩, fun h ↦ ?_⟩
  · obtain rfl | hssu := hX.eq_or_ssubset
    · have hcon := preconnGE_add_two_le_encard_of_not_isComplete (h' hXn.le) h.pre
      enat_to_nat!; lia
    simp only [vertexSet_deleteVerts]
    exact sdiff_nonempty.2 hssu.not_subset
  rw [← preconnGE_iff_connGE_of_not_isComplete h', preconnGE_iff_forall_preconnected]
  exact fun X hX hXn ↦ (h X hX hXn).pre

lemma connGE_map_iff_of_injOn {α' : Type*} {φ : α → α'} (hφ : InjOn φ V(G)) :
    (φ ''ᴳ G).ConnGE n ↔ G.ConnGE n := by
  obtain hss | hnt := V(G).subsingleton_or_nontrivial
  · rw [connGE_iff_of_vertexSet_subsingleton, connGE_iff_of_vertexSet_subsingleton hss]
    · simp [hφ.encard_image]
    simpa [← encard_le_one_iff_subsingleton, hφ.encard_image] using hss
  rw [connGE_iff_preconnGE, preconnGE_map_iff_of_injOn hφ, vertexSet_map, hφ.encard_image,
    connGE_iff_preconnGE hnt]
  simpa [← one_lt_encard_iff_nontrivial, hφ.encard_image] using hnt

@[simp]
lemma connGE_edgeMap_iff {β' : Type*} {φ : β → β'} {hφ} :
    (G.edgeMap φ hφ).ConnGE n ↔ G.ConnGE n := by
  obtain hss | hnt := V(G).subsingleton_or_nontrivial
  · rw [connGE_iff_of_vertexSet_subsingleton (by simpa), connGE_iff_of_vertexSet_subsingleton hss]
    simp
  rw [connGE_iff_preconnGE (by simpa)]
  simp [connGE_iff_preconnGE hnt]

lemma IsComplete.connGE_iff (h : G.IsComplete) (n : ℕ) :
    G.ConnGE n ↔ (V(G).Subsingleton ∧ n ≤ V(G).encard ∨ n < V(G).encard) := by
  refine ⟨fun h ↦ ?_, fun h => ?_⟩
  · apply h.le_card.imp (fun h1 ↦ ?_) id
    obtain hem | ⟨x, hsin⟩ := h1.eq_empty_or_singleton
    · simp_all
    simp_all [connGE_iff_of_vertexSet_singleton hsin]
  obtain ⟨hss, hn⟩ | hn := h
  · obtain hem | ⟨x, hsin⟩ := hss.eq_empty_or_singleton
    · simp_all
    simp_all [connGE_iff_of_vertexSet_singleton hsin]
  exact ⟨fun C hC ↦ le_trans (by simp) (lt_of_lt_of_le hn <| encard_le_encard
  <| (h.isSep_iff_subset.mp hC).superset).le, Or.inr hn⟩

lemma IsComplete.connGE_iff' (h : G.IsComplete) (n : ℕ) :
    G.ConnGE n ↔ (V(G).Subsingleton ∧ n = V(G).encard ∨ n < V(G).encard) := by
  rw [h.connGE_iff, le_iff_eq_or_lt]
  tauto

lemma IsComplete.connGE (h : G.IsComplete) (hn : n < V(G).encard) : G.ConnGE n := by
  simp [h.connGE_iff, hn]

lemma ConnGE.isSpanningSubgraph (h : H.ConnGE n) (hsle : H ≤s G) : G.ConnGE n where
  le_cut C hC := by simpa using h.le_cut <| hC.of_isSpanningSubgraph hsle
  le_card := hsle.vertexSet_eq ▸ h.le_card

lemma ConnGE.of_deleteEdges (h : (G ＼ F).ConnGE n) : G.ConnGE n :=
  h.isSpanningSubgraph deleteEdges_isSpanningSubgraph

lemma ConnGE.deleteVerts (h : G.ConnGE n) (hFin : (V(G) ∩ X).Finite) :
    (G - X).ConnGE (n - (V(G) ∩ X).encard).toNat where
  le_cut C hC := by
    rw [ENat.natCast_toNat (by simp), tsub_le_iff_right, ← encard_union_eq]
    exact h.le_cut hC.of_deleteVerts
    · have := by simpa only [vertexSet_deleteVerts, subset_sdiff] using hC.subset_vx
      exact this.2.mono_right inter_subset_right
  le_card := by
    rw [inter_comm] at hFin
    by_cases hss : V(G - X).Subsingleton
    · left
      exact hss
    have : V(G - X).encard = V(G).encard - (X ∩ V(G)).encard := by
      rw [vertexSet_deleteVerts, ← sdiff_inter_self_eq_sdiff, encard_sdiff inter_subset_right hFin]
    rw [not_subsingleton_iff, ← one_lt_encard_iff_nontrivial, this] at hss
    refine h.le_card.imp (fun h a ha b hb ↦ ?_) (fun h ↦ ?_)
    · rw [deleteVerts_vertexSet] at ha hb
      exact h ha.1 hb.1
    rw [ENat.natCast_toNat (by simp), this, inter_comm]
    enat_to_nat! <;> omega

lemma ConnGE.vertexSet_encard_of_nontrivial (h : G.ConnGE n) (hnt : V(G).Nontrivial) :
    n + 1 ≤ V(G).encard := by
  rw [ENat.add_one_le_iff (by simp)]
  exact h.le_card.resolve_left hnt.not_subsingleton

lemma PreconnGE.deleteVerts (hX : X.Finite) (h : G.PreconnGE (n + hX.toFinset.card)) :
    (G - X).PreconnGE n := by
  simp_rw [preconnGE_iff_forall_preconnected, deleteVerts_deleteVerts]
  refine fun Y hY hYn ↦ h.preconnected_deleteVerts ?_
  grw [encard_union_le, add_comm, Nat.cast_add, hX.encard_eq_coe_toFinset_card,
    ENat.add_lt_add_right_iff, and_iff_left (by simp), hYn]

lemma ConnGE.deleteVerts' (hX : X.Finite) (h : G.ConnGE (n + hX.toFinset.card)) :
    (G - X).ConnGE n := by
  rw [← deleteVerts_vertexSet_inter]
  have hwin := (h.deleteVerts (X := V(G) ∩ X) (hX.subset (by grind)))
  grw [Nat.cast_add, inter_subset_right, inter_subset_right, hX.encard_eq_coe_toFinset_card,
    ENat.add_sub_cancel_right _ (by simp), ENat.toNat_natCast] at hwin
  · assumption
  · simp
  simp

lemma connGE_delete_vertex_of_add_one (hG : G.ConnGE (n + 1)) (x : α) : (G - {x}).ConnGE n := by
  have := hG.deleteVerts (X := {x}) ((finite_singleton x).inter_of_right _)
  grw [inter_subset_right, encard_singleton, Nat.cast_add, Nat.cast_one,
    ENat.add_sub_cancel_right _ (by simp), ENat.toNat_natCast] at this
  · assumption
  simp

lemma preconnGE_delete_vertex_of_add_one (hG : G.PreconnGE (n + 1)) (x : α) :
    (G - {x}).PreconnGE n :=
  PreconnGE.deleteVerts (by simp) (by simpa)

/-- If `v` is adjacent to every other vertex, then deleting it drops the preconnectivity by one. -/
lemma PreconnGE.preconnGE_add_one_of_delete_of_forall_adj (hG : (G - {v}).PreconnGE n)
    (hv : ∀ x ∈ V(G), x ≠ v → G.Adj x v) : G.PreconnGE (n + 1) := by
  obtain rfl | hne := eq_or_ne G ⊥
  · simp
  refine preconnGE_iff_forall_preconnected.2 fun X hX hXn ↦ ?_
  by_cases hvX : v ∈ X
  · have hwin := hG.preconnected_deleteVerts (X := X \ {v}) ?_
    · rwa [deleteVerts_deleteVerts, singleton_union, insert_sdiff_self_of_mem hvX] at hwin
    grw [← ENat.add_one_lt_add_one_iff, encard_sdiff_singleton_add_one hvX, hXn, Nat.cast_add,
      Nat.cast_one]
  refine (connected_of_vertex (u := v) ?_ (fun y hy ↦ ?_)).pre
  · obtain ⟨u, hu⟩ := ne_bot_iff.1 hne
    obtain rfl | huv := eq_or_ne u v
    · simp [hu, hvX]
    simp [hvX, (hv u hu huv).right_mem]
  obtain rfl | hne := eq_or_ne y v
  · simpa using hy
  simp only [vertexSet_deleteVerts, mem_sdiff] at hy
  refine Adj.connBetween ?_
  simp [deleteVerts_adj_iff, hvX, hy.2, hv y hy.1 hne]

/-- If `v` is adjacent to every other vertex, then deleting it drops the connectivity by one. -/
lemma ConnGE.connGE_add_one_of_delete_of_forall_adj (hG : (G - {v}).ConnGE n) (hV : 3 ≤ V(G).encard)
    (hv : ∀ x ∈ V(G), x ≠ v → G.Adj x v) : G.ConnGE (n + 1) := by
  have hvV : v ∈ V(G) := by
    obtain ⟨x, hx⟩ :=
      (one_lt_encard_iff_nontrivial.1 (show 1 < V(G).encard by enat_to_nat!; lia)).exists_ne v
    exact (hv x hx.1 hx.2).right_mem
  by_cases hcomp : G.IsComplete
  · have h' : (G - {v}).IsComplete := hcomp.isInducedSubgraph <| deleteVerts_isInducedSubgraph ..
    obtain h | h := (h'.connGE_iff' _).1 hG
    · grw [← encard_sdiff_add_encard_inter (t := {v}), inter_subset_right,
        ← vertexSet_deleteVerts, encard_le_one_iff_subsingleton.2 h.1, encard_singleton] at hV
      enat_to_nat; lia
    refine (hcomp.connGE_iff' ..).2 <| .inr ?_
    grw [← encard_sdiff_singleton_add_one hvV, ← vertexSet_deleteVerts, Nat.cast_add, Nat.cast_one,
      ENat.add_one_lt_add_one_iff]
    assumption
  rw [← preconnGE_iff_connGE_of_not_isComplete (fun _ ↦ hcomp)]
  exact hG.pre.preconnGE_add_one_of_delete_of_forall_adj hv

@[simp]
lemma EdgeConnGE_zero : G.EdgeConnGE 0 := by
  simp [EdgeConnGE]

lemma EdgeConnGE.anti_right (hle : n ≤ m) (h : G.EdgeConnGE m) : G.EdgeConnGE n := by
  intro s t hs ht
  exact h hs ht |>.anti_right hle

@[simp]
lemma edgeConnGE_one_iff : G.EdgeConnGE 1 ↔ G.Preconnected := by
  simp [EdgeConnGE, edgeConnBetweenGE_one_iff, Preconnected]

end Graph
