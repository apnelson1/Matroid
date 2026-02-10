import Matroid.ForMathlib.Tactic.ENatToNat
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

@[gcongr]
lemma ConnBetween.walkable_eq_walkable (h : G.ConnBetween x y) : G.walkable x = G.walkable y :=
  walkable_eq_walkable_of_mem h.symm

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

@[simps (attr := grind =)]
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
    simp only [mem_setOf_eq] at ha hb
    exact hb.2 <| ha.2.trans hab.connBetween

lemma not_connBetween (S : G.Separation) (hx : x ∈ S.left) (hy : y ∈ S.right) :
    ¬ G.ConnBetween x y := by
  rintro ⟨W, hW, rfl, rfl⟩
  rw [← S.not_left_mem_iff (S.right_subset hy)] at hy
  obtain ⟨e, x, y, hinc, hx, hy⟩ := exists_dInc_prop_not_prop hx hy
  exact hy <| S.left_mem_of_adj hx (hW.isLink_of_dInc hinc).adj

def isSepBetween_of_vertexDelete (S : (G - X).Separation) (hx : x ∈ S.left)
    (hy : y ∈ S.right) : G.IsSepBetween x y (V(G) ∩ X) := by
  refine ⟨inter_subset_left, ?_, ?_, ?_⟩
  · simp [(S.left_subset hx).2]
  · simp [(S.right_subset hy).2]
  · simpa [vertexDelete_vertexSet_inter] using S.not_connBetween hx hy

end Separation

lemma exists_mem_left_of_nonempty_separation (h : Nonempty G.Separation) (hx : x ∈ V(G)) :
    ∃ S : G.Separation, x ∈ S.left := by
  obtain ⟨S⟩ := h
  obtain hxS | hxS := S.mem_or_mem hx
  · exact ⟨S, hxS⟩
  · exact ⟨S.symm, by simpa using hxS⟩


/-- A graph is preconnected if for every pair of vertices, there is a path between them. -/
def Preconnected (G : Graph α β) : Prop :=
  ∀ x y, x ∈ V(G) → y ∈ V(G) → G.ConnBetween x y

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

lemma Preconnected.isSpanningSubgraph (h : H.Preconnected) (hsle : H ≤s G) : G.Preconnected :=
  fun s t hs ht ↦ (h s t (hsle.vertexSet_eq ▸ hs) (hsle.vertexSet_eq ▸ ht)).mono hsle.le

@[simp]
lemma IsComplete.preconnected (h : G.IsComplete) : G.Preconnected := by
  intro s t hs ht
  obtain rfl | hne := eq_or_ne s t
  · simpa
  exact h s hs t ht hne |>.connBetween

lemma preconnected_of_exists_connBetween (h : ∃ x, ∀ y ∈ V(G), G.ConnBetween x y) :
    G.Preconnected := by
  obtain ⟨x, hx⟩ := h
  exact fun s t hs ht ↦ (hx s hs).symm.trans <| hx t ht

lemma preconnected_iff_exists_connBetween (hG : V(G).Nonempty) :
    G.Preconnected ↔ ∃ x, ∀ y ∈ V(G), G.ConnBetween x y := by
  refine ⟨fun h => ⟨hG.some, fun y hy ↦ h hG.some y hG.some_mem hy⟩, fun ⟨x, hx⟩ => ?_⟩
  exact fun s t hs ht ↦ (hx s hs).symm.trans <| hx t ht

lemma exists_not_connBetween_of_not_preconnected (h : ¬ G.Preconnected) (hx : x ∈ V(G)) :
    ∃ y ∈ V(G), ¬ G.ConnBetween x y := by
  simp only [preconnected_iff_exists_connBetween ⟨x, hx⟩, not_exists, not_forall, exists_prop] at h
  exact h x

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

lemma Separation.not_connected (S : G.Separation) : ¬ G.Connected := by
  obtain ⟨x, hx⟩ := S.nonempty_left
  obtain ⟨y, hy⟩ := S.nonempty_right
  exact fun h ↦ S.not_connBetween hx hy <| h.connBetween (S.left_subset hx)
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
  exact ⟨(exists_separation_of_not_connBetween hx hy hxy).choose⟩

lemma not_connected_iff_nonempty_separation :
    V(G).Nonempty ∧ ¬ G.Connected ↔ Nonempty G.Separation :=
  ⟨fun ⟨hV, hconn⟩ ↦ nonempty_separation_of_not_connected hV hconn,
  fun ⟨S⟩ => ⟨S.vertexSet_nontrivial.nonempty, S.not_connected⟩⟩

lemma Connected.of_isSpanningSubgraph (h : H.Connected) (hsle : H ≤s G) : G.Connected := by
  rw [connected_iff] at h ⊢
  exact ⟨hsle.vertexSet_eq ▸ h.1, h.2.isSpanningSubgraph hsle⟩

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

lemma IsSep.of_vertexDelete (h : (G - X).IsSep S) : G.IsSep (S ∪ (V(G) ∩ X)) where
  subset_vx := by
    have := by simpa [subset_diff] using h.subset_vx
    simp [this.1]
  not_connected := by
    rw [union_comm, ← vertexDelete_vertexDelete, vertexDelete_vertexSet_inter]
    exact h.not_connected

lemma IsSep.of_isSpanningSubgraph (h : G.IsSep S) (hsle : H ≤s G) : H.IsSep S where
  subset_vx := by simp [hsle.vertexSet_eq, h.subset_vx]
  not_connected h' := h.not_connected (h'.of_isSpanningSubgraph <| by gcongr)

lemma IsComplete.isInducedSubgraph (hG : G.IsComplete) (hH : H ≤i G) : H.IsComplete := by
  rintro x hx y hy hne
  exact hH.adj_of_adj (hG x (hH.vertexSet_mono hx) y (hH.vertexSet_mono hy) hne) hx hy

@[simp]
lemma IsComplete.isSep_iff_subset (h : G.IsComplete) : G.IsSep S ↔ S = V(G) := by
  refine ⟨fun hS => hS.subset_vx.antisymm ?_, ?_⟩
  · have := h.isInducedSubgraph (G.vertexDelete_isInducedSubgraph S)
    |>.connected_iff.not.mp hS.not_connected
    simpa only [vertexDelete_vertexSet, not_nonempty_iff_eq_empty, diff_eq_empty] using this
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
  minimal :
    ∀ S' F',
      IsMixedSep G S' F' →
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
    rw [edgeDelete_edgeSet_inter] at hc
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

lemma PreconnGE.anti_right (hle : n ≤ m) (h : G.PreconnGE m) : G.PreconnGE n := by
  intro s t hs ht
  exact h hs ht |>.anti_right hle

@[simp]
lemma preconnGE_one_iff : G.PreconnGE 1 ↔ G.Preconnected := by
  simp [PreconnGE, connBetweenGE_one_iff, Preconnected]

lemma preconnGE_iff_forall_connBetweenGE :
    G.PreconnGE n ↔ ∀ ⦃s t⦄, s ∈ V(G) → t ∈ V(G) → G.ConnBetweenGE s t n := Iff.rfl

lemma preconnGE_iff_forall_preconnected :
    G.PreconnGE n ↔ ∀ ⦃X : Set α⦄, X.encard < ↑n → (G - X).Preconnected := by
  refine ⟨fun h X hX => ?_, fun h s t hs ht C hC => ?_⟩
  · rw [preconnected_iff_isEmpty_separation]
    by_contra! hS
    obtain ⟨S⟩ := hS
    have hcut := h (diff_subset <| S.left_subset S.nonempty_left.some_mem)
        (diff_subset <| S.right_subset S.nonempty_right.some_mem)
        (S.isSepBetween_of_vertexDelete (X := X) S.nonempty_left.some_mem S.nonempty_right.some_mem)
    exact hcut.trans (encard_le_encard inter_subset_right) |>.not_gt hX
  · by_contra! hCn
    have hpre : (G - C).Preconnected := h (X := C) hCn
    have hs' : s ∈ V(G - C) := by simp [vertexDelete_vertexSet, hs, hC.left_not_mem]
    have ht' : t ∈ V(G - C) := by simp [vertexDelete_vertexSet, ht, hC.right_not_mem]
    exact hC.not_connBetween <| hpre s t hs' ht'

lemma preconnGE_iff_forall_setConnGE : G.PreconnGE n ↔ ∀ S T : Set α, S ⊆ V(G) → T ⊆ V(G) →
    G.SetConnGE S T (min ↑n (min S.encard T.encard)).toNat := by
  refine ⟨fun h S T hS hT C hC ↦ ?_, fun h s t hs ht C hC ↦ ?_⟩
  · rw [ENat.coe_toNat (by simp)]
    by_contra! hCcd
    obtain ⟨hCn, hCS, hCT⟩ := (by simpa using hCcd); clear hCcd
    obtain ⟨s, hs, hsC⟩ := diff_nonempty_of_encard_lt_encard hCS
    obtain ⟨t, ht, htC⟩ := diff_nonempty_of_encard_lt_encard hCT
    have := by simpa [SetConnected] using hC.ST_disconnects
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
  rw [ENat.coe_toNat (by simp)] at hcd
  simpa [hsC.not_ge, htC.not_ge] using hcd

lemma PreconnGE.isSpanningSubgraph (hconn : H.PreconnGE n) (hsle : H ≤s G) : G.PreconnGE n :=
  fun _ _ hs ht => hconn (hsle.vertexSet_eq ▸ hs) (hsle.vertexSet_eq ▸ ht) |>.of_le hsle.le

@[simp]
lemma IsComplete.preconnGE (h : G.IsComplete) (n : ℕ) : G.PreconnGE n :=
  fun _ _ hs ht ↦ h.connBetweenGE hs ht n

lemma encard_le_preconnGE_of_not_isComplete (h : ¬ G.IsComplete) (hn : G.PreconnGE n) :
    n ≤ V(G).encard := by
  obtain ⟨x, hx, y, hy, hne, hxy⟩ := by simpa [IsComplete] using h
  exact connBetweenGE_le_encard (hn hx hy) hne hxy

-- lemma PreconnGE.edgeDelete_singleton_of_not_isComplete (h : G.PreconnGE n)
--     (hne : ¬ G.IsComplete) (e : β) : (G ＼ {e}).PreconnGE (n - 1) := by
--   obtain he | he := (em <| e ∈ E(G)).symm
--   · rw [edgeDelete_eq _ (by simpa)]
--     exact h.anti_right (by omega)
--   rintro s t hs ht


@[simp]
lemma connGE_zero : G.ConnGE 0 := by
  obtain h | h := V(G).eq_empty_or_nonempty <;> simp [connGE_iff, h]

lemma ConnGE.anti_right (hle : n ≤ m) (h : G.ConnGE m) : G.ConnGE n where
  le_cut C hC := (by norm_cast : (n : ℕ∞) ≤ ↑m).trans (h.le_cut hC)
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
lemma bouquet_vertexDelete : (bouquet v F) - v = ⊥ :=
  (vertexDelete_eq_bot_iff (bouquet v F) {v}).mpr <| by simp

@[simp]
lemma connGE_bouquet_iff (n : ℕ) : (bouquet v F).ConnGE n ↔ n ≤ 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ConnGE.anti_right h <| by simp⟩
  simpa using h.le_cut (C := {v}) ⟨by simp, by
    rw [← vertexDelete_singleton, bouquet_vertexDelete]
    simp⟩

lemma connGE_iff_of_vertexSet_singleton (h : V(G) = {x}) : G.ConnGE n ↔ n ≤ 1 := by
  rw [eq_bouquet h, connGE_bouquet_iff]

lemma ConnGE.pre (h : G.ConnGE n) : G.PreconnGE n := by
  rw [preconnGE_iff_forall_preconnected]
  intro X hX
  by_contra! hc
  have := mt Connected.pre hc
  have := by simpa using h.le_cut (isSep_of_not_connected this)
  exact hX.not_ge <| this.trans <| encard_le_encard inter_subset_right

/-- If `G` is not complete, (or contain a complete graph as a spanning subgraph), then
  `G.PreconnGE n` is equivalent to `G.ConnGE n`. -/
lemma preconnGE_iff_connGE_of_not_isComplete (h : ¬ G.IsComplete) (n : ℕ) :
    G.PreconnGE n ↔ G.ConnGE n := by
  refine ⟨fun hn ↦ ⟨fun C hC ↦ ?_ , ?_⟩, fun hn ↦ hn.pre⟩
  · have := hC.not_connected
    rw [connected_iff, not_and_or] at this
    simp only [vertexDelete_vertexSet, not_nonempty_iff_eq_empty, diff_eq_empty] at this
    obtain hsu | hne := this
    · obtain ⟨x, hx, y, hy, hne, hxy⟩ := by simpa [IsComplete] using h
      exact connBetweenGE_le_encard (hn hx hy) hne hxy |>.trans <| encard_le_encard hsu
    rw [preconnGE_iff_forall_preconnected] at hn
    exact not_lt.mp <| mt (hn (X := C)) hne
  rw [or_iff_not_imp_left, not_subsingleton_iff]
  rintro -
  obtain ⟨x, hx, y, hy, hne, hxy⟩ := by simpa [IsComplete] using h
  grw [← ENat.add_one_le_iff (by simp), connBetweenGE_le_diff_encard (hn hx hy) hne hxy,
    ← encard_insert_of_notMem (a := x) (by simp)]
  exact encard_le_encard <| by simp [hx, insert_subset_iff]

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

lemma ConnGE.isSpanningSubgraph (h : H.ConnGE n) (hsle : H ≤s G) : G.ConnGE n where
  le_cut C hC := by simpa using h.le_cut <| hC.of_isSpanningSubgraph hsle
  le_card := hsle.vertexSet_eq ▸ h.le_card

lemma ConnGE.of_edgeDelete (h : (G ＼ F).ConnGE n) : G.ConnGE n :=
  h.isSpanningSubgraph edgeDelete_isSpanningSubgraph

lemma ConnGE.vertexDelete (h : G.ConnGE n) (hFin : (V(G) ∩ X).Finite) :
    (G - X).ConnGE (n - (V(G) ∩ X).encard).toNat where
  le_cut C hC := by
    rw [ENat.coe_toNat (by simp), tsub_le_iff_right, ← encard_union_eq]
    exact h.le_cut hC.of_vertexDelete
    · have := by simpa [subset_diff] using hC.subset_vx
      exact this.2.mono_right inter_subset_right
  le_card := by
    rw [inter_comm] at hFin
    by_cases hss : V(G - X).Subsingleton
    · left
      exact hss
    have : V(G - X).encard = V(G).encard - (X ∩ V(G)).encard := by
      rw [vertexDelete_vertexSet, ← diff_inter_self_eq_diff, encard_diff inter_subset_right hFin]
    rw [not_subsingleton_iff, ← one_lt_encard_iff_nontrivial, this] at hss
    refine h.le_card.imp (fun h a ha b hb ↦ h ha.1 hb.1) (fun h ↦ ?_)
    rw [ENat.coe_toNat (by simp), this, inter_comm]
    enat_to_nat! <;> omega

-- lemma ConnGE.edgeDelete_singleton (h : G.ConnGE (n+1)) (e : β) :
--     (G ＼ {e}).ConnGE n where
--   le_cut C hC := by
--     by_contra! hcd
--     have := h.le_cut hC.of_edgeDelete
--   le_card := by
--     rw [← encard_singleton]

-- lemma ConnGE.edgeDelete_parallel (h : G.ConnGE (n+1)) (u v : α) :
--     (G ＼ {e | G.IsLink e u v}).ConnGE n where
--   le_cut C hC := by

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
