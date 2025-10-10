import Matroid.Graph.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Tactic.TFAE
import Mathlib.Data.Set.Card

variable {α β : Type*} [CompleteLattice α] {x y z u v w : α} {e f : β} {G H K : Graph α β}
    {F F₁ F₂ : Set β} {X Y : Set α}

open Set Partition

open scoped Sym2

namespace Graph

/-- `IsSubgraph H G` means that `V(H) ⊆ V(G)`, and every link in `H` is a link in `G`. -/
structure IsSubgraph (H G : Graph α β) : Prop where
  vertexSet_subset : V(H) ⊆ V(G)
  isLink_of_isLink : ∀ ⦃e x y⦄, H.IsLink e x y → G.IsLink e x y

/-- The subgraph order is a partial order on graphs. -/
instance : PartialOrder (Graph α β) where
  le := IsSubgraph
  le_refl _ := ⟨rfl.subset, by simp⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, fun _ _ _ h ↦ h₂.2 (h₁.2 h)⟩
  le_antisymm G H h₁ h₂ := Graph.ext (h₁.1.antisymm h₂.1)
    fun e x y ↦ ⟨fun a ↦ h₁.isLink_of_isLink a, fun a ↦ h₂.isLink_of_isLink a⟩

lemma IsLink.of_le (h : H.IsLink e x y) (hle : H ≤ G) : G.IsLink e x y :=
  hle.2 h

lemma IsLink.of_le_of_mem (h : G.IsLink e x y) (hle : H ≤ G) (he : e ∈ E(H)) : H.IsLink e x y := by
  obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet he
  obtain ⟨rfl, rfl⟩ | ⟨rfl,rfl⟩ := (huv.of_le hle).eq_and_eq_or_eq_and_eq h
  · assumption
  exact huv.symm

lemma Inc.of_le (h : H.Inc e x) (hle : H ≤ G) : G.Inc e x :=
  (h.choose_spec.of_le hle).inc_left

lemma Inc.of_le_of_mem (h : G.Inc e x) (hle : H ≤ G) (he : e ∈ E(H)) : H.Inc e x := by
  obtain ⟨y, hy⟩ := h
  exact (hy.of_le_of_mem hle he).inc_left

lemma IsLoopAt.of_le (h : H.IsLoopAt e x) (hle : H ≤ G) : G.IsLoopAt e x :=
  IsLink.of_le h hle

lemma IsNonloopAt.of_le (h : H.IsNonloopAt e x) (hle : H ≤ G) : G.IsNonloopAt e x := by
  obtain ⟨y, hxy, he⟩ := h
  exact ⟨y, hxy, he.of_le hle⟩

lemma Adj.of_le (h : H.Adj x y) (hle : H ≤ G) : G.Adj x y :=
  (h.choose_spec.of_le hle).adj

lemma vertexSet_mono (h : H ≤ G) : V(H) ⊆ V(G) :=
  h.1

lemma vertexPartition_mono (h : H ≤ G) : P(H) ⊆ P(G) := by
  change P(H).parts ⊆ P(G).parts
  rw [G.vertexPartition_parts, H.vertexPartition_parts]
  exact h.1

lemma edgeSet_mono (h : H ≤ G) : E(H) ⊆ E(G) := by
  refine fun e he ↦ ?_
  obtain ⟨x, y, h'⟩ := exists_isLink_of_mem_edgeSet he
  exact (h'.of_le h).edge_mem

lemma le_iff : H ≤ G ↔ (V(H) ⊆ V(G)) ∧ ∀ ⦃e x y⦄, H.IsLink e x y → G.IsLink e x y :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

lemma isLink_iff_isLink_of_le_of_mem (hle : H ≤ G) (he : e ∈ E(H)) :
    G.IsLink e x y ↔ H.IsLink e x y :=
  ⟨fun h ↦ h.of_le_of_mem hle he, fun h ↦ h.of_le hle⟩

lemma le_of_le_le_subset_subset {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) (hV : V(H₁) ⊆ V(H₂))
    (hE : E(H₁) ⊆ E(H₂)) : H₁ ≤ H₂ where
  vertexSet_subset := hV
  isLink_of_isLink e x y h := by
    rw [← G.isLink_iff_isLink_of_le_of_mem h₂ (hE h.edge_mem)]
    exact h.of_le h₁

lemma ext_of_le_le {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) (hV : V(H₁) = V(H₂))
    (hE : E(H₁) = E(H₂)) : H₁ = H₂ :=
  (le_of_le_le_subset_subset h₁ h₂ (by simp [hV]) hE.subset).antisymm <|
    (le_of_le_le_subset_subset h₂ h₁ (by simp [hV]) hE.symm.subset)

lemma isLink_eq_of_le (hle : H ≤ G) (he : e ∈ E(H)) : H.IsLink e = G.IsLink e := by
  ext x y
  exact ⟨fun h ↦ h.of_le hle, fun h ↦ h.of_le_of_mem hle he⟩

lemma isLink_eqOn_of_le (hle : H ≤ G) : EqOn H.IsLink G.IsLink E(H) :=
  fun _ ↦ isLink_eq_of_le hle

lemma inc_eq_of_le (hle : H ≤ G) (he : e ∈ E(H)) : H.Inc e = G.Inc e := by
  unfold Graph.Inc
  rw [isLink_eq_of_le hle he]

lemma inc_eqOn_of_le (hle : H ≤ G) : EqOn H.Inc G.Inc E(H) :=
  fun _ ↦ inc_eq_of_le hle

lemma isLoopAt_eq_of_le (hle : H ≤ G) (he : e ∈ E(H)) : H.IsLoopAt e = G.IsLoopAt e := by
  unfold Graph.IsLoopAt
  rw [isLink_eq_of_le hle he]

lemma isLoopAt_eqOn_of_le (hle : H ≤ G) : EqOn H.IsLoopAt G.IsLoopAt E(H) :=
  fun _ ↦ isLoopAt_eq_of_le hle

lemma isNonloopAt_eq_of_le (hle : H ≤ G) (he : e ∈ E(H)) : H.IsNonloopAt e = G.IsNonloopAt e := by
  unfold Graph.IsNonloopAt
  rw [isLink_eq_of_le hle he]

lemma isNonloopAt_eqOn_of_le (hle : H ≤ G) : EqOn H.IsNonloopAt G.IsNonloopAt E(H) :=
  fun _ ↦ isNonloopAt_eq_of_le hle

lemma vertexSet_ssubset_or_edgeSet_ssubset_of_lt (h : G < H) : V(G) ⊂ V(H) ∨ E(G) ⊂ E(H) := by
  rw [lt_iff_le_and_ne] at h
  simp only [ssubset_iff_subset_ne, vertexSet_mono h.1, ne_eq, true_and, edgeSet_mono h.1]
  by_contra! heq
  exact h.2 <| ext_of_le_le h.1 le_rfl heq.1 heq.2


/- TODO : Is is reasonable to only keep the `EqOn` versions of the above?
Also, what about functional `≤` versions? -/

/-! ### Spanning Subgraphs -/

/-- A spanning subgraph of `G` is a subgraph of `G` with the same vertex set. -/
@[mk_iff]
structure IsSpanningSubgraph (H G : Graph α β) : Prop where
  vertexSet_eq : V(H) = V(G)
  isLink_of_isLink : ∀ ⦃e x y⦄, H.IsLink e x y → G.IsLink e x y

/-- `H ≤s G` means that `H` is a spanning subgraph of `G`. -/
infixl:50 " ≤s " => Graph.IsSpanningSubgraph

lemma IsSpanningSubgraph.le (hsle : H ≤s G) : H ≤ G where
  vertexSet_subset := by rw [hsle.vertexSet_eq]
  isLink_of_isLink := hsle.isLink_of_isLink

lemma IsSpanningSubgraph.vertexSet (hsle : H ≤s G) : V(H) = V(G) := by
  simp_rw [hsle.vertexSet_eq]

lemma IsSpanningSubgraph.of_isSpanningSubgraph_left (hsle : H ≤s G) (hHK : H ≤ K) (hKG : K ≤ G) :
    H ≤s K where
  vertexSet_eq := hHK.vertexSet_subset.antisymm <| hsle.vertexSet_eq ▸ hKG.vertexSet_subset
  isLink_of_isLink := hHK.isLink_of_isLink

lemma IsSpanningSubgraph.of_isSpanningSubgraph_right (hsle : H ≤s G) (hHK : H ≤ K) (hKG : K ≤ G) :
    K ≤s G where
  vertexSet_eq := hKG.vertexSet_subset.antisymm <| hsle.vertexSet_eq ▸ hHK.vertexSet_subset
  isLink_of_isLink := hKG.isLink_of_isLink

/-! ### Induced Subgraphs -/

/-- An induced subgraph of `G` is a subgraph `H` of `G` such that every link of `G`
involving two vertices of `H` is also a link of `H`. -/
structure IsInducedSubgraph (H G : Graph α β) : Prop where
  le : H ≤ G
  isLink_of_mem_mem : ∀ ⦃e x y⦄, G.IsLink e x y → x ∈ V(H) → y ∈ V(H) → H.IsLink e x y

/-- `H ≤i G` means that `H` is an induced subgraph of `G`. -/
scoped infixl:50 " ≤i " => Graph.IsInducedSubgraph


lemma IsInducedSubgraph.trans {G₁ G₂ G₃ : Graph α β} (h₁₂ : G₁ ≤i G₂) (h₂₃ : G₂ ≤i G₃) : G₁ ≤i G₃ :=
  ⟨h₁₂.le.trans h₂₃.le, fun _ _ _ h hx hy ↦ h₁₂.isLink_of_mem_mem
    (h₂₃.isLink_of_mem_mem h (vertexSet_mono h₁₂.le hx) (vertexSet_mono h₁₂.le hy)) hx hy⟩

lemma isInducedSubgraph_iff :
    H ≤i G ↔ H ≤ G ∧ ∀ ⦃e x y⦄, G.IsLink e x y → x ∈ V(H) → y ∈ V(H) → H.IsLink e x y :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

lemma IsInducedSubgraph.adj_of_adj (h : H ≤i G) (hxy : G.Adj x y) (hx : x ∈ V(H)) (hy : y ∈ V(H)) :
    H.Adj x y := by
  obtain ⟨e, hxy⟩ := hxy
  exact (h.isLink_of_mem_mem hxy hx hy).adj

/-! ### Closed Subgraphs -/

/-- A closed subgraph of `G` is a union of components of `G`.  -/
@[mk_iff]
structure IsClosedSubgraph (H G : Graph α β) : Prop extends H ≤ G where
  closed : ∀ ⦃e x⦄, G.Inc e x → x ∈ V(H) → e ∈ E(H)

/-- `H ≤c G` means that `H` is a closed subgraph of `G`. i.e. a union of components of `G`. -/
scoped infixl:50 " ≤c " => Graph.IsClosedSubgraph

lemma IsClosedSubgraph.le (h : H ≤c G) : H ≤ G := h.1

lemma IsClosedSubgraph.vertexSet_mono (h : H ≤c G) : V(H) ⊆ V(G) := Graph.vertexSet_mono h.le

lemma IsClosedSubgraph.edgeSet_mono (h : H ≤c G) : E(H) ⊆ E(G) := Graph.edgeSet_mono h.le

lemma IsClosedSubgraph.isInducedSubgraph (h : H ≤c G) : H ≤i G where
  le := h.le
  isLink_of_mem_mem _ _ _ he hx _ := he.of_le_of_mem h.le (h.closed he.inc_left hx)

lemma IsClosedSubgraph.trans {G₁ G₂ G₃ : Graph α β} (h₁ : G₁ ≤c G₂) (h₂ : G₂ ≤c G₃) : G₁ ≤c G₃ where
  toIsSubgraph := h₁.le.trans h₂.le
  closed _ _ h hx :=  h₁.closed (h.of_le_of_mem h₂.le (h₂.closed h (h₁.vertexSet_mono hx))) hx

@[simp]
lemma isClosedSubgraph_self : G ≤c G where
  toIsSubgraph := le_refl G
  closed _ _ he _ := he.edge_mem

lemma Inc.of_isClosedSubgraph_of_mem (h : G.Inc e x) (hle : H ≤c G) (hx : x ∈ V(H)) : H.Inc e x :=
  h.of_le_of_mem hle.le (hle.closed h hx)

lemma IsLink.of_isClosedSubgraph_of_mem (h : G.IsLink e x y) (hle : H ≤c G) (hx : x ∈ V(H)) :
    H.IsLink e x y :=
  h.of_le_of_mem hle.le (h.inc_left.of_isClosedSubgraph_of_mem hle hx).edge_mem

lemma IsClosedSubgraph.isLink_iff_of_mem (h : H ≤c G) (hx : x ∈ V(H)) :
    H.IsLink e x y ↔ G.IsLink e x y :=
  ⟨fun he ↦ he.of_le h.le, fun he ↦ he.of_isClosedSubgraph_of_mem h hx⟩

lemma IsClosedSubgraph.mem_iff_mem_of_isLink (h : H ≤c G) (he : G.IsLink e x y) :
    x ∈ V(H) ↔ y ∈ V(H) := by
  refine ⟨fun hin ↦ ?_, fun hin ↦ ?_⟩
  on_goal 2 => rw [isLink_comm] at he
  all_goals rw [← h.isLink_iff_of_mem hin] at he; exact he.right_mem

lemma IsClosedSubgraph.mem_tfae_of_isLink (h : H ≤c G) (he : G.IsLink e x y) :
    List.TFAE [x ∈ V(H), y ∈ V(H), e ∈ E(H)] := by
  tfae_have 1 → 2 := (h.mem_iff_mem_of_isLink he).mp
  tfae_have 2 → 3 := (he.symm.of_isClosedSubgraph_of_mem h · |>.edge_mem)
  tfae_have 3 → 1 := (he.of_le_of_mem h.le · |>.left_mem)
  tfae_finish

lemma IsClosedSubgraph.edge_mem_iff_vertex_mem_of_inc (h : H ≤c G) (hex : G.Inc e x) :
    e ∈ E(H) ↔ x ∈ V(H) := ⟨fun he ↦ hex.of_le_of_mem h.le he |>.vertex_mem, h.closed hex⟩

lemma IsClosedSubgraph.adj_of_adj_of_mem (h : H ≤c G) (hx : x ∈ V(H)) (hxy : G.Adj x y) :
    H.Adj x y := by
  obtain ⟨e, hexy⟩ := hxy
  exact (hexy.of_isClosedSubgraph_of_mem h hx).adj

lemma IsClosedSubgraph.mem_iff_mem_of_adj (h : H ≤c G) (hxy : G.Adj x y) :
    x ∈ V(H) ↔ y ∈ V(H) := by
  obtain ⟨e, hexy⟩ := hxy
  exact mem_iff_mem_of_isLink h hexy

lemma IsClosedSubgraph.of_le_of_le {G₁ : Graph α β} (hHG : H ≤c G) (hHG₁ : H ≤ G₁) (hG₁ : G₁ ≤ G):
    H ≤c G₁ where
  toIsSubgraph := hHG₁
  closed _ _ he hx := ((he.of_le hG₁).of_isClosedSubgraph_of_mem hHG hx).edge_mem

lemma not_isClosedSubgraph_iff_of_IsInducedSubgraph (hle : H ≤i G) : ¬ H ≤c G ↔ ∃ x y, G.Adj x y ∧
    x ∈ V(H) ∧ y ∉ V(H) := by
  rw [not_iff_comm]
  push_neg
  exact ⟨fun hncl ↦ ⟨hle.le, fun e x ⟨y, hexy⟩ hxH =>
    hle.isLink_of_mem_mem hexy hxH (hncl x y ⟨e, hexy⟩ hxH) |>.edge_mem⟩,
    fun hcl x y hexy hx ↦ (hcl.mem_iff_mem_of_adj hexy).mp hx⟩

/-! ### Components -/

/-- A component of `G` is a minimal nonempty closed subgraph of `G`. -/
def IsCompOf (H G : Graph α β) : Prop := Minimal (fun H ↦ H ≤c G ∧ V(H).Nonempty) H

lemma IsCompOf.isClosedSubgraph (h : H.IsCompOf G) : H ≤c G :=
  h.prop.1

lemma IsCompOf.isInducedSubgraph (hHco : H.IsCompOf G) : H ≤i G :=
  hHco.isClosedSubgraph.isInducedSubgraph

lemma IsCompOf.le (h : H.IsCompOf G) : H ≤ G :=
  h.isClosedSubgraph.le

lemma IsCompOf.nonempty (h : H.IsCompOf G) : V(H).Nonempty :=
  h.prop.2
