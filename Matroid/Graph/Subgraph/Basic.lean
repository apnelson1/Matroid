import Matroid.Graph.Basic
import Mathlib.Data.Set.Card

variable {α β : Type*} {x y z u v w : α} {e f : β} {G H K : Graph α β} {F F₁ F₂ : Set β}
    {X Y : Set α}

open Set

open scoped Sym2

namespace Graph

/-- `Copy` creates an identical graph with different definitions for its vertex set and edge set.
  This is mainly used to create graphs with improved definitional properties. -/
@[simps (attr := grind =)]
def copy (G : Graph α β) {V : Set α} {E : Set β} {IsLink : β → α → α → Prop} (hV : V(G) = V)
    (hE : E(G) = E) (h_isLink : ∀ e x y, G.IsLink e x y ↔ IsLink e x y) : Graph α β where
  vertexSet := V
  edgeSet := E
  IsLink := IsLink
  isLink_symm e he x y := by
    simp_rw [← h_isLink]
    apply G.isLink_symm (hE ▸ he)
  eq_or_eq_of_isLink_of_isLink := by
    simp_rw [← h_isLink]
    exact G.eq_or_eq_of_isLink_of_isLink
  edge_mem_iff_exists_isLink := by
    simp_rw [← h_isLink, ← hE]
    exact G.edge_mem_iff_exists_isLink
  left_mem_of_isLink := by
    simp_rw [← h_isLink, ← hV]
    exact G.left_mem_of_isLink

lemma copy_eq (G : Graph α β) {V : Set α} {E : Set β} {IsLink : β → α → α → Prop}
    (hV : V(G) = V) (hE : E(G) = E) (h_isLink : ∀ e x y, G.IsLink e x y ↔ IsLink e x y) :
    G.copy hV hE h_isLink = G := by
  ext <;> simp_all

/-- `IsSubgraph H G` means that `V(H) ⊆ V(G)`, and every link in `H` is a link in `G`.

  One way to view is that `vertex_subset` ensures the vertices are a subset and `isLink_of_isLink`
  for the vertices. Alternativly, if a vertex has an incident edge, it's existance in guranteed by
  `isLink` condition so the vertex condition exists to handle the isolated vertices. -/
structure IsSubgraph (H G : Graph α β) : Prop where
  vertex_subset : V(H) ⊆ V(G)
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

@[gcongr]
lemma vertexSet_mono (h : H ≤ G) : V(H) ⊆ V(G) :=
  h.1

@[simp]
lemma vertexSet_monotone : Monotone (Graph.vertexSet (α := α) (β := β)) :=
  fun _ _ ↦ vertexSet_mono

@[gcongr]
lemma edgeSet_mono (h : H ≤ G) : E(H) ⊆ E(G) := by
  refine fun e he ↦ ?_
  obtain ⟨x, y, h'⟩ := exists_isLink_of_mem_edgeSet he
  exact (h'.of_le h).edge_mem

@[simp]
lemma edgeSet_monotone : Monotone (Graph.edgeSet (α := α) (β := β)) :=
  fun _ _ ↦ edgeSet_mono

lemma le_iff : H ≤ G ↔ (V(H) ⊆ V(G)) ∧ ∀ ⦃e x y⦄, H.IsLink e x y → G.IsLink e x y :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

@[grind =>]
lemma isLink_iff_isLink_of_le_of_mem (hle : H ≤ G) (he : e ∈ E(H)) :
    G.IsLink e x y ↔ H.IsLink e x y :=
  ⟨fun h ↦ h.of_le_of_mem hle he, fun h ↦ h.of_le hle⟩

@[grind =_]
lemma isLink_iff_isLink_and_mem_of_le (hle : H ≤ G) : H.IsLink e x y ↔ G.IsLink e x y ∧ e ∈ E(H) :=
  ⟨fun h ↦ ⟨h.of_le hle, h.edge_mem⟩, fun h ↦ h.1.of_le_of_mem hle h.2⟩

lemma le_of_le_le_subset_subset {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) (hV : V(H₁) ⊆ V(H₂))
    (hE : E(H₁) ⊆ E(H₂)) : H₁ ≤ H₂ where
  vertex_subset := hV
  isLink_of_isLink e x y h := by
    rw [← G.isLink_iff_isLink_of_le_of_mem h₂ (hE h.edge_mem)]
    exact h.of_le h₁

lemma ext_of_le_le {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) (hV : V(H₁) = V(H₂))
    (hE : E(H₁) = E(H₂)) : H₁ = H₂ :=
  (le_of_le_le_subset_subset h₁ h₂ hV.subset hE.subset).antisymm <|
    (le_of_le_le_subset_subset h₂ h₁ hV.symm.subset hE.symm.subset)

/-- If `H` is a subgraph of `G` containing all edges and isolated vertices of `G`, then `H = G`-/
lemma eq_of_le_of_edgeSet_subset_of_isolated (hle : H ≤ G) (hE : E(G) ⊆ E(H))
    (hV : ∀ ⦃v⦄, G.Isolated v → v ∈ V(H)) : H = G := by
  refine ext_of_le_le hle le_rfl ((vertexSet_mono hle).antisymm ?_) ((edgeSet_mono hle).antisymm hE)
  exact fun v hv ↦ (isolated_or_exists_isLink hv).elim (fun h ↦ hV h)
    fun ⟨e, y, h⟩ ↦ (h.of_le_of_mem hle  (hE h.edge_mem)).left_mem

lemma le_of_le_le_edgeSet_subset_of_isolated {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G)
    (hE : E(H₁) ⊆ E(H₂)) (hV : ∀ ⦃v⦄, H₁.Isolated v → v ∈ V(H₂)) : H₁ ≤ H₂ := by
  refine le_of_le_le_subset_subset h₁ h₂ ?_ hE
  exact fun v hv ↦ (isolated_or_exists_isLink hv).elim (hV ·)
    fun ⟨e, y, h⟩ ↦ h.of_le h₁ |>.of_le_of_mem h₂ (hE h.edge_mem) |>.left_mem

lemma ext_of_le_le_of_isolated {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) (hE : E(H₁) = E(H₂))
    (h : I(H₁) = I(H₂)) : H₁ = H₂ := by
  refine (le_of_le_le_edgeSet_subset_of_isolated h₁ h₂ hE.subset ?_).antisymm
    (le_of_le_le_edgeSet_subset_of_isolated h₂ h₁ hE.superset ?_)
  · exact fun v hv ↦ H₂.isolatedSet_subset (congrArg (v ∈ ·) h |>.mp hv)
  · exact fun v hv ↦ H₁.isolatedSet_subset (congrArg (v ∈ ·) h.symm |>.mp hv)

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

lemma sum_ncard_lt_of_lt [Finite α] [Finite β] (h : G < H) :
    V(G).ncard + E(G).ncard < V(H).ncard + E(H).ncard := by
  obtain hV | hE := vertexSet_ssubset_or_edgeSet_ssubset_of_lt h
  · have hE' : E(G) ⊆ E(H) := edgeSet_mono h.1
    have hVncard : V(G).ncard < V(H).ncard := ncard_lt_ncard hV
    have hEncard : E(G).ncard ≤ E(H).ncard := ncard_le_ncard hE'
    omega
  · have hV' : V(G) ⊆ V(H) := vertexSet_mono h.1
    have hVncard : V(G).ncard ≤ V(H).ncard := ncard_le_ncard hV'
    have hEncard : E(G).ncard < E(H).ncard := ncard_lt_ncard hE
    omega

@[gcongr]
lemma neighbor_mono (hle : G ≤ H) : N(G, x) ⊆ N(H, x) :=
  fun _ ⟨hne, hy⟩ ↦ ⟨hne, hy.of_le hle⟩

@[gcongr]
lemma setNeighbor_mono (hle : G ≤ H) (S : Set α) : N(G, S) ⊆ N(H, S) :=
  fun _ ⟨hne, x, hxS, hadj⟩ ↦ ⟨hne, x, hxS, hadj.of_le hle⟩

@[gcongr]
lemma incEdges_mono (hle : G ≤ H) (x : α) : E(G, x) ⊆ E(H, x) :=
  fun _ he ↦ he.of_le hle

@[gcongr]
lemma setIncEdges_mono (hle : G ≤ H) (S : Set α) : E(G, S) ⊆ E(H, S) :=
  fun _ ⟨x, hxS, he⟩ ↦ ⟨x, hxS, he.of_le hle⟩

@[gcongr]
lemma endSet_mono (hle : G ≤ H) (e : β) : V(G, e) ⊆ V(H, e) :=
  fun _ hx ↦ hx.of_le hle

@[simp]
lemma endSet_eq_of_le (hle : G ≤ H) (he : e ∈ E(G)) : V(H, e) = V(G, e) := by
  ext v
  rw [mem_endSet_iff, mem_endSet_iff, inc_eq_inc_iff.mpr]
  exact isLink_eq_of_le hle he |>.symm

@[gcongr]
lemma endSetSet_mono (hle : G ≤ H) (F : Set β) : V(G, F) ⊆ V(H, F) :=
  fun _ ⟨e, he, hx⟩ ↦ ⟨e, he, hx.of_le hle⟩

lemma endSetSet_subset_of_subset_of_le (hle : G ≤ H) (hF : F ⊆ E(G)) : V(H, F) ⊆ V(G) :=
  fun _ ⟨_, he, hx⟩ ↦ hx.of_le_of_mem hle (hF he) |>.vertex_mem

@[gcongr]
lemma linkEdges_mono (hle : G ≤ H) (u v : α) : E(G, u, v) ⊆ E(H, u, v) :=
  fun _ he ↦ he.of_le hle

lemma linkEdgesSet_mono (hle : G ≤ H) (S T : Set α) : E(G, S, T) ⊆ E(H, S, T) := by
  rintro e ⟨x, hxS, y, hyT, he⟩
  use x, hxS, y, hyT, he.of_le hle

@[grind =>]
lemma linkEdgesSet_eq_inter_of_le (hle : G ≤ H) (S T : Set α) : E(G, S, T) = E(G) ∩ E(H, S, T) := by
  ext e
  simp only [mem_linkEdgesSet_iff, mem_inter_iff]
  grind [isLink_iff_isLink_and_mem_of_le]

lemma linkEdgesSet_eq_inter_of_le' (hle : G ≤ H) (S) : δ(G, S) = E(G) ∩ δ(H, S) := by
  ext e
  rw [linkEdgesSet_eq_inter_of_le hle]
  grind

instance [Finite α] [Finite β] : WellFoundedLT (Graph α β) :=
  ⟨Subrelation.wf sum_ncard_lt_of_lt (measure fun (G : Graph α β) => V(G).ncard + E(G).ncard).2⟩

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

namespace IsSpanningSubgraph

@[simp]
lemma le (h : G ≤s H) : G ≤ H where
  vertex_subset := h.vertexSet_eq.subset
  isLink_of_isLink := h.isLink_of_isLink

lemma isSpanningSubgraph_iff_le_vertexSet_eq : G ≤s H ↔ G ≤ H ∧ V(G) = V(H) :=
  ⟨fun h ↦ ⟨h.le, h.vertexSet_eq⟩, fun h ↦ ⟨h.2, h.1.isLink_of_isLink⟩⟩

lemma trans {G₁ G₂ G₃ : Graph α β} (h₁₂ : G₁ ≤s G₂) (h₂₃ : G₂ ≤s G₃) : G₁ ≤s G₃ :=
  ⟨h₁₂.vertexSet_eq.trans h₂₃.vertexSet_eq, (h₁₂.le.trans h₂₃.le).isLink_of_isLink⟩

instance : IsPartialOrder (Graph α β) (· ≤s ·) where
  refl _ := ⟨rfl, fun _ _ _ ↦ id⟩
  trans _ _ _ h₁ h₂ := h₁.trans h₂
  antisymm _ _ h₁ h₂ := antisymm h₁.le h₂.le

lemma of_isSpanningSubgraph_left (h : H ≤s G) (hHK : H ≤ K) (hKG : K ≤ G) : H ≤s K where
  vertexSet_eq := (vertexSet_mono hHK).antisymm ((vertexSet_mono hKG).trans_eq h.vertexSet_eq.symm)
  isLink_of_isLink := hHK.isLink_of_isLink

lemma of_isSpanningSubgraph_right (h : H ≤s G) (hHK : H ≤ K) (hKG : K ≤ G) : K ≤s G where
  vertexSet_eq := (vertexSet_mono hKG).antisymm <| h.vertexSet_eq.symm.le.trans
  <| vertexSet_mono hHK
  isLink_of_isLink := hKG.isLink_of_isLink

lemma eq_of_edgeSet (h : H ≤s G) (hE : E(H) = E(G)) : H = G :=
  ext_of_le_le h.le le_rfl h.vertexSet_eq hE

end IsSpanningSubgraph

/-! ### Induced Subgraphs -/

/-- An induced subgraph of `G` is a subgraph `H` of `G` such that every link of `G`
involving two vertices of `H` is also a link of `H`. -/
structure IsInducedSubgraph (H G : Graph α β) : Prop where
  le : H ≤ G
  isLink_of_mem_mem : ∀ ⦃e x y⦄, G.IsLink e x y → x ∈ V(H) → y ∈ V(H) → H.IsLink e x y

/-- `H ≤i G` means that `H` is an induced subgraph of `G`. -/
scoped infixl:50 " ≤i " => Graph.IsInducedSubgraph

lemma IsInducedSubgraph.trans {G₁ G₂ G₃ : Graph α β} (h₁₂ : G₁ ≤i G₂) (h₂₃ : G₂ ≤i G₃) :
    G₁ ≤i G₃ :=
  ⟨h₁₂.le.trans h₂₃.le, fun _ _ _ h hx hy ↦ h₁₂.isLink_of_mem_mem
    (h₂₃.isLink_of_mem_mem h (vertexSet_mono h₁₂.le hx) (vertexSet_mono h₁₂.le hy))
    hx hy⟩

lemma IsInducedSubgraph.adj_of_mem_mem (h : H ≤i G) (hxy : G.Adj x y) (hx : x ∈ V(H))
    (hy : y ∈ V(H)) : H.Adj x y := by
  obtain ⟨e, hxy⟩ := hxy
  exact (h.isLink_of_mem_mem hxy hx hy).adj

instance : IsPartialOrder (Graph α β) (· ≤i ·) where
  refl _ := ⟨le_rfl, by tauto⟩
  trans _ _ _ h₁ h₂ := h₁.trans h₂
  antisymm _ _ h₁ h₂ := antisymm h₁.le h₂.le

lemma IsInducedSubgraph.vertexSet_mono (h : H ≤i G) : V(H) ⊆ V(G) :=
  h.le.vertex_subset

lemma IsInducedSubgraph.edgeSet_mono (h : H ≤i G) : E(H) ⊆ E(G) :=
  G.edgeSet_mono h.le

lemma isInducedSubgraph_iff :
    H ≤i G ↔ H ≤ G ∧ ∀ ⦃e x y⦄, G.IsLink e x y → x ∈ V(H) → y ∈ V(H) → H.IsLink e x y :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

lemma IsInducedSubgraph.adj_of_adj (h : H ≤i G) (hxy : G.Adj x y) (hx : x ∈ V(H)) (hy : y ∈ V(H)) :
    H.Adj x y := by
  obtain ⟨e, hxy⟩ := hxy
  exact (h.isLink_of_mem_mem hxy hx hy).adj

lemma IsInducedSubgraph.eq_of_vertexSet (h : H ≤i G) (hV : V(H) = V(G)) : H = G :=
  ext_of_le_le h.le le_rfl hV <| antisymm h.edgeSet_mono <| fun e he ↦ by
    obtain ⟨_, _, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
    exact h.isLink_of_mem_mem hxy (hV ▸ hxy.left_mem) (hV ▸ hxy.right_mem) |>.edge_mem

lemma IsInducedSubgraph.le_of_le_subset (h : H ≤i G) (h' : K ≤ G) (hsu : V(K) ⊆ V(H)) :
    K ≤ H := by
  refine le_of_le_le_subset_subset h' h.le hsu ?_
  intro e he
  rw [isInducedSubgraph_iff] at h
  obtain ⟨u, v, huv⟩ := K.exists_isLink_of_mem_edgeSet he
  exact h.2 (huv.of_le h') (hsu huv.left_mem) (hsu huv.right_mem) |>.edge_mem

/-! ### Closed Subgraphs -/

/-- A closed subgraph of `G` is a union of components of `G`.  -/
@[mk_iff]
structure IsClosedSubgraph (H G : Graph α β) : Prop where
  le : H ≤ G
  closed : ∀ ⦃e x⦄, G.Inc e x → x ∈ V(H) → e ∈ E(H)

/-- `H ≤c G` means that `H` is a closed subgraph of `G`. i.e. a union of components of `G`. -/
scoped infixl:50 " ≤c " => Graph.IsClosedSubgraph

lemma IsClosedSubgraph.vertexSet_mono (h : H ≤c G) : V(H) ⊆ V(G) := Graph.vertexSet_mono h.le

lemma IsClosedSubgraph.edgeSet_mono (h : H ≤c G) : E(H) ⊆ E(G) := Graph.edgeSet_mono h.le

lemma IsClosedSubgraph.isInducedSubgraph (h : H ≤c G) : H ≤i G where
  le := h.le
  isLink_of_mem_mem _ _ _ he hx _ := he.of_le_of_mem h.le (h.closed he.inc_left hx)

lemma IsClosedSubgraph.trans {G₁ G₂ G₃ : Graph α β} (h₁ : G₁ ≤c G₂) (h₂ : G₂ ≤c G₃) : G₁ ≤c G₃ where
  le := h₁.le.trans h₂.le
  closed _ _ h hx :=  h₁.closed (h.of_le_of_mem h₂.le (h₂.closed h (h₁.vertexSet_mono hx))) hx

instance : IsPartialOrder (Graph α β) (· ≤c ·) where
  refl _ := ⟨le_rfl, fun _ _ h _ ↦ h.edge_mem⟩
  trans _ _ _ h₁ h₂ := h₁.trans h₂
  antisymm _ _ h₁ h₂ := antisymm h₁.le h₂.le

@[simp]
lemma isClosedSubgraph_self : G ≤c G where
  le := le_rfl
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

lemma isClosedSubgraph_iff_le_and_linkEdgesSet_empty : H ≤c G ↔ (H ≤i G) ∧ δ(G, V(H)) = ∅ := by
  refine ⟨fun h ↦ ⟨h.isInducedSubgraph, ?_⟩,
    fun ⟨hle, hem⟩ ↦ ⟨hle.le, fun e x ⟨y, hxy⟩ hxH ↦ ?_⟩⟩
  · ext e
    simp only [mem_linkEdgesSet_iff, mem_diff, mem_empty_iff_false, iff_false, not_exists, not_and,
      and_imp]
    rintro x hxH y hyG hyH hxy
    exact hyH <| hxy.of_isClosedSubgraph_of_mem h hxH |>.right_mem
  simp only [Set.ext_iff, mem_empty_iff_false, iff_false] at hem
  specialize hem e
  simp only [hxy.mem_linkEdgesSet_iff, hxH, mem_diff, hxy.right_mem, true_and, not_true_eq_false,
    and_false, false_and, or_false, not_not] at hem
  exact hle.isLink_of_mem_mem hxy hxH hem |>.edge_mem

lemma IsClosedSubgraph.linkEdgesSet_empty (h : H ≤c G) : δ(G, V(H)) = ∅ := by
  rw [isClosedSubgraph_iff_le_and_linkEdgesSet_empty] at h
  exact h.2

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
  le := hHG₁
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

@[simp]
lemma IsCompOf.isClosedSubgraph (h : H.IsCompOf G) : H ≤c G :=
  h.prop.1

@[simp]
lemma IsCompOf.isInducedSubgraph (hHco : H.IsCompOf G) : H ≤i G :=
  hHco.isClosedSubgraph.isInducedSubgraph

@[simp]
lemma IsCompOf.le (h : H.IsCompOf G) : H ≤ G :=
  h.isClosedSubgraph.le

@[simp]
lemma IsCompOf.nonempty (h : H.IsCompOf G) : V(H).Nonempty :=
  h.prop.2

lemma IsCompOf.subset (h : H.IsCompOf G) : V(H) ⊆ V(G) :=
  IsClosedSubgraph.vertexSet_mono h.isClosedSubgraph

instance instvxNonemptyOfEdgeNonempty (G : Graph α β) [hE : Nonempty E(G)] : Nonempty V(G) := by
  obtain ⟨x, y, hbtw⟩ := exists_isLink_of_mem_edgeSet hE.some.prop
  use x, hbtw.left_mem
