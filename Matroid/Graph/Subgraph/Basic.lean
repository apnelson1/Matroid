import Matroid.Graph.Basic

variable {α β : Type*} {x y z u v w : α} {e f : β} {G H K : Graph α β} {F F₁ F₂ : Set β}
    {X Y : Set α}

open Set

open scoped Sym2

namespace Graph

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

@[gcongr] lemma vertexSet_mono (h : H ≤ G) : V(H) ⊆ V(G) := h.vertexSet_mono

@[gcongr] lemma edgeSet_mono (h : H ≤ G) : E(H) ⊆ E(G) := h.edgeSet_mono

@[simp]
lemma vertexSet_monotone : Monotone (Graph.vertexSet (α := α) (β := β)) :=
  fun _ _ ↦ (·.vertexSet_mono)

@[simp]
lemma edgeSet_monotone : Monotone (Graph.edgeSet (α := α) (β := β)) :=
  fun _ _ ↦ (·.edgeSet_mono)

lemma le_iff : H ≤ G ↔ (V(H) ⊆ V(G)) ∧ ∀ ⦃e x y⦄, H.IsLink e x y → G.IsLink e x y :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

@[deprecated IsSubgraph.isLink_iff (since := "2026-05-04")]
lemma isLink_iff_isLink_of_le_of_mem (hle : H ≤ G) (he : e ∈ E(H)) :
    G.IsLink e x y ↔ H.IsLink e x y :=
  ⟨fun h ↦ h.of_le_of_mem hle he, fun h ↦ h.of_le hle⟩

@[grind =_]
lemma isLink_iff_isLink_and_mem_of_le (hle : H ≤ G) : H.IsLink e x y ↔ G.IsLink e x y ∧ e ∈ E(H) :=
  ⟨fun h ↦ ⟨h.of_le hle, h.edge_mem⟩, fun h ↦ h.1.of_le_of_mem hle h.2⟩

lemma le_of_le_le_subset_subset {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) (hV : V(H₁) ⊆ V(H₂))
    (hE : E(H₁) ⊆ E(H₂)) : H₁ ≤ H₂ := (Compatible.of_le_le h₁ h₂).le_iff.mpr ⟨hV, hE⟩

lemma ext_of_le_le {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) (hV : V(H₁) = V(H₂))
    (hE : E(H₁) = E(H₂)) : H₁ = H₂ :=
  (le_of_le_le_subset_subset h₁ h₂ hV.subset hE.subset).antisymm <|
    (le_of_le_le_subset_subset h₂ h₁ hV.symm.subset hE.symm.subset)

/-- If `H` is a subgraph of `G` containing all edges and isolated vertices of `G`, then `H = G`-/
lemma eq_of_le_of_edgeSet_subset_of_isolated (hle : H ≤ G) (hE : E(G) ⊆ E(H))
    (hV : ∀ ⦃v⦄, G.Isolated v → v ∈ V(H)) : H = G := by
  refine ext_of_le_le hle le_rfl (hle.vertexSet_mono.antisymm ?_) (hle.edgeSet_mono.antisymm hE)
  exact fun v hv ↦ (isolated_or_exists_isLink hv).elim (fun h ↦ hV h)
    fun ⟨e, y, h⟩ ↦ (h.of_le_of_mem hle  (hE h.edge_mem)).left_mem

lemma le_of_le_le_edgeSet_subset_of_isolated {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G)
    (hE : E(H₁) ⊆ E(H₂)) (hV : ∀ ⦃v⦄, H₁.Isolated v → v ∈ V(H₂)) : H₁ ≤ H₂ := by
  refine le_of_le_le_subset_subset h₁ h₂ ?_ hE
  exact fun v hv ↦ (isolated_or_exists_isLink hv).elim (hV ·)
    fun ⟨e, y, h⟩ ↦ h.of_le h₁ |>.of_le_of_mem h₂ (hE h.edge_mem) |>.left_mem

lemma ext_of_le_le_of_isolated {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) (hE : E(H₁) = E(H₂))
    (h : Isol(H₁) = Isol(H₂)) : H₁ = H₂ := by
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

@[grind .]
lemma lt_of_le_of_vertexSet_ssubset (hle : G ≤ H) (h : V(G) ⊂ V(H)) : G < H := by
  grind [hle.lt_iff_ne]

@[grind .]
lemma lt_of_le_of_edgeSet_ssubset (hle : G ≤ H) (h : E(G) ⊂ E(H)) : G < H := by
  grind [hle.lt_iff_ne]

lemma exists_edge_or_vertex_of_lt (h : G < H) : (∃ e ∈ E(H), e ∉ E(G)) ∨ ∃ v ∈ V(H), v ∉ V(G) := by
  have := h.ne
  contrapose! this
  refine ext_of_le_le h.le le_rfl ?_ ?_
  · grind [h.le.vertexSet_mono]
  grind [h.le.edgeSet_mono]

lemma sum_ncard_lt_of_lt [Finite α] [Finite β] (h : G < H) :
    V(G).ncard + E(G).ncard < V(H).ncard + E(H).ncard := by
  obtain hV | hE := vertexSet_ssubset_or_edgeSet_ssubset_of_lt h
  · have hE' : E(G) ⊆ E(H) := h.1.edgeSet_mono
    have hVncard : V(G).ncard < V(H).ncard := ncard_lt_ncard hV
    have hEncard : E(G).ncard ≤ E(H).ncard := ncard_le_ncard hE'
    omega
  · have hV' : V(G) ⊆ V(H) := h.1.vertexSet_mono
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
lemma incVertexSet_mono (hle : G ≤ H) (F : Set β) : V(G, F) ⊆ V(H, F) :=
  fun _ ⟨e, he, hx⟩ ↦ ⟨e, he, hx.of_le hle⟩

lemma incVertexSet_subset_of_subset_of_le (hle : G ≤ H) (hF : F ⊆ E(G)) : V(H, F) ⊆ V(G) :=
  fun _ ⟨_, he, hx⟩ ↦ hx.of_le_of_mem hle (hF he) |>.vertex_mem

@[gcongr]
lemma linkEdges_mono (hle : G ≤ H) (u v : α) : E(G, u, v) ⊆ E(H, u, v) :=
  fun _ he ↦ he.of_le hle

lemma setLinkEdges_mono (hle : G ≤ H) (S T : Set α) : E(G, S, T) ⊆ E(H, S, T) := by
  rintro e ⟨x, hxS, y, hyT, he⟩
  use x, hxS, y, hyT, he.of_le hle

@[grind =>]
lemma setLinkEdges_eq_inter_of_le (hle : G ≤ H) (S T : Set α) : E(G, S, T) = E(G) ∩ E(H, S, T) := by
  ext e
  simp only [mem_setLinkEdges_iff, mem_inter_iff]
  grind

lemma setLinkEdges_eq_inter_of_le' (hle : G ≤ H) (S) : δ(G, S) = E(G) ∩ δ(H, S) := by
  ext e
  rw [setLinkEdges_eq_inter_of_le hle]
  grind

instance [Finite α] [Finite β] : WellFoundedLT (Graph α β) :=
  ⟨Subrelation.wf sum_ncard_lt_of_lt (measure fun (G : Graph α β) => V(G).ncard + E(G).ncard).2⟩

/- TODO : Is is reasonable to only keep the `EqOn` versions of the above?
Also, what about functional `≤` versions? -/

/-! ### Spanning Subgraphs -/

namespace IsSpanningSubgraph

-- lemma isSpanningSubgraph_iff_le_vertexSet_eq : G ≤s H ↔ G ≤ H ∧ V(G) = V(H) :=
--   ⟨fun h ↦ ⟨h.le, h.vertexSet_eq⟩, fun h ↦ ⟨h.2, h.1.isLink_of_isLink⟩⟩

lemma mk' (hV : V(H) = V(G)) (hl : ∀ ⦃e x y⦄, H.IsLink e x y → G.IsLink e x y) : H ≤s G where
  vertexSet_eq := hV

lemma le' (h : H ≤s G) : H ≤ G := h.le

@[deprecated IsSpanningSubgraph.anti_right (since := "2026-05-04")]
lemma of_isSpanningSubgraph_left (h : H ≤s G) (hHK : H ≤ K) (hKG : K ≤ G) : H ≤s K :=
  anti_right hHK hKG h

@[deprecated IsSpanningSubgraph.mono_left (since := "2026-05-04")]
lemma of_isSpanningSubgraph_right (h : H ≤s G) (hHK : H ≤ K) (hKG : K ≤ G) : K ≤s G :=
  mono_left hHK hKG h

@[deprecated IsSpanningSubgraph.ext_of_edgeSet (since := "2026-05-04")]
lemma eq_of_edgeSet (h : H ≤s G) (hE : E(H) = E(G)) : H = G := ext_of_edgeSet hE h

end IsSpanningSubgraph

/-! ### Induced Subgraphs -/

lemma IsInducedSubgraph.le' (h : H ≤i G) : H ≤ G := h.le

@[deprecated IsInducedSubgraph.adj_congr (since := "2026-05-04")]
lemma IsInducedSubgraph.adj_of_mem_mem (h : H ≤i G) (hxy : G.Adj x y) (hx : x ∈ V(H))
    (hy : y ∈ V(H)) : H.Adj x y := (adj_congr hx hy h).mpr hxy

@[deprecated IsInducedSubgraph.adj_congr (since := "2026-05-04")]
lemma IsInducedSubgraph.adj_of_adj (h : H ≤i G) (hxy : G.Adj x y) (hx : x ∈ V(H)) (hy : y ∈ V(H)) :
    H.Adj x y := (adj_congr hx hy h).mpr hxy

@[deprecated IsInducedSubgraph.ext_of_vertexSet (since := "2026-05-04")]
lemma IsInducedSubgraph.eq_of_vertexSet (h : H ≤i G) (hV : V(H) = V(G)) : H = G :=
  ext_of_vertexSet hV h

/-! ### Closed Subgraphs -/

-- lemma IsClosedSubgraph.edgeSet_mono (h : H ≤c G) : E(H) ⊆ E(G) := h.le.edgeSet_mono

lemma IsClosedSubgraph.le' (h : H ≤c G) : H ≤ G := h.le

@[deprecated IsClosedSubgraph.inc_congr (since := "2026-05-04")]
lemma Inc.of_isClosedSubgraph_of_mem (h : G.Inc e x) (hle : H ≤c G) (hx : x ∈ V(H)) : H.Inc e x :=
  (hle.inc_congr hx).mpr h

@[deprecated IsClosedSubgraph.isLink_congr (since := "2026-05-04")]
lemma IsLink.of_isClosedSubgraph_of_mem (h : G.IsLink e x y) (hle : H ≤c G) (hx : x ∈ V(H)) :
    H.IsLink e x y := (hle.isLink_congr hx).mpr h

@[deprecated IsClosedSubgraph.isLink_congr (since := "2026-05-04")]
lemma IsClosedSubgraph.isLink_iff_of_mem (h : H ≤c G) (hx : x ∈ V(H)) :
    H.IsLink e x y ↔ G.IsLink e x y := isLink_congr hx h

@[deprecated IsClosedSubgraph.mem_iff_of_isLink (since := "2026-05-04")]
lemma IsClosedSubgraph.mem_iff_mem_of_isLink (h : H ≤c G) (he : G.IsLink e x y) :
    x ∈ V(H) ↔ y ∈ V(H) := mem_iff_of_isLink he h

lemma isClosedSubgraph_iff_le_and_setLinkEdges_empty : H ≤c G ↔ (H ≤i G) ∧ δ(G, V(H)) = ∅ := by
  refine ⟨fun h ↦ ⟨h.isInducedSubgraph, ?_⟩,
    fun ⟨hle, hem⟩ ↦ ⟨hle, fun e x ⟨y, hxy⟩ hxH ↦ ?_⟩⟩
  · ext e
    simp only [mem_setLinkEdges_iff, mem_diff, mem_empty_iff_false, iff_false, not_exists, not_and,
      and_imp]
    rintro x hxH y hyG hyH hxy
    exact hyH <| (h.isLink_congr hxH).mpr hxy |>.right_mem
  simp only [Set.ext_iff, mem_empty_iff_false, iff_false] at hem
  specialize hem e
  simp only [hxy.mem_setLinkEdges_iff, hxH, mem_diff, hxy.right_mem, true_and, not_true_eq_false,
    and_false, false_and, or_false, not_not] at hem
  exact hle.isLink_of_mem_mem hxy hxH hem |>.edge_mem

lemma IsClosedSubgraph.setLinkEdges_empty (h : H ≤c G) : δ(G, V(H)) = ∅ := by
  rw [isClosedSubgraph_iff_le_and_setLinkEdges_empty] at h
  exact h.2

lemma IsClosedSubgraph.adj_of_adj_of_mem (h : H ≤c G) (hx : x ∈ V(H)) (hxy : G.Adj x y) :
    H.Adj x y := by
  obtain ⟨e, hexy⟩ := hxy
  exact (h.isLink_congr hx).mpr hexy |>.adj

@[deprecated IsClosedSubgraph.mem_iff_of_adj (since := "2026-05-04")]
lemma IsClosedSubgraph.mem_iff_mem_of_adj (h : H ≤c G) (hxy : G.Adj x y) :
    x ∈ V(H) ↔ y ∈ V(H) := mem_iff_of_adj hxy h

@[deprecated IsClosedSubgraph.anti_right (since := "2026-05-04")]
lemma IsClosedSubgraph.of_le_of_le {G₁ : Graph α β} (hHG : H ≤c G) (hHG₁ : H ≤ G₁) (hG₁ : G₁ ≤ G):
    H ≤c G₁ := anti_right hHG₁ hG₁ hHG

@[deprecated IsInducedSubgraph.not_isClosedSubgraph_iff_exists_adj (since := "2026-05-04")]
lemma not_isClosedSubgraph_iff_of_IsInducedSubgraph (hle : H ≤i G) : ¬ H ≤c G ↔ ∃ x y, G.Adj x y ∧
    x ∈ V(H) ∧ y ∉ V(H) := IsInducedSubgraph.not_isClosedSubgraph_iff_exists_adj hle

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
  h.isClosedSubgraph.vertexSet_mono

instance instvxNonemptyOfEdgeNonempty (G : Graph α β) [hE : Nonempty E(G)] : Nonempty V(G) := by
  obtain ⟨x, y, hbtw⟩ := exists_isLink_of_mem_edgeSet hE.some.prop
  use x, hbtw.left_mem
