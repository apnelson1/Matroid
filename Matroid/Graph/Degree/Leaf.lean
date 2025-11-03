import Matroid.Graph.Degree.Basic
import Matroid.Graph.Subgraph.Add

variable {α β : Type*} [CompleteLattice α] {x y z u v w : α} {e f : β} {G H : Graph α β}

open Set WList

namespace Graph

/-! ### Isolated vertices -/



/-- An `Isolated` vertex is one that is incident with no edge. -/
@[mk_iff]
structure Isolated (G : Graph α β) (x : α) : Prop where
  not_inc : ∀ ⦃e⦄, ¬ G.Inc e x
  mem : x ∈ V(G)

lemma Isolated.eDegree (h : G.Isolated x) : G.eDegree x = 0 := by
  simp [eDegree_eq_tsum_mem, h.not_inc]

lemma isolated_iff_eDegree (hx : x ∈ V(G)) : G.Isolated x ↔ G.eDegree x = 0 := by
  simp [isolated_iff, hx, eDegree_eq_tsum_mem]

lemma Isolated.degree (h : G.Isolated x) : G.degree x = 0 := by
  rw [Graph.degree, h.eDegree, ENat.toNat_zero]

lemma isolated_iff_degree [G.LocallyFinite] (hx : x ∈ V(G)) : G.Isolated x ↔ G.degree x = 0 := by
  rw [← Nat.cast_inj (R := ℕ∞), natCast_degree_eq, isolated_iff_eDegree hx, Nat.cast_zero]

lemma Isolated.not_adj (h : G.Isolated x) : ¬ G.Adj x y :=
  fun ⟨_, he⟩ ↦ h.not_inc he.inc_left

lemma Isolated.not_isLink (h : G.Isolated x) : ¬ G.IsLink e x y :=
  fun he ↦ h.not_inc he.inc_left

lemma isolated_or_exists_isLink (hx : x ∈ V(G)) : G.Isolated x ∨ ∃ e y, G.IsLink e x y := by
  simp [isolated_iff, Inc, ← not_exists, hx, em']

/-- If `H` is a subgraph of `G` containing all edges and isolated vertices of `G`, then `H = G`-/
lemma eq_of_le_of_edgeSet_subset_of_isolated (hle : H ≤ G) (hE : E(G) ⊆ E(H))
    (hV : ∀ ⦃v⦄, G.Isolated v → v ∈ V(H)) : H = G := by
  refine ext_of_le_le hle le_rfl ((vertexSet_mono hle).antisymm ?_) ((edgeSet_mono hle).antisymm hE)
  exact fun v hv ↦ (isolated_or_exists_isLink hv).elim (fun h ↦ hV h)
    fun ⟨e, y, h⟩ ↦ (h.of_le_of_mem hle  (hE h.edge_mem)).left_mem

/-! ### Leaves -/

/-- `G.IsPendant e x` means that `e` is a nonloop edge at `x`, and is also the only edge at `x`. -/
@[mk_iff]
structure IsPendant (G : Graph α β) (e : β) (x : α) : Prop where
  isNonloopAt : G.IsNonloopAt e x
  edge_unique : ∀ ⦃f⦄, G.Inc f x → f = e

lemma IsPendant.not_isLoopAt (h : G.IsPendant e x) (f : β) : ¬ G.IsLoopAt f x := by
  refine fun h' ↦ h.isNonloopAt.not_isLoopAt x ?_
  rwa [← h.edge_unique h'.inc]

lemma IsPendant.eDegree (h : G.IsPendant e x) : G.eDegree x = 1 := by
  have hrw : {e | G.IsNonloopAt e x} = {e} := by
    simp +contextual only [Set.ext_iff, mem_setOf_eq, mem_singleton_iff, iff_def, h.isNonloopAt,
      implies_true, and_true]
    exact fun f hf ↦ h.edge_unique hf.inc
  simp [eDegree_eq_encard_add_encard, h.not_isLoopAt, hrw]

lemma Inc.isPendant_of_eDegree_le_one (h : G.Inc e x) (hdeg : G.eDegree x ≤ 1) :
    G.IsPendant e x := by
  replace hdeg := hdeg.antisymm h.one_le_eDegree
  have hnl : ∀ f, ¬ G.IsLoopAt f x := fun f hf ↦ by simpa using hf.two_le_eDegree.trans_eq hdeg
  refine ⟨h.isLoopAt_or_isNonloopAt.elim (fun h ↦ (hnl _ h).elim) id, fun f hf ↦ ?_⟩
  rw [inc_iff_isLoopAt_or_isNonloopAt, or_iff_right (hnl _)] at h hf
  rw [eDegree_eq_encard_add_encard] at hdeg
  have hss := encard_le_one_iff_subsingleton.1 <| le_add_self.trans hdeg.le
  exact hss hf h

lemma Inc.isPendant_of_degree_eq_one (h : G.Inc e x) (hdeg : G.degree x = 1) : G.IsPendant e x := by
  refine h.isPendant_of_eDegree_le_one ?_
  simp only [degree, ENat.toNat_eq_iff_eq_coe, Nat.cast_one] at hdeg
  exact hdeg.le

lemma Inc.isPendant_of_degree_le_one [G.LocallyFinite] (h : G.Inc e x) (hdeg : G.degree x ≤ 1) :
    G.IsPendant e x :=
  h.isPendant_of_eDegree_le_one <| by rwa [← natCast_degree_eq, ← Nat.cast_one, Nat.cast_le]

lemma IsPendant.edgeSet_delete_vertex_eq (h : G.IsPendant e x) : E(G - {x}) = E(G) \ {e} := by
  ext f
  simp only [vertexDelete_edgeSet, mem_singleton_iff, mem_setOf_eq, mem_diff]
  refine ⟨fun ⟨z, y, h'⟩ ↦ ⟨h'.1.edge_mem, ?_⟩, fun ⟨hfE, hfe⟩ ↦ ?_⟩
  · rintro rfl
    cases h.isNonloopAt.inc.eq_or_eq_of_isLink h'.1 <;> simp_all
  obtain ⟨y, hyx, hy⟩ := h.isNonloopAt
  obtain ⟨z, w, hzw⟩ := exists_isLink_of_mem_edgeSet hfE
  refine ⟨z, w, hzw, fun h_eq ↦ hfe ?_, fun h_eq ↦ hfe ?_⟩
  · exact h.edge_unique ((h_eq ▸ hzw).inc_left)
  exact h.edge_unique (h_eq ▸ hzw.inc_right)

-- lemma IsPendant.eq_addEdge (h : G.IsPendant e x) :
--     ∃ y ∈ V(G), G.IsLink e x y ∧ y ≠ x ∧ e ∉ E(G-{x}) ∧ G = (G - {x}).addEdge e x y := by
--   obtain ⟨y, hne, hexy⟩ := h.isNonloopAt
--   refine ⟨y, hexy.right_mem, hexy, hne, ?_, ext_of_le_le le_rfl ?_ ?_ ?_⟩
--   · rw [h.edgeSet_delete_vertex_eq]
--     simp
--   · exact Graph.union_le (by simpa) (by simp)
--   · rw [addEdge_vertexSet, vertexDelete_vertexSet, ← union_singleton, union_assoc]
--     simp [insert_eq_of_mem hexy.right_mem, insert_eq_of_mem hexy.left_mem]
--   rw [addEdge_edgeSet, h.edgeSet_delete_vertex_eq, insert_diff_singleton,
--     insert_eq_of_mem hexy.edge_mem]

-- lemma IsPendant.exists_eq_addEdge (h : G.IsPendant e x) :
--     ∃ (y : α) (H : Graph α β), x ∉ V(H) ∧ y ∈ V(H) ∧ e ∉ E(H) ∧ G = H.addEdge e x y := by
--   obtain ⟨y, hyV, -, hyx, -, h_eq⟩ := h.eq_addEdge
--   refine ⟨y, _, by simp, by simp [hyV, hyx], ?_, h_eq⟩
--   rw [h.edgeSet_delete_vertex_eq]
--   simp

/-- A leaf is a degree-one vertex. -/
def IsLeaf (G : Graph α β) (v : α) : Prop := ∃ e, G.IsPendant e v

lemma IsPendant.isLeaf (h : G.IsPendant e x) : G.IsLeaf x :=
  ⟨e, h⟩

@[simp]
lemma eDegree_eq_one_iff : G.eDegree v = 1 ↔ G.IsLeaf v := by
  refine ⟨fun h ↦ ?_, fun ⟨e, h⟩ ↦ h.eDegree⟩
  obtain ⟨e, he⟩ | hn := em <| ∃ e, G.Inc e v
  · exact ⟨e, he.isPendant_of_eDegree_le_one h.le⟩
  simp [← eDegree_eq_zero_iff_inc, h] at hn

@[simp]
lemma degree_eq_one_iff : G.degree v = 1 ↔ G.IsLeaf v := by
  simp [← eDegree_eq_one_iff, degree]

lemma IsLeaf.eDegree (h : G.IsLeaf v) : G.eDegree v = 1 := by
  simpa

lemma IsLeaf.degree (h : G.IsLeaf v) : G.degree v = 1 := by
  simpa

lemma IsLeaf.mem (h : G.IsLeaf v) : v ∈ V(G) :=
  h.choose_spec.isNonloopAt.vertex_mem

lemma IsLeaf.vertexSet_nontrivial (h : G.IsLeaf v) : V(G).Nontrivial := by
  obtain ⟨e, he⟩ := h
  exact he.isNonloopAt.vertexSet_nontrivial

/-- Maybe not needed with `IsPendant`. -/
lemma IsLeaf.exists_unique_inc (h : G.IsLeaf x) : ∃! e, G.Inc e x :=
  ⟨h.choose, h.choose_spec.isNonloopAt.inc, h.choose_spec.edge_unique⟩

lemma IsLeaf.exists_unique_adj (h : G.IsLeaf x) : ∃! y, G.Adj x y := by
  obtain ⟨e, ⟨y, he⟩, hunique⟩ := h.exists_unique_inc
  refine ⟨y, he.adj, fun z ⟨f, hz⟩ ↦ ?_⟩
  rw [hunique f hz.inc_left] at hz
  exact hz.right_unique he

lemma IsLeaf.eq_of_adj_adj (h : G.IsLeaf x) (hu : G.Adj x u) (hv : G.Adj x v) :
    u = v := by
  obtain ⟨y, hy, hun⟩ := h.exists_unique_adj
  rw [hun u hu, hun v hv]

lemma IsLeaf.dup_of_inc_inc (h : G.IsLeaf x) (he : G.Inc e x) (hf : G.Inc f x) :
    e = f := by
  obtain ⟨g, hg, hun⟩ := h.exists_unique_inc
  rw [hun e he, hun f hf]

lemma IsLeaf.not_adj_self (h : G.IsLeaf x) : ¬ G.Adj x x := by
  rintro ⟨e, he : G.IsLoopAt e x⟩
  obtain ⟨f, h⟩ := h
  exact h.not_isLoopAt e he

lemma IsLeaf.ne_of_adj (h : G.IsLeaf x) (hxy : G.Adj x y) : x ≠ y :=
  fun h' ↦ h.not_adj_self <| h' ▸ hxy

lemma IsLeaf.not_isLoopAt (h : G.IsLeaf x) (e) : ¬ G.IsLoopAt e x :=
  fun h' ↦ h.not_adj_self h'.adj

/-- A leaf edge is an edge incident with a degree-one vertex. -/
def IsLeafEdge (G : Graph α β) (e : β) := ∃ x, G.IsPendant e x
