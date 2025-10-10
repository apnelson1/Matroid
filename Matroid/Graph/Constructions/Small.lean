import Matroid.Graph.Constructions.Basic

variable {α β : Type*} [CompleteLattice α] {x y z u v w a b : α} {e f : β} {G H : Graph α β}
  {F F₁ F₂ : Set β} {X Y : Set α} {P : Partition α} {l : β → α → α → Prop}

open Set Function Relation Partition

open scoped Sym2

namespace Graph


/-! ### Graphs with one vertex  -/

/-- A graph with one vertex and loops at that vertex -/
@[simps]
def bouquet (v : α) (F : Set β) : Graph α β where
  vertexPartition := indiscrete' v
  edgeSet := {e | e ∈ F ∧ v ≠ ⊥}
  IsLink e x y := e ∈ F ∧ v ≠ ⊥ ∧ x = v ∧ y = v
  isLink_symm e := by simp +contextual [Symmetric]
  eq_or_eq_of_isLink_of_isLink := by aesop
  edge_mem_iff_exists_isLink := by aesop
  left_mem_of_isLink := by aesop

@[simp]
lemma bouquet_vertexSet_of_nonempty (hv : v ≠ ⊥) : V(bouquet v F) = {v} := by
  simp [hv]

@[simp]
lemma bouquet_inc_iff (hv : v ≠ ⊥) : (bouquet v F).Inc e x ↔ e ∈ F ∧ x = v := by
  simp [Inc, hv]

@[simp]
lemma bouquet_isLoopAt (hv : v ≠ ⊥) : (bouquet v F).IsLoopAt e x ↔ e ∈ F ∧ x = v := by
  simp [← isLink_self_iff, hv]

@[simp]
lemma bouquet_not_isNonloopAt : ¬ (bouquet v F).IsNonloopAt e x := by
  simp +contextual [IsNonloopAt, eq_comm]

/-- Every graph on just one vertex is a bouquet on that vertex-/
lemma eq_bouquet (hvV : v ∈ V(G)) (hss : V(G).Subsingleton) :
    G = bouquet v E(G) := by
  have hrw := hss.eq_singleton_of_mem hvV
  have hv := G.ne_bot_of_mem hvV
  refine Graph.ext_inc (by rwa [bouquet_vertexSet_of_nonempty hv])
    fun e x ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp [bouquet_inc_iff hv, ← mem_singleton_iff, ← hrw, h.edge_mem, h.vertex_mem]
  simp only [bouquet_inc_iff hv] at h
  obtain ⟨z, w, hzw⟩ := exists_isLink_of_mem_edgeSet h.1
  rw [h.2, ← show z = v from (show z ∈ {v} from hrw ▸ hzw.left_mem)]
  exact hzw.inc_left

/-- Every graph on just one vertex is a bouquet on that vertex-/
lemma exists_eq_bouquet_edge (hvV : v ∈ V(G)) (hss : V(G).Subsingleton) :
    ∃ F, G = bouquet v F :=
  ⟨E(G), eq_bouquet hvV hss⟩

lemma exists_eq_bouquet (hne : V(G).Nonempty) (hss : V(G).Subsingleton) :
    ∃ x F, G = bouquet x F :=
  ⟨_, _, eq_bouquet hne.some_mem hss⟩

lemma bouquet_empty (hv : v ≠ ⊥) :
    bouquet v ∅ = Graph.noEdge (indiscrete v hv) β := by
  ext <;> simp [hv]

lemma bouquet_mono (hss : F₁ ⊆ F₂) :
    bouquet v F₁ ≤s bouquet v F₂ where
  vertexSet_eq := rfl
  isLink_of_isLink := by aesop

/-! ### Two vertices -/

/-- A graph with two vertices and no loops.
  If `a` or `b` is empty, the graph is empty.
  If `a` and `b` are not disjoint, the graph is `bouquet (a ∪ b) F`.
  Else, the graph has vertices `a` and `b` and edges `F` between them. -/
@[simps]
def banana (a b : α) (F : Set β) : Graph α β where
  vertexPartition := Partition.pair a b
  edgeSet := {e | e ∈ F ∧ a ≠ ⊥ ∧ b ≠ ⊥}
  IsLink e x y := (e ∈ F ∧ a ≠ ⊥ ∧ b ≠ ⊥) ∧
    s(x, y) = s((Partition.pair a b).foo a, (Partition.pair a b).foo b)
  isLink_symm _ _ _ := by aesop
  eq_or_eq_of_isLink_of_isLink := by aesop
  edge_mem_iff_exists_isLink := by aesop
  left_mem_of_isLink e x y := by
    rintro ⟨⟨he, ha, hb⟩, h⟩
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h
    · apply foo_mem_of_le (indiscrete'_le_mk' (by simp) : indiscrete' a ≤ Partition.mk' {a, b})
      simp [ha.ne_empty]
    · apply foo_mem_of_le (indiscrete'_le_mk' (by simp) : indiscrete' b ≤ Partition.mk' {a, b})
      simp [hb.ne_empty]

lemma banana_comm : banana a b F = banana b a F := by
  refine Graph.ext ?_ fun e x y ↦ ?_
  · rw [banana_vertexSet, banana_vertexSet, Set.pair_comm]
  simp_rw [banana_isLink]
  refine and_congr (and_congr_right fun _ ↦ and_comm) ?_
  simp_rw [Set.pair_comm a b, Sym2.eq_swap]

@[simp]
lemma banana_vertexSet_of_isPartition (h : IsPartition {a, b}) : V(banana a b F) = {a, b} := by
  rw [banana_vertexSet, h.mk'_parts]

@[simp]
lemma banana_eq_bouquet : banana a a F = bouquet a F :=
  Graph.ext (by simp) (by aesop)

@[simp↓]
lemma banana_isLink_of_isPartition (h : IsPartition {a, b}) :
    (banana a b F).IsLink e x y ↔ e ∈ F ∧ s(x, y) = s(a, b) := by
  simp only [banana_isLink, h.nonempty_not_mem (show a ∈ ({ a, b } : Set _) from by simp),
    h.nonempty_not_mem (show b ∈ ({ a, b } : Set _) from by simp), and_self, and_true, Sym2.eq,
    Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, and_congr_right_iff]
  refine fun heF ↦ or_congr ?_ ?_ <;> apply and_congr
  · revert x
    rw [eq_iff_eq_cancel_left]
    exact foo_eq_self_of_mem <| by simp [h]
  · revert y
    rw [eq_iff_eq_cancel_left]
    exact foo_eq_self_of_mem <| by simp [h]
  · revert x
    rw [eq_iff_eq_cancel_left]
    exact foo_eq_self_of_mem <| by simp [h]
  · revert y
    rw [eq_iff_eq_cancel_left]
    exact foo_eq_self_of_mem <| by simp [h]

@[simp]
lemma banana_isLink_of_mem (heF : e ∈ F) : (banana a b F).IsLink e a b ↔ IsPartition {a, b} := by
  refine ⟨fun hab ↦ exists_subset_iff_isPartition.mp ?_, fun h ↦ ?_⟩
  · use P(banana a b F), pair_subset hab.left_mem hab.right_mem
  · exact (banana_isLink_of_isPartition h).mpr ⟨heF, rfl⟩

@[simp]
lemma banana_edgeSet_of_nonempty (ha : a ≠ ⊥) (hb : b ≠ ⊥) : E(banana a b F) = F := by
  simp [ha, hb]

@[simp]
lemma banana_inc_of_isPartition (h : IsPartition {a, b}) :
    (banana a b F).Inc e x ↔ e ∈ F ∧ (x = a ∨ x = b) := by
  simp_rw [Inc, banana_isLink_of_isPartition h]
  aesop

@[simp]
lemma banana_adj_of_isPartition (h : IsPartition {a, b}) :
    (banana a b F).Adj x y ↔ F.Nonempty ∧ s(x, y) = s(a, b) := by
  simp_rw [Adj, banana_isLink_of_isPartition h, exists_and_right]
  rfl

@[simp]
lemma banana_isNonloopAt_of_isPartition (h : IsPartition {a, b}) :
    (banana a b F).IsNonloopAt e x ↔ e ∈ F ∧ (x = a ∨ x = b) ∧ a ≠ b := by
  simp_rw [isNonloopAt_iff_inc_not_isLoopAt, ← isLink_self_iff, banana_isLink_of_isPartition h,
    banana_inc_of_isPartition h]
  aesop

@[simp]
lemma banana_isNonloopAt_left_of_mem (heF : e ∈ F) :
    (banana a b F).IsNonloopAt e a ↔ IsPartition {a, b} ∧ a ≠ b := by
  refine ⟨fun ⟨x, hxa, hx⟩ ↦ ?_, fun ⟨h, hne⟩ ↦ ?_⟩
  · rw [← mk'_parts_iff, ← mk'_pair_nontrivial_iff, ← banana_vertexPartition]
    use x, hx.right_mem', a, hx.left_mem'
  rw [banana_isNonloopAt_of_isPartition h]
  simp [heF, hne]

@[simp]
lemma banana_isNonloopAt_right_of_mem (heF : e ∈ F) :
    (banana a b F).IsNonloopAt e b ↔ IsPartition {a, b} ∧ a ≠ b := by
  rw [banana_comm, banana_isNonloopAt_left_of_mem heF, ne_comm, pair_comm]

@[simp]
lemma banana_isLoopAt_of_isPartition (h : IsPartition {a, b}) :
    (banana a b F).IsLoopAt e x ↔ e ∈ F ∧ x = a ∧ a = b := by
  simp only [← isLink_self_iff, banana_isLink_of_isPartition h, and_congr_right_iff]
  aesop

@[simp]
lemma banana_isloopAt_of_eq (ha : a ≠ ⊥) : (banana a a F).IsLoopAt e x ↔ e ∈ F ∧ x = a := by
  simp [ha, ← isLink_self_iff]

@[simp]
lemma banana_not_isloopAt_of_disjoint (ha : a ≠ ⊥) (hb : b ≠ ⊥) (hab : Disjoint a b) :
    ¬ (banana a b F).IsLoopAt e x := by
  unfold IsLoopAt
  have h := isPartition_pair_of_disjoint ha.ne_empty hb.ne_empty hab
  rw [banana_isLink_of_isPartition h]
  aesop

lemma banana_mono {X Y : Set β} (hXY : X ⊆ Y) : banana a b X ≤s banana a b Y where
  vertexSet_eq := rfl
  isLink_of_isLink := by simp +contextual [subset_def ▸ hXY]

/-- A graph with a single edge `e` from `u` to `v` -/
@[simps! vertexPartition vertexSet]
protected def singleEdge (e : β) (u v : α) := banana u v {e}

lemma singleEdge_comm (e : β) (u v : α) : Graph.singleEdge e u v = Graph.singleEdge e v u := by
  unfold Graph.singleEdge
  rw [banana_comm]

@[simp]
lemma singleEdge_vertexSet_of_isPartition (h : IsPartition {u, v}) :
    V(Graph.singleEdge e u v) = {u, v} :=
  banana_vertexSet_of_isPartition h

@[simp]
lemma singleEdge_isLink : (Graph.singleEdge e u v).IsLink f x y ↔ (f = e ∧ u ≠ ⊥ ∧ v ≠ ⊥)∧
    s(x, y) = s((Partition.mk' {u, v}).foo u, (Partition.mk' {u, v}).foo v) := by
  simp [Graph.singleEdge, banana_isLink]

@[simp↓]
lemma singleEdge_isLink_of_isPartition (h : IsPartition {u, v}) :
    (Graph.singleEdge e u v).IsLink f x y ↔ (f = e) ∧ s(x,y) = s(u,v) := by
  rw [Graph.singleEdge, banana_isLink_of_isPartition h, mem_singleton_iff]

@[simp]
lemma singleEdge_isLink_of_mem : (Graph.singleEdge e u v).IsLink e u v ↔ IsPartition {u, v} := by
  rw [Graph.singleEdge, banana_isLink_of_mem]
  rfl

@[simp]
lemma singleEdge_edgeSet_of_nonempty (hu : u ≠ ⊥) (hv : v ≠ ⊥) :
    E(Graph.singleEdge e u v) = {e} := by
  simp only [Graph.singleEdge, banana_edgeSet_of_nonempty hu hv]

@[simp]
lemma singleEdge_inc_of_isPartition (h : IsPartition {u, v}) :
    (Graph.singleEdge e u v).Inc f x ↔ f = e ∧ (x = u ∨ x = v) := by
  simp_rw [Graph.singleEdge, banana_inc_of_isPartition h, mem_singleton_iff]

@[simp]
lemma singleEdge_adj_of_isPartition (h : IsPartition {u, v}) :
    (Graph.singleEdge e u v).Adj x y ↔ s(x, y) = s(u, v) := by
  simp_rw [Graph.singleEdge, banana_adj_of_isPartition h, singleton_nonempty, true_and]

lemma singleEdge_le_of_isLink (h : G.IsLink e u v) : Graph.singleEdge e u v ≤ G where
  vertexSet_subset := by
    obtain (rfl | hne) := eq_or_ne u v
    · simp [G.ne_empty_of_mem, h.left_mem]
    rw [singleEdge_vertexSet_of_isPartition (isPartition_of_subset (P := P(G))
      (by simp [pair_subset, h.left_mem, h.right_mem]))]
    exact pair_subset h.left_mem h.right_mem
  isLink_of_isLink f x y hxy := by
    simp_rw [singleEdge_isLink] at hxy
    obtain ⟨⟨rfl, -⟩, heq⟩ := hxy
    rw [foo_eq_self_of_mem, foo_eq_self_of_mem] at heq
    rwa [h.isLink_iff_sym2_eq, eq_comm]
    all_goals
    · rw [mem_mk'_iff (pairwiseDisjoint_pair_iff.mpr h.eq_or_disjoint)]
      simp [h.right_nonempty.ne_empty, h.left_nonempty.ne_empty]

lemma singleEdge_isNonloopAt_iff_isPartition :
    (Graph.singleEdge e u v).IsNonloopAt e u ↔ IsPartition {u, v} ∧ u ≠ v := by
  rw [Graph.singleEdge, banana_isNonloopAt_left_of_mem (by simp)]

lemma singleEdge_isNonloopAt_left_of_isPartition (h : IsPartition {u, v}) :
    (Graph.singleEdge e u v).IsNonloopAt f u ↔ e = f ∧ u ≠ v := by
  rw [Graph.singleEdge, banana_isNonloopAt_of_isPartition h]
  simp [eq_comm]

lemma singleEdge_isNonloopAt_right_of_isPartition (h : IsPartition {u, v}) :
    (Graph.singleEdge e u v).IsNonloopAt f v ↔ e = f ∧ u ≠ v := by
  rw [Graph.singleEdge, banana_isNonloopAt_of_isPartition h]
  simp [eq_comm]

lemma singleEdge_isNonloopAt :
    (Graph.singleEdge e u v).IsNonloopAt e u ↔ u ≠ ⊥ ∧ v ≠ ⊥ ∧ Disjoint u v := by
  rw [singleEdge_isNonloopAt_iff_isPartition, isPartition_pair_iff]
  simp_rw [nonempty_iff_ne_empty]
  aesop

lemma singleEdge_isLoopAt_left_of_isPartition (h : IsPartition {u, v}) :
    (Graph.singleEdge e u v).IsLoopAt f u ↔ e = f ∧ u = v := by
  rw [Graph.singleEdge, banana_isLoopAt_of_isPartition h]
  simp [eq_comm]

lemma singleEdge_isLoopAt_right_of_isPartition (h : IsPartition {u, v}) :
    (Graph.singleEdge e u v).IsLoopAt f v ↔ e = f ∧ u = v := by
  rw [Graph.singleEdge, banana_isLoopAt_of_isPartition h]
  simp [eq_comm]

@[simp]
lemma singleEdge_le_iff (huv : IsPartition {u, v}) : Graph.singleEdge e u v ≤ G ↔ G.IsLink e u v :=
  ⟨fun h ↦ h.isLink_of_isLink <| singleEdge_isLink_of_mem.mpr huv, singleEdge_le_of_isLink⟩
