import Matroid.Graph.Constructions.Basic

variable {α β : Type*} [CompleteLattice α] {x y z u v w a b : α} {e f : β} {G H : Graph α β}
  {F F₁ F₂ : Set β} {X Y : Set α} {P : Partition α} {l : β → α → α → Prop}

open Set Function Relation Partition

omit [CompleteLattice α] in
@[simp]
lemma Set.pair_nontrivial_iff : ({a, b} : Set α).Nontrivial ↔ a ≠ b := by
  simp [Set.Nontrivial, ne_comm]

open scoped Sym2

namespace Graph


/-! ### Graphs with one (or no) vertex  -/

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
lemma bouquet_bot : bouquet (⊥ : α) F = ⊥ := by
  rw [← vertexSet_eq_empty_iff, bouquet_vertexSet]
  simp

@[simp↓]
lemma bouquet_vertexSet_of_ne_bot (hv : v ≠ ⊥) : V(bouquet v F) = {v} := by
  simp [hv]

@[simp↓]
lemma bouquet_edgeSet_of_ne_bot (hv : v ≠ ⊥) : E(bouquet v F) = F := by
  simp [hv]

@[simp]
lemma bouquet_inc (hv : v ≠ ⊥) : (bouquet v F).Inc e x ↔ e ∈ F ∧ x = v := by
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
  refine Graph.ext_inc (by rwa [bouquet_vertexSet_of_ne_bot hv])
    fun e x ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp [bouquet_inc hv, ← mem_singleton_iff, ← hrw, h.edge_mem, h.vertex_mem]
  simp only [bouquet_inc hv] at h
  obtain ⟨z, w, hzw⟩ := exists_isLink_of_mem_edgeSet h.1
  rw [h.2, ← show z = v from (show z ∈ {v} from hrw ▸ hzw.left_mem)]
  exact hzw.inc_left

/-- Every graph on just one vertex is a bouquet on that vertex-/
lemma exists_eq_bouquet_edge (hvV : v ∈ V(G)) (hss : V(G).Subsingleton) : ∃ F, G = bouquet v F :=
  ⟨E(G), eq_bouquet hvV hss⟩

lemma exists_eq_bouquet_iff : (∃ x F, G = bouquet x F) ↔ V(G).Subsingleton := by
  classical
  refine ⟨fun ⟨x, F, h⟩ ↦ ?_, fun hss ↦ ?_⟩
  · by_cases hx : x = ⊥ <;> simp [h, hx]
  by_cases hne : V(G).Nonempty
  · exact ⟨_, _, eq_bouquet hne.some_mem hss⟩
  exact ⟨⊥, ∅, by simp_all⟩

lemma eq_bouquet_iff (hx : x ≠ ⊥) : G = bouquet x F ↔ V(G) = {x} ∧ E(G) = F := by
  refine ⟨?_, fun ⟨hV, hE⟩ ↦ ?_⟩
  · rintro rfl
    simp [hx]
  subst F
  apply eq_bouquet <;> simp_all

lemma bouquet_empty (hv : v ≠ ⊥) : bouquet v ∅ = Graph.noEdge (indiscrete v hv) β := by
  ext <;> simp [hv]

lemma bouquet_mono (hss : F₁ ⊆ F₂) : bouquet v F₁ ≤s bouquet v F₂ where
  vertexSet_eq := rfl
  isLink_of_isLink := by aesop

/-! ### Two vertices -/

/-- A graph with two vertices and no loops.
  If `a` or `b` is empty, the graph is empty.
  If `a` and `b` are not disjoint, the graph is `bouquet (a ∪ b) F`.
  Else, the graph has vertices `a` and `b` and edges `F` between them. -/
@[simps]
noncomputable def banana (a b : α) (F : Set β) : Graph α β where
  vertexPartition := Partition.pair a b
  edgeSet := {e | e ∈ F ∧ a ≠ ⊥ ∧ b ≠ ⊥}
  IsLink e x y := (e ∈ F ∧ a ≠ ⊥ ∧ b ≠ ⊥) ∧
    s(x, y) = s(pairLeft a b, pairRight a b)
  isLink_symm _ _ _ := by aesop
  eq_or_eq_of_isLink_of_isLink := by aesop
  edge_mem_iff_exists_isLink := by aesop
  left_mem_of_isLink e x y := by
    rintro ⟨⟨he, ha, hb⟩, h⟩
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h
    · exact pairLeft_mem_of_not_bot ha
    · exact pairRight_mem_of_not_bot hb

lemma banana_comm : banana a b F = banana b a F := by
  refine Graph.ext ?_ fun e x y ↦ ?_
  · rw [banana_vertexSet, banana_vertexSet, Partition.pair_comm]
  simp_rw [banana_isLink, pairRight, Sym2.eq_swap (a := pairLeft a b)]
  exact and_congr_left' (and_congr_right fun _ ↦ and_comm)

@[simp↓]
lemma banana_vertexSet_of_isPartition (h : IsPartition {a, b}) : V(banana a b F) = {a, b} := by
  rw [banana_vertexSet, pair_parts_eq_pair_iff_isPartition.mp h]

lemma banana_vertexSet_of_disjoint (hxy : Disjoint a b) : V(banana a b F) = {a, b} \ {⊥} := by
  rw [banana_vertexSet, pair_parts_of_disjoint hxy]

@[simp]
lemma banana_self_eq_bouquet : banana a a F = bouquet a F :=
  Graph.ext (by simp) (by aesop)

lemma banana_eq_bouquet_of_not_disjoint (hxy : ¬ Disjoint a b) :
    banana a b F = bouquet (a ⊔ b) F := by
  have ha := left_ne_bot_of_not_disjoint hxy
  have hb := right_ne_bot_of_not_disjoint hxy
  rw [eq_bouquet_iff (by aesop)]
  simp [ha, hb, hxy]

lemma banana_vertexSet_nontrivial_iff :
    V(banana a b F).Nontrivial ↔ a ≠ b ∧ IsPartition {a, b} := by
  refine ⟨fun h => ?_, fun h => by use a, ?_, b, ?_, h.1 <;> simp [h.2]⟩
  by_cases hdj : Disjoint a b
  · by_cases ha : a = ⊥ <;> by_cases hb : b = ⊥ <;> simp_all
  simp_all

@[simp↓]
lemma banana_isLink_of_isPartition (h : IsPartition {a, b}) :
    (banana a b F).IsLink e x y ↔ e ∈ F ∧ s(x, y) = s(a, b) := by
  simp [h, h.ne_bot_of_mem (by simp : a ∈ _), h.ne_bot_of_mem (by simp : b ∈ _)]

@[simp]
lemma banana_isLink_of_mem (heF : e ∈ F) : (banana a b F).IsLink e a b ↔ IsPartition {a, b} := by
  refine ⟨fun hab ↦ exists_subset_iff_isPartition.mp ?_, fun h ↦ ?_⟩
  · use P(banana a b F), pair_subset hab.left_mem hab.right_mem
  · exact (banana_isLink_of_isPartition h).mpr ⟨heF, rfl⟩

@[simp↓]
lemma banana_edgeSet_of_ne_bot (ha : a ≠ ⊥) (hb : b ≠ ⊥) : E(banana a b F) = F := by
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
  · rw [← pair_parts_nontrivial_iff]
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
  rw [banana_isLink_of_isPartition <| isPartition_pair_of_disjoint ha hb hab]
  aesop

lemma banana_mono {X Y : Set β} (hXY : X ⊆ Y) : banana a b X ≤s banana a b Y where
  vertexSet_eq := rfl
  isLink_of_isLink := by simp +contextual [subset_def ▸ hXY]

/-- A graph with a single edge `e` from `u` to `v` -/
@[simps! vertexPartition vertexSet]
protected noncomputable def singleEdge (e : β) (u v : α) := banana u v {e}

lemma banana_singleton (e : β) (u v : α) : banana u v {e} = Graph.singleEdge e u v := rfl

lemma singleEdge_comm (e : β) (u v : α) : Graph.singleEdge e u v = Graph.singleEdge e v u := by
  unfold Graph.singleEdge
  rw [banana_comm]

@[simp]
lemma singleEdge_vertexSet_of_isPartition (h : IsPartition {u, v}) :
    V(Graph.singleEdge e u v) = {u, v} :=
  banana_vertexSet_of_isPartition h

@[simp]
lemma singleEdge_isLink : (Graph.singleEdge e u v).IsLink f x y ↔ (f = e ∧ u ≠ ⊥ ∧ v ≠ ⊥)∧
    s(x, y) = s(pairLeft u v, pairRight u v) := by
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
lemma singleEdge_edgeSet_of_ne_bot (hu : u ≠ ⊥) (hv : v ≠ ⊥) : E(Graph.singleEdge e u v) = {e} :=
  banana_edgeSet_of_ne_bot hu hv

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
    · simp [G.ne_bot_of_mem, h.left_mem]
    rw [singleEdge_vertexSet_of_isPartition (isPartition_of_subset (P := P(G))
      (by simp [pair_subset, h.left_mem, h.right_mem]))]
    exact pair_subset h.left_mem h.right_mem
  isLink_of_isLink f x y hxy := by
    have hP : IsPartition {u, v} := (isPartition_of_subset (P := P(G))
      (by simp [pair_subset, h.left_mem, h.right_mem]))
    simp_rw [singleEdge_isLink] at hxy
    obtain ⟨⟨rfl, hu, hv⟩, heq⟩ := hxy
    rw [h.isLink_iff_sym2_eq, heq, eq_comm, hP.pairLeft_eq_left, hP.pairRight_eq_right]

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
