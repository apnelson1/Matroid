import Matroid.Graph.Subgraph.Basic
import Matroid.Graph.Minor.Repartition
import Matroid.ForMathlib.Partition.Constructor
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.PFun

variable {α β : Type*} {x y z u v w a b : Set α} {e f : β} {G H : Graph α β} {F F₁ F₂ : Set β}
  {X Y : Set (Set α)} {P : Partition (Set α)} {l : β → Set α → Set α → Prop}

open Set Function Relation Partition

open scoped Sym2

namespace Graph

/-- `Copy` creates an identical graph with different definitions for its vertex set and edge set.
  This is mainly used to create graphs with improved definitional properties. -/
@[simps]
def copy (G : Graph α β) {E : Set β} (hP : P(G) = P) (hV : V(G) = X) (hE : E(G) = E)
    (h_isLink : ∀ e x y, G.IsLink e x y ↔ l e x y) : Graph α β where
  vertexPartition := P
  vertexSet := X
  vertexSet_eq_parts := by
    rw [← hV, ← hP, G.vertexSet_eq_parts]
  edgeSet := E
  IsLink := l
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

lemma copy_eq_self (G : Graph α β) {E : Set β} (hP : P(G) = P) (hV : V(G) = X) (hE : E(G) = E)
    (h_isLink : ∀ e x y, G.IsLink e x y ↔ l e x y) : G.copy hP hV hE h_isLink = G := by
  subst hV hE
  ext <;> simp_all [copy]

@[simps]
def mk_of_symm (P : Partition (Set α)) (l : β → Set α → Set α → Prop) [∀ e, IsSymm _ (l e)] :
    Graph α β where
  vertexPartition := P
  IsLink e x y :=
    let l' := Relation.restrict (l e) P.parts
    (∀ ⦃a b c d⦄, l' a b → l' c d → a = c ∨ a = d) ∧ l' x y
  isLink_symm e he x y := by
    rintro ⟨hl, hxy⟩
    exact ⟨hl, symm hxy⟩
  eq_or_eq_of_isLink_of_isLink e x y v w := by
    rintro ⟨hl, hxy⟩ ⟨-, hvw⟩
    exact hl hxy hvw
  left_mem_of_isLink _ _ _ h := h.2.left_mem

lemma IsLink.of_mk_of_symm [∀ e, IsSymm _ (l e)] (h : (mk_of_symm P l).IsLink e x y) : l e x y :=
  Relation.restrict_le (l e) P.parts _ _ h.2

lemma mk_of_symm_eq_self (G : Graph α β) : mk_of_symm P(G) G.IsLink = G :=
  Graph.ext (by simp) (fun e x y ↦ by
    simp [Relation.restrict_eq_self _ (G.domain_IsLink_subset_vertexSet e)]
    exact fun _ => G.eq_or_eq_of_isLink_of_isLink (e := e))

@[simps!]
def mk' (V : Partition (Set α)) (l : β → Set α → Set α → Prop) : Graph α β :=
  mk_of_symm V (fun e => SymmClosure (l e))

/-- The graph with vertex set `V` and no edges -/
@[simps]
protected def noEdge (P : Partition (Set α)) (β : Type*) : Graph α β where
  vertexPartition := P
  edgeSet := ∅
  IsLink _ _ _ := False
  isLink_symm := by simp
  eq_or_eq_of_isLink_of_isLink := by simp
  edge_mem_iff_exists_isLink := by simp
  left_mem_of_isLink := by simp

lemma eq_empty_or_vertexSet_nonempty (G : Graph α β) : G = Graph.noEdge ⊥ β ∨ V(G).Nonempty := by
  refine (em (V(G) = ∅)).elim (fun he ↦ .inl (Graph.ext he fun e x y ↦ ?_)) (Or.inr ∘
    nonempty_iff_ne_empty.mpr)
  simp only [noEdge_edgeSet, mem_empty_iff_false, not_false_eq_true, not_isLink_of_notMem_edgeSet,
    iff_false]
  exact fun h ↦ by simpa [he] using h.left_mem

@[simp]
lemma noEdge_le_iff : Graph.noEdge P β ≤ G ↔ P.parts ⊆ V(G) := by
  simp [le_iff]

@[simp]
lemma noEdge_not_inc : ¬ (Graph.noEdge P β).Inc e x := by
  simp [Inc]

@[simp]
lemma noEdge_not_isLoopAt : ¬ (Graph.noEdge P β).IsLoopAt e x := by
  simp [← isLink_self_iff]

@[simp]
lemma noEdge_not_isNonloopAt : ¬ (Graph.noEdge P β).IsNonloopAt e x := by
  simp [IsNonloopAt]

@[simp]
lemma noEdge_not_adj : ¬ (Graph.noEdge P β).Adj x y := by
  simp [Adj]


lemma edgeSet_eq_empty_iff : E(G) = ∅ ↔ G = Graph.noEdge P(G) β := by
  refine ⟨fun h ↦ Graph.vertexPartition_ext rfl ?_, fun h ↦ by rw [h, noEdge_edgeSet]⟩
  simp only [noEdge_isLink, iff_false]
  refine fun e x y he ↦ ?_
  have := h ▸ he.edge_mem
  simp at this

@[simp]
lemma le_noEdge_iff : G ≤ Graph.noEdge P β ↔ V(G) ⊆ P.parts ∧ E(G) = ∅ :=
  ⟨fun h ↦ ⟨vertexSet_mono h, subset_empty_iff.1 (edgeSet_mono h)⟩,
    fun h ↦ ⟨h.1, fun e x y he ↦ by simpa [h] using he.edge_mem⟩⟩

instance : OrderBot (Graph α β) where
  bot := Graph.noEdge ⊥ β
  bot_le := by simp

@[simp]
lemma bot_vertexSet : V((⊥ : Graph α β)) = ⊥ := rfl

@[simp]
lemma bot_edgeSet : E((⊥ : Graph α β)) = ⊥ := rfl

@[simp]
lemma bot_isClosedSubgraph (G : Graph α β) : ⊥ ≤c G where
  toIsSubgraph := bot_le (a := G)
  closed := by simp

@[simp]
lemma bot_isInducedSubgraph (G : Graph α β) : ⊥ ≤i G :=
  G.bot_isClosedSubgraph.isInducedSubgraph

@[simp]
lemma noEdge_empty : Graph.noEdge (⊥ : Partition (Set α)) β = ⊥ := rfl

@[simp]
lemma bot_not_isLink : ¬ (⊥ : Graph α β).IsLink e x y :=
  id

@[simp]
lemma vertexSet_eq_empty_iff : V(G) = ∅ ↔ G = ⊥ := by
  refine ⟨fun h ↦ bot_le.antisymm' ⟨by simp [h], fun e x y he ↦ False.elim ?_⟩, fun h ↦ by simp [h]⟩
  simpa [h] using he.left_mem

@[simp]
lemma vertexSet_nonempty_iff : V(G).Nonempty ↔ G ≠ ⊥ :=
  nonempty_iff_ne_empty.trans <| not_iff_not.mpr vertexSet_eq_empty_iff

/-! ### Graphs with one vertex  -/

/-- A graph with one vertex and loops at that vertex -/
@[simps]
def bouquet (v : Set α) (F : Set β) : Graph α β where
  vertexPartition := indiscrete' v
  edgeSet := {e | e ∈ F ∧ v.Nonempty}
  IsLink e x y := e ∈ F ∧ v.Nonempty ∧ x = v ∧ y = v
  isLink_symm e := by simp +contextual [Symmetric]
  eq_or_eq_of_isLink_of_isLink := by aesop
  edge_mem_iff_exists_isLink := by aesop
  left_mem_of_isLink := by aesop

@[simp]
lemma bouquet_vertexSet_of_nonempty (hv : v.Nonempty) : V(bouquet v F) = {v} := by
  simp [hv.ne_empty]

@[simp]
lemma bouquet_inc_iff (hv : v.Nonempty) : (bouquet v F).Inc e x ↔ e ∈ F ∧ x = v := by
  simp [Inc, hv]

@[simp]
lemma bouquet_isLoopAt (hv : v.Nonempty) : (bouquet v F).IsLoopAt e x ↔ e ∈ F ∧ x = v := by
  simp [← isLink_self_iff, hv]

@[simp]
lemma bouquet_not_isNonloopAt : ¬ (bouquet v F).IsNonloopAt e x := by
  simp +contextual [IsNonloopAt, eq_comm]

/-- Every graph on just one vertex is a bouquet on that vertex-/
lemma eq_bouquet (hvV : v ∈ V(G)) (hss : V(G).Subsingleton) :
    G = bouquet v E(G) := by
  have hrw := hss.eq_singleton_of_mem hvV
  have hv := G.nonempty_of_mem hvV
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

lemma bouquet_empty (hv : v.Nonempty) :
    bouquet v ∅ = Graph.noEdge (indiscrete v hv.ne_empty) β := by
  ext <;> simp [hv.ne_empty]

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
def banana (a b : Set α) (F : Set β) : Graph α β where
  vertexPartition := .mk' {a, b}
  edgeSet := {e | e ∈ F ∧ a.Nonempty ∧ b.Nonempty}
  IsLink e x y := (e ∈ F ∧ a.Nonempty ∧ b.Nonempty) ∧
    s(x, y) = s((Partition.mk' {a, b}).foo a, (Partition.mk' {a, b}).foo b)
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
lemma banana_edgeSet_of_nonempty (ha : a.Nonempty) (hb : b.Nonempty) : E(banana a b F) = F := by
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
lemma banana_isloopAt_of_eq (ha : a.Nonempty) : (banana a a F).IsLoopAt e x ↔ e ∈ F ∧ x = a := by
  simp [ha, ← isLink_self_iff]

@[simp]
lemma banana_not_isloopAt_of_disjoint (ha : a.Nonempty) (hb : b.Nonempty) (hab : Disjoint a b) :
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
protected def singleEdge (e : β) (u v : Set α) := banana u v {e}

lemma singleEdge_comm (e : β) (u v : Set α) : Graph.singleEdge e u v = Graph.singleEdge e v u := by
  unfold Graph.singleEdge
  rw [banana_comm]

@[simp]
lemma singleEdge_vertexSet_of_isPartition (h : IsPartition {u, v}) :
    V(Graph.singleEdge e u v) = {u, v} :=
  banana_vertexSet_of_isPartition h

@[simp]
lemma singleEdge_isLink : (Graph.singleEdge e u v).IsLink f x y ↔ (f = e ∧ u.Nonempty ∧ v.Nonempty)∧
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
lemma singleEdge_edgeSet_of_nonempty (hu : u.Nonempty) (hv : v.Nonempty) :
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
    (Graph.singleEdge e u v).IsNonloopAt e u ↔ u.Nonempty ∧ v.Nonempty ∧ Disjoint u v := by
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

/-! ### Complete graphs -/

/-- The complete graph on `n` vertices. -/
@[simps]
def CompleteGraph (n : ℕ+) : Graph ℕ (Sym2 ℕ) where
  vertexPartition := Partition.discrete (Set.Iio n)
  edgeSet := {s | (∀ i ∈ s, i < n) ∧ ¬ s.IsDiag}
  IsLink e x y := ∃ i : ℕ, i < n ∧ ∃ j : ℕ, j < n ∧ i ≠ j ∧ e = s(i, j) ∧ x = {i} ∧ y = {j}
  isLink_symm e he x y := by
    simp only [forall_exists_index, and_imp]
    rintro i hi j hj hne rfl rfl rfl
    use j, hj, i, hi, hne.symm, Sym2.eq_swap
  eq_or_eq_of_isLink_of_isLink e x y z w h := by
    obtain ⟨i, hi, j, hj, hne, rfl, rfl, rfl⟩ := h
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, forall_exists_index,
      and_imp]
    rintro k hk l hl hnekl (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) rfl rfl <;> tauto
  edge_mem_iff_exists_isLink e := by
    cases e with | h x y
    simp +contextual only [mem_setOf_eq, Sym2.mem_iff, forall_eq_or_imp, forall_eq,
      Sym2.isDiag_iff_proj_eq, ne_eq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk,
      iff_def, and_imp, forall_exists_index]
    refine ⟨fun hx hy hne ↦ ?_, fun A B a ha b hb hne ↦ ?_⟩
    · use {x}, {y}, x, hx, y, hy, hne, by simp
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) rfl rfl <;> tauto
  left_mem_of_isLink e x y := by
    rintro ⟨i, hi, j, hj, hne, rfl, rfl, rfl⟩
    simpa

@[simp]
lemma CompleteGraph_adj (n : ℕ+) (x y : ℕ) (hx : x < n) (hy : y < n) :
    (CompleteGraph n).Adj {x} {y} ↔ x ≠ y := by
  unfold Adj
  simp [hx, hy]

-- /-- The star graph with `n` leaves with center `v` -/
-- @[simps]
-- def StarGraph (v : α) (f : β →. α) : Graph α β where
--   vertexSet := {v} ∪ f.ran
--   edgeSet := f.Dom
--   IsLink e x y := ∃ (he : e ∈ f.Dom), s(v, f.fn e he) = s(x, y)
--   edge_mem_iff_exists_isLink e := ⟨fun h ↦ ⟨v, f.fn e h, h, rfl⟩, fun ⟨x, y, he, h⟩ ↦ he⟩
--   isLink_symm e he x y h := by beta_reduce; rwa [Sym2.eq_swap]
--   eq_or_eq_of_isLink_of_isLink e x y z w h1 h2 := by
--     obtain ⟨he, h⟩ := h1
--     obtain ⟨_, h'⟩ := h2
--     have := h.symm.trans h'
--     simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at this
--     tauto
--   left_mem_of_isLink e x y h := by
--     simp only [PFun.fn_apply, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk,
--       singleton_union, mem_insert_iff] at h ⊢
--     obtain ⟨he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h <;> tauto


-- /-! ### Graph constructor from a list of pairs of vertices -/

-- /-- The graph with vertex set `S` and edges over `ℕ` between pairs of vertices according to the
--  list
--   `l`.-/
-- @[simps]
-- def fromList (S : Set α) (l : List (α × α)) : Graph α ℕ where
--   vertexSet := S ∪ {x | ∃ p ∈ l, x = p.1 ∨ x = p.2}
--   edgeSet := Finset.range l.length
--   IsLink e x y := ∃ p, l[e]? = some p ∧ s(x,y) = s(p.1, p.2)
--   isLink_symm e x y h1 h2 := by beta_reduce; rwa [Sym2.eq_swap]
--   eq_or_eq_of_isLink_of_isLink e x y z w h₁ h₂ := by aesop
--   edge_mem_iff_exists_isLink e := by
--     simp [Set.mem_image, Finset.mem_range, Sym2.exists, and_comm]
--     refine ⟨fun h ↦ ?_, fun ⟨x, y, a, b, hor, h⟩ ↦ ?_⟩
--     · use l[e].fst, l[e].snd, l[e].fst, l[e].snd
--       simp
--     · rw [← isSome_getElem? l e, h]
--       tauto
--   left_mem_of_isLink e x y h := by
--     obtain ⟨p, hep, hs⟩ := h
--     right
--     simp only [Prod.mk.eta, Sym2.eq, Sym2.rel_iff', Prod.exists, mem_setOf_eq] at hs ⊢
--     obtain rfl | hp := hs
--     · use x, y, List.mem_of_getElem? hep, by tauto
--     · use y, x, ?_, by tauto
--       rw [← Prod.swap_eq_iff_eq_swap] at hp
--       exact List.mem_of_getElem? <| hp ▸ hep
