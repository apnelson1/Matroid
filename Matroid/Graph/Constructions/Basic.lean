import Matroid.Graph.Subgraph.Basic
import Matroid.Graph.Nodup
import Mathlib.Data.Set.Lattice
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

lemma eq_empty_or_vertexSet_nonempty (G : Graph α β) : G = Graph.noEdge ⊥ β ∨ V(G) ≠ ⊥ := by
  refine (em (V(G) = ⊥)).elim (fun he ↦ .inl (Graph.ext he fun e x y ↦ ?_)) Or.inr
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
  le := bot_le
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
lemma vertexSet_eq_empty_iff : V(G) = ⊥ ↔ G = ⊥ := by
  refine ⟨fun h ↦ bot_le.antisymm' ⟨by simp [h], fun e x y he ↦ False.elim ?_⟩, fun h ↦ by simp [h]⟩
  simpa [h] using he.left_mem

@[simp]
lemma vertexSet_nonempty_iff : V(G) ≠ ⊥ ↔ G ≠ ⊥ :=
  not_iff_not.mpr vertexSet_eq_empty_iff

/-- A graph with a single edge `e` from `u` to `v` -/
@[simps]
protected def singleEdge (e : β) (u v : Set α) (hu : u ≠ ∅) (hv : v ≠ ∅) (huv : Disjoint u v) :
    Graph α β where
  vertexPartition := Partition.bipartition u v hu hv huv
  edgeSet := {e}
  IsLink e' x y := e' = e ∧ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))
  isLink_symm := by tauto
  eq_or_eq_of_isLink_of_isLink e_2 x_1 y_1 v_2 w_1 := by
    rintro ⟨rfl, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ ⟨-, _⟩ <;>
    tauto
  edge_mem_iff_exists_isLink := by tauto
  left_mem_of_isLink e x y := by
    rintro ⟨rfl, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ <;> rw [mem_parts, mem_bipartition_iff] <;> simp

lemma singleEdge_comm (e : β) (huv : Disjoint u v) (hu : u ≠ ∅) (hv : v ≠ ∅) :
    Graph.singleEdge e u v hu hv huv = Graph.singleEdge e v u hv hu huv.symm := by
  apply Graph.vertexPartition_ext <;> simp [or_comm, Partition.ext_iff]

lemma singleEdge_isLink_iff (huv : Disjoint u v) (hu : u ≠ ∅) (hv : v ≠ ∅) :
    (Graph.singleEdge e u v hu hv huv).IsLink f x y ↔ (f = e) ∧ s(x,y) = s(u,v) := by
  simp [Graph.singleEdge]

@[simp]
lemma singleEdge_inc_iff (huv : Disjoint u v) (hu : u ≠ ∅) (hv : v ≠ ∅) :
    (Graph.singleEdge e u v hu hv huv).Inc f x ↔ f = e ∧ (x = u ∨ x = v) := by
  simp only [Inc, singleEdge_isLink, exists_and_left, and_congr_right_iff]
  aesop

@[simp]
lemma singleEdge_adj_iff (huv : Disjoint u v) (hu : u ≠ ∅) (hv : v ≠ ∅) :
    (Graph.singleEdge e u v hu hv huv).Adj x y ↔ (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  simp [Adj]

@[simp]
lemma singleEdge_le_iff (huv : Disjoint u v) (hu : u ≠ ∅) (hv : v ≠ ∅) :
    Graph.singleEdge e u v hu hv huv ≤ G ↔ G.IsLink e u v := by
  simp only [le_iff, singleEdge_vertexSet, singleEdge_isLink, and_imp]
  refine ⟨fun h ↦ h.2 rfl (.inl ⟨rfl, rfl⟩), fun h ↦ ⟨?_, ?_⟩⟩
  · rintro a (rfl | rfl) <;> simp [h.left_mem, h.right_mem]
  rintro e x y rfl (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · assumption
  exact h.symm

/-! ### Graphs with one vertex  -/

/-- A graph with one vertex and loops at that vertex -/
@[simps]
def bouquet (v : Set α) (F : Set β) (hv : v ≠ ∅) : Graph α β where
  vertexPartition := Partition.indiscrete v hv
  edgeSet := F
  IsLink e x y := e ∈ F ∧ x = v ∧ y = v
  isLink_symm e := by simp +contextual [Symmetric]
  eq_or_eq_of_isLink_of_isLink := by aesop
  edge_mem_iff_exists_isLink := by aesop
  left_mem_of_isLink := by aesop

@[simp]
lemma bouquet_inc_iff (hv : v ≠ ∅) : (bouquet v F hv).Inc e x ↔ e ∈ F ∧ x = v := by
  simp [Inc]

@[simp]
lemma bouquet_isLoopAt (hv : v ≠ ∅) : (bouquet v F hv).IsLoopAt e x ↔ e ∈ F ∧ x = v := by
  simp [← isLink_self_iff]

@[simp]
lemma bouquet_not_isNonloopAt (hv : v ≠ ∅) : ¬ (bouquet v F hv).IsNonloopAt e x := by
  simp +contextual [IsNonloopAt, eq_comm]

/-- Every graph on just one vertex is a bouquet on that vertex-/
lemma eq_bouquet (hvV : v ∈ V(G)) (hss : V(G).Subsingleton) (hv : v ≠ ∅) :
    G = bouquet v E(G) hv := by
  have hrw := hss.eq_singleton_of_mem hvV
  refine Graph.ext_inc hrw fun e x ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp [bouquet_inc_iff, ← mem_singleton_iff, ← hrw, h.edge_mem, h.vertex_mem]
  simp only [bouquet_inc_iff] at h
  obtain ⟨z, w, hzw⟩ := exists_isLink_of_mem_edgeSet h.1
  rw [h.2, ← show z = v from (show z ∈ {v} from hrw ▸ hzw.left_mem)]
  exact hzw.inc_left

/-- Every graph on just one vertex is a bouquet on that vertex-/
lemma exists_eq_bouquet_edge (hvV : v ∈ V(G)) (hss : V(G).Subsingleton) (hv : v ≠ ∅) :
    ∃ F, G = bouquet v F hv :=
  ⟨E(G), eq_bouquet hvV hss hv⟩

lemma exists_eq_bouquet (hne : V(G).Nonempty) (hss : V(G).Subsingleton) :
    ∃ x F hx, G = bouquet x F hx :=
  ⟨_, _, _, eq_bouquet hne.some_mem hss
   <| P(G).ne_bot_of_mem <| G.mem_vertexPartition_iff.mpr hne.some_mem⟩

lemma bouquet_empty (hv : v ≠ ∅) : bouquet v ∅ hv = Graph.noEdge (Partition.indiscrete v hv) β := by
  ext <;> simp

lemma bouquet_mono (hv : v ≠ ∅) (hss : X ⊆ Y) :
    bouquet v X hv ≤s bouquet v Y hv where
  vertexSet_eq := rfl
  isLink_of_isLink := by aesop

/-! ### Two vertices -/

/-- A graph with exactly two vertices and no loops. -/
@[simps]
def banana (a b : Set α) (ha : a ≠ ∅) (hb : b ≠ ∅) (hab : Disjoint a b) (F : Set β) :
    Graph α β where
  vertexPartition := Partition.bipartition a b ha hb hab
  edgeSet := F
  IsLink e x y := e ∈ F ∧ ((x = a ∧ y = b) ∨ (x = b ∧ y = a))
  isLink_symm _ _ _ := by aesop
  eq_or_eq_of_isLink_of_isLink := by aesop
  edge_mem_iff_exists_isLink := by aesop
  left_mem_of_isLink := by aesop

@[simp]
lemma banana_inc_iff (ha : a ≠ ∅) (hb : b ≠ ∅) (hab : Disjoint a b) :
    (banana a b ha hb hab F).Inc e x ↔ e ∈ F ∧ (x = a ∨ x = b) := by
  simp only [Inc, banana_isLink, exists_and_left, and_congr_right_iff]
  aesop

lemma banana_comm (ha : a ≠ ∅) (hb : b ≠ ∅) (hab : Disjoint a b) (F : Set β) :
    banana a b ha hb hab F = banana b a hb ha hab.symm F :=
  Graph.ext_inc (by simp [Set.pair_comm]) <| by simp [or_comm]

@[simp]
lemma banana_isNonloopAt_iff (ha : a ≠ ∅) (hb : b ≠ ∅) (hab : Disjoint a b) :
    (banana a b ha hb hab F).IsNonloopAt e x ↔ e ∈ F ∧ (x = a ∨ x = b) ∧ a ≠ b := by
  simp_rw [isNonloopAt_iff_inc_not_isLoopAt, ← isLink_self_iff, banana_isLink, banana_inc_iff]
  aesop

@[simp]
lemma banana_isLoopAt_iff (ha : a ≠ ∅) (hb : b ≠ ∅) (hab : Disjoint a b) :
    (banana a b ha hb hab F).IsLoopAt e x ↔ e ∈ F ∧ x = a ∧ a = b := by
  simp only [← isLink_self_iff, banana_isLink, and_congr_right_iff]
  aesop

@[simp]
lemma banana_singleton (e : β) (ha : a ≠ ∅) (hb : b ≠ ∅) (hab : Disjoint a b) :
    banana a b ha hb hab {e} = Graph.singleEdge e a b ha hb hab := by
  ext <;> rfl

lemma banana_mono (ha : a ≠ ∅) (hb : b ≠ ∅) (hab : Disjoint a b) {X Y : Set β} (hXY : X ⊆ Y) :
    banana a b ha hb hab X ≤s banana a b ha hb hab Y where
  vertexSet_eq := rfl
  isLink_of_isLink := by simp +contextual [subset_def ▸ hXY]

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
