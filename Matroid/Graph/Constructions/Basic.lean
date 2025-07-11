import Matroid.Graph.Subgraph
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.PFun

variable {α β : Type*} {x y z u v w a b : α} {e f : β} {G H : Graph α β} {F F₁ F₂ : Set β}
  {X Y : Set α}

open Set Function

open scoped Sym2

namespace Graph

/-- The graph with vertex set `V` and no edges -/
@[simps]
protected def noEdge (V : Set α) (β : Type*) : Graph α β where
  vertexSet := V
  edgeSet := ∅
  IsLink _ _ _ := False
  isLink_symm := by simp
  dup_or_dup_of_isLink_of_isLink := by simp
  edge_mem_iff_exists_isLink := by simp
  left_mem_of_isLink := by simp

lemma eq_empty_or_vertexSet_nonempty (G : Graph α β) : G = Graph.noEdge ∅ β ∨ V(G).Nonempty := by
  refine V(G).eq_empty_or_nonempty.elim (fun he ↦ .inl (Graph.ext he fun e x y ↦ ?_)) Or.inr
  simp only [noEdge_isLink, iff_false]
  exact fun h ↦ by simpa [he] using h.left_mem

@[simp]
lemma noEdge_le_iff {V : Set α} : Graph.noEdge V β ≤ G ↔ V ⊆ V(G) := by
  simp [le_iff]

@[simp]
lemma noEdge_not_inc {V : Set α} : ¬ (Graph.noEdge V β).Inc e x := by
  simp [Inc]

@[simp]
lemma noEdge_not_isLoopAt {V : Set α} : ¬ (Graph.noEdge V β).IsLoopAt e x := by
  simp [← isLink_self_iff]

@[simp]
lemma noEdge_not_isNonloopAt {V : Set α} : ¬ (Graph.noEdge V β).IsNonloopAt e x := by
  simp [IsNonloopAt]

@[simp]
lemma noEdge_not_adj {V : Set α} : ¬ (Graph.noEdge V β).Adj x y := by
  simp [Adj]

lemma edgeDelete_eq_noEdge (G : Graph α β) (hF : E(G) ⊆ F) : G ＼ F = Graph.noEdge V(G) β := by
  refine Graph.ext rfl fun e x y ↦ ?_
  simp only [edgeDelete_isLink, noEdge_isLink, iff_false, not_and, not_not]
  exact fun h ↦ hF h.edge_mem

lemma edgeSet_eq_empty_iff : E(G) = ∅ ↔ G = Graph.noEdge V(G) β := by
  refine ⟨fun h ↦ Graph.ext rfl ?_, fun h ↦ by rw [h, noEdge_edgeSet]⟩
  simp only [noEdge_isLink, iff_false]
  refine fun e x y he ↦ ?_
  have := h ▸ he.edge_mem
  simp at this

@[simp]
lemma le_noEdge_iff : G ≤ Graph.noEdge X β ↔ V(G) ⊆ X ∧ E(G) = ∅ :=
  ⟨fun h ↦ ⟨vertexSet_mono h, subset_empty_iff.1 (edgeSet_mono h)⟩,
    fun h ↦ ⟨h.1, fun e x y he ↦ by simpa [h] using he.edge_mem⟩⟩

instance : OrderBot (Graph α β) where
  bot := Graph.noEdge ∅ β
  bot_le := by simp

@[simp]
lemma bot_vertexSet : V((⊥ : Graph α β)) = ∅ := rfl

@[simp]
lemma bot_edgeSet : V((⊥ : Graph α β)) = ∅ := rfl

@[simp]
lemma bot_isClosedSubgraph (G : Graph α β) : ⊥ ≤c G where
  le := bot_le
  closed := by simp

@[simp]
lemma bot_isInducedSubgraph (G : Graph α β) : ⊥ ≤i G :=
  G.bot_isClosedSubgraph.isInducedSubgraph

@[simp]
lemma noEdge_empty : Graph.noEdge (∅ : Set α) β = ⊥ := rfl

@[simp]
lemma bot_not_isLink : ¬ (⊥ : Graph α β).IsLink e x y :=
  id

@[simp]
lemma vertexSet_eq_empty_iff : V(G) = ∅ ↔ G = ⊥ := by
  refine ⟨fun h ↦ bot_le.antisymm' ⟨by simp [h], fun e x y he ↦ False.elim ?_⟩, fun h ↦ by simp [h]⟩
  simpa [h] using he.left_mem

@[simp]
lemma vertexSet_nonempty_iff : V(G).Nonempty ↔ G ≠ ⊥ := not_iff_not.mp <| by
  simp [not_nonempty_iff_eq_empty]

/-- A graph with a single edge `e` from `u` to `v` -/
@[simps]
protected def singleEdge (u v : α) (e : β) : Graph α β where
  vertexSet := {u,v}
  edgeSet := {e}
  IsLink e' x y := e' = e ∧ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))
  isLink_symm := by tauto
  dup_or_dup_of_isLink_of_isLink := by aesop
  edge_mem_iff_exists_isLink := by tauto
  left_mem_of_isLink := by tauto

lemma singleEdge_comm (u v : α) (e : β) : Graph.singleEdge u v e = Graph.singleEdge v u e := by
  ext <;> simp [or_comm]

lemma singleEdge_isLink_iff :
    (Graph.singleEdge u v e).IsLink f x y ↔ (f = e) ∧ s(x,y) = s(u,v) := by
  simp [Graph.singleEdge]

@[simp]
lemma singleEdge_inc_iff :
    (Graph.singleEdge u v e).Inc f x ↔ f = e ∧ (x = u ∨ x = v) := by
  simp only [Inc, singleEdge_isLink, exists_and_left, and_congr_right_iff]
  aesop

@[simp]
lemma singleEdge_adj_iff :
    (Graph.singleEdge u v e).Adj x y ↔ (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  simp [Adj]

@[simp]
lemma singleEdge_le_iff : Graph.singleEdge u v e ≤ G ↔ G.IsLink e u v := by
  simp only [le_iff, singleEdge_vertexSet, Set.pair_subset_iff, singleEdge_isLink_iff, and_imp,
    Sym2.eq_iff]
  refine ⟨fun h ↦ h.2 rfl (.inl ⟨rfl, rfl⟩), fun h ↦ ⟨⟨h.left_mem, h.right_mem⟩, ?_⟩⟩
  rintro e x y rfl (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · assumption
  exact h.symm



/-! ### Graphs with one vertex  -/

/-- A graph with one vertex and loops at that vertex -/
@[simps]
def bouquet (v : α) (F : Set β) : Graph α β where
  vertexSet := {v}
  edgeSet := F
  IsLink e x y := e ∈ F ∧ x = v ∧ y = v
  isLink_symm e := by simp +contextual [Symmetric]
  dup_or_dup_of_isLink_of_isLink := by aesop
  edge_mem_iff_exists_isLink := by aesop
  left_mem_of_isLink := by aesop

@[simp]
lemma bouquet_inc_iff : (bouquet v F).Inc e x ↔ e ∈ F ∧ x = v := by
  simp [Inc]

@[simp]
lemma bouquet_isLoopAt : (bouquet v F).IsLoopAt e x ↔ e ∈ F ∧ x = v := by
  simp [← isLink_self_iff]

@[simp]
lemma bouquet_not_isNonloopAt : ¬ (bouquet v F).IsNonloopAt e x := by
  simp +contextual [IsNonloopAt, eq_comm]

/-- Every graph on just one vertex is a bouquet on that vertex-/
lemma eq_bouquet (hv : v ∈ V(G)) (hss : V(G).Subsingleton) : G = bouquet v E(G) := by
  have hrw := hss.eq_singleton_of_mem hv
  refine Graph.ext_inc (by simpa) fun e x ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp [bouquet_inc_iff, ← mem_singleton_iff, ← hrw, h.edge_mem, h.vertex_mem]
  simp only [bouquet_inc_iff] at h
  obtain ⟨z,w, hzw⟩ := exists_isLink_of_mem_edgeSet h.1
  rw [h.2, ← show z = v from (show z ∈ {v} from hrw ▸ hzw.left_mem)]
  exact hzw.inc_left

/-- Every graph on just one vertex is a bouquet on that vertex-/
lemma exists_eq_bouquet_edge (hv : v ∈ V(G)) (hss : V(G).Subsingleton) : ∃ F, G = bouquet v F :=
  ⟨E(G), eq_bouquet hv hss⟩

lemma exists_eq_bouquet (hne : V(G).Nonempty) (hss : V(G).Subsingleton) : ∃ x F, G = bouquet x F :=
  ⟨_, _, eq_bouquet hne.some_mem hss⟩

lemma bouquet_empty (v : α) : bouquet v ∅ = Graph.noEdge {v} β := by
  ext <;> simp

lemma bouquet_mono (v : α) {X Y : Set β} (hss : X ⊆ Y) : bouquet v X ≤s bouquet v Y where
  le := ⟨by simp, by simp +contextual [subset_def ▸ hss]⟩
  vertexSet_eq := rfl

/-! ### Two vertices -/

/-- A graph with exactly two vertices and no loops. -/
@[simps]
def banana (a b : α) (F : Set β) : Graph α β where
  vertexSet := {a,b}
  edgeSet := F
  IsLink e x y := e ∈ F ∧ ((x = a ∧ y = b) ∨ (x = b ∧ y = a))
  isLink_symm _ _ _ := by aesop
  dup_or_dup_of_isLink_of_isLink := by aesop
  edge_mem_iff_exists_isLink := by aesop
  left_mem_of_isLink := by aesop

@[simp]
lemma banana_inc_iff : (banana a b F).Inc e x ↔ e ∈ F ∧ (x = a ∨ x = b) := by
  simp only [Inc, banana_isLink, exists_and_left, and_congr_right_iff]
  aesop

lemma banana_comm (a b : α) (F : Set β) : banana a b F = banana b a F :=
  Graph.ext_inc (pair_comm ..) <| by simp [or_comm]

@[simp]
lemma banana_isNonloopAt_iff :
    (banana a b F).IsNonloopAt e x ↔ e ∈ F ∧ (x = a ∨ x = b) ∧ a ≠ b := by
  simp_rw [isNonloopAt_iff_inc_not_isLoopAt, ← isLink_self_iff, banana_isLink, banana_inc_iff]
  aesop

@[simp]
lemma banana_isLoopAt_iff :
    (banana a b F).IsLoopAt e x ↔ e ∈ F ∧ x = a ∧ a = b := by
  simp only [← isLink_self_iff, banana_isLink, and_congr_right_iff]
  aesop

@[simp]
lemma banana_singleton (e : β) : banana a b {e} = Graph.singleEdge a b e := by
  ext <;> rfl

lemma banana_mono {X Y : Set β} (hXY : X ⊆ Y) : banana a b X ≤s banana a b Y where
  le := ⟨by simp, by simp +contextual [subset_def ▸ hXY]⟩
  vertexSet_eq := rfl

/-! ### Complete graphs -/

/-- The complete graph on `n` vertices. -/
@[simps]
def CompleteGraph (n : ℕ) : Graph ℕ (Sym2 ℕ) where
  vertexSet := Set.Iio n
  edgeSet := {s | (∀ i ∈ s, i < n) ∧ ¬ s.IsDiag}
  IsLink e x y := x < n ∧ y < n ∧ x ≠ y ∧ e = s(x, y)
  isLink_symm e he x y := by beta_reduce; rw [Sym2.eq_swap]; tauto
  dup_or_dup_of_isLink_of_isLink e x y z w h := by
    simp only [h, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
    tauto
  edge_mem_iff_exists_isLink e := by
    induction' e with x y
    simp +contextual only [mem_setOf_eq, Sym2.mem_iff, forall_eq_or_imp, forall_eq,
      Sym2.isDiag_iff_proj_eq, ne_eq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk,
      exists_and_left, iff_def, and_imp, forall_exists_index]
    refine ⟨fun hx hy hne ↦ ?_, fun a ha b hb hne heq ↦ ?_⟩
    · use x, hx, y, hy, hne, by simp
    · simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at heq
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := heq <;> tauto
  left_mem_of_isLink e x y h := h.1

@[simp]
lemma CompleteGraph_adj (n : ℕ) (x y : ℕ) (hx : x < n) (hy : y < n) :
    (CompleteGraph n).Adj x y ↔ x ≠ y := by
  unfold Adj
  simp [hx, hy]

/-- The star graph with `n` leaves with center `v` -/
@[simps]
def StarGraph (v : α) (f : β →. α) : Graph α β where
  vertexSet := {v} ∪ f.ran
  edgeSet := f.Dom
  IsLink e x y := ∃ (he : e ∈ f.Dom), s(v, f.fn e he) = s(x, y)
  edge_mem_iff_exists_isLink e := ⟨fun h ↦ ⟨v, f.fn e h, h, rfl⟩, fun ⟨x, y, he, h⟩ ↦ he⟩
  isLink_symm e he x y h := by beta_reduce; rwa [Sym2.eq_swap]
  dup_or_dup_of_isLink_of_isLink e x y z w h1 h2 := by
    obtain ⟨he, h⟩ := h1
    obtain ⟨_, h'⟩ := h2
    have := h.symm.trans h'
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at this
    tauto
  left_mem_of_isLink e x y h := by
    simp only [PFun.fn_apply, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk,
      singleton_union, mem_insert_iff] at h ⊢
    obtain ⟨he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h <;> tauto


/-! ### Graph constructor from a list of pairs of vertices -/

/-- The graph with vertex set `S` and edges over `ℕ` between pairs of vertices according to the list
  `l`.-/
@[simps]
def fromList (S : Set α) (l : List (α × α)) : Graph α ℕ where
  vertexSet := S ∪ {x | ∃ p ∈ l, x = p.1 ∨ x = p.2}
  edgeSet := Finset.range l.length
  IsLink e x y := ∃ p, l[e]? = some p ∧ s(x,y) = s(p.1, p.2)
  isLink_symm e x y h1 h2 := by beta_reduce; rwa [Sym2.eq_swap]
  dup_or_dup_of_isLink_of_isLink e x y z w h₁ h₂ := by aesop
  edge_mem_iff_exists_isLink e := by
    simp [Set.mem_image, Finset.mem_range, Sym2.exists, and_comm]
    refine ⟨fun h ↦ ?_, fun ⟨x, y, a, b, hor, h⟩ ↦ ?_⟩
    · use l[e].fst, l[e].snd, l[e].fst, l[e].snd
      simp
    · rw [← isSome_getElem? l e, h]
      tauto
  left_mem_of_isLink e x y h := by
    obtain ⟨p, hep, hs⟩ := h
    right
    simp only [Prod.mk.eta, Sym2.eq, Sym2.rel_iff', Prod.exists, mem_setOf_eq] at hs ⊢
    obtain rfl | hp := hs
    · use x, y, List.mem_of_getElem? hep, by tauto
    · use y, x, ?_, by tauto
      rw [← Prod.swap_eq_iff_eq_swap] at hp
      exact List.mem_of_getElem? <| hp ▸ hep
