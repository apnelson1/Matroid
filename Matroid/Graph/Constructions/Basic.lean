import Matroid.Graph.Subgraph.Basic
import Mathlib.Data.PFun
import Mathlib.Combinatorics.SimpleGraph.Basic

variable {α β : Type*} {x y z u v w a b : α} {e f : β} {G H : Graph α β} {F F₁ F₂ : Set β}
  {X Y V : Set α}

open Set Function

open scoped Sym2

namespace Graph

/-- The graph with vertex set `V` and no edges -/
@[simps (attr := grind =)]
protected def noEdge (V : Set α) (β : Type*) : Graph α β where
  vertexSet := V
  edgeSet := ∅
  IsLink _ _ _ := False
  isLink_symm := by simp
  eq_or_eq_of_isLink_of_isLink := by simp
  edge_mem_iff_exists_isLink := by simp
  left_mem_of_isLink := by simp

@[simp]
lemma noEdge_le_iff : Graph.noEdge V β ≤ G ↔ V ⊆ V(G) := by
  simp [le_iff]

@[simp]
lemma noEdge_not_inc : ¬ (Graph.noEdge V β).Inc e x := by
  simp [Inc]

@[simp]
lemma noEdge_not_isLoopAt : ¬ (Graph.noEdge V β).IsLoopAt e x := by
  simp [← isLink_self_iff]

@[simp]
lemma noEdge_not_isNonloopAt : ¬ (Graph.noEdge V β).IsNonloopAt e x := by
  simp [IsNonloopAt]

@[simp]
lemma noEdge_not_adj : ¬ (Graph.noEdge V β).Adj x y := by
  simp [Adj]

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

@[simp]
lemma noEdge_incEdges : E(Graph.noEdge X β, x) = ∅ := by
  ext e
  simp

instance : OrderBot (Graph α β) where
  bot := Graph.noEdge ∅ β
  bot_le := by simp

@[simp]
lemma bot_vertexSet : V((⊥ : Graph α β)) = ∅ := rfl

@[simp]
lemma bot_edgeSet : E((⊥ : Graph α β)) = ∅ := rfl

instance : IsEmpty V((⊥ : Graph α β)) := isEmpty_coe_sort.mpr rfl
instance : IsEmpty E((⊥ : Graph α β)) := isEmpty_coe_sort.mpr rfl

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

lemma eq_bot_or_vertexSet_nonempty (G : Graph α β) : G = ⊥ ∨ V(G).Nonempty := by
  refine (em (V(G) = ∅)).elim (fun he ↦ .inl (Graph.ext he fun e x y ↦ ?_)) (Or.inr ∘
    nonempty_iff_ne_empty.mpr)
  simp only [bot_not_isLink, iff_false]
  exact fun h ↦ by simpa [he] using h.left_mem

@[simp]
lemma vertexSet_eq_empty_iff : V(G) = ∅ ↔ G = ⊥ := by
  refine ⟨fun h ↦ bot_le.antisymm' ⟨by simp [h], fun e x y he ↦ False.elim ?_⟩, fun h ↦ by simp [h]⟩
  simpa [h] using he.left_mem

@[push, simp]
lemma ne_bot_iff : G ≠ ⊥ ↔ V(G).Nonempty := not_iff_not.mp <| by
  simp [not_nonempty_iff_eq_empty]

@[push, simp]
lemma vertexSet_not_nonempty_iff : ¬ V(G).Nonempty ↔ G = ⊥ := by
  simp [not_nonempty_iff_eq_empty]

lemma ne_bot_of_mem_vertexSet (h : x ∈ V(G)) : G ≠ ⊥ :=
  ne_bot_iff.mpr ⟨x, h⟩

instance : Inhabited (Graph α β) where
  default := ⊥

/-- A graph with a single edge `e` from `u` to `v` -/
@[simps (attr := grind =)]
protected def singleEdge (u v : α) (e : β) : Graph α β where
  vertexSet := {u,v}
  edgeSet := {e}
  IsLink e' x y := e' = e ∧ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))
  isLink_symm := by tauto
  eq_or_eq_of_isLink_of_isLink := by aesop
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
@[simps (attr := grind =)]
def bouquet (v : α) (F : Set β) : Graph α β where
  vertexSet := {v}
  edgeSet := F
  IsLink e x y := e ∈ F ∧ x = v ∧ y = v
  isLink_symm e := by simp +contextual [Symmetric]
  eq_or_eq_of_isLink_of_isLink := by aesop
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

@[simp]
lemma bouquet_adj_iff : (bouquet v F).Adj x y ↔ F.Nonempty ∧ x = v ∧ y = v := by
  simp only [Adj, bouquet_isLink, exists_and_right, and_congr_left_iff, and_imp]
  exact fun _ _ ↦ Iff.rfl

/-- Every graph on just one vertex is a bouquet on that vertex-/
lemma eq_bouquet_of_mem (hv : v ∈ V(G)) (hss : V(G).Subsingleton) : G = bouquet v E(G) := by
  have hrw := hss.eq_singleton_of_mem hv
  refine Graph.ext_inc (by simpa) fun e x ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp [bouquet_inc_iff, ← mem_singleton_iff, ← hrw, h.edge_mem, h.vertex_mem]
  simp only [bouquet_inc_iff] at h
  obtain ⟨z,w, hzw⟩ := exists_isLink_of_mem_edgeSet h.1
  rw [h.2, ← show z = v from (show z ∈ {v} from hrw ▸ hzw.left_mem)]
  exact hzw.inc_left

lemma eq_bouquet (hV : V(G) = {v}) : G = bouquet v E(G) :=
  eq_bouquet_of_mem (by simp [hV]) (by simp [hV])

/-- Every graph on just one vertex is a bouquet on that vertex-/
lemma exists_eq_bouquet_edge (hv : v ∈ V(G)) (hss : V(G).Subsingleton) : ∃ F, G = bouquet v F :=
  ⟨E(G), eq_bouquet_of_mem hv hss⟩

lemma exists_eq_bouquet (hne : V(G).Nonempty) (hss : V(G).Subsingleton) : ∃ x F, G = bouquet x F :=
  ⟨_, _, eq_bouquet_of_mem hne.some_mem hss⟩

lemma bouquet_empty (v : α) : bouquet v ∅ = Graph.noEdge {v} β := by
  ext <;> simp

lemma bouquet_mono (v : α) {X Y : Set β} (hss : X ⊆ Y) : bouquet v X ≤s bouquet v Y where
  vertexSet_eq := rfl
  isLink_of_isLink := by simp +contextual [subset_def ▸ hss]

@[simp]
lemma bouquet_incEdges : E(bouquet v F, v) = F := by
  ext e
  simp

@[simp]
lemma bouquet_le_iff_of_mem (hv : v ∈ V(G)) (F : Set β) :
    bouquet v F ≤ G ↔ ∀ e ∈ F, G.IsLoopAt e v := by
  refine ⟨fun h e heF ↦ IsLoopAt.of_le (by simpa) h, fun h ↦ ⟨by simpa, ?_⟩⟩
  rintro e x y ⟨hef, rfl, rfl⟩
  exact h e hef

@[simp]
lemma bouquet_le_iff_of_nonempty (v : α) (hF : F.Nonempty) :
    bouquet v F ≤ G ↔ ∀ e ∈ F, G.IsLoopAt e v := by
  refine ⟨fun h e heF ↦ IsLoopAt.of_le (by simpa) h, fun h ↦ ⟨?_, ?_⟩⟩
  · simp only [bouquet_vertexSet, singleton_subset_iff]
    exact (h _ hF.some_mem).vertex_mem
  rintro e x y ⟨hef, rfl, rfl⟩
  exact h e hef

/-! ### Two vertices -/

/-- A graph with exactly two vertices and no loops. -/
@[simps (attr := grind =)]
def banana (a b : α) (F : Set β) : Graph α β where
  vertexSet := {a,b}
  edgeSet := F
  IsLink e x y := e ∈ F ∧ ((x = a ∧ y = b) ∨ (x = b ∧ y = a))
  isLink_symm _ _ _ := by aesop
  eq_or_eq_of_isLink_of_isLink := by aesop
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
lemma banana_adj_iff : (banana a b F).Adj x y ↔ F.Nonempty ∧ (x = a ∧ y = b ∨ x = b ∧ y = a) := by
  simp only [Adj, banana_isLink, exists_and_right, and_congr_left_iff]
  exact fun _ ↦ Iff.rfl

@[simp]
lemma banana_singleton (e : β) : banana a b {e} = Graph.singleEdge a b e := by
  ext <;> rfl

lemma banana_mono {X Y : Set β} (hXY : X ⊆ Y) : banana a b X ≤s banana a b Y where
  vertexSet_eq := rfl
  isLink_of_isLink := by simp +contextual [subset_def ▸ hXY]

@[simp]
lemma banana_eq_bouquet : banana a a F = bouquet a F := by
  ext a b c <;> simp

@[simp]
lemma banana_eq_noEdge : banana a b ∅ = Graph.noEdge {a, b} β := by
  ext <;> simp

@[simp]
lemma banana_incEdges_left : E(banana a b F, a) = F := by
  ext e
  simp

@[simp]
lemma banana_incEdges_right : E(banana a b F, b) = F := by
  ext e
  simp

/-! ### Complete graphs -/

/-- The complete graph on `n` vertices. -/
@[simps (attr := grind =)]
def CompleteGraph (n : ℕ) : Graph ℕ (Sym2 ℕ) where
  vertexSet := Set.Iio n
  edgeSet := {s | (∀ i ∈ s, i < n) ∧ ¬ s.IsDiag}
  IsLink e x y := x < n ∧ y < n ∧ x ≠ y ∧ e = s(x, y)
  isLink_symm e he x y := by beta_reduce; rw [Sym2.eq_swap]; tauto
  eq_or_eq_of_isLink_of_isLink e x y z w h := by
    simp only [h, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
    tauto
  edge_mem_iff_exists_isLink e := by
    induction e with
    | h x y =>
    simp +contextual only [mem_setOf_eq, Sym2.mem_iff, forall_eq_or_imp, forall_eq,
      Sym2.isDiag_iff_proj_eq, ne_eq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk,
      exists_and_left, iff_def, and_imp, forall_exists_index]
    refine ⟨fun hx hy hne ↦ ?_, fun a ha b hb hne heq ↦ ?_⟩
    · use x, hx, y, hy, hne, by simp
    · obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := heq <;> tauto
  left_mem_of_isLink e x y h := h.1

@[simp]
lemma CompleteGraph_adj (n x y : ℕ) (hx : x < n) (hy : y < n) :
    (CompleteGraph n).Adj x y ↔ x ≠ y := by
  unfold Adj
  simp [hx, hy]

def IsComplete (G : Graph α β) : Prop := ∀ x ∈ V(G), ∀ y ∈ V(G), x ≠ y → G.Adj x y

@[simp]
lemma completeGraph_isComplete (n : ℕ+) : (CompleteGraph n).IsComplete := by
  rintro u hu v hv hne
  use s(u, v)
  simp_all

@[simp]
lemma bot_isComplete : (⊥ : Graph α β).IsComplete := by
  simp [IsComplete]

@[simp]
lemma bouquet_isComplete (v : α) (F : Set β) : (bouquet v F).IsComplete := by
  rintro a ha b hb hne
  simp only [bouquet_vertexSet, mem_singleton_iff] at ha hb
  subst a b
  exact (hne rfl).elim

@[simp]
lemma singleEdge_isComplete (u v : α) (e : β) : (Graph.singleEdge u v e).IsComplete := by
  rintro a ha b hb hne
  simp only [singleEdge_vertexSet, mem_insert_iff, mem_singleton_iff] at ha hb
  obtain rfl | rfl := ha <;> obtain rfl | rfl := hb <;> simp at hne ⊢

lemma banana_isComplete (a b : α) (hF : F.Nonempty) : (banana a b F).IsComplete := by
  rintro x hx y hy hne
  simp only [banana_vertexSet, mem_insert_iff, mem_singleton_iff] at hx hy
  obtain rfl | rfl := hx <;> obtain rfl | rfl := hy <;> simp [hF] at hne ⊢

@[simp]
lemma banana_isComplete_iff (a b : α) (F : Set β) :
    (banana a b F).IsComplete ↔ a = b ∨ F.Nonempty := by
  obtain rfl | hne := eq_or_ne a b
  · simp only [true_or, iff_true]
    intro x
    simp +contextual
  simp only [hne, false_or]
  exact ⟨fun h ↦ ⟨_, h a (by simp) b (by simp) hne |>.choose_spec.edge_mem⟩, banana_isComplete a b⟩

/-- The star graph with `n` leaves with center `v` -/
@[simps (attr := grind =)]
def StarGraph (v : α) (f : β →. α) : Graph α β where
  vertexSet := {v} ∪ f.ran
  edgeSet := f.Dom
  IsLink e x y := ∃ (he : e ∈ f.Dom), s(v, f.fn e he) = s(x, y)
  edge_mem_iff_exists_isLink e := ⟨fun h ↦ ⟨v, f.fn e h, h, rfl⟩, fun ⟨x, y, he, h⟩ ↦ he⟩
  isLink_symm e he x y h := by beta_reduce; rwa [Sym2.eq_swap]
  eq_or_eq_of_isLink_of_isLink e x y z w h1 h2 := by
    obtain ⟨he, h⟩ := h1
    obtain ⟨_, h'⟩ := h2
    have := h.symm.trans h'
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at this
    tauto
  left_mem_of_isLink e x y h := by
    simp only [PFun.fn_apply, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk,
      singleton_union, mem_insert_iff] at h ⊢
    obtain ⟨he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h <;> tauto

@[simp]
lemma starGraph_inc_iff (v : α) (f : β →. α) (e : β) (x : α) :
    (StarGraph v f).Inc e x ↔ v = x ∧ e ∈ f.Dom ∨ x ∈ f e := by
  simp only [Inc, StarGraph_isLink, PFun.fn_apply, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
    Prod.swap_prod_mk, PFun.mem_dom]
  refine ⟨fun ⟨e', ⟨a, ha⟩, h⟩ ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h
    · left
      simp [Exists.intro a ha]
    right
    apply Part.get_mem
  obtain ⟨rfl, y, hy⟩ | hx := h
  · use y, ⟨y, hy⟩
    simp [Part.get_eq_of_mem hy]
  · use v, ⟨x, hx⟩
    simp [Part.get_eq_of_mem hx]

@[simp]
lemma starGraph_adj_iff (v : α) (f : β →. α) (x y : α) :
    (StarGraph v f).Adj x y ↔ (v = x ∧ y ∈ f.ran ∨ v = y ∧ x ∈ f.ran) := by
  simp only [Adj, StarGraph_isLink, PFun.fn_apply, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
    Prod.swap_prod_mk, PFun.mem_dom]
  refine ⟨fun ⟨e, ⟨a, ha⟩, h⟩ ↦ ?_, fun h ↦ ?_⟩
  · apply h.imp (fun h ↦ ?_) (fun h ↦ ?_) <;>
    · use h.1, e
      rw [← h.2]
      apply Part.get_mem
  obtain ⟨rfl, e, h⟩ | ⟨rfl, e, h⟩ := h <;>
  · use e, ⟨_, h⟩
    simp [Part.get_eq_of_mem h]

-- /-! ### Graph constructor from a list of pairs of vertices -/

/-- The graph with vertex set `S` and edges over `ℕ` between pairs of vertices according to the list
  `l`.-/
@[simps (attr := grind =)]
def fromList (S : Set α) (l : List (α × α)) : Graph α ℕ where
  vertexSet := S ∪ {x | ∃ p ∈ l, x = p.1 ∨ x = p.2}
  edgeSet := Finset.range l.length
  IsLink e x y := ∃ p, l[e]? = some p ∧ s(x,y) = s(p.1, p.2)
  isLink_symm e x y h1 h2 := by beta_reduce; rwa [Sym2.eq_swap]
  eq_or_eq_of_isLink_of_isLink e x y z w h₁ h₂ := by aesop
  edge_mem_iff_exists_isLink e := by
    simp only [Finset.coe_range, mem_Iio, Prod.mk.eta, Sym2.eq, Sym2.rel_iff', and_comm,
      Prod.exists, Prod.mk.injEq, Prod.swap_prod_mk]
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

@[simps (attr := grind =)]
def OfSimpleGraph (G : SimpleGraph α) : Graph α (Sym2 α) where
  vertexSet := univ
  edgeSet := {s | ∃ x y, G.Adj x y ∧ s(x, y) = s}
  IsLink e x y := G.Adj x y ∧ s(x, y) = e
  isLink_symm e he x y h := by use h.1.symm, Sym2.eq_swap ▸ h.2
  eq_or_eq_of_isLink_of_isLink e x y z w h1 h2 := by
    have := by simpa using h1.2.trans h2.2.symm
    tauto
  left_mem_of_isLink e x y h := by simp

@[simps (attr := grind =)]
def OfSimpleGraphSet {S : Set α} (G : SimpleGraph S) : Graph α (Sym2 α) where
  vertexSet := S
  edgeSet := {s | ∃ x y, G.Adj x y ∧ s(x.val, y.val) = s}
  IsLink e x y := ∃ (hx : x ∈ S) (hy : y ∈ S), G.Adj ⟨x, hx⟩ ⟨y, hy⟩ ∧ s(x, y) = e
  isLink_symm e he x y h := by
    obtain ⟨hx, hy, h, rfl⟩ := h
    use hy, hx, h.symm, Sym2.eq_swap
  eq_or_eq_of_isLink_of_isLink e x y z w h1 h2 := by
    obtain ⟨-, -, -, rfl⟩ := h1
    obtain ⟨-, -, -, heq⟩ := h2
    have := by simpa using heq
    tauto
  left_mem_of_isLink e x y h := h.1
  edge_mem_iff_exists_isLink e := ⟨fun ⟨a, b, hab, he⟩ ↦ ⟨a.val, b.val, a.prop, b.prop, hab, by
    assumption⟩, fun ⟨x, y, hx, hy, h, heq⟩ ↦ ⟨⟨x, hx⟩, ⟨y, hy⟩, h, heq⟩⟩

@[simps! (attr := grind =)]
def LineSimpleGraph (G : Graph α β) : SimpleGraph E(G) :=
  SimpleGraph.fromRel (fun e f ↦ ∃ x, G.Inc e x ∧ G.Inc f x)

/-- The line graph of a graph `G` is the simple graph with the same vertices as `G` and edges
    given by the pairs of edges in `G` that have a common vertex. -/
@[simps (attr := grind =)]
def LineGraph (G : Graph α β) : Graph β (Sym2 β) where
  vertexSet := E(G)
  edgeSet := Sym2.mk '' { (e, f) | (e ≠ f) ∧ ∃ x, G.Inc e x ∧ G.Inc f x }
  IsLink a e f := s(e, f) = a ∧ e ≠ f ∧ ∃ x, G.Inc e x ∧ G.Inc f x
  edge_mem_iff_exists_isLink a := by simp only [and_comm, mem_image, mem_setOf_eq, Prod.exists]
  isLink_symm a ha e f hef := by
    simp_all only [mem_image, mem_setOf_eq, Prod.exists]
    simp_rw [and_comm, Sym2.eq_swap]
    simp [hef.1, hef.2.1.symm, hef.2.2]
  eq_or_eq_of_isLink_of_isLink := by
    rintro a e f g h ⟨rfl, hef, h⟩ ⟨heq, hgf, h'⟩
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at heq
    tauto
  left_mem_of_isLink := by
    rintro a e f ⟨rfl, hef, ⟨x, he, hf⟩⟩
    exact he.edge_mem

scoped notation "L(" G ")" => LineGraph G

@[simp]
lemma lineGraph_inc (G : Graph α β) (s : Sym2 β) (e : β) : L(G).Inc s e ↔ s ∈ E(L(G)) ∧ e ∈ s := by
  unfold Inc
  simp +contextual only [LineGraph_isLink, LineGraph_edgeSet, mem_image, mem_setOf_eq, Prod.exists,
    iff_def, forall_exists_index, and_imp]
  refine ⟨fun a hs hne x he ha ↦ ?_, fun a b hne x ha hb hs hes ↦ ?_⟩ <;> subst s
  · exact ⟨⟨e, a, ⟨hne, x, he, ha⟩, rfl⟩, by simp⟩
  obtain rfl | rfl := by simpa using hes
  · use b, rfl, hne, x
  use a, Sym2.eq_swap, hne.symm, x

@[simp]
lemma lineGraph_adj (G : Graph α β) (e f : β) :
    L(G).Adj e f ↔ e ≠ f ∧ ∃ x, G.Inc e x ∧ G.Inc f x := by
  simp [Adj]

lemma lineGraph_bouquet_isComplete (v : α) (F : Set β) : L(bouquet v F).IsComplete := by
  rintro a ha b hb hne
  simp_all

lemma lineGraph_banana_isComplete (a b : α) (F : Set β) : L(banana a b F).IsComplete := by
  rintro e f hne
  simp_all

lemma lineGraph_singleEdge_isComplete (u v : α) (e : β) : L(Graph.singleEdge u v e).IsComplete := by
  rintro a ha b hb hne
  simp_all

lemma lineGraph_starGraph_isComplete (v : α) (f : β →. α) : L(StarGraph v f).IsComplete := by
  rintro e h e'
  simp_all only [LineGraph_vertexSet, StarGraph_edgeSet, PFun.mem_dom, ne_eq, lineGraph_adj,
    starGraph_inc_iff, and_true, forall_exists_index, not_false_iff, true_and]
  intro _ _ _
  use v
  simp

/-- Note: a loop becomes a leaf. -/
@[simps (attr := grind =)]
def mixedLineGraph (G : Graph α β) : Graph (α ⊕ β) (α × β) where
  vertexSet := Sum.inl '' V(G) ∪ Sum.inr '' E(G)
  edgeSet := {(a, b) | G.Inc b a}
  IsLink e x y := G.Inc e.2 e.1 ∧ s(Sum.inl e.1, Sum.inr e.2) = s(x, y)
  isLink_symm e he x y h := ⟨h.1, by simp [h.2]⟩
  eq_or_eq_of_isLink_of_isLink e a b c d hab hcd := by
    have := by simpa using hab.2.symm.trans hcd.2
    tauto
  left_mem_of_isLink e x y h := by
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := by simpa using h.2
    · simp [h.1.vertex_mem]
    simp [h.1.edge_mem]
  edge_mem_iff_exists_isLink e := by simp

scoped notation "L'(" G ")" => mixedLineGraph G

@[simp]
lemma mixedLineGraph_inc (G : Graph α β) (e : α × β) (a : α ⊕ β) :
    L'(G).Inc e a ↔ G.Inc e.2 e.1 ∧ (Sum.inr e.2 = a ∨ Sum.inl e.1 = a) := by
  simp [Inc]

lemma mixedLineGraph_adj (G : Graph α β) (a b : α ⊕ β) :
    L'(G).Adj a b ↔ ∃ x e, G.Inc e x ∧ s(Sum.inl x, Sum.inr e) = s(a, b) := by
  simp [Adj]

@[simp]
lemma mixedLineGraph_vertex_not_adj (G : Graph α β) (x y : α) :
    ¬ L'(G).Adj (Sum.inl x) (Sum.inl y) := by
  intro ⟨e, h⟩
  simp at h

@[simp]
lemma mixedLineGraph_edge_not_adj (G : Graph α β) (e f : β) :
    ¬ L'(G).Adj (Sum.inr e) (Sum.inr f) := by
  intro ⟨e, h⟩
  simp at h
