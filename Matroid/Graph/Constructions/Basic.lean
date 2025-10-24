import Matroid.Graph.Subgraph.Basic
import Matroid.ForMathlib.Partition.Constructor
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.PFun

variable {α β : Type*} [CompleteLattice α] {x y z u v w a b : α} {e f : β} {G H : Graph α β}
  {F F₁ F₂ : Set β} {X Y : Set α} {P : Partition α} {l : β → α → α → Prop}

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
def mk_of_symm (P : Partition α) (l : β → α → α → Prop) [∀ e, IsSymm _ (l e)] :
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
def mk' (V : Partition α) (l : β → α → α → Prop) : Graph α β :=
  mk_of_symm V (fun e => SymmClosure (l e))

/-- The graph with vertex set `V` and no edges -/
@[simps]
protected def noEdge (P : Partition α) (β : Type*) : Graph α β where
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
lemma noEdge_empty : Graph.noEdge (⊥ : Partition α) β = ⊥ := rfl

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

instance : Inhabited (Graph α β) where
  default := ⊥

/-! ### Complete graphs -/

/-- The complete graph on `n` vertices. -/
@[simps]
def CompleteGraph (n : ℕ+) : Graph (Set ℕ) (Sym2 ℕ) where
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
-- def fromList (S : α) (l : List (α × α)) : Graph α ℕ where
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
