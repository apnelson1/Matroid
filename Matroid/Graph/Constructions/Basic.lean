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
@[simps!]
protected def noEdge (V : Set α) (β : Type*) : Graph α β := by
  apply mk_of_unique V (fun _ _ _ => False) (∅ : Set β) <;> simp

@[simp]
lemma noEdge_dup (V : Set α) : (Graph.noEdge V β).Dup = Partition.discrete V := rfl

@[simp]
lemma noEdge_vertexSet (V : Set α) : V(Graph.noEdge V β) = V := by
  simp [Graph.noEdge]

lemma eq_empty_or_vertexSet_nonempty (G : Graph α β) : G = Graph.noEdge ∅ β ∨ V(G).Nonempty := by
  refine V(G).eq_empty_or_nonempty.elim (fun he ↦ .inl (Graph.ext ?_ fun e x y ↦ ?_)) Or.inr
  · ext x y
    contrapose! he
    simp only [noEdge_vertexSet, mem_empty_iff_false, not_false_eq_true, not_dup_of_not_left_mem,
      and_true, and_false, or_false] at he
    exact ⟨x, he.left_mem⟩
  simp only [noEdge_isLink, iff_false]
  exact fun h ↦ by simpa [he] using h.left_mem

instance {V : Set α} : Nodup (Graph.noEdge V β) := by
  unfold Graph.noEdge
  infer_instance

@[simp]
lemma noEdge_isLabelSubgraph_iff {V : Set α} :
    Graph.noEdge V β ≤l G ↔ (∀ u v, u ∈ V → v ∈ V → (G.Dup u v ↔ u = v)) := by
  rw [isLabelSubgraph_iff, ← vertexSet_def, Partition.induce_eq_iff_rel]
  simp only [dup_eq_discrete, noEdge_vertexSet, Partition.supp_discrete, Partition.rel_discrete_eq,
    funext_iff, eq_iff_iff, and_congr_right_iff, noEdge_edgeSet, mem_empty_iff_false,
    not_false_eq_true, not_isLink_of_notMem_edgeSet, IsEmpty.forall_iff, implies_true, and_true]
  refine forall₃_congr fun u v hu => ⟨fun h hv => by simpa [hv] using h, fun h => ⟨by tauto, ?_⟩⟩
  rintro rfl
  tauto

@[simp]
lemma noEdge_le_iff {V : Set α} :
    Graph.noEdge V β ≤ G ↔ (∀ u v, u ∈ V → (G.Dup u v ↔ u = v)) := by
  rw [le_iff, Partition.subset_iff_rel]
  simp only [noEdge_dup, Partition.supp_discrete, Partition.rel_discrete_iff, noEdge_edgeSet,
    mem_empty_iff_false, not_false_eq_true, not_isLink_of_notMem_edgeSet, IsEmpty.forall_iff,
    implies_true, and_true]
  apply forall₃_congr fun u v hu => ⟨fun h => ?_, fun h => ?_⟩
  on_goal 1 => rw [← h, and_iff_right_iff_imp]
  on_goal 2 => rw [h, and_iff_right_iff_imp]
  all_goals rintro rfl; exact hu

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

lemma edgeDelete_eq_noEdge (G : Graph α β) [Nodup G] (hF : E(G) ⊆ F) :
    G ＼ F = Graph.noEdge V(G) β := by
  refine Graph.ext (by simp) fun e x y ↦ ?_
  simp only [edgeDelete_isLink, noEdge_isLink, iff_false, not_and, not_not]
  exact fun h ↦ hF h.edge_mem

lemma edgeSet_eq_empty_iff [G.Nodup] : E(G) = ∅ ↔ G = Graph.noEdge V(G) β := by
  refine ⟨fun h ↦ Graph.ext (by ext; simp) ?_, fun h ↦ by rw [h, noEdge_edgeSet]⟩
  simp only [noEdge_isLink, iff_false]
  refine fun e x y he ↦ ?_
  have := h ▸ he.edge_mem
  simp at this

lemma eq_noEdge_iff : G = Graph.noEdge V(G) β ↔ E(G) = ∅ ∧ G.Nodup := by
  refine ⟨fun h => ?_, fun ⟨hE, hL⟩ => edgeSet_eq_empty_iff.mp hE⟩
  have hL : G.Nodup := by
    rw [h]
    infer_instance
  rw [edgeSet_eq_empty_iff]
  exact ⟨h, hL⟩

@[simp]
lemma le_noEdge_iff : G ≤ Graph.noEdge X β ↔ V(G) ⊆ X ∧ E(G) = ∅ ∧ G.Nodup := by
  simp only [le_iff, dup_eq_discrete, noEdge_vertexSet, Partition.subset_iff_rel, vertexSet_def,
    Partition.rel_discrete_iff, noEdge_edgeSet, mem_empty_iff_false, not_false_eq_true,
    not_isLink_of_notMem_edgeSet, imp_false]
  refine ⟨fun ⟨hD, hl⟩ => ⟨fun x hx => (hD x x hx).mp (G.dup_refl_iff |>.mpr hx) |>.1, ?_,
    ⟨fun x y hxy => hD x y hxy.left_mem |>.mp hxy |>.2⟩⟩,
    fun ⟨hV, hE, hN⟩ => ⟨fun x y hx => by simp [hV hx, hx], ?_⟩⟩
  · contrapose! hl
    exact ⟨hl.some, exists_isLink_of_mem_edgeSet hl.some_mem⟩
  contrapose! hE
  obtain ⟨e, x, y, hl⟩ := hE
  use e, hl.edge_mem

instance : OrderBot (Graph α β) where
  bot := Graph.noEdge ∅ β
  bot_le := by simp

@[simp]
lemma bot_dup : (⊥ : Graph α β).Dup = ⊥ := by
  change Partition.discrete ∅ = _
  simp

@[simp]
lemma bot_vertexSet : V((⊥ : Graph α β)) = ∅ := by
  change V(Graph.noEdge ∅ β) = ∅
  rw [noEdge_vertexSet]

@[simp]
lemma bot_edgeSet : E((⊥ : Graph α β)) = ∅ := by
  change E(Graph.noEdge ∅ β) = ∅
  rw [noEdge_edgeSet]

@[simp]
lemma bot_isClosedSubgraph (G : Graph α β) : ⊥ ≤c G where
  toIsSubgraph := bot_le (a := G)
  closed := by simp

@[simp]
lemma bot_isInducedSubgraph (G : Graph α β) : ⊥ ≤i G :=
  G.bot_isClosedSubgraph.isInducedSubgraph

@[simp]
lemma bot_isLabelSubgraph : ⊥ ≤l G := by
  simp only [bot_le, isLabelSubgraph_of_le]

@[simp]
lemma noEdge_empty : Graph.noEdge (∅ : Set α) β = ⊥ := rfl

@[simp]
lemma bot_not_isLink : ¬ (⊥ : Graph α β).IsLink e x y := id

@[simp]
lemma vertexSet_eq_empty_iff : V(G) = ∅ ↔ G = ⊥ :=
  ⟨fun h => IsLabelSubgraph.antisymm
    ⟨by simp [h, Partition.eq_bot h], fun e x y he ↦ False.elim (by simpa [h] using he.left_mem)⟩
    (isLabelSubgraph_of_le bot_le), fun h ↦ by simp [h]⟩

@[simp]
lemma vertexSet_nonempty_iff : V(G).Nonempty ↔ G ≠ ⊥ := not_iff_not.mp <| by
  simp [not_nonempty_iff_eq_empty]

/-- A graph with a single edge `e` from `u` to `v` -/
@[simps! dup edgeSet isLink]
protected def singleEdge (u v : α) (e : β) : Graph α β := by
  apply mk_of_unique {u,v} (fun e' x y => e' = e ∧ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))) {e}
  <;> try tauto
  aesop

@[simp] lemma singleEdge_vertexSet : V(Graph.singleEdge u v e) = {u,v} := by
  simp [Graph.singleEdge]

instance {u v : α} : Nodup (Graph.singleEdge u v e) := by
  unfold Graph.singleEdge
  infer_instance

lemma singleEdge_comm (u v : α) (e : β) : Graph.singleEdge u v e = Graph.singleEdge v u e := by
  ext <;> simp [or_comm]

lemma isLink_singleEdge : (Graph.singleEdge u v e).IsLink e u v := by
  simp [Graph.singleEdge]

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
lemma singleEdge_isLabelSubgraph_iff :
    Graph.singleEdge u v e ≤l G ↔ (G.Dup u v → u = v) ∧ G.IsLink e u v := by
  refine ⟨fun h => ⟨fun hD => ?_, h.isLink_of_isLink isLink_singleEdge⟩, fun ⟨hD, hl⟩ => ⟨?_, ?_⟩⟩
  · rw [h.dup_iff (by simp) (by simp)] at hD
    exact eq_of_dup hD
  · rw [← vertexSet_def, Partition.induce_eq_iff_rel]
    ext x y
    simp only [dup_eq_discrete, singleEdge_vertexSet, Partition.supp_discrete, mem_insert_iff,
      mem_singleton_iff, Partition.rel_discrete_iff, and_congr_right_iff]
    rintro (rfl | rfl) <;> constructor
    · rintro ⟨(rfl | rfl), hD'⟩ <;> tauto
    · rintro rfl
      simp [G.refl_of_isLink hl]
    · rintro ⟨(rfl | rfl), hD'⟩
      · exact hD hD'.symm |>.symm
      rfl
    rintro rfl
    simp [G.refl_of_isLink hl.symm]
  simp only [singleEdge_isLink, and_imp]
  rintro e x y rfl (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · exact hl
  exact hl.symm

-- lemma singleEdge_le_iff_NodupAt (hu : G.NodupAt u) (hv : G.NodupAt v) :
--     Graph.singleEdge u v e ≤ G ↔ G.IsLink e u v := by
--   simp only [le_iff, singleEdge_vertexSet, mem_insert_iff, mem_singleton_iff, dup_iff_eq,
--     singleEdge_isLink, and_imp]
--   refine ⟨fun h ↦ h.2 rfl (.inl ⟨rfl, rfl⟩), fun h ↦ ⟨fun x y => ?_, ?_⟩⟩
--   · rintro (rfl | rfl)
--     · simp [hu.dup_iff, h.left_mem]
--     simp [hv.dup_iff, h.right_mem]
--   rintro e x y rfl (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
--   · exact h
--   exact h.symm

-- @[simp]
-- lemma singleEdge_le_iff [G.Nodup] : Graph.singleEdge u v e ≤ G ↔ G.IsLink e u v :=
--   singleEdge_le_iff_NodupAt (Nodup.NodupAt u) (Nodup.NodupAt v)

/-! ### Graphs with one vertex  -/

/-- A graph with one vertex and loops at that vertex -/
@[simps! dup edgeSet isLink]
def bouquet (v : α) (F : Set β) : Graph α β := by
  apply mk_of_unique {v} (fun e x y => e ∈ F ∧ x = v ∧ y = v) F <;> try tauto
  aesop

@[simp]
lemma bouquet_vertexSet : V(Graph.bouquet v F) = {v} := by
  simp [Graph.bouquet]

instance {v : α} : Nodup (Graph.bouquet v F) := by
  unfold Graph.bouquet
  infer_instance

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
  refine Graph.ext_inc ?_ fun e x ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · ext x y
    simp only [dup_iff_eq, bouquet_vertexSet, mem_singleton_iff]
    refine ⟨fun h => by simp [hss h.left_mem h.right_mem, hss h.right_mem hv], ?_⟩
    rintro ⟨rfl, rfl⟩
    exact G.dup_refl_iff.mpr hv
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
  dup_eq := by ext x y; simp
  isLink_of_isLink e x y := by simp +contextual [mem_of_subset_of_mem hss]

/-! ### Two vertices -/

/-- A graph with exactly two vertices and no loops. -/
@[simps! dup edgeSet isLink]
def banana (a b : α) (F : Set β) : Graph α β := by
  apply mk_of_unique {a,b} (fun e x y => e ∈ F ∧ ((x = a ∧ y = b) ∨ (x = b ∧ y = a))) F
  <;> try tauto
  aesop

instance {a b : α} : Nodup (Graph.banana a b F) := by
  unfold Graph.banana
  infer_instance

@[simp]
lemma banana_vertexSet : V(Graph.banana a b F) = {a,b} := by
  simp [Graph.banana]

@[simp]
lemma banana_inc_iff : (banana a b F).Inc e x ↔ e ∈ F ∧ (x = a ∨ x = b) := by
  simp only [Inc, banana_isLink, exists_and_left, and_congr_right_iff]
  aesop

lemma banana_comm (a b : α) (F : Set β) : banana a b F = banana b a F :=
  Graph.ext_inc (by ext; simp [or_comm]) <| by simp [or_comm]

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
  dup_eq := by ext x y; simp
  isLink_of_isLink e x y := by simp +contextual [mem_of_subset_of_mem hXY]

/-! ### Complete graphs -/

/-- The complete graph on `n` vertices. -/
@[simps! dup edgeSet isLink]
def CompleteGraph (n : ℕ) : Graph ℕ (Sym2 ℕ) := by
  refine mk_of_unique (Set.Iio n) (fun e x y => x < n ∧ y < n ∧ x ≠ y ∧ e = s(x, y))
    {s | (∀ i ∈ s, i < n) ∧ ¬ s.IsDiag}
    (fun e ⟨he, hediag⟩ x y ⟨hx, hy, hne, heq⟩ => ⟨hy, hx, hne.symm, heq ▸ Sym2.eq_swap⟩)
    (by aesop) ?_ (by tauto)
  simp +contextual only [mem_setOf_eq, ne_eq, exists_and_left, iff_def, and_imp,
    forall_exists_index, Sym2.mem_iff, forall_eq_or_imp, implies_true, and_self,
    Sym2.isDiag_iff_proj_eq, not_false_eq_true, and_true]
  rintro e he hdiag
  refine ⟨e.out.1, he _ e.out_fst_mem, e.out.2, he _ e.out_snd_mem, ?_, by simp⟩
  contrapose! hdiag
  rwa [← Quot.out_eq e, Sym2.isDiag_iff_proj_eq]

instance {n : ℕ} : Nodup (Graph.CompleteGraph n) := by
  unfold Graph.CompleteGraph
  infer_instance

@[simp]
lemma CompleteGraph_vertexSet (n : ℕ) : V(CompleteGraph n) = Set.Iio n := by
  simp [CompleteGraph]

@[simp]
lemma CompleteGraph_adj (n : ℕ) (x y : ℕ) (hx : x < n) (hy : y < n) :
    (CompleteGraph n).Adj x y ↔ x ≠ y := by
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
--   dup_or_dup_of_isLink_of_isLink e x y z w h1 h2 := by
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

-- /-- The graph with vertex set `S` and edges over `ℕ` between pairs of vertices according to the list
--   `l`.-/
-- @[simps]
-- def fromList (S : Set α) (l : List (α × α)) : Graph α ℕ where
--   vertexSet := S ∪ {x | ∃ p ∈ l, x = p.1 ∨ x = p.2}
--   edgeSet := Finset.range l.length
--   IsLink e x y := ∃ p, l[e]? = some p ∧ s(x,y) = s(p.1, p.2)
--   isLink_symm e x y h1 h2 := by beta_reduce; rwa [Sym2.eq_swap]
--   dup_or_dup_of_isLink_of_isLink e x y z w h₁ h₂ := by aesop
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
