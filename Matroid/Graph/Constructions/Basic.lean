import Matroid.Graph.Subgraph.Basic
import Matroid.Graph.Nodup
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.PFun

variable {α β : Type*} {x y z u v w a b : α} {e f : β} {G H : Graph α β} {F F₁ F₂ : Set β}
  {X Y : Set α}

open Set Function Relation Partition

open scoped Sym2

namespace Graph

/-- `Copy` creates an identical graph with different definitions for its vertex set and edge set.
  This is mainly used to create graphs with improved definitional properties. -/
@[simps]
def copy (G : Graph α β) {V : Partition (Set α)} {E : Set β}
    {IsLink : β → α → α → Prop} (hV : V(G) = V) (hE : E(G) = E)
    (h_isLink : ∀ e x y, G.IsLink e x y ↔ IsLink e x y) : Graph α β where
  vertexSet := V
  edgeSet := E
  IsLink := IsLink
  isLink_symm e he x y := by
    simp_rw [← h_isLink]
    apply G.isLink_symm (hE ▸ he)
  dup_or_dup_of_isLink_of_isLink := by
    simp_rw [btwVx, ← h_isLink, ← hV]
    exact G.dup_or_dup_of_isLink_of_isLink
  edge_mem_iff_exists_isLink := by
    simp_rw [← h_isLink, ← hE]
    exact G.edge_mem_iff_exists_isLink
  mem_vertexSet_of_isLink := by
    simp_rw [← h_isLink, ← hV]
    exact G.mem_vertexSet_of_isLink
  isLink_of_dup := by
    simp_rw [← h_isLink, ← hV]
    exact G.isLink_of_dup

lemma copy_eq_self (G : Graph α β) {V : Partition (Set α)} {E : Set β}
    {IsLink : β → α → α → Prop} (hV : V(G) = V)(hE : E(G) = E)
    (h_isLink : ∀ e x y, G.IsLink e x y ↔ IsLink e x y) :
    G.copy hV hE h_isLink = G := by
  ext <;> simp_all


@[simps]
def mk' (P : Partition (Set α)) (l : β → α → α → Prop) : Graph α β where
  vertexSet := P
  IsLink e x y :=
    let l' := SymmClosure (l e)
    (btwVx P (fun x y ↦ x ∈ P.supp ∧ y ∈ P.supp ∧ l' x y)) ∧ Domp P l' x y
  isLink_symm e he x y := by
    rintro ⟨h, hxy⟩
    exact ⟨h, symm hxy⟩
  dup_or_dup_of_isLink_of_isLink e x y v w := by
    rintro ⟨h, x', hPxx', y', hy'x', hPy'y⟩ ⟨_, v', hPvv', w', hw'v', hPw'w⟩
    obtain h | h := h (⟨hPxx'.right_mem, hPy'y.left_mem, symm hy'x'⟩)
      (⟨hPvv'.right_mem, hPw'w.left_mem, symm hw'v'⟩)
    · exact Or.inl <| trans' (trans' hPxx' h) (symm hPvv')
    · exact Or.inr <| trans' (trans' hPxx' h) hPw'w
  mem_vertexSet_of_isLink e x y := by
    rintro ⟨h, z, hxz, hzy⟩
    exact hxz.left_mem
  isLink_of_dup e x y z := by
    rintro hxy ⟨h, hyz⟩
    exact ⟨h, trans' hxy hyz⟩

@[simp]
lemma mk'_btwVx_foo {P : Partition (Set α)} {l : β → α → α → Prop}
    (h : btwVx P <| SymmClosure (l e)) :
    btwVx P (fun x y ↦ x ∈ P.supp ∧ y ∈ P.supp ∧ SymmClosure (l e) x y) :=
  btwVx_anti_right (fun _ _ ⟨_, _, h⟩ ↦ h) h

lemma isLink_mk'_of_mem {P : Partition (Set α)} {l : β → α → α → Prop} (hl : l e x y)
    (h : btwVx P (fun x y ↦ x ∈ P.supp ∧ y ∈ P.supp ∧ SymmClosure (l e) x y)) (hx : x ∈ P.supp)
    (hy : y ∈ P.supp) : (mk' P l).IsLink e x y :=
  ⟨h, x, rel_self_of_mem_supp hx, y, Or.inr hl, rel_self_of_mem_supp hy⟩

@[simps]
def mk_of_domp (P : Partition (Set α)) (l : β → α → α → Prop) [∀ e, IsSymm α (l e)]
    (h : ∀ ⦃e⦄, btwVx P (l e)) : Graph α β where
  vertexSet := P
  IsLink e := Domp P (l e)
  isLink_symm e he := IsSymm.symm
  dup_or_dup_of_isLink_of_isLink := by
    rintro e x y a b ⟨w, hPxw, z, hlzw, hPzy⟩ ⟨d, hPad, c, hlcd, hPcb⟩
    obtain hPzc | hPzd := h (symm hlzw) (symm hlcd)
    · left
      rwa [left_rw P hPxw, left_rw P hPzc, comm_of P]
    right
    rwa [← right_rw P hPcb, ← right_rw P hPzd]
  mem_vertexSet_of_isLink e x y := by
    rw [domp_def']
    rintro ⟨z, hxz, hzy⟩
    exact hxz.left_mem
  isLink_of_dup e x y z := trans'

lemma isLink_mk_of_domp_of_mem {P : Partition (Set α)} {l : β → α → α → Prop} [∀ e, IsSymm α (l e)]
    (h : ∀ ⦃e⦄, btwVx P (l e)) (hl : l e x y) (hx : x ∈ P.supp) (hy : y ∈ P.supp) :
    (mk_of_domp P l h).IsLink e x y := by
  rw [mk_of_domp_isLink]
  exact ⟨x, Partition.rel_self_of_mem_supp hx, y, symm hl, Partition.rel_self_of_mem_supp hy⟩

@[simp↓]
lemma mk'_eq_mk_of_domp {P : Partition (Set α)} {l : β → α → α → Prop} [∀ e, IsSymm α (l e)]
    (h : ∀ ⦃e⦄, btwVx P (l e)) : mk' P l = mk_of_domp P l h :=
  Graph.ext (by rfl) (by
    simp only [mk'_isLink, symmClosure_eq_self, mk_of_domp_isLink, and_iff_right_iff_imp]
    rintro _ _ _ _ _ _ _ _ ⟨_, _, hab⟩ ⟨_, _, hcd⟩
    exact h hab hcd)

@[simps]
def mk_of_unique (V : Set α) (IsLink : β → α → α → Prop)
    (edgeSet : Set β := {e | ∃ x y, IsLink e x y})
    (isLink_symm : ∀ ⦃e : β⦄, e ∈ edgeSet → Symmetric (IsLink e))
    (dup_or_dup_of_isLink_of_isLink : ∀ ⦃e x y v w⦄, IsLink e x y → IsLink e v w → x = v ∨ x = w)
    (edge_mem_iff_exists_isLink : ∀ e, e ∈ edgeSet ↔ ∃ x y, IsLink e x y := by
      exact fun _ ↦ Iff.rfl)
    (left_mem_of_isLink : ∀ ⦃e x y⦄, IsLink e x y → x ∈ V) : Graph α β where
  edgeSet := edgeSet
  edge_mem_iff_exists_isLink := edge_mem_iff_exists_isLink
  vertexSet := Partition.discrete V
  IsLink := IsLink
  isLink_symm := isLink_symm
  dup_or_dup_of_isLink_of_isLink e x y v w hl hl' := by
    simp_rw [rel_discrete_iff]
    obtain rfl | rfl := dup_or_dup_of_isLink_of_isLink hl hl'
    · exact Or.inl ⟨rfl, left_mem_of_isLink hl⟩
    exact Or.inr ⟨rfl, left_mem_of_isLink hl⟩
  mem_vertexSet_of_isLink e x y hl :=
    (supp_discrete V).symm ▸ ⟨{x}, by simp [left_mem_of_isLink hl], by simp⟩
  isLink_of_dup e x y z hxy hl := by
    obtain ⟨rfl, hx⟩ := rel_discrete_iff.mp hxy
    exact hl

instance (V : Set α) (IsLink : β → α → α → Prop) (edgeSet : Set β)
    (isLink_symm : ∀ ⦃e : β⦄, e ∈ edgeSet → Symmetric (IsLink e))
    (dup_or_dup_of_isLink_of_isLink : ∀ ⦃e x y v w⦄, IsLink e x y → IsLink e v w → x = v ∨ x = w)
    (edge_mem_iff_exists_isLink : ∀ e, e ∈ edgeSet ↔ ∃ x y, IsLink e x y)
    (left_mem_of_isLink : ∀ ⦃e x y⦄, IsLink e x y → x ∈ V) :
    Nodup (mk_of_unique V IsLink edgeSet isLink_symm dup_or_dup_of_isLink_of_isLink
    edge_mem_iff_exists_isLink left_mem_of_isLink) where
  vertexSet_atomic := by simp

lemma Nodup.of_isLabelSubgraph (h : G ≤l H) [H.Nodup] : G.Nodup :=
  ⟨Nodup.vertexSet_atomic.atomic_of_le h.vertexSet_le⟩
alias IsLabelSubgraph.Nodup := Nodup.of_isLabelSubgraph

lemma Nodup.of_le (h : G ≤ H) [H.Nodup] : G.Nodup :=
  Nodup.of_isLabelSubgraph <| isLabelSubgraph_of_le h

@[simp]
lemma vertexSet_subset_discrete_iff_of_nodup {V : Set α} [G.Nodup] :
    V(G) ⊆ Partition.discrete V ↔ L(G) ⊆ V := by
  rw [vertexSet_eq_discrete]
  simp

/-- The graph with vertex set `V` and no edges -/
@[simps! vertexSet edgeSet isLink]
protected def noEdge (V : Set α) (β : Type*) : Graph α β := by
  apply mk_of_unique V (fun _ _ _ => False) (∅ : Set β) (edge_mem_iff_exists_isLink := ?_) <;> simp

lemma eq_empty_or_labelSet_nonempty (G : Graph α β) : G = Graph.noEdge ∅ β ∨ L(G).Nonempty := by
  refine L(G).eq_empty_or_nonempty.elim (fun he ↦ .inl (Graph.ext ?_ fun e x y ↦ ?_)) Or.inr
  · ext x y
    simp only [noEdge_vertexSet, discrete_empty, rel_bot, iff_false]
    contrapose! he
    exact ⟨x, he.left_mem⟩
  simp only [noEdge_isLink, iff_false]
  exact fun h ↦ by simpa [he] using h.left_mem

instance {V : Set α} : Nodup (Graph.noEdge V β) := by
  unfold Graph.noEdge
  infer_instance

@[simp]
lemma noEdge_isLabelSubgraph_iff {V : Set α} :
    Graph.noEdge V β ≤l G ↔ V ⊆ L(G) ∧ Atomic (V(G).induce V) := by
  refine ⟨fun h => ?_, fun h => ⟨by rwa [noEdge_vertexSet, discrete_isInducedSubpartition_iff],
    fun _ _ _ hl => by simp at hl⟩⟩
  have := inter_eq_left.mpr h.labelSet
  have := h.vertexSet_isInducedSubpartition
  simp_all

@[simp]
lemma noEdge_le_iff {V : Set α} : Graph.noEdge V β ≤ G ↔ Partition.discrete V ⊆ V(G) :=
  ⟨(·.vertexSet_subset), fun h => ⟨h, fun e x y hl => by simp at hl⟩⟩

@[simp]
lemma noEdge_le_of_nodup {V : Set α} [G.Nodup] : Graph.noEdge V β ≤ G ↔ V ⊆ L(G) := by
  rw [noEdge_le_iff, vertexSet_eq_discrete]
  simp

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

-- lemma edgeDelete_eq_noEdge (G : Graph α β) [Nodup G] (hF : E(G) ⊆ F) :
--     G ＼ F = Graph.noEdge V(G) β := by
--   refine Graph.ext (by simp) fun e x y ↦ ?_
--   simp only [edgeDelete_isLink, noEdge_isLink, iff_false, not_and, not_not]
--   exact fun h ↦ hF h.edge_mem

lemma edgeSet_eq_empty_iff [G.Nodup] : E(G) = ∅ ↔ G = Graph.noEdge L(G) β := by
  refine ⟨fun h ↦ Graph.ext (by rw [vertexSet_eq_discrete]; simp) ?_,
    fun h ↦ by rw [h, noEdge_edgeSet]⟩
  simp only [noEdge_isLink, iff_false]
  refine fun e x y he ↦ ?_
  have := h ▸ he.edge_mem
  simp at this

lemma eq_noEdge_iff : G = Graph.noEdge L(G) β ↔ E(G) = ∅ ∧ G.Nodup := by
  refine ⟨fun h => ?_, fun ⟨hE, hL⟩ => edgeSet_eq_empty_iff.mp hE⟩
  have hL : G.Nodup := by
    rw [h]
    infer_instance
  rw [edgeSet_eq_empty_iff]
  exact ⟨h, hL⟩

@[simp]
lemma le_noEdge_iff : G ≤ Graph.noEdge X β ↔ L(G) ⊆ X ∧ E(G) = ∅ ∧ G.Nodup := by
  refine ⟨fun h => ⟨by simpa using labelSet_mono h, by simpa using edgeSet_mono h, Nodup.of_le h⟩,
    fun ⟨hV, hE, hN⟩ => ⟨by simpa, fun e x y hl => ?_⟩⟩
  have := hE ▸ hl.edge_mem
  simp at this

instance : OrderBot (Graph α β) where
  bot := Graph.noEdge ∅ β
  bot_le G := by simp

@[simp]
lemma bot_vertexSet : V((⊥ : Graph α β)) = ⊥ := by
  change Partition.discrete ∅ = _
  simp

@[simp]
lemma bot_labelSet : L((⊥ : Graph α β)) = ∅ := by
  change L(Graph.noEdge ∅ β) = ∅
  simp

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
lemma labelSet_eq_empty_iff : L(G) = ∅ ↔ G = ⊥ :=
  ⟨fun h => IsLabelSubgraph.antisymm
    ⟨by simp [Partition.eq_bot h], fun e x y he ↦ by simpa [h] using he.left_mem⟩
    (isLabelSubgraph_of_le bot_le), fun h ↦ by simp [h]⟩

@[simp]
lemma labelSet_nonempty_iff : L(G).Nonempty ↔ G ≠ ⊥ := not_iff_not.mp <| by
  simp [not_nonempty_iff_eq_empty]

/-- A graph with a single edge `e` from `u` to `v` -/
@[simps! vertexSet edgeSet isLink]
protected def singleEdge (u v : α) (e : β) : Graph α β := by
  apply mk_of_unique {u,v} (fun e' x y => e' = e ∧ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))) {e}
    (edge_mem_iff_exists_isLink := ?_)
  <;> try tauto
  aesop

@[simp] lemma singleEdge_labelSet : L(Graph.singleEdge u v e) = {u,v} := by
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
    Graph.singleEdge u v e ≤l G ↔ (V(G) u v → u = v) ∧ G.IsLink e u v := by
  refine ⟨fun h => ⟨fun hD => ?_, h.isLink_of_isLink isLink_singleEdge⟩, fun ⟨hD, hl⟩ => ⟨?_, ?_⟩⟩
  · rw [h.dup_iff (by simp) (by simp)] at hD
    exact eq_of_dup hD
  · simp only [singleEdge_vertexSet, discrete_isInducedSubpartition_iff, pair_subset_iff,
    hl.left_mem, hl.right_mem, and_self, true_and, atomic_iff_rel_le_eq]
    rintro a b hab
    obtain ⟨(rfl | rfl), (rfl | rfl), hdup⟩ := (by simpa using hab) <;> simp_all [Rel.symm]
  rintro e' x y ⟨rfl, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
  · exact hl
  exact hl.symm

-- @[simp]
-- lemma singleEdge_le_iff [G.Nodup] : Graph.singleEdge u v e ≤ G ↔ G.IsLink e u v :=
--   singleEdge_le_iff_NodupAt (Nodup.NodupAt u) (Nodup.NodupAt v)

/-! ### Graphs with one vertex  -/

/-- A graph with one vertex and loops at that vertex -/
@[simps! vertexSet edgeSet isLink]
def bouquet (v : α) (F : Set β) : Graph α β := by
  apply mk_of_unique {v} (fun e x y => e ∈ F ∧ x = v ∧ y = v) F (edge_mem_iff_exists_isLink := ?_)
  <;> try tauto
  aesop

@[simp]
lemma bouquet_labelSet : L(Graph.bouquet v F) = {v} := by
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
lemma eq_bouquet (hv : v ∈ L(G)) (hss : L(G).Subsingleton) : G = bouquet v E(G) := by
  have hrw := hss.eq_singleton_of_mem hv
  refine Graph.ext_inc ?_ fun e x ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · ext x y
    simp only [bouquet_vertexSet, rel_discrete_iff, mem_singleton_iff]
    refine ⟨fun h => by simp [hss h.left_mem h.right_mem, hss h.right_mem hv], ?_⟩
    rintro ⟨rfl, rfl⟩
    rwa [rel_self_iff_mem_supp]
  · simp [bouquet_inc_iff, ← mem_singleton_iff, ← hrw, h.edge_mem, h.label_mem]
  simp only [bouquet_inc_iff] at h
  obtain ⟨z,w, hzw⟩ := exists_isLink_of_mem_edgeSet h.1
  rw [h.2, ← show z = v from (show z ∈ {v} from hrw ▸ hzw.left_mem)]
  exact hzw.inc_left

/-- Every graph on just one vertex is a bouquet on that vertex-/
lemma exists_eq_bouquet_edge (hv : v ∈ L(G)) (hss : L(G).Subsingleton) : ∃ F, G = bouquet v F :=
  ⟨E(G), eq_bouquet hv hss⟩

lemma exists_eq_bouquet (hne : L(G).Nonempty) (hss : L(G).Subsingleton) : ∃ x F, G = bouquet x F :=
  ⟨_, _, eq_bouquet hne.some_mem hss⟩

lemma bouquet_empty (v : α) : bouquet v ∅ = Graph.noEdge {v} β := by
  ext <;> simp

lemma bouquet_mono (v : α) {X Y : Set β} (hss : X ⊆ Y) : bouquet v X ≤s bouquet v Y where
  vertexSet_eq := by ext x y; simp
  isLink_of_isLink e x y := by simp +contextual [mem_of_subset_of_mem hss]

/-! ### Two vertices -/

/-- A graph with exactly two vertices and no loops. -/
@[simps! vertexSet edgeSet isLink]
def banana (a b : α) (F : Set β) : Graph α β := by
  apply mk_of_unique {a,b} (fun e x y => e ∈ F ∧ ((x = a ∧ y = b) ∨ (x = b ∧ y = a))) F
    (edge_mem_iff_exists_isLink := ?_)
  <;> try tauto
  aesop

instance {a b : α} : Nodup (Graph.banana a b F) := by
  unfold Graph.banana
  infer_instance

@[simp]
lemma banana_labelSet : L(Graph.banana a b F) = {a,b} := by
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
  vertexSet_eq := by ext x y; simp
  isLink_of_isLink e x y := by simp +contextual [mem_of_subset_of_mem hXY]

/-! ### Complete graphs -/

/-- The complete graph on `n` vertices. -/
@[simps! vertexSet edgeSet isLink]
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
lemma CompleteGraph_labelSet (n : ℕ) : L(CompleteGraph n) = Set.Iio n := by
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

-- /-- The graph with vertex set `S` and edges over `ℕ` between pairs of vertices according to the
--   list `l`.-/
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
