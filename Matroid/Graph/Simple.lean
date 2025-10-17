import Matroid.Graph.Finite
import Matroid.Graph.Basic
import Matroid.Graph.Constructions.Basic

variable {α β : Type*} [CompleteLattice α] {x y z u v w a b : α} {e f : β} {G H : Graph α β}
  {F F₁ F₂ : Set β} {X Y : Set α} {P : WList α β}

open Set Function WList

namespace Graph

/-- A loopless graph is one where the ends of every edge are distinct. -/
@[mk_iff]
protected class Loopless (G : Graph α β) : Prop where
  not_isLoopAt : ∀ e x, ¬ G.IsLoopAt e x

@[simp]
lemma not_isLoopAt (G : Graph α β) [G.Loopless] (e : β) (x : α) : ¬ G.IsLoopAt e x :=
  Loopless.not_isLoopAt e x

lemma not_adj_self (G : Graph α β) [G.Loopless] (x : α) : ¬ G.Adj x x :=
  fun ⟨e, he⟩ ↦ Loopless.not_isLoopAt e x he

lemma Adj.ne [G.Loopless] (hxy : G.Adj x y) : x ≠ y :=
  fun h ↦ G.not_adj_self x <| h ▸ hxy

lemma loopless_iff_forall_ne_of_adj : G.Loopless ↔ ∀ x y, G.Adj x y → x ≠ y :=
  ⟨fun _ _ _ h ↦ h.ne, fun h ↦ ⟨fun _ x hex ↦ h x x hex.adj rfl⟩⟩

lemma vertexSet_nontrivial_of_edgeSet_nonempty [G.Loopless] (hE : E(G).Nonempty) :
    V(G).Nontrivial := by
  obtain ⟨e, he⟩ := hE
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
  exact ⟨x, hxy.left_mem, y, hxy.right_mem, hxy.adj.ne⟩

lemma Loopless.mono (hG : G.Loopless) (hle : H ≤ G) : H.Loopless := by
  rw [loopless_iff_forall_ne_of_adj] at hG ⊢
  exact fun x y hxy ↦ hG x y <| hxy.of_le hle

lemma Inc.isNonloopAt [G.Loopless] (h : G.Inc e x) : G.IsNonloopAt e x :=
  h.isLoopAt_or_isNonloopAt.elim (False.elim ∘ Loopless.not_isLoopAt _ _) id

instance [G.Loopless] (X : Set α) : G[X].Loopless where
  not_isLoopAt e x (h : G[X].IsLink e x x) := h.1.adj.ne rfl

instance [G.Loopless] (X : Set α) : (G - X).Loopless :=
  ‹G.Loopless›.mono vertexDelete_le

instance [G.Loopless] (F : Set β) : (G ↾ F).Loopless :=
  ‹G.Loopless›.mono edgeRestrict_le

instance [G.Loopless] (F : Set β) : (G ＼ F).Loopless :=
  ‹G.Loopless›.mono edgeDelete_le

lemma eq_noEdge_or_vertexSet_nontrivial (G : Graph α β) [G.Loopless] :
    (G = ⊥) ∨ (∃ x, G = Graph.noEdge (Partition.indiscrete' x) β) ∨ V(G).Nontrivial := by
  obtain rfl | ⟨v, hv⟩ := G.eq_empty_or_vertexSet_nonempty
  · simp
  obtain h | h := eq_singleton_or_nontrivial hv
  · refine .inr <| .inl ⟨v, Graph.ext (by simpa [G.ne_bot_of_mem hv]) fun e x y ↦ ?_⟩
    simp only [noEdge_isLink, iff_false]
    refine fun he ↦ he.adj.ne ?_
    rw [show x = v by simpa [h] using he.left_mem, show y = v by simpa [h] using he.right_mem]
  simp [h]

lemma Loopless.union {α : Type*} [Order.Frame α] {G H : Graph α β} [G.Loopless] [H.Loopless]
    (hG' : G.Dup_agree H) : (G ∪ H).Loopless where
  not_isLoopAt := by simp [union_isLoopAt_iff hG']

section Simple

/-- A `Simple` graph is a `Loopless` graph where no pair of vertices
are the ends of more than one edge. -/
@[mk_iff]
class Simple (G : Graph α β) : Prop extends G.Loopless where
  eq_of_isLink : ∀ ⦃e f x y⦄, G.IsLink e x y → G.IsLink f x y → e = f

variable [G.Simple]

lemma IsLink.unique_edge (h : G.IsLink e x y) (h' : G.IsLink f x y) : e = f :=
  Simple.eq_of_isLink h h'

lemma ends_injective (G : Graph α β) [G.Simple] : Function.Injective G.ends := by
  intro ⟨e, he⟩ ⟨f, hf⟩ hef
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
  obtain ⟨z, w, hzw⟩ := exists_isLink_of_mem_edgeSet hf
  simp only [hxy.ends_eq, hzw.ends_eq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Subtype.mk.injEq,
    Prod.swap_prod_mk] at hef
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hef
  · simp [hxy.unique_edge hzw]
  simp [hxy.unique_edge hzw.symm]

lemma finite_of_vertexSet_finite (h : V(G).Finite) : G.Finite where
  vertexSet_finite := h
  edgeSet_finite := by
    change Finite _ at *
    exact Finite.of_injective _ G.ends_injective

@[simp]
lemma Simple.vertexSet_finite_iff : V(G).Finite ↔ G.Finite :=
  ⟨finite_of_vertexSet_finite, fun _ ↦ Finite.vertexSet_finite⟩

omit [G.Simple] in
lemma Simple.mono (hG : G.Simple) (hle : H ≤ G) : H.Simple where
  not_isLoopAt e x := by simp [hG.toLoopless.mono hle]
  eq_of_isLink e f x y he hf := (he.of_le hle).unique_edge (hf.of_le hle)

instance : (G ↾ F).Simple := ‹G.Simple›.mono edgeRestrict_le
instance : (G ＼ F).Simple := ‹G.Simple›.mono edgeDelete_le
instance : (G - X).Simple := ‹G.Simple›.mono vertexDelete_le

instance : G[X].Simple where
  eq_of_isLink e f x y := by
    simp only [induce_isLink, and_imp]
    exact fun h _ _ h' _ _ ↦ h.unique_edge h'

instance (V : Partition (Set α)) : (Graph.noEdge V β).Simple where
  not_isLoopAt := by simp
  eq_of_isLink := by simp

-- lemma singleEdge_simple (e : β) (hxy : Disjoint x y) : (Graph.singleEdge e x y).Simple where
--   not_isLoopAt f z := by
--     obtain (rfl | hnep) := x.eq_empty_or_nonempty
--     · rw [IsLoopAt, singleEdge_isLink]
--       simp
--     obtain (rfl | hneq) := y.eq_empty_or_nonempty
--     · rw [IsLoopAt, singleEdge_isLink]
--       simp
--     rw [IsLoopAt, singleEdge_isLink_of_disjoint hnep hneq hxy]
--     aesop
--   eq_of_isLink := by aesop

/-- In a simple graph, the bijection between edges at `x` and neighbours of `x`. -/
noncomputable def incAdjEquiv (G : Graph α β) [G.Simple] (x : α) :
    {e // G.Inc e x} ≃ {y // G.Adj x y} where
  toFun e := ⟨e.2.choose, _, e.2.choose_spec⟩
  invFun y := ⟨y.2.choose, _, y.2.choose_spec⟩
  left_inv := by
    rintro ⟨e, he⟩
    simp only [Subtype.mk.injEq]
    generalize_proofs h h'
    exact (h.choose_spec.unique_edge h'.choose_spec).symm
  right_inv := by
    rintro ⟨y, hy⟩
    simp only [Subtype.mk.injEq]
    generalize_proofs h h'
    exact (h.choose_spec.right_unique h'.choose_spec).symm

@[simp]
lemma isLink_incAdjEquiv (e : {e // G.Inc e x}) : G.IsLink e.1 x (G.incAdjEquiv x e) := by
  simp only [incAdjEquiv, Equiv.coe_fn_mk]
  generalize_proofs h
  exact h.choose_spec

@[simp]
lemma adj_incAdjEquiv (e : {e // G.Inc e x}) : G.Adj x (G.incAdjEquiv x e) :=
  (isLink_incAdjEquiv e).adj

@[simp]
lemma isLink_incAdjEquiv_symm (y : {y // G.Adj x y}) : G.IsLink ((G.incAdjEquiv x).symm y) x y := by
  simp only [incAdjEquiv, Equiv.coe_fn_symm_mk]
  generalize_proofs h
  exact h.choose_spec

@[simp]
lemma inc_incAdjEquiv_symm (y : {y // G.Adj x y}) : G.Inc ((G.incAdjEquiv x).symm y) x :=
  (isLink_incAdjEquiv_symm y).inc_left

/-! ### Operations -/

lemma Simple.union {α : Type*} [Order.Frame α] {G H : Graph α β} [G.Simple] [H.Simple]
    (hG' : G.Dup_agree H) (h : ∀ ⦃e f x y⦄, G.IsLink e x y → H.IsLink f x y → e = f) :
    (G ∪ H).Simple where
  eq_of_isLink e f x y he hf := by
    rw [union_isLink hG'] at he hf
    obtain hf | hf := hf
    · obtain he | he := he
      · exact he.unique_edge hf
      rw [h hf he.1]
    obtain he | he := he
    · exact h he hf.1
    exact he.1.unique_edge hf.1
  not_isLoopAt := (Loopless.union hG').not_isLoopAt

-- omit [G.Simple] in
-- lemma IsPath.toGraph_simple {P : WList (Set α) β} (hP : G.IsPath P) : P.toGraph.Simple where
--   not_isLoopAt e x h := by
--     rw [← isLink_self_iff, hP.isWalk.wellFormed.toGraph_isLink] at h
--     induction P with
--     | nil => simp at h
--     | cons u f P ih =>
--       simp only [cons_isPath_iff] at hP
--       simp only [isLink_cons_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk,
--         and_comm, or_self] at h
--       aesop
--   eq_of_isLink e f x y he hf := by
--     rw [hP.isWalk.wellFormed.toGraph_isLink] at he hf
--     induction P with
--     | nil => simp_all
--     | cons u g P ih =>
--     · simp only [isLink_cons_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
--         Prod.swap_prod_mk] at he hf
--       simp only [cons_isPath_iff] at hP
--       have hrw (v' e') : ¬ P.IsLink e' u v' := fun h ↦ hP.2.2 h.left_mem
--       have hrw' (v' e') : ¬ P.IsLink e' v' u := fun h ↦ hP.2.2 h.right_mem
--       obtain rfl | hne := eq_or_ne x u
--       · simp_all
--       obtain rfl | hne' := eq_or_ne y u
--       · simp_all
--       exact ih hP.1 (by simpa [hne, hne'] using he) (by simpa [hne, hne'] using hf)

end Simple

/-! ### Small Graphs -/

-- lemma eq_banana [G.Loopless] (hV : V(G) = {a,b}) : G = banana a b E(G) := by
--   refine Graph.ext_inc ?_ fun e x ↦ ?_
--   · sorry
--   rw [banana_inc_of_disjoint]
--   simp only [banana_inc]
--   refine ⟨fun h ↦ ⟨h.edge_mem, by simpa using (show x ∈ {a,b} from hV ▸ h.vertex_mem)⟩, ?_⟩
--   suffices aux : ∀ c, V(G) = {x,c} → e ∈ E(G) → G.Inc e x by
--     rintro ⟨he, rfl | rfl⟩
--     · exact aux _ hV he
--     exact aux _ (pair_comm _ _ ▸ hV) he
--   intro c hC he
--   obtain ⟨z,w, hezw⟩ := exists_isLink_of_mem_edgeSet he
--   obtain rfl | hzx := eq_or_ne z x
--   · exact hezw.inc_left
--   obtain rfl | hwx := eq_or_ne w x
--   · exact hezw.inc_right
--   have h1 := hC ▸ hezw.left_mem
--   have h2 := hC ▸ hezw.right_mem
--   obtain rfl : z = c := by simpa [hzx] using h1
--   obtain rfl : w = z := by simpa [hwx] using h2
--   exact (hezw.adj.ne rfl).elim

-- lemma exists_eq_banana [G.Loopless] (hV : V(G) = {a,b}) : ∃ F, G = banana a b F :=
--   ⟨_, eq_banana hV⟩

-- lemma exists_eq_banana_of_encard [G.Loopless] (hV : V(G).encard = 2) :
--     ∃ a b F, a ≠ b ∧ G = banana a b F := by
--   obtain ⟨a, b, hab, hV⟩ := encard_eq_two.1 hV
--   exact ⟨a, b, E(G), hab, eq_banana hV⟩

-- lemma banana_loopless (hab : a ≠ b) (F : Set β) : (banana a b F).Loopless where
--   not_isLoopAt e x := by
--     rintro h
--     rw [banana_isloopAt] at h
    -- simp [hab, banana_isloopAt sorry]
