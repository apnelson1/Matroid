import Matroid.Graph.Subgraph.Union
import Matroid.Graph.Walk.Path

variable {α β : Type*} {x y z u v w a b : α} {e f : β} {G H : Graph α β} {F F₁ F₂ : Set β}
    {X Y : Set α} {G H : Graph α β} {P : WList α β}

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

lemma IsLink.ne [G.Loopless] (he : G.IsLink e x y) : x ≠ y :=
  Adj.ne ⟨e, he⟩

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

@[simp]
lemma Inc.isNonloopAt [G.Loopless] (h : G.Inc e x) : G.IsNonloopAt e x :=
  h.isLoopAt_or_isNonloopAt.elim (False.elim ∘ Loopless.not_isLoopAt _ _) id

@[simp]
lemma setOf_isLoopAt_empty [G.Loopless] : {e | G.IsLoopAt e x} = ∅ := by
  ext e
  simp

lemma setOf_isNonloopAt_incEdges [G.Loopless] (x : α) : {e | G.IsNonloopAt e x} = E(G, x) := by
  ext e
  simp +contextual [iff_def, IsNonloopAt.inc]

instance [G.Loopless] (X : Set α) : G[X].Loopless where
  not_isLoopAt e x (h : G[X].IsLink e x x) := h.1.adj.ne rfl

instance [G.Loopless] (X : Set α) : (G - X).Loopless :=
  ‹G.Loopless›.mono vertexDelete_le

instance [G.Loopless] (F : Set β) : (G ↾ F).Loopless :=
  ‹G.Loopless›.mono edgeRestrict_le

instance [G.Loopless] (F : Set β) : (G ＼ F).Loopless :=
  ‹G.Loopless›.mono edgeDelete_le

lemma eq_noEdge_or_vertexSet_nontrivial (G : Graph α β) [G.Loopless] :
    (G = ⊥) ∨ (∃ x, G = Graph.noEdge {x} β) ∨ V(G).Nontrivial := by
  obtain rfl | ⟨v, hv⟩ := G.eq_bot_or_vertexSet_nonempty
  · simp
  obtain h | h := eq_singleton_or_nontrivial hv
  · refine .inr <| .inl ⟨v, Graph.ext (by simpa) fun e x y ↦ ?_⟩
    simp only [noEdge_isLink, iff_false]
    refine fun he ↦ he.adj.ne ?_
    rw [show x = v by simpa [h] using he.left_mem, show y = v by simpa [h] using he.right_mem]
  simp [h]

instance Loopless.union [G.Loopless] [H.Loopless] : (G ∪ H).Loopless where
  not_isLoopAt := by simp [union_isLoopAt_iff]

/-- Maximally loopless subgraph of `G`. -/
def loopRemove (G : Graph α β) : Graph α β := G ↾ {e | ∀ x, ¬ G.IsLoopAt e x}

instance : (loopRemove G).Loopless where
  not_isLoopAt e x := by
    simp only [loopRemove, edgeRestrict_isLoopAt_iff, mem_setOf_eq, not_and, not_forall, not_not]
    exact fun h ↦ ⟨x, h⟩

lemma loopRemove_le (G : Graph α β) : loopRemove G ≤ G := edgeRestrict_le

lemma loopRemove_isSpanningSubgraph (G : Graph α β) : loopRemove G ≤s G :=
  edgeRestrict_isSpanningSubgraph

@[simp]
lemma loopRemove_vertexSet : V(loopRemove G) = V(G) := by
  simp only [loopRemove, edgeRestrict_vertexSet]

@[simp]
lemma loopRemove_edgeSet : E(loopRemove G) = {e ∈ E(G) | ∀ x, ¬ G.IsLoopAt e x} := by
  simp only [loopRemove, edgeRestrict_edgeSet]
  rw [setOf_and]
  rfl

@[simp]
lemma loopRemove_isLink : (loopRemove G).IsLink e x y ↔ G.IsLink e x y ∧ x ≠ y := by
  rw [and_comm]
  simp only [loopRemove, edgeRestrict_isLink, mem_setOf_eq, ne_eq, and_congr_left_iff]
  intro h
  rw [iff_not_comm]
  simp only [not_forall, not_not]
  refine ⟨fun h' ↦ ⟨x, h' ▸ h⟩, fun ⟨z, hz⟩ ↦ ?_⟩
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hz.isLink_iff.mp h <;> rfl

/-- Proof that `loopRemove` is the maximally loopless subgraph of `G`. -/
lemma le_loopRemove [H.Loopless] (h : H ≤ G) : H ≤ loopRemove G where
  vertex_subset := by simp [vertexSet_mono h]
  isLink_of_isLink e x y he := by
    rw [loopRemove_isLink]
    refine ⟨he.of_le h, he.ne⟩

@[simp]
lemma loopRemove_eq [G.Loopless] : loopRemove G = G :=
  (loopRemove_le G).antisymm (le_loopRemove le_rfl)

@[simp]
lemma loopRemove_eq_iff [G.Loopless] : loopRemove G = G ↔ G.Loopless :=
  ⟨fun _ ↦ ‹G.Loopless›, fun _ ↦ loopRemove_eq⟩

lemma IsPath.loopRemove (hP : G.IsPath P) : (loopRemove G).IsPath P := by
  induction P with
  | nil => simp_all
  | cons x e w ih =>
    simp_all only [cons_isPath_iff, loopRemove_isLink, ne_eq, true_and, not_false_eq_true, and_true,
      forall_const]
    rintro rfl
    exact hP.2.2 first_mem

lemma loopRemove_isSpanningSubgraph_edgeDelete_isLoopAt (G : Graph α β) (x : α) :
    loopRemove G ≤s (G ＼ {e | G.IsLoopAt e x}) := by
  rw [edgeDelete_eq_edgeRestrict]
  apply edgeRestrict_isSpanningSubgraph_edgeRestrict
  intro e ⟨he, hel⟩
  use he, he, hel x

lemma loopRemove_le_edgeDelete_isLoopAt (G : Graph α β) (x : α) :
    loopRemove G ≤ (G ＼ {e | G.IsLoopAt e x}) :=
  G.loopRemove_isSpanningSubgraph_edgeDelete_isLoopAt x |>.le

lemma IsLoopAt.loopRemove_isSpanningSubgraph_edgeDelete (h : G.IsLoopAt e x) :
    loopRemove G ≤s (G ＼ {e}) :=
  G.loopRemove_isSpanningSubgraph_edgeDelete_isLoopAt x |>.trans
  <| G.edgeDelete_isSpanningSubgraph_anti_right <| by simpa

lemma IsLoopAt.loopRemove_le_edgeDelete (h : G.IsLoopAt e x) : loopRemove G ≤ (G ＼ {e}) :=
  h.loopRemove_isSpanningSubgraph_edgeDelete.le

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

instance (V : Set α) : (Graph.noEdge V β).Simple where
  not_isLoopAt := by simp
  eq_of_isLink := by simp

lemma singleEdge_simple (hne : x ≠ y) (e : β) : (Graph.singleEdge x y e).Simple where
  not_isLoopAt f z := by
    simp only [← isLink_self_iff, singleEdge_isLink, not_and, not_or]
    aesop
  eq_of_isLink := by aesop

noncomputable def adjIncFun (G : Graph α β) (x : α) : N(G, x) → E(G, x) :=
  fun y ↦ ⟨y.2.choose, _, y.2.choose_spec⟩

lemma adjIncFun_injective (G : Graph α β) (x : α) : Function.Injective (G.adjIncFun x) := by
  intro y z hyz
  have hy : G.IsLink (adjIncFun G x y) x y := y.2.choose_spec
  have hz : G.IsLink (adjIncFun G x y) x z := hyz ▸ z.2.choose_spec
  exact SetCoe.ext <| hz.isLink_iff_eq.mp hy

/-- In a simple graph, the bijection between edges at `x` and neighbours of `x`. -/
noncomputable def incAdjEquiv (G : Graph α β) [G.Simple] (x : α) :
    E(G, x) ≃ N(G, x) where
  toFun e := ⟨e.2.choose, _, e.2.choose_spec⟩
  invFun y := G.adjIncFun x y
  left_inv := by
    rintro ⟨e, he⟩
    simp only [Subtype.mk.injEq, adjIncFun]
    generalize_proofs h h'
    exact (h.choose_spec.unique_edge h'.choose_spec).symm
  right_inv := by
    rintro ⟨y, hy⟩
    simp only [Subtype.mk.injEq, adjIncFun]
    generalize_proofs h h'
    exact (h.choose_spec.right_unique h'.choose_spec).symm

@[simp]
lemma isLink_incAdjEquiv (e : E(G, x)) : G.IsLink e.1 x (G.incAdjEquiv x e) := by
  simp only [incAdjEquiv, Equiv.coe_fn_mk]
  generalize_proofs h
  exact h.choose_spec

@[simp]
lemma adj_incAdjEquiv (e : E(G, x)) : G.Adj x (G.incAdjEquiv x e) :=
  (isLink_incAdjEquiv e).adj

@[simp]
lemma isLink_incAdjEquiv_symm (y : N(G, x)) : G.IsLink ((G.incAdjEquiv x).symm y) x y := by
  simp only [incAdjEquiv, Equiv.coe_fn_symm_mk, adjIncFun]
  generalize_proofs h
  exact h.choose_spec

@[simp]
lemma inc_incAdjEquiv_symm (y : N(G, x)) : G.Inc ((G.incAdjEquiv x).symm y) x :=
  (isLink_incAdjEquiv_symm y).inc_left

/-! ### Operations -/

lemma Simple.union [H.Simple] (h : ∀ ⦃e f x y⦄, G.IsLink e x y → H.IsLink f x y → e = f) :
    (G ∪ H).Simple where
  eq_of_isLink e f x y he hf := by
    rw [union_isLink_iff] at he hf
    obtain hf | hf := hf
    · obtain he | he := he
      · exact he.unique_edge hf
      rw [h hf he.1]
    obtain he | he := he
    · exact h he hf.1
    exact he.1.unique_edge hf.1

omit [G.Simple] in
lemma IsPath.toGraph_simple {P : WList α β} (hP : G.IsPath P) : P.toGraph.Simple where
  not_isLoopAt e x h := by
    rw [← isLink_self_iff, hP.isWalk.wellFormed.toGraph_isLink] at h
    induction P with
    | nil => simp at h
    | cons u f P ih =>
      simp only [cons_isPath_iff] at hP
      simp only [isLink_cons_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk,
        and_comm, or_self] at h
      aesop
  eq_of_isLink e f x y he hf := by
    rw [hP.isWalk.wellFormed.toGraph_isLink] at he hf
    induction P with
    | nil => simp_all
    | cons u g P ih =>
    · simp only [isLink_cons_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
        Prod.swap_prod_mk] at he hf
      simp only [cons_isPath_iff] at hP
      have hrw (v' e') : ¬ P.IsLink e' u v' := fun h ↦ hP.2.2 h.left_mem
      have hrw' (v' e') : ¬ P.IsLink e' v' u := fun h ↦ hP.2.2 h.right_mem
      obtain rfl | hne := eq_or_ne x u
      · simp_all
      obtain rfl | hne' := eq_or_ne y u
      · simp_all
      exact ih hP.2.1 (by simpa [hne, hne'] using he) (by simpa [hne, hne'] using hf)

end Simple

/-! ### Small Graphs -/

lemma eq_banana [G.Loopless] (hV : V(G) = {a,b}) : G = banana a b E(G) := by
  refine Graph.ext_inc (by simpa) fun e x ↦ ?_
  simp only [banana_inc_iff]
  refine ⟨fun h ↦ ⟨h.edge_mem, by simpa using (show x ∈ {a,b} from hV ▸ h.vertex_mem)⟩, ?_⟩
  suffices aux : ∀ c, V(G) = {x,c} → e ∈ E(G) → G.Inc e x by
    rintro ⟨he, rfl | rfl⟩
    · exact aux _ hV he
    exact aux _ (pair_comm _ _ ▸ hV) he
  intro c hC he
  obtain ⟨z,w, hezw⟩ := exists_isLink_of_mem_edgeSet he
  obtain rfl | hzx := eq_or_ne z x
  · exact hezw.inc_left
  obtain rfl | hwx := eq_or_ne w x
  · exact hezw.inc_right
  have h1 := hC ▸ hezw.left_mem
  have h2 := hC ▸ hezw.right_mem
  obtain rfl : z = c := by simpa [hzx] using h1
  obtain rfl : w = z := by simpa [hwx] using h2
  exact (hezw.adj.ne rfl).elim

lemma exists_eq_banana [G.Loopless] (hV : V(G) = {a,b}) : ∃ F, G = banana a b F :=
  ⟨_, eq_banana hV⟩

lemma exists_eq_banana_of_encard [G.Loopless] (hV : V(G).encard = 2) :
    ∃ a b F, a ≠ b ∧ G = banana a b F := by
  obtain ⟨a, b, hab, hV⟩ := encard_eq_two.1 hV
  exact ⟨a, b, E(G), hab, eq_banana hV⟩

lemma banana_loopless (hab : a ≠ b) (F : Set α) : (banana a b F).Loopless where
  not_isLoopAt e x := by simp [hab]

instance lineGraph_simple : L(G).Simple where
  not_isLoopAt e x h := by
    unfold IsLoopAt at h
    simp [-isLink_self_iff] at h
  eq_of_isLink e f x y he hf := by
    obtain ⟨rfl, hne, h⟩ := he
    obtain ⟨rfl, -, h'⟩ := hf
    rfl

instance mixedLineGraph_simple : L'(G).Simple where
  not_isLoopAt ab x h := by
    unfold IsLoopAt at h
    cases x <;> simp [-isLink_self_iff] at h
  eq_of_isLink e f x y h1 h2 := by
    cases e
    cases f
    rw [mixedLineGraph_isLink] at h1 h2
    rw [← h1.2] at h2
    simp_all
