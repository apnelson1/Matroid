import Matroid.Graph.Subgraph
import Matroid.Graph.Basic
import Matroid.Graph.Finite

variable {α β : Type*} {x y z u v w : α} {e f : β} {G H : Graph α β} {F F₁ F₂ : Set β} {X Y : Set α}
    {G H : Graph α β}

open Set Function

namespace Graph

/-- A loopless graph is one where the ends of every edge are distinct. -/
@[mk_iff]
protected class Loopless (G : Graph α β) : Prop where
  not_isLoopAt : ∀ e x, ¬ G.IsLoopAt e x

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
    (G = Graph.noEdge ∅ β) ∨ (∃ x, G = Graph.noEdge {x} β) ∨ V(G).Nontrivial := by
  obtain rfl | ⟨v, hv⟩ := G.eq_empty_or_vertexSet_nonempty
  · simp
  obtain h | h := eq_singleton_or_nontrivial hv
  · refine .inr <| .inl ⟨v, Graph.ext (by simpa) fun e x y ↦ ?_⟩
    simp only [noEdge_isLink, iff_false]
    refine fun he ↦ he.adj.ne ?_
    rw [show x = v by simpa [h] using he.left_mem, show y = v by simpa [h] using he.right_mem]
  simp [h]

/-- A `Simple` graph is a `Loopless` graph where no pair of vertices
are the ends of more than one edge. -/
@[mk_iff]
class Simple (G : Graph α β) : Prop extends G.Loopless where
  eq_of_isLink : ∀ ⦃e f x y⦄, G.IsLink e x y → G.IsLink f x y → e = f

lemma IsLink.unique_edge [G.Simple] (h : G.IsLink e x y) (h' : G.IsLink f x y) : e = f :=
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

lemma finite_of_vertexSet_finite [G.Simple] (h : V(G).Finite) : G.Finite where
  vertexSet_finite := h
  edgeSet_finite := by
    change Finite _ at *
    exact Finite.of_injective _ G.ends_injective

lemma vertexSet_finite_iff [G.Simple] : V(G).Finite ↔ G.Finite :=
  ⟨finite_of_vertexSet_finite, fun _ ↦ Finite.vertexSet_finite⟩
