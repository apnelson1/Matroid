import Mathlib.Combinatorics.Graph.Basic

variable {α β : Type*} {x y z u v w : α} {e f : β} {G H : Graph α β}


open Set

namespace Graph


/-
For mathlib
-/

@[simp]
lemma not_isLink_of_notMem_edgeSet (he : e ∉ E(G)) : ¬ G.IsLink e x y :=
  mt IsLink.edge_mem he

@[simp]
lemma not_inc_of_notMem_edgeSet (he : e ∉ E(G)) : ¬ G.Inc e x :=
  mt Inc.edge_mem he

/-- The set of ends of an edge `e`. -/
def endSet (G : Graph α β) (e : β) : Set α := {x | G.Inc e x}

@[simp]
lemma mem_endSet_iff : x ∈ G.endSet e ↔ G.Inc e x := Iff.rfl

lemma IsLink.endSet_eq (h : G.IsLink e x y) : G.endSet e = {x,y} := by
  ext a
  simp only [mem_endSet_iff, mem_insert_iff, mem_singleton_iff]
  refine ⟨fun h' ↦ h'.eq_or_eq_of_isLink h, ?_⟩
  rintro (rfl | rfl)
  · exact h.inc_left
  exact h.inc_right

lemma IsLoopAt.endSet_eq (h : G.IsLoopAt e x) : G.endSet e = {x} := by
  rw [IsLink.endSet_eq h, pair_eq_singleton]

lemma endSet_eq_of_notMem_edgeSet (he : e ∉ E(G)) : G.endSet e = ∅ := by
  simp only [endSet, eq_empty_iff_forall_notMem, mem_setOf_eq]
  exact fun x hx ↦ he hx.edge_mem

lemma inc_iff_isLoopAt_or_isNonloopAt : G.Inc e x ↔ G.IsLoopAt e x ∨ G.IsNonloopAt e x :=
  ⟨Inc.isLoopAt_or_isNonloopAt, fun h ↦ h.elim IsLoopAt.inc IsNonloopAt.inc⟩

/-- The function which maps a term in the subtype of edges of `G` to an unordered pair of
elements in the subtype of vertices of `G`.
Used mostly as an implementation details. -/
protected noncomputable def ends (G : Graph α β) (e : E(G)) : Sym2 (V(G)) :=
  have h := exists_isLink_of_mem_edgeSet e.2
  s(⟨_, h.choose_spec.choose_spec.left_mem⟩, ⟨_, h.choose_spec.choose_spec.right_mem⟩)

lemma IsLink.ends_eq (h : G.IsLink e x y) :
    G.ends ⟨e, h.edge_mem⟩ = s(⟨x, h.left_mem⟩,⟨y, h.right_mem⟩) := by
  simp only [Graph.ends, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Subtype.mk.injEq, Prod.swap_prod_mk]
  generalize_proofs h₁ h₂
  exact h₁.choose_spec.choose_spec.eq_and_eq_or_eq_and_eq h

lemma IsNonloopAt.vertexSet_nontrivial (h : G.IsNonloopAt e x) : G.vertexSet.Nontrivial := by
  obtain ⟨y, hne, h⟩ := h
  exact nontrivial_of_mem_mem_ne h.left_mem h.right_mem hne.symm
