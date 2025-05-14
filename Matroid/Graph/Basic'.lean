/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Jun Kwon
-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sym.Sym2

/-!
# Multigraphs

A multigraph is a set of vertices and a set of edges,
together with incidence data that associates each edge `e`
with an unordered pair `(x,y)` of vertices.
`x` and `y` may be equal, in which case `e` is a 'loop',
and there may also be more than one edge `e` associated with each pair `x` and `y`.
A multigraph where neither of these occurs is 'simple',
and these objects are described by `SimpleGraph`.

This module defines `Graph α β` for a vertex type `α` and an edge type `β`,
and gives basic API for incidence and adjacency.

## Main definitions

For `G : Graph α β`, ...

* `V(G)` denotes the vertex set of `G` as a term in `Set α`.
* `E(G)` denotes the edge set of `G` as a term in `Set β`.
* `G.IsLink e x y` means that the edge `e : β` has vertices `x : α` and `y : α` as its ends.
* `G.Inc e x` means that the edge `e : β` has `x` as one of its ends.
* `G.Adj x y` means that there is an edge `e` having `x` and `y` as its ends.
* `G.IsLoopAt e x` means that `e` is a loop edge with both ends equal to `x`.
* `G.IsNonloopAt e x` means that `e` is a non-loop edge with one end equal to `x`.

## Implementation notes

Unlike the design of `SimpleGraph`, the vertex and edge sets of `G` are modelled as sets
`V(G) : Set α` and `E(G) : Set β`, within ambient types, rather than being types themselves.
This mimics the 'embedded set' design used in `Matroid`, which seems to be more amenable to
formalizing real-world proofs in combinatorics.

A specific advantage is that this will allow subgraphs of `G : Graph α β` to also be terms in
`Graph α β`, and so there is no need for an extensive `Graph.subgraph` API and all the associated
definitions and canonical coercion maps. The same will go for minors and the various other
partial orders on multigraphs.

The main tradeoff is that certain parts of the API will require caring about whether a term
`x : α` or `e : β` is a 'real' vertex or edge of the graph, rather than something outside
the vertex or edge set. This is an issue, but is likely quite amenable to automation.

## Notation

Relecting written mathematics, we use the compact notations `V(G)` and `E(G)` to describe
vertex and edge sets formally, but use the longer terms `vertexSet` and `edgeSet` within
lemma names to refer to the same objects.

-/

variable {α β : Type*} {x y z u v w : α} {e f : β}

open Set

/-- A multigraph with vertex set `V : Set α` and edge set `E : Set β`,
as described by a predicate describing whether an edge `e : β` has ends `x` and `y`. -/
structure Graph (α β : Type*) where
  /-- The vertex set. -/
  vertexSet : Set α
  /-- The edge set. -/
  edgeSet : Set β
  /-- The predicate that an edge `e` goes from `x` to `y`. -/
  IsLink : β → α → α → Prop
  /-- If `e` goes from `x` to `y`, it goes from `y` to `x`. -/
  isLink_symm : ∀ ⦃e x y⦄, IsLink e x y → IsLink e y x
  /-- An edge is incident with at most one pair of vertices. -/
  eq_or_eq_of_isLink_of_isLink : ∀ ⦃e x y v w⦄, IsLink e x y → IsLink e v w → x = v ∨ x = w
  /-- If `e` is incident to something, then `e` is in the edge set -/
  edge_mem_iff_exists_isLink : ∀ e, e ∈ edgeSet ↔ ∃ x y, IsLink e x y
  /-- If some edge `e` is incident to `x`, then `x ∈ V`. -/
  left_mem_of_isLink : ∀ ⦃e x y⦄, IsLink e x y → x ∈ vertexSet

initialize_simps_projections Graph (IsLink → isLink)

namespace Graph

scoped notation "V(" G ")" => Graph.vertexSet G

scoped notation "E(" G ")" => Graph.edgeSet G

variable {G H : Graph α β}

/-! ### Edge-vertex-vertex incidence -/

lemma IsLink.symm (h : G.IsLink e x y) : G.IsLink e y x :=
  G.isLink_symm h

lemma isLink_comm : G.IsLink e x y ↔ G.IsLink e y x :=
  ⟨IsLink.symm, IsLink.symm⟩

lemma IsLink.edge_mem (h : G.IsLink e x y) : e ∈ E(G) :=
  (edge_mem_iff_exists_isLink ..).2 ⟨x, y, h⟩

lemma IsLink.left_mem (h : G.IsLink e x y) : x ∈ V(G) :=
  G.left_mem_of_isLink h

lemma IsLink.right_mem (h : G.IsLink e x y) : y ∈ V(G) :=
  h.symm.left_mem

lemma exists_isLink_of_mem_edgeSet (h : e ∈ E(G)) : ∃ x y, G.IsLink e x y :=
  (edge_mem_iff_exists_isLink ..).1 h

lemma IsLink.left_eq_or_eq_of_isLink (h : G.IsLink e x y) (h' : G.IsLink e z w) : x = z ∨ x = w :=
  G.eq_or_eq_of_isLink_of_isLink h h'

lemma IsLink.left_eq_of_isLink_of_ne (h : G.IsLink e x y) (h' : G.IsLink e z w) (hzx : x ≠ z) : x = w :=
  (h.left_eq_or_eq_of_isLink h').elim (False.elim ∘ hzx) id

lemma IsLink.eq_of_isLink (h : G.IsLink e x y) (h' : G.IsLink e x z) : y = z := by
  obtain rfl | rfl := h.symm.left_eq_or_eq_of_isLink h'.symm; rfl
  obtain rfl | rfl := h'.symm.left_eq_or_eq_of_isLink h.symm <;> rfl

lemma IsLink.isLink_iff_eq (h : G.IsLink e x y) : G.IsLink e x z ↔ z = y :=
  ⟨fun h' ↦ h'.eq_of_isLink h, fun h' ↦ h' ▸ h⟩

lemma edgeSet_eq_setOf_exists_isLink : E(G) = {e | ∃ x y, G.IsLink e x y} :=
  Set.ext fun e ↦ G.edge_mem_iff_exists_isLink e

lemma not_isLink_of_not_mem_edgeSet (he : e ∉ E(G)) (x y : α) : ¬ G.IsLink e x y := by
  contrapose! he
  exact he.edge_mem

lemma IsLink.eq_and_eq_or_eq_and_eq_of_isLink {x' y' : α} (h : G.IsLink e x y) (h' : G.IsLink e x' y') :
    (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  obtain rfl | rfl := h.left_eq_or_eq_of_isLink h'
  · obtain rfl | rfl := h.symm.left_eq_or_eq_of_isLink h'
    · obtain rfl | rfl := h'.symm.left_eq_or_eq_of_isLink h <;> simp
    simp
  obtain rfl | rfl := h.symm.left_eq_or_eq_of_isLink h'
  · simp
  obtain rfl | rfl := h'.left_eq_or_eq_of_isLink h <;> simp

lemma IsLink.isLink_iff (h : G.IsLink e x y) {x' y' : α} :
    G.IsLink e x' y' ↔ (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  refine ⟨h.eq_and_eq_or_eq_and_eq_of_isLink, ?_⟩
  rintro (⟨rfl, rfl⟩ | ⟨rfl,rfl⟩)
  · assumption
  exact h.symm

lemma IsLink.isLink_iff_sym2_eq (h : G.IsLink e x y) {x' y' : α} :
    G.IsLink e x' y' ↔ s(x,y) = s(x',y') := by
  rw [h.isLink_iff, Sym2.eq_iff]

/-! ### Edge-vertex incidence -/

/-- `G.Inc e x` means that `x` is one of the ends of `e`. -/
def Inc (G : Graph α β) (e : β) (x : α) : Prop := ∃ y, G.IsLink e x y

@[simp]
lemma Inc.edge_mem (h : G.Inc e x) : e ∈ E(G) :=
  h.choose_spec.edge_mem

@[simp]
lemma Inc.vx_mem (h : G.Inc e x) : x ∈ V(G) :=
  h.choose_spec.left_mem

@[simp]
lemma IsLink.inc_left (h : G.IsLink e x y) : G.Inc e x :=
  ⟨y, h⟩

@[simp]
lemma IsLink.inc_right (h : G.IsLink e x y) : G.Inc e y :=
  ⟨x, h.symm⟩

lemma Inc.eq_or_eq_of_isLink (h : G.Inc e x) (h' : G.IsLink e y z) : x = y ∨ x = z :=
  h.choose_spec.left_eq_or_eq_of_isLink h'

lemma Inc.eq_of_isLink_of_ne_left (h : G.Inc e x) (h' : G.IsLink e y z) (hxy : x ≠ y) : x = z :=
  (h.eq_or_eq_of_isLink h').elim (False.elim ∘ hxy) id

/-- Given a proof that `e` is incident with `x`, noncomputably find the other end of `e`.
(If `e` is a loop, this is equal to `x` itself). -/
noncomputable def Inc.other (h : G.Inc e x) : α := h.choose

@[simp]
lemma Inc.isLink_other (h : G.Inc e x) : G.IsLink e x h.other :=
  h.choose_spec

@[simp]
lemma Inc.inc_other (h : G.Inc e x) : G.Inc e h.other :=
  h.isLink_other.inc_right

lemma Inc.eq_or_eq_or_eq_of_inc_of_inc (hx : G.Inc e x) (hy : G.Inc e y) (hz : G.Inc e z) :
    x = y ∨ x = z ∨ y = z := by
  by_contra! hcon
  obtain ⟨x', hx'⟩ := hx
  obtain rfl := hy.eq_of_isLink_of_ne_left hx' hcon.1.symm
  obtain rfl := hz.eq_of_isLink_of_ne_left hx' hcon.2.1.symm
  exact hcon.2.2 rfl

/-- The binary incidence predicate can be expressed in terms of the unary one. -/
lemma isLink_iff_inc : G.IsLink e x y ↔ G.Inc e x ∧ G.Inc e y ∧ ∀ z, G.Inc e z → z = x ∨ z = y := by
  refine ⟨fun h ↦ ⟨h.inc_left, h.inc_right, fun z h' ↦ h'.eq_or_eq_of_isLink h⟩, ?_⟩
  rintro ⟨⟨x', hx'⟩, ⟨y', hy'⟩, h⟩
  obtain rfl | rfl := h _ hx'.inc_right
  · obtain rfl | rfl := hx'.left_eq_or_eq_of_isLink hy'
    · assumption
    exact hy'.symm
  assumption

/-- `G.IsLoopAt e x` means that `e` is a loop edge at the vertex `x`. -/
def IsLoopAt (G : Graph α β) (e : β) (x : α) : Prop := G.IsLink e x x

@[simp]
lemma isLink_self_iff : G.IsLink e x x ↔ G.IsLoopAt e x := Iff.rfl

lemma IsLoopAt.isLink (h : G.IsLoopAt e x) : G.IsLink e x x := h

lemma IsLoopAt.inc (h : G.IsLoopAt e x) : G.Inc e x :=
  IsLink.inc_left h

lemma IsLoopAt.eq_of_inc (h : G.IsLoopAt e x) (h' : G.Inc e y) : x = y := by
  obtain rfl | rfl := h'.eq_or_eq_of_isLink h <;> rfl

lemma IsLoopAt.isLink_iff_eq (h : G.IsLoopAt e x) : G.IsLink e x y ↔ x = y :=
  ⟨h.eq_of_isLink, fun h' ↦ by rwa [← h']⟩

@[simp]
lemma IsLoopAt.edge_mem (h : G.IsLoopAt e x) : e ∈ E(G) :=
  h.inc.edge_mem

@[simp]
lemma IsLoopAt.vx_mem (h : G.IsLoopAt e x) : x ∈ V(G) :=
  h.inc.vx_mem

/-- `G.IsNonloopAt e x` means that `e` is an edge from `x` to some `y ≠ x`. -/
@[mk_iff]
structure IsNonloopAt (G : Graph α β) (e : β) (x : α) : Prop where
  inc : G.Inc e x
  exists_isLink_ne : ∃ y ≠ x, G.IsLink e x y

@[simp]
lemma IsNonloopAt.edge_mem (h : G.IsNonloopAt e x) : e ∈ E(G) :=
  h.inc.edge_mem

@[simp]
lemma IsNonloopAt.vx_mem (h : G.IsNonloopAt e x) : x ∈ V(G) :=
  h.inc.vx_mem

lemma IsLoopAt.not_isNonloop_at (h : G.IsLoopAt e x) (y : α) : ¬ G.IsNonloopAt e y := by
  intro h'
  obtain ⟨z, hyz, hy⟩ := h'.exists_isLink_ne
  rw [← h.eq_of_inc hy.inc_left, ← h.eq_of_inc hy.inc_right] at hyz
  exact hyz rfl

lemma IsNonloopAt.not_isLoopAt (h : G.IsNonloopAt e x) (y : α) : ¬ G.IsLoopAt e y :=
  fun h' ↦ h'.not_isNonloop_at x h

lemma Inc.isLoopAt_or_isNonloopAt (h : G.Inc e x) : G.IsLoopAt e x ∨ G.IsNonloopAt e x := by
  obtain ⟨y, hy⟩ := h
  obtain rfl | hne := eq_or_ne x y
  · exact .inl hy
  exact .inr ⟨hy.inc_left, y, hne.symm, hy⟩

lemma Inc.isLoopAt_or_isLink_ne (h : G.Inc e x) : G.IsLoopAt e x ∨ ∃ y ≠ x, G.IsLink e x y := by
  obtain ⟨y, hy⟩ := h
  obtain rfl | hne := eq_or_ne x y
  · exact .inl hy
  exact .inr ⟨y, hne.symm, hy⟩

lemma IsLink.isNonloopAt_iff_ne (h : G.IsLink e x y) : G.IsNonloopAt e x ↔ x ≠ y := by
  obtain rfl | hne := eq_or_ne x y
  · exact iff_of_false (IsLoopAt.not_isNonloop_at h x) <| by simp
  rw [isNonloopAt_iff]
  exact iff_of_true ⟨h.inc_left, ⟨y, hne.symm, h⟩⟩ hne

lemma IsLink.isNonloopAt_of_ne (h : G.IsLink e x y) (hxy : x ≠ y) : G.IsNonloopAt e x :=
  h.isNonloopAt_iff_ne.2 hxy

lemma IsLink.isNonloopAt_right_of_ne (h : G.IsLink e x y) (hxy : x ≠ y) : G.IsNonloopAt e y :=
  h.symm.isNonloopAt_iff_ne.2 hxy.symm

lemma exists_isLoopAt_or_isLink_of_mem_edgeSet (h : e ∈ E(G)) :
    (∃ x, G.IsLoopAt e x) ∨ ∃ x y, G.IsLink e x y ∧ x ≠ y := by
  obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet h
  obtain rfl | hne := eq_or_ne x y
  · exact .inl ⟨x, h⟩
  exact .inr ⟨x, y, h, hne⟩

/-! ### Adjacency -/

/-- `G.Adj x y` means that `G` has an edge from `x` to `y`. -/
def Adj (G : Graph α β) (x y : α) : Prop := ∃ e, G.IsLink e x y

lemma Adj.symm (h : G.Adj x y) : G.Adj y x :=
  ⟨_, h.choose_spec.symm⟩

lemma adj_comm : G.Adj x y ↔ G.Adj y x :=
  ⟨Adj.symm, Adj.symm⟩

@[simp]
lemma Adj.mem_left (h : G.Adj x y) : x ∈ V(G) :=
  h.choose_spec.left_mem

@[simp]
lemma Adj.mem_right (h : G.Adj x y) : y ∈ V(G) :=
  h.symm.mem_left

lemma IsLink.adj (h : G.IsLink e x y) : G.Adj x y :=
  ⟨e, h⟩



/-! ### Extensionality -/

/-- A constructor for `Graph` in which the edge set is inferred from the incidence predicate
rather than supplied explicitly. -/
@[simps]
protected def mk' (V : Set α) (IsLink : β → α → α → Prop)
    (isLink_symm : ∀ ⦃e x y⦄, IsLink e x y → IsLink e y x)
    (eq_or_eq_of_isLink_of_isLink : ∀ ⦃e x y v w⦄, IsLink e x y → IsLink e v w → x = v ∨ x = w)
    (left_mem_of_isLink : ∀ ⦃e x y⦄, IsLink e x y → x ∈ V) : Graph α β where
  vertexSet := V
  edgeSet := {e | ∃ x y, IsLink e x y}
  IsLink := IsLink
  isLink_symm := isLink_symm
  eq_or_eq_of_isLink_of_isLink := eq_or_eq_of_isLink_of_isLink
  edge_mem_iff_exists_isLink _ := Iff.rfl
  left_mem_of_isLink := left_mem_of_isLink

@[simp]
lemma mk'_eq_self (G : Graph α β) : Graph.mk' V(G) G.IsLink (fun _ _ _ ↦ IsLink.symm)
  (fun _ _ _ _ _ h h' ↦ h.left_eq_or_eq_of_isLink h') (fun _ _ _ ↦ IsLink.left_mem) = G := by
  have h := G.edgeSet_eq_setOf_exists_isLink
  cases G with | mk V E IsLink _ _ _ => simpa [Graph.mk'] using h.symm

/-- Two graphs with the same vertex set and binary incidences are equal. -/
@[ext]
protected lemma ext {G₁ G₂ : Graph α β} (hV : V(G₁) = V(G₂))
    (h : ∀ e x y, G₁.IsLink e x y ↔ G₂.IsLink e x y) : G₁ = G₂ := by
  rw [← G₁.mk'_eq_self, ← G₂.mk'_eq_self]
  simp_rw [hV]
  convert rfl using 2
  ext
  rw [h]

/-- Two graphs with the same vertex set and unary incidences are equal. -/
lemma ext_inc {G₁ G₂ : Graph α β} (hV : V(G₁) = V(G₂)) (h : ∀ e x, G₁.Inc e x ↔ G₂.Inc e x) :
    G₁ = G₂ :=
  Graph.ext hV fun _ _ _ ↦ by simp_rw [isLink_iff_inc, h]

@[simps]
def copy (G : Graph α β) {V : Set α} {E : Set β} {IsLink : β → α → α → Prop} (hV : V(G) = V)
    (hE : E(G) = E) (h_isLink : ∀ e x y, G.IsLink e x y ↔ IsLink e x y) : Graph α β where
  vertexSet := V
  edgeSet := E
  IsLink := IsLink
  isLink_symm := by
    simp_rw [← h_isLink]
    exact G.isLink_symm
  eq_or_eq_of_isLink_of_isLink := by
    simp_rw [← h_isLink]
    exact G.eq_or_eq_of_isLink_of_isLink
  edge_mem_iff_exists_isLink := by
    simp_rw [← h_isLink, ← hE]
    exact G.edge_mem_iff_exists_isLink
  left_mem_of_isLink := by
    simp_rw [← h_isLink, ← hV]
    exact G.left_mem_of_isLink

lemma copy_eq_self (G : Graph α β) {V : Set α} {E : Set β} {IsLink : β → α → α → Prop}
    (hV : V(G) = V) (hE : E(G) = E) (h_isLink : ∀ e x y, G.IsLink e x y ↔ IsLink e x y) :
    G.copy hV hE h_isLink = G := by
  ext <;> simp_all

end Graph
