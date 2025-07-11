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
with an unordered pair `s(x,y)` of vertices called the *ends* of `e`.
The pair of `e` and `s(x,y)` is called a *link*.
The vertices `x` and `y` may be equal, in which case `e` is a *loop*.
There may be more than one edge with the same ends.

If a multigraph has no loops and has at most one edge for every given ends, it is called *simple*,
and these objects are also formalized as `SimpleGraph`.

This module defines `Graph α β` for a vertex type `α` and an edge type `β`,
and gives basic API for incidence, adjacency and extensionality.
The design broadly follows [Chou1994].

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
This mimics the 'embedded set' design used in `Matroid`, which seems to be more convenient for
formalizing real-world proofs in combinatorics.

A specific advantage is that this allows subgraphs of `G : Graph α β` to also exist on
an equal footing with `G` as terms in `Graph α β`,
and so there is no need for a `Graph.subgraph` type and all the associated
definitions and canonical coercion maps. The same will go for minors and the various other
partial orders on multigraphs.

The main tradeoff is that parts of the API will need to care about whether a term
`x : α` or `e : β` is a 'real' vertex or edge of the graph, rather than something outside
the vertex or edge set. This is an issue, but is likely amenable to automation.

## Notation

Reflecting written mathematics, we use the compact notations `V(G)` and `E(G)` to
refer to the `vertexSet` and `edgeSet` of `G : Graph α β`.
If `G.IsLink e x y` then we refer to `e` as `edge` and `x` and `y` as `left` and `right` in names.
-/

variable {α β : Type*} {x y z u v w : α} {e f : β}

open Set

/-- A multigraph with vertices of type `α` and edges of type `β`,
as described by vertex and edge sets `vertexSet : Set α` and `edgeSet : Set β`,
and a predicate `IsLink` describing whether an edge `e : β` has vertices `x y : α` as its ends.

The `edgeSet` structure field can be inferred from `IsLink`
via `edge_mem_iff_exists_isLink` (and this structure provides default values
for `edgeSet` and `edge_mem_iff_exists_isLink` that use `IsLink`).
While the field is not strictly necessary, when defining a graph we often
immediately know what the edge set should be,
and furthermore having `edgeSet` separate can be convenient for
definitional equality reasons.
-/
structure Graph (α β : Type*) where
  /-- The vertex relation showing which vertex labels represents a same vertex. -/
  dup : α → α → Prop
  /-- The vertex set. -/
  vertexSet : Set α := {x | dup x x}
  /-- The vertex relation is reflexive for all vertices in the vertex set. -/
  dup_refl_iff : ∀ x, x ∈ vertexSet ↔ dup x x := by exact fun x ↦ Iff.rfl
  /-- The vertex relation is symmetric. -/
  dup_symm x y : dup x y → dup y x
  /-- The vertex relation is transitive. -/
  dup_trans x y z : dup x y → dup y z → dup x z
  /-- The binary incidence predicate, stating that `x` and `y` are the ends of an edge `e`.
  If `G.IsLink e x y` then we refer to `e` as `edge` and `x` and `y` as `left` and `right`. -/
  IsLink : β → α → α → Prop
  /-- The edge set. -/
  edgeSet : Set β := {e | ∃ x y, IsLink e x y}
  /-- If `e` goes from `x` to `y`, it goes from `y` to `x`. -/
  isLink_symm : ∀ ⦃e⦄, e ∈ edgeSet → (Symmetric <| IsLink e)
  /-- An edge is incident with at most one pair of vertices. -/
  dup_or_dup_of_isLink_of_isLink : ∀ ⦃e x y v w⦄, IsLink e x y → IsLink e v w → dup x v ∨ dup x w
  /-- An edge `e` is incident to something if and only if `e` is in the edge set. -/
  edge_mem_iff_exists_isLink : ∀ e, e ∈ edgeSet ↔ ∃ x y, IsLink e x y := by exact fun _ ↦ Iff.rfl
  /-- If some edge `e` is incident to `x`, then `x ∈ V`. -/
  left_mem_of_isLink : ∀ ⦃e x y⦄, IsLink e x y → x ∈ vertexSet
  /-- If `x` and `y` represent the same vertex, it has the same incidence relation. -/
  isLink_of_dup : ∀ ⦃e x y z⦄, dup x y → IsLink e x z → IsLink e y z

namespace Graph

variable {G : Graph α β}

/-- `V(G)` denotes the `vertexSet` of a graph `G`. -/
scoped notation "V(" G ")" => Graph.vertexSet G

/-- `E(G)` denotes the `edgeSet` of a graph `G`. -/
scoped notation "E(" G ")" => Graph.edgeSet G

/-! ### Vertex relation -/

lemma dup_of_mem_vertexSet (hx : x ∈ V(G)) : G.dup x x :=
  G.dup_refl_iff x |>.mp hx

protected lemma dup.symm (h : G.dup x y) : G.dup y x := G.dup_symm _ _ h

instance : IsSymm α (G.dup) where
  symm := G.dup_symm

lemma dup_comm : G.dup x y ↔ G.dup y x := ⟨.symm, .symm⟩

protected lemma dup.trans (h : G.dup x y) (h' : G.dup y z) : G.dup x z :=
  G.dup_trans _ _ _ h h'

instance : IsTrans α (G.dup) where
  trans := G.dup_trans

@[simp]
lemma dup.dup_left {x y z : α} (h : G.dup x y) : G.dup x z ↔ G.dup y z :=
  ⟨h.symm.trans, h.trans⟩

@[simp]
lemma dup.dup_right {x y z : α} (h : G.dup x y) : G.dup z x ↔ G.dup z y :=
  ⟨(·.trans h), (·.trans h.symm)⟩

lemma dup.left_mem (hx : G.dup x y) : x ∈ V(G) := by
  rw [G.dup_refl_iff]
  exact hx.trans hx.symm

lemma dup.right_mem (hy : G.dup x y) : y ∈ V(G) := by
  rw [G.dup_refl_iff]
  exact hy.symm.trans hy

lemma not_dup_symm (h : ¬ G.dup x y) : ¬ G.dup y x := fun hyx ↦ h hyx.symm

lemma not_dup_comm : ¬ G.dup x y ↔ ¬ G.dup y x := ⟨not_dup_symm, not_dup_symm⟩

@[simp] lemma not_dup_of_not_mem_left (h : ¬ x ∈ V(G)) : ¬ G.dup x y := fun h' ↦ h h'.left_mem
@[simp] lemma not_dup_of_not_mem_right (h : ¬ y ∈ V(G)) : ¬ G.dup x y := fun h' ↦ h h'.right_mem

/-! ### Edge-vertex-vertex incidence -/

lemma IsLink.edge_mem (h : G.IsLink e x y) : e ∈ E(G) :=
  (edge_mem_iff_exists_isLink ..).2 ⟨x, y, h⟩

protected lemma IsLink.symm (h : G.IsLink e x y) : G.IsLink e y x :=
  G.isLink_symm h.edge_mem h

lemma IsLink.dup_left (h : G.IsLink e x y) (hrel : G.dup x z) : G.IsLink e z y :=
  G.isLink_of_dup hrel h

lemma IsLink.dup_right (h : G.IsLink e x y) (hrel : G.dup y z) : G.IsLink e x z :=
  h.symm.dup_left hrel |>.symm

@[simp high]
lemma dup.isLink_left {x y z : α} (h : G.dup x y) : G.IsLink e x z ↔ G.IsLink e y z :=
  ⟨(·.dup_left h), (·.dup_left h.symm)⟩

@[simp high]
lemma dup.isLink_right {x y z : α} (h : G.dup x y) : G.IsLink e z x ↔ G.IsLink e z y :=
  ⟨(·.dup_right h), (·.dup_right h.symm)⟩

lemma IsLink.left_mem (h : G.IsLink e x y) : x ∈ V(G) :=
  G.left_mem_of_isLink h

lemma IsLink.right_mem (h : G.IsLink e x y) : y ∈ V(G) :=
  h.symm.left_mem

lemma isLink_comm : G.IsLink e x y ↔ G.IsLink e y x :=
  ⟨.symm, .symm⟩

lemma exists_isLink_of_mem_edgeSet (h : e ∈ E(G)) : ∃ x y, G.IsLink e x y :=
  (edge_mem_iff_exists_isLink ..).1 h

lemma edgeSet_eq_setOf_exists_isLink : E(G) = {e | ∃ x y, G.IsLink e x y} :=
  Set.ext G.edge_mem_iff_exists_isLink

lemma IsLink.left_dup_or_dup (h : G.IsLink e x y) (h' : G.IsLink e z w) :
    G.dup x z ∨ G.dup x w := G.dup_or_dup_of_isLink_of_isLink h h'

lemma IsLink.right_dup_or_dup (h : G.IsLink e x y) (h' : G.IsLink e z w) :
    G.dup y z ∨ G.dup y w := h.symm.left_dup_or_dup h'

lemma IsLink.left_dup_of_right_ndup (h : G.IsLink e x y) (h' : G.IsLink e z w)
    (hzx : ¬ G.dup x z) : G.dup x w :=
  (h.left_dup_or_dup h').elim (False.elim ∘ hzx) id

lemma IsLink.right_unique (h : G.IsLink e x y) (h' : G.IsLink e x z) : G.dup y z := by
  obtain hyz | hyx := h.right_dup_or_dup h'.symm
  · exact hyz
  obtain hzy | hzx := h'.right_dup_or_dup h.symm
  · exact hzy.symm
  exact hyx.trans hzx.symm

lemma IsLink.left_unique (h : G.IsLink e x z) (h' : G.IsLink e y z) : G.dup x y :=
  h.symm.right_unique h'.symm

lemma IsLink.dup_and_dup_or_dup_and_dup {x' y' : α} (h : G.IsLink e x y) (h' : G.IsLink e x' y') :
    G.dup x x' ∧ G.dup y y' ∨ G.dup x y' ∧ G.dup y x' := by
  obtain hx | hx := h.left_dup_or_dup h'
  · simp [h.right_unique <| h'.dup_left hx.symm, hx]
  simp [(h'.symm.right_unique <| h.dup_left hx).symm, hx]

lemma IsLink.isLink_iff (h : G.IsLink e x y) {x' y' : α} :
    G.IsLink e x' y' ↔ G.dup x x' ∧ G.dup y y' ∨ G.dup x y' ∧ G.dup y x' := by
  refine ⟨h.dup_and_dup_or_dup_and_dup, ?_⟩
  rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
  · rwa [hx.isLink_left, hy.isLink_right] at h
  rwa [isLink_comm, hy.isLink_left, hx.isLink_right] at h

-- lemma IsLink.isLink_iff_sym2_eq (h : G.IsLink e x y) {x' y' : α} :
--     G.IsLink e x' y' ↔ s(x,y) = s(x',y') := by
--   rw [h.isLink_iff, Sym2.eq_iff]

/-! ### Edge-vertex incidence -/

/-- The unary incidence predicate of `G`. `G.Inc e x` means that the vertex `x`
is one or both of the ends of the edge `e`.
In the `Inc` namespace, we use `edge` and `vertex` to refer to `e` and `x`. -/
def Inc (G : Graph α β) (e : β) (x : α) : Prop := ∃ y, G.IsLink e x y

-- Cannot be @[simp] because `x` can not be inferred by `simp`.
lemma Inc.edge_mem (h : G.Inc e x) : e ∈ E(G) :=
  h.choose_spec.edge_mem

-- Cannot be @[simp] because `e` can not be inferred by `simp`.
lemma Inc.vertex_mem (h : G.Inc e x) : x ∈ V(G) :=
  h.choose_spec.left_mem

-- Cannot be @[simp] because `y` can not be inferred by `simp`.
lemma IsLink.inc_left (h : G.IsLink e x y) : G.Inc e x :=
  ⟨y, h⟩

-- Cannot be @[simp] because `x` can not be inferred by `simp`.
lemma IsLink.inc_right (h : G.IsLink e x y) : G.Inc e y :=
  ⟨x, h.symm⟩

@[simp]
lemma dup.inc (h : G.dup x y) : G.Inc e x ↔ G.Inc e y := by
  unfold Inc
  simp_rw [h.isLink_left]

lemma Inc.dup (hi : G.Inc e x) (h : G.dup x y) : G.Inc e y := by
  obtain ⟨z, hz⟩ := hi
  use z, hz.dup_left h

lemma Inc.dup_or_dup_of_isLink (h : G.Inc e x) (h' : G.IsLink e y z) : G.dup x y ∨ G.dup x z :=
  h.choose_spec.left_dup_or_dup h'

lemma Inc.dup_of_isLink_of_ndup_left (h : G.Inc e x) (h' : G.IsLink e y z) (hxy : ¬ G.dup x y) :
    G.dup x z := (h.dup_or_dup_of_isLink h').elim (False.elim ∘ hxy) id

lemma IsLink.isLink_iff_dup (h : G.IsLink e x y) : G.IsLink e x z ↔ G.dup z y :=
  ⟨fun h' ↦ h'.right_unique h, fun h' ↦ h'.isLink_right.mpr h⟩

/-- The binary incidence predicate can be expressed in terms of the unary one. -/
lemma isLink_iff_inc :
    G.IsLink e x y ↔ G.Inc e x ∧ G.Inc e y ∧ ∀ z, G.Inc e z → G.dup z x ∨ G.dup z y := by
  refine ⟨fun h ↦ ⟨h.inc_left, h.inc_right, fun z h' ↦ h'.dup_or_dup_of_isLink h⟩, ?_⟩
  rintro ⟨⟨x', hx'⟩, ⟨y', hy'⟩, h⟩
  obtain hx | hy := h _ hx'.inc_right
  · obtain hy | hxy' := hx'.left_dup_or_dup hy'
    · rwa [hy.symm.isLink_right, ← hx.isLink_right]
    rwa [isLink_comm, hxy'.isLink_right]
  rwa [← hy.isLink_right]

/-- Given a proof that the edge `e` is incident with the vertex `x` in `G`,
noncomputably find the other end of `e`. (If `e` is a loop, this is equal to `x` itself). -/
protected noncomputable def Inc.other (h : G.Inc e x) : α := h.choose

@[simp]
lemma Inc.isLink_other (h : G.Inc e x) : G.IsLink e x h.other :=
  h.choose_spec

@[simp]
lemma Inc.inc_other (h : G.Inc e x) : G.Inc e h.other :=
  h.isLink_other.inc_right

lemma Inc.dup_or_dup_or_dup (hx : G.Inc e x) (hy : G.Inc e y) (hz : G.Inc e z) :
    G.dup x y ∨ G.dup x z ∨ G.dup y z := by
  by_contra! hcon
  obtain ⟨x', hx'⟩ := hx
  obtain hy := hy.dup_of_isLink_of_ndup_left hx' <| not_dup_symm hcon.1
  obtain hz := hz.dup_of_isLink_of_ndup_left hx' <| not_dup_symm hcon.2.1
  exact hcon.2.2 <| hy.trans hz.symm

/-- `G.IsLoopAt e x` means that both ends of the edge `e` are equal to the vertex `x`. -/
def IsLoopAt (G : Graph α β) (e : β) (x : α) : Prop := G.IsLink e x x

@[simp]
lemma isLink_self_iff : G.IsLink e x x ↔ G.IsLoopAt e x := Iff.rfl

lemma IsLoopAt.inc (h : G.IsLoopAt e x) : G.Inc e x :=
  IsLink.inc_left h

lemma IsLoopAt.dup_of_inc (h : G.IsLoopAt e x) (h' : G.Inc e y) : G.dup x y := by
  obtain hy | hy := h'.dup_or_dup_of_isLink h <;> exact hy.symm

lemma IsLoopAt.dup (h : G.IsLoopAt e x) (h' : G.dup x y) : G.IsLoopAt e y :=
  h.dup_left h' |>.dup_right h'

lemma dup.isLoopAt (h : G.dup x y) : G.IsLoopAt e x ↔ G.IsLoopAt e y :=
  ⟨fun h' ↦ h'.dup h, fun h' ↦ h'.dup h.symm⟩

-- Cannot be @[simp] because `x` can not be inferred by `simp`.
lemma IsLoopAt.edge_mem (h : G.IsLoopAt e x) : e ∈ E(G) :=
  h.inc.edge_mem

-- Cannot be @[simp] because `e` can not be inferred by `simp`.
lemma IsLoopAt.vertex_mem (h : G.IsLoopAt e x) : x ∈ V(G) :=
  h.inc.vertex_mem

/-- `G.IsNonloopAt e x` means that the vertex `x` is one but not both of the ends of the edge =`e`,
or equivalently that `e` is incident with `x` but not a loop at `x` -
see `Graph.isNonloopAt_iff_inc_not_isLoopAt`. -/
def IsNonloopAt (G : Graph α β) (e : β) (x : α) : Prop := ∃ y, ¬ G.dup x y ∧ G.IsLink e x y

lemma IsNonloopAt.inc (h : G.IsNonloopAt e x) : G.Inc e x :=
  h.choose_spec.2.inc_left

-- Cannot be @[simp] because `x` can not be inferred by `simp`.
lemma IsNonloopAt.edge_mem (h : G.IsNonloopAt e x) : e ∈ E(G) :=
  h.inc.edge_mem

-- Cannot be @[simp] because `e` can not be inferred by `simp`.
lemma IsNonloopAt.vertex_mem (h : G.IsNonloopAt e x) : x ∈ V(G) :=
  h.inc.vertex_mem

lemma IsNonloopAt.dup (h : G.IsNonloopAt e x) (h' : G.dup x y) : G.IsNonloopAt e y := by
  obtain ⟨z, hxz, hy⟩ := h
  use z, fun hyz => hxz <| h'.trans hyz, hy.dup_left h'

lemma dup.isNonloopAt (h : G.dup x y) : G.IsNonloopAt e x ↔ G.IsNonloopAt e y :=
  ⟨(·.dup h), (·.dup h.symm)⟩

lemma IsLoopAt.not_isNonloopAt (h : G.IsLoopAt e x) (y : α) : ¬ G.IsNonloopAt e y := by
  rintro ⟨z, hyz, hy⟩
  refine hyz ?_
  rw [← (h.dup_of_inc hy.inc_left).dup_left]
  exact h.dup_of_inc hy.inc_right

lemma IsNonloopAt.not_isLoopAt (h : G.IsNonloopAt e x) (y : α) : ¬ G.IsLoopAt e y :=
  fun h' ↦ h'.not_isNonloopAt x h

lemma isNonloopAt_iff_inc_not_isLoopAt : G.IsNonloopAt e x ↔ G.Inc e x ∧ ¬ G.IsLoopAt e x :=
  ⟨fun h ↦ ⟨h.inc, h.not_isLoopAt _⟩,
    fun ⟨⟨y, hy⟩, hn⟩ ↦ ⟨y, mt (fun h ↦ hy.dup_right h.symm) hn, hy⟩⟩

lemma isLoopAt_iff_inc_not_isNonloopAt : G.IsLoopAt e x ↔ G.Inc e x ∧ ¬ G.IsNonloopAt e x := by
  simp +contextual [isNonloopAt_iff_inc_not_isLoopAt, iff_def, IsLoopAt.inc]

lemma Inc.isLoopAt_or_isNonloopAt (h : G.Inc e x) : G.IsLoopAt e x ∨ G.IsNonloopAt e x := by
  simp [isNonloopAt_iff_inc_not_isLoopAt, h, em]

/-! ### Adjacency -/

/-- `G.Adj x y` means that `G` has an edge whose ends are the vertices `x` and `y`. -/
def Adj (G : Graph α β) (x y : α) : Prop := ∃ e, G.IsLink e x y

protected lemma Adj.symm (h : G.Adj x y) : G.Adj y x :=
  ⟨_, h.choose_spec.symm⟩

lemma adj_comm (x y) : G.Adj x y ↔ G.Adj y x :=
  ⟨.symm, .symm⟩

-- Cannot be @[simp] because `y` can not be inferred by `simp`.
lemma Adj.left_mem (h : G.Adj x y) : x ∈ V(G) :=
  h.choose_spec.left_mem

-- Cannot be @[simp] because `x` can not be inferred by `simp`.
lemma Adj.right_mem (h : G.Adj x y) : y ∈ V(G) :=
  h.symm.left_mem

lemma IsLink.adj (h : G.IsLink e x y) : G.Adj x y :=
  ⟨e, h⟩

lemma Adj.dup (h : G.Adj x y) (h' : G.dup x z) : G.Adj z y := by
  obtain ⟨e, he⟩ := h
  use e, he.dup_left h'

lemma dup.adj (h : G.dup x y) : G.Adj x z ↔ G.Adj y z :=
  ⟨(·.dup h), (·.dup h.symm)⟩

/-! ### Extensionality -/

def mk_of_unique (V : Set α) (IsLink : β → α → α → Prop) (edgeSet : Set β)
(isLink_symm : ∀ ⦃e : β⦄, e ∈ edgeSet → Symmetric (IsLink e))
(dup_or_dup_of_isLink_of_isLink : ∀ ⦃e x y v w⦄, IsLink e x y → IsLink e v w → x = v ∨ x = w)
(edge_mem_iff_exists_isLink : ∀ e, e ∈ edgeSet ↔ ∃ x y, IsLink e x y)
(left_mem_of_isLink : ∀ ⦃e x y⦄, IsLink e x y → x ∈ V) : Graph α β where
  vertexSet := V
  edgeSet := edgeSet
  edge_mem_iff_exists_isLink := edge_mem_iff_exists_isLink
  dup x y := x = y ∧ x ∈ V
  dup_refl_iff x := by simp
  dup_symm x y := by
    rintro ⟨rfl, hx⟩
    exact ⟨rfl, hx⟩
  dup_trans x y z := by
    rintro ⟨rfl, hx⟩ ⟨rfl, -⟩
    exact ⟨rfl, hx⟩
  IsLink := IsLink
  isLink_symm := isLink_symm
  dup_or_dup_of_isLink_of_isLink e x y v w hl hl' := by
    obtain rfl | rfl := dup_or_dup_of_isLink_of_isLink hl hl'
    · exact Or.inl ⟨rfl, left_mem_of_isLink hl⟩
    exact Or.inr ⟨rfl, left_mem_of_isLink hl⟩
  left_mem_of_isLink e x y hl := left_mem_of_isLink hl
  isLink_of_dup e x y z hxy hl := by
    obtain ⟨rfl, hx⟩ := hxy
    exact hl

def mk_of_unique' (V : Set α) (IsLink : β → α → α → Prop)
(isLink_symm : ∀ ⦃e x y⦄, IsLink e x y → IsLink e y x)
(dup_or_dup_of_isLink_of_isLink : ∀ ⦃e x y v w⦄, IsLink e x y → IsLink e v w → x = v ∨ x = w)
(left_mem_of_isLink : ∀ ⦃e x y⦄, IsLink e x y → x ∈ V) : Graph α β where
  vertexSet := V
  dup x y := x = y ∧ x ∈ V
  dup_refl_iff x := by simp
  dup_symm x y := by
    rintro ⟨rfl, hx⟩
    exact ⟨rfl, hx⟩
  dup_trans x y z := by
    rintro ⟨rfl, hx⟩ ⟨rfl, -⟩
    exact ⟨rfl, hx⟩
  IsLink := IsLink
  isLink_symm e he x y hl := isLink_symm hl
  dup_or_dup_of_isLink_of_isLink e x y v w hl hl' := by
    obtain rfl | rfl := dup_or_dup_of_isLink_of_isLink hl hl'
    · exact Or.inl ⟨rfl, left_mem_of_isLink hl⟩
    exact Or.inr ⟨rfl, left_mem_of_isLink hl⟩
  left_mem_of_isLink e x y hl := left_mem_of_isLink hl
  isLink_of_dup e x y z hxy hl := by
    obtain ⟨rfl, hx⟩ := hxy
    exact hl

/-- `edgeSet` can be determined using `IsLink`, so the graph constructed from `G.vertexSet` and
`G.IsLink` using any value for `edgeSet` is equal to `G` itself. -/
@[simp]
lemma mk_eq_self (G : Graph α β) {E : Set β} (hE : ∀ e, e ∈ E ↔ ∃ x y, G.IsLink e x y) :
    Graph.mk G.dup V(G) G.dup_refl_iff G.dup_symm G.dup_trans G.IsLink E
    (by simpa [show E = E(G) by simp [Set.ext_iff, hE, G.edge_mem_iff_exists_isLink]]
      using G.isLink_symm)
    (fun _ _ _ _ _ h h' ↦ h.left_dup_or_dup h') hE
    (fun _ _ _ ↦ IsLink.left_mem) G.isLink_of_dup = G := by
  obtain rfl : E = E(G) := by simp [Set.ext_iff, hE, G.edge_mem_iff_exists_isLink]
  cases G with | _ _ _ _ _ _ h _ => simp

/-- Two graphs with the same vertex set and binary incidences are equal.
(We use this as the default extensionality lemma rather than adding `@[ext]`
to the definition of `Graph`, so it doesn't require equality of the edge sets.) -/
@[ext]
protected lemma ext {G₁ G₂ : Graph α β} (hV : G₁.dup = G₂.dup)
    (h : ∀ e x y, G₁.IsLink e x y ↔ G₂.IsLink e x y) : G₁ = G₂ := by
  rw [← G₁.mk_eq_self G₁.edge_mem_iff_exists_isLink, ← G₂.mk_eq_self G₂.edge_mem_iff_exists_isLink]
  convert rfl using 2
  · exact hV.symm
  · ext x
    simp [dup_refl_iff, hV]
  · simp [funext_iff, h]
  simp [edgeSet_eq_setOf_exists_isLink, h]

/-- Two graphs with the same vertex set and unary incidences are equal. -/
lemma ext_inc {G₁ G₂ : Graph α β} (hV : G₁.dup = G₂.dup) (h : ∀ e x, G₁.Inc e x ↔ G₂.Inc e x) :
    G₁ = G₂ :=
  Graph.ext hV fun _ _ _ ↦ by simp_rw [isLink_iff_inc, h, hV]

end Graph
