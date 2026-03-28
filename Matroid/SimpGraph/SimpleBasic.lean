/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Jun Kwon
-/
module

public import Mathlib.Data.Rel
public import Mathlib.Data.Sym.Sym2

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
* `G.incidenceSet x` is the set of edges incident to `x`.
* `G.loopSet x` is the set of loops with both ends equal to `x`.
* `G.copy` creates a definitional copy of a graph with propositionally equal data.
* `G.Compatible H` means that `G` and `H` agree on the incidence relation for their shared edges.
* `Graph.noEdge V` is the graph with vertex set `V` and no edges.
* `Graph.bouquet v E` is the graph with vertex set `{v}` and edge set `E`,
  where every edge is a loop at `v`.
* `Graph.banana u v E` is the graph with vertex set `{u, v}` and edge set `E`,
  where every edge connects `u` and `v`.

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

@[expose] public section

variable {α β : Type*} {u u' v v' w w' : α} {a b c d a' b' c' d' : β} {e f : Sym2 β}

open Set Sym2

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
  /-- The relation pairing two half-edges. -/
  IsTwin : β → β → Prop
  /-- The relation is symmetric. -/
  IsTwin_symm : Symmetric IsTwin
  /-- The relation is irreflexive. -/
  IsTwin_irrefl : Std.Irrefl IsTwin
  /-- The relation is unique. -/
  IsTwin_unique : ∀ ⦃a b c : β⦄, IsTwin a b → IsTwin a c → b = c
  /-- halfedge-vertex incidence -/
  IsBase : β → α → Prop
  /-- A half-edge is based on at most one vertex. -/
  IsBase_unique : ∀ ⦃a x y⦄, IsBase a x → IsBase a y → x = y
  /-- A half-edge is based on a vertex must be paired with another half-edge. -/
  exists_isTwin_iff_exists_isBase : ∀ ⦃a⦄, (∃ x, IsBase a x) ↔ ∃ b, IsTwin a b
  /-- The vertex set. -/
  vertexSet : Set α
  /-- Vertex set contains all base points of half-edges. -/
  mem_vertexSet_of_isBase : ∀ ⦃a x⦄, IsBase a x → x ∈ vertexSet

namespace Graph

variable {G G₁ G₂ H : Graph α β}

/-- `V(G)` denotes the `vertexSet` of a graph `G`. -/
scoped notation "V(" G ")" => Graph.vertexSet G

instance : Std.Symm G.IsTwin := ⟨G.IsTwin_symm⟩
instance : Std.Irrefl G.IsTwin := G.IsTwin_irrefl

@[symm, grind →] lemma IsTwin.symm (h : G.IsTwin a b) : G.IsTwin b a := G.IsTwin_symm h
@[grind .] lemma IsTwin.irrefl : ¬ G.IsTwin a a := G.IsTwin_irrefl.irrefl a
@[grind .] lemma IsTwin.unique (h : G.IsTwin a b) (h' : G.IsTwin a c) : b = c :=
  G.IsTwin_unique h h'

@[grind →] lemma IsBase.vertex_mem (h : G.IsBase a v) : v ∈ V(G) := G.mem_vertexSet_of_isBase h
@[grind .] lemma IsBase.unique (h : G.IsBase a u) (h' : G.IsBase a v) : u = v :=
  G.IsBase_unique h h'

def halfEdgeSet (G : Graph α β) : Set β := SetRel.dom {(a, b) | G.IsTwin a b}
scoped notation "H(" G ")" => Graph.halfEdgeSet G

@[simp] lemma mem_halfEdgeSet_iff : a ∈ H(G) ↔ ∃ b, G.IsTwin a b := by simp [halfEdgeSet]

def edgeSet (G : Graph α β) : Set (Sym2 β) := {e | ∃ a b, G.IsTwin a b ∧ e = s(a, b)}
scoped notation "E(" G ")" => Graph.edgeSet G

@[simp] lemma mem_edgeSet_iff : e ∈ E(G) ↔ ∃ a b, G.IsTwin a b ∧ e = s(a, b) := by simp [edgeSet]

@[simp] lemma mk_mem_edgeSet_iff : s(a, b) ∈ E(G) ↔ G.IsTwin a b := by
  simp only [mem_edgeSet_iff, Sym2.eq, rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
  refine ⟨?_, fun h ↦ ⟨a, b, h, by tauto⟩⟩
  rintro ⟨c, d, hcd, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;> grind

/-! ### vertex-halfedge-halfedge-vertex incidence -/

@[mk_iff]
structure IsStep (G : Graph α β) (u : α) (a b : β) (v : α) : Prop where
  isTwin : G.IsTwin a b
  isBase_left : G.IsBase a u
  isBase_right : G.IsBase b v

@[symm, grind →]
lemma IsStep.symm (h : G.IsStep u a b v) : G.IsStep v b a u where
  isTwin := symm_of _ h.isTwin
  isBase_left := h.isBase_right
  isBase_right := h.isBase_left

lemma IsStep.comm : G.IsStep u a b v ↔ G.IsStep v b a u := ⟨.symm, .symm⟩

@[grind →] lemma IsStep.left_mem (h : G.IsStep u a b v) : u ∈ V(G) := h.isBase_left.vertex_mem
@[grind →] lemma IsStep.right_mem (h : G.IsStep u a b v) : v ∈ V(G) := h.isBase_right.vertex_mem
@[grind →] lemma IsStep.left_halfEdge_mem (h : G.IsStep u a b v) : a ∈ H(G) := ⟨b, h.isTwin⟩
@[grind →] lemma IsStep.right_halfEdge_mem (h : G.IsStep u a b v) : b ∈ H(G) := ⟨a, h.isTwin.symm⟩

@[grind .]
lemma IsStep.isStep_iff (h : G.IsStep u a b v) :
    G.IsStep u' a b' v' ↔ u = u' ∧ b = b' ∧ v = v' := by
  refine ⟨fun h' ↦ ?_, ?_⟩
  · obtain rfl := h.isTwin.unique h'.isTwin
    obtain rfl := h.isBase_left.unique h'.isBase_left
    obtain rfl := h.isBase_right.unique h'.isBase_right
    tauto
  rintro ⟨rfl, rfl, rfl⟩
  exact h

lemma IsTwin.exists_isStep (h : G.IsTwin a b) : ∃ u v, G.IsStep u a b v := by
  obtain ⟨u, hua⟩ := G.exists_isTwin_iff_exists_isBase (a := a) |>.mpr ⟨b, h⟩
  obtain ⟨v, hvb⟩ := G.exists_isTwin_iff_exists_isBase (a := b) |>.mpr ⟨a, h.symm⟩
  use u, v, h

lemma IsStep.edge_mem (h : G.IsStep u a b v) : s(a, b) ∈ E(G) := by
  use a, b, h.isTwin

lemma exists_isStep_of_mem_halfEdgeSet (h : a ∈ H(G)) : ∃ b u v, G.IsStep u a b v := by
  obtain ⟨b, (hb : G.IsTwin a b)⟩ := h
  obtain ⟨u, hua⟩ := G.exists_isTwin_iff_exists_isBase (a := a) |>.mpr ⟨b, hb⟩
  obtain ⟨v, hvb⟩ := G.exists_isTwin_iff_exists_isBase (a := b) |>.mpr ⟨a, hb.symm⟩
  use b, u, v, hb, hua, hvb

lemma halfEdgeSet_eq_setOf_exists_isStep : H(G) = {a | ∃ b u v, G.IsStep u a b v} :=
  Set.ext fun _ ↦ ⟨G.exists_isStep_of_mem_halfEdgeSet, fun ⟨_, _, _, h⟩ ↦ h.left_halfEdge_mem⟩

/-! ### halfEdge-vertex-vertex incidence -/

def IsDart (G : Graph α β) (a : β) (u v : α) : Prop := ∃ b, G.IsStep u a b v

lemma IsDart.edge_mem (h : G.IsDart a u v) : a ∈ H(G) := by
  obtain ⟨b, h⟩ := h
  exact h.left_halfEdge_mem

lemma IsDart.left_mem (h : G.IsDart a u v) : u ∈ V(G) := h.choose_spec.left_mem

lemma IsDart.right_mem (h : G.IsDart a u v) : v ∈ V(G) := h.choose_spec.right_mem

lemma IsDart.isDart_iff (h : G.IsDart a u v) : G.IsDart a u' v' ↔ u = u' ∧ v = v' := by
  obtain ⟨b, h⟩ := h
  simp_rw [IsDart, h.isStep_iff]
  tauto

/-! ### Edge-vertex-vertex incidence -/

def IsLink (G : Graph α β) (e : Sym2 β) (u v : α) : Prop := ∃ a b, G.IsStep u a b v ∧ e = s(a, b)

lemma IsLink.edge_mem (h : G.IsLink e u v) : e ∈ E(G) := by
  obtain ⟨a, b, h, rfl⟩ := h
  exact h.edge_mem

lemma IsLink.left_mem (h : G.IsLink e u v) : u ∈ V(G) := h.choose_spec.choose_spec.1.left_mem

lemma IsLink.right_mem (h : G.IsLink e u v) : v ∈ V(G) := h.choose_spec.choose_spec.1.right_mem

@[symm] def IsLink.symm (h : G.IsLink e u v) : G.IsLink e v u := by
  obtain ⟨a, b, h, rfl⟩ := h
  use b, a, h.symm, eq_swap

lemma isLink_comm : G.IsLink e u v ↔ G.IsLink e v u := ⟨.symm, .symm⟩

lemma IsStep.isLink (h : G.IsStep u a b v) : G.IsLink s(a, b) u v := by use a, b, h

lemma edge_mem_iff_exists_isLink : e ∈ E(G) ↔ ∃ u v, G.IsLink e u v := by
  constructor
  · rintro ⟨a, b, h, rfl⟩
    obtain ⟨u, v, huv⟩ := h.exists_isStep
    exact ⟨u, v, huv.isLink⟩
  rintro ⟨u, v, h⟩
  exact h.edge_mem

lemma edgeSet_eq_setOf_exists_isLink : E(G) = {e | ∃ x y, G.IsLink e x y} :=
  Set.ext fun _ ↦ G.edge_mem_iff_exists_isLink

lemma IsLink.left_eq_or_eq (h : G.IsLink e u v) (h' : G.IsLink e u' v') : u = u' ∨ u = v' := by
  obtain ⟨a, b, h, rfl⟩ := h
  obtain ⟨a', b', h', heq⟩ := h'
  grind

lemma IsLink.right_eq_or_eq (h : G.IsLink e u v) (h' : G.IsLink e u' v') : v = u' ∨ v = v' :=
  h.symm.left_eq_or_eq h'

lemma IsLink.left_eq_of_right_ne (h : G.IsLink e u v) (h' : G.IsLink e u' v') (hu : u ≠ u') :
    u = v' := (h.left_eq_or_eq h').elim (False.elim ∘ hu) id

lemma IsLink.right_unique (h : G.IsLink e u v) (h' : G.IsLink e u v') : v = v' := by
  obtain rfl | rfl := h.right_eq_or_eq h'.symm
  · rfl
  obtain rfl | rfl := h'.right_eq_or_eq h.symm <;> rfl

lemma IsLink.left_unique (h : G.IsLink e u v) (h' : G.IsLink e u' v) : u = u' :=
  h.symm.right_unique h'.symm

lemma IsLink.eq_and_eq_or_eq_and_eq (h : G.IsLink e u v) (h' : G.IsLink e u' v') :
    (u = u' ∧ v = v') ∨ (u = v' ∧ v = u') := by
  obtain rfl | rfl := h.left_eq_or_eq h'
  · simp [h.right_unique h']
  simp [h'.symm.right_unique h]

lemma IsLink.isLink_iff (h : G.IsLink e u v) :
    G.IsLink e u' v' ↔ (u = u' ∧ v = v') ∨ (u = v' ∧ v = u') := by
  refine ⟨h.eq_and_eq_or_eq_and_eq, ?_⟩
  rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · assumption
  exact h.symm

lemma IsLink.isLink_iff_sym2_eq (h : G.IsLink e u v) : G.IsLink e u' v' ↔ s(u, v) = s(u', v') := by
  rw [h.isLink_iff, Sym2.eq_iff]

/-! ### Edge-vertex incidence -/

/-- The unary incidence predicate of `G`. `G.Inc e x` means that the vertex `x`
is one or both of the ends of the edge `e`.
In the `Inc` namespace, we use `edge` and `vertex` to refer to `e` and `x`. -/
def Inc (G : Graph α β) (e : Sym2 β) (v : α) : Prop := ∃ u, G.IsLink e v u

lemma Inc.edge_mem (h : G.Inc e v) : e ∈ E(G) :=
  h.choose_spec.edge_mem

@[simp]
lemma not_inc_of_notMem_edgeSet (he : e ∉ E(G)) : ¬ G.Inc e v :=
  mt Inc.edge_mem he

lemma Inc.vertex_mem (h : G.Inc e v) : v ∈ V(G) :=
  h.choose_spec.left_mem

lemma IsLink.inc_left (h : G.IsLink e v u) : G.Inc e v :=
  ⟨u, h⟩

lemma IsLink.inc_right (h : G.IsLink e v u) : G.Inc e u :=
  ⟨v, h.symm⟩

lemma Inc.eq_or_eq_of_isLink (h : G.Inc e u) (h' : G.IsLink e v w) : u = v ∨ u = w :=
  h.choose_spec.left_eq_or_eq h'

lemma Inc.eq_of_isLink_of_ne_left (h : G.Inc e u) (h' : G.IsLink e v w) (huv : u ≠ v) : u = w :=
  (h.eq_or_eq_of_isLink h').elim (False.elim ∘ huv) id

lemma IsLink.isLink_iff_eq (h : G.IsLink e v u) : G.IsLink e v w ↔ w = u :=
  ⟨fun h' ↦ h'.right_unique h, fun h' ↦ h' ▸ h⟩

/-- The binary incidence predicate can be expressed in terms of the unary one. -/
lemma isLink_iff_inc : G.IsLink e u v ↔ G.Inc e u ∧ G.Inc e v ∧ ∀ z, G.Inc e z → z = u ∨ z = v := by
  refine ⟨fun h ↦ ⟨h.inc_left, h.inc_right, fun z h' ↦ h'.eq_or_eq_of_isLink h⟩, ?_⟩
  rintro ⟨⟨x', hx'⟩, ⟨y', hy'⟩, h⟩
  obtain rfl | rfl := h _ hx'.inc_right
  · obtain rfl | rfl := hx'.left_eq_or_eq hy'
    · assumption
    exact hy'.symm
  assumption

/-- Given a proof that the edge `e` is incident with the vertex `x` in `G`,
noncomputably find the other end of `e`. (If `e` is a loop, this is equal to `x` itself). -/
protected noncomputable def Inc.other (h : G.Inc e u) : α := h.choose

@[simp]
lemma Inc.isLink_other (h : G.Inc e u) : G.IsLink e u h.other :=
  h.choose_spec

@[simp]
lemma Inc.inc_other (h : G.Inc e u) : G.Inc e h.other :=
  h.isLink_other.inc_right

lemma Inc.eq_or_eq_or_eq (hu : G.Inc e u) (hv : G.Inc e v) (hw : G.Inc e w) :
    u = v ∨ u = w ∨ v = w := by
  by_contra! ⟨huv, huw, hvw⟩
  obtain ⟨u', hu'⟩ := hu
  obtain rfl := hv.eq_of_isLink_of_ne_left hu' huv.symm
  obtain rfl := hw.eq_of_isLink_of_ne_left hu' huw.symm
  exact hvw rfl

lemma inc_eq_inc_iff_isLink_eq_isLink : G₁.Inc e = G₂.Inc f ↔ G₁.IsLink e = G₂.IsLink f := by
  constructor <;> rintro h
  · ext x y
    rw [isLink_iff_inc, isLink_iff_inc, h]
  · simp [funext_iff, Inc, h]

/-- `G.IsLoopAt e x` means that both ends of the edge `e` are equal to the vertex `x`. -/
def IsLoopAt (G : Graph α β) (e : Sym2 β) (v : α) : Prop := G.IsLink e v v

@[simp]
lemma isLink_self_iff : G.IsLink e v v ↔ G.IsLoopAt e v := Iff.rfl

lemma IsLoopAt.inc (h : G.IsLoopAt e v) : G.Inc e v :=
  IsLink.inc_left h

lemma IsLoopAt.eq_of_inc (h : G.IsLoopAt e v) (h' : G.Inc e v') : v = v' := by
  obtain rfl | rfl := h'.eq_or_eq_of_isLink h <;> rfl

-- Cannot be @[simp] because `x` cannot be inferred by `simp`.
lemma IsLoopAt.edge_mem (h : G.IsLoopAt e v) : e ∈ E(G) :=
  h.inc.edge_mem

-- Cannot be @[simp] because `e` cannot be inferred by `simp`.
lemma IsLoopAt.vertex_mem (h : G.IsLoopAt e v) : v ∈ V(G) :=
  h.inc.vertex_mem

/-- `G.IsNonloopAt e x` means that the vertex `x` is one but not both of the ends of the edge =`e`,
or equivalently that `e` is incident with `x` but not a loop at `x` -
see `Graph.isNonloopAt_iff_inc_not_isLoopAt`. -/
def IsNonloopAt (G : Graph α β) (e : Sym2 β) (v : α) : Prop := ∃ u ≠ v, G.IsLink e v u

lemma IsNonloopAt.inc (h : G.IsNonloopAt e v) : G.Inc e v :=
  h.choose_spec.2.inc_left

lemma IsNonloopAt.edge_mem (h : G.IsNonloopAt e v) : e ∈ E(G) := h.inc.edge_mem

lemma IsNonloopAt.vertex_mem (h : G.IsNonloopAt e v) : v ∈ V(G) := h.inc.vertex_mem

lemma IsLoopAt.not_isNonloopAt (h : G.IsLoopAt e v) (u : α) : ¬ G.IsNonloopAt e u := by
  rintro ⟨z, hyz, hy⟩
  rw [← h.eq_of_inc hy.inc_left, ← h.eq_of_inc hy.inc_right] at hyz
  exact hyz rfl

lemma IsNonloopAt.not_isLoopAt (h : G.IsNonloopAt e v) (u : α) : ¬ G.IsLoopAt e u :=
  fun h' ↦ h'.not_isNonloopAt v h

lemma isNonloopAt_iff_inc_not_isLoopAt : G.IsNonloopAt e v ↔ G.Inc e v ∧ ¬ G.IsLoopAt e v := by
  refine ⟨fun h ↦ ⟨h.inc, h.not_isLoopAt _⟩, fun ⟨h, hn⟩ ↦ ?_⟩
  obtain ⟨u, hu⟩ := h
  exact ⟨u, mt (fun h ↦ h ▸ hu) hn, hu⟩

lemma isLoopAt_iff_inc_not_isNonloopAt : G.IsLoopAt e v ↔ G.Inc e v ∧ ¬ G.IsNonloopAt e v := by
  simp +contextual [isNonloopAt_iff_inc_not_isLoopAt, iff_def, IsLoopAt.inc]

lemma Inc.isLoopAt_or_isNonloopAt (h : G.Inc e v) : G.IsLoopAt e v ∨ G.IsNonloopAt e v := by
  simp [isNonloopAt_iff_inc_not_isLoopAt, h, em]

/-! ### Adjacency -/

/-- `G.Adj x y` means that `G` has an edge whose ends are the vertices `x` and `y`. -/
def Adj (G : Graph α β) (u v : α) : Prop := ∃ e, G.IsLink e u v

@[symm]
protected lemma Adj.symm (h : G.Adj u v) : G.Adj v u :=
  ⟨_, h.choose_spec.symm⟩

instance : Std.Symm G.Adj where
  symm _ _ := Adj.symm

lemma adj_comm (x y) : G.Adj x y ↔ G.Adj y x := ⟨.symm, .symm⟩

lemma Adj.left_mem (h : G.Adj u v) : u ∈ V(G) :=
  h.choose_spec.left_mem

lemma Adj.right_mem (h : G.Adj u v) : v ∈ V(G) :=
  h.symm.left_mem

lemma IsLink.adj (h : G.IsLink e u v) : G.Adj u v := ⟨e, h⟩

-- /-! ### Extensionality -/

-- /-- `edgeSet` can be determined using `IsLink`, so the graph constructed from `G.vertexSet` and
-- `G.IsLink` using any value for `edgeSet` is equal to `G` itself. -/
-- @[simp]
-- lemma mk_eq_self (G : Graph α β) {E : Set β} (hE : ∀ e, e ∈ E ↔ ∃ x y, G.IsLink e x y) :
--     Graph.mk V(G) G.IsLink E
--     (by simpa [show E = E(G) by simp [Set.ext_iff, hE, G.edge_mem_iff_exists_isLink]]
--       using G.isLink_symm)
--     (fun _ _ _ _ _ h h' ↦ h.left_eq_or_eq h') hE
--     (fun _ _ _ ↦ IsLink.left_mem) = G := by
--   obtain rfl : E = E(G) := by simp [Set.ext_iff, hE, G.edge_mem_iff_exists_isLink]
--   cases G with | _ _ _ _ _ _ h _ => simp

-- /-- Two graphs with the same vertex set and binary incidences are equal.
-- (We use this as the default extensionality lemma rather than adding `@[ext]`
-- to the definition of `Graph`, so it doesn't require equality of the edge sets.) -/
-- @[ext]
-- protected lemma ext {G₁ G₂ : Graph α β} (hV : V(G₁) = V(G₂))
--     (h : ∀ e x y, G₁.IsLink e x y ↔ G₂.IsLink e x y) : G₁ = G₂ := by
--   rw [← G₁.mk_eq_self G₁.edge_mem_iff_exists_isLink, ← G₂.mk_eq_self G₂.edge_mem_iff_exists_isLink]
--   convert rfl using 2
--   · exact hV.symm
--   · simp [funext_iff, h]
--   simp [edgeSet_eq_setOf_exists_isLink, h]

-- /-- Two graphs with the same vertex set and unary incidences are equal. -/
-- lemma ext_inc {G₁ G₂ : Graph α β} (hV : V(G₁) = V(G₂)) (h : ∀ e x, G₁.Inc e x ↔ G₂.Inc e x) :
--     G₁ = G₂ :=
--   Graph.ext hV fun _ _ _ ↦ by simp_rw [isLink_iff_inc, h]

-- /-- `Graph.copy` produces a graph equal to `G` but with provided definitional choices
-- for `vertexSet`, `edgeSet`, and `IsLink`. This is mainly useful for improving
-- definitional equalities while keeping the same underlying graph. -/
-- @[simps]
-- def copy (G : Graph α β) {vertexSet : Set α} {edgeSet : Set β} {IsLink : β → α → α → Prop}
--     (hvertexSet : V(G) = vertexSet) (hedgeSet : E(G) = edgeSet)
--     (hIsLink : ∀ e x y, G.IsLink e x y ↔ IsLink e x y) : Graph α β where
--   vertexSet := vertexSet
--   edgeSet := edgeSet
--   IsLink := IsLink
--   isLink_symm e he x y := by
--     simp_rw [← hIsLink]
--     apply G.isLink_symm (hedgeSet ▸ he)
--   eq_or_eq_of_isLink_of_isLink := by
--     simp_rw [← hIsLink]
--     exact G.eq_or_eq_of_isLink_of_isLink
--   edge_mem_iff_exists_isLink := by
--     simp_rw [← hIsLink, ← hedgeSet]
--     exact G.edge_mem_iff_exists_isLink
--   left_mem_of_isLink := by
--     simp_rw [← hIsLink, ← hvertexSet]
--     exact G.left_mem_of_isLink

-- @[simp]
-- lemma copy_eq (G : Graph α β) {V : Set α} {E : Set β} {IsLink : β → α → α → Prop}
--     (hV : V(G) = V) (hE : E(G) = E) (h_isLink : ∀ e x y, G.IsLink e x y ↔ IsLink e x y) :
--     G.copy hV hE h_isLink = G := by
--   ext <;> simp_all

/-! ### Sets of edges or loops incident to a vertex -/

/-- `G.incidenceSet x` is the set of edges incident to `x` in `G`. -/
def incidenceSet (x : α) : Set (Sym2 β) := {e | G.Inc e x}

@[simp] theorem mem_incidenceSet (x : α) (e : Sym2 β) : e ∈ G.incidenceSet x ↔ G.Inc e x := Iff.rfl

theorem incidenceSet_subset_edgeSet (x : α) : G.incidenceSet x ⊆ E(G) :=
  fun _ ⟨_, hy⟩ ↦ hy.edge_mem

/-- `G.loopSet x` is the set of loops at `x` in `G`. -/
def loopSet (x : α) : Set (Sym2 β) := {e | G.IsLoopAt e x}

@[simp] theorem mem_loopSet (x : α) (e : Sym2 β) : e ∈ G.loopSet x ↔ G.IsLoopAt e x := Iff.rfl

/-- The loopSet is included in the incidenceSet. -/
theorem loopSet_subset_incidenceSet (x : α) : G.loopSet x ⊆ G.incidenceSet x := fun _ he ↦ ⟨x, he⟩

/-!
### Compatibility of Graphs

We define two graphs to be `Compatible` if for each edge belonging to their shared edge set,
the incidence relation (i.e., which pairs of vertices it links) is the same in both graphs.
-/

/-- Two graphs are compatible if their shared edges have the same ends in both graphs. -/
def Compatible (G H : Graph α β) : Prop :=
  ∀ ⦃e⦄, e ∈ E(G) → e ∈ E(H) → ∀ x y, G.IsLink e x y ↔ H.IsLink e x y

lemma Compatible.isLink_congr (heG : e ∈ E(G)) (heH : e ∈ E(H)) (h : G.Compatible H) {x y : α} :
    G.IsLink e x y ↔ H.IsLink e x y :=
  h heG heH x y

lemma Compatible.refl (G : Graph α β) : G.Compatible G :=
  fun _ _ _ _ _ => .rfl

@[simp]
lemma Compatible.rfl {G : Graph α β} : G.Compatible G := .refl _

instance : Std.Refl (Compatible : Graph α β → Graph α β → Prop) where
  refl _ := .rfl

@[symm]
lemma Compatible.symm (h : G.Compatible H) : H.Compatible G :=
  fun _ heH heG x y => (h heG heH x y).symm

instance : Std.Symm (Compatible : Graph α β → Graph α β → Prop) where
  symm _ _ := Compatible.symm

lemma IsLink.of_compatible (hGH : G.Compatible H) (heH : e ∈ E(H)) (h : G.IsLink e u v) :
    H.IsLink e u v :=
  (hGH h.edge_mem heH u v).mp h

lemma Compatible.of_disjoint_edgeSet (h : Disjoint E(G) E(H)) : Compatible G H :=
  fun _ heG heH _ _ ↦ h.notMem_of_mem_left heG heH |>.elim

lemma Inc.of_compatible (hGH : G.Compatible H) (heH : e ∈ E(H)) (h : G.Inc e u) : H.Inc e u := by
  obtain ⟨y, hy⟩ := h
  exact ⟨y, hy.of_compatible hGH heH⟩

lemma IsLoopAt.of_compatible (hGH : G.Compatible H) (heH : e ∈ E(H)) (h : G.IsLoopAt e u) :
    H.IsLoopAt e u :=
  IsLink.of_compatible hGH heH h

lemma IsNonloopAt.of_compatible (hGH : G.Compatible H) (heH : e ∈ E(H)) (h : G.IsNonloopAt e u) :
    H.IsNonloopAt e u := by
  obtain ⟨y, hne, hy⟩ := h
  exact ⟨y, hne, hy.of_compatible hGH heH⟩

/-! ### Graphs with no edges -/

/-- The graph with vertex set `vertexSet` and no edges -/
@[simps (attr := grind =)]
def noEdge (vertexSet : Set α) (β : Type*) : Graph α β where
  vertexSet := vertexSet
  IsTwin _ _ := False
  IsTwin_symm _ _ := by simp
  IsTwin_irrefl := ⟨by simp⟩
  IsTwin_unique := by simp
  IsBase _ _ := False
  IsBase_unique := by simp
  exists_isTwin_iff_exists_isBase := by simp
  mem_vertexSet_of_isBase := by simp

variable {vertexSet : Set α} {edgeSet : Set β}

lemma edgeSet_eq_empty : E(G) = ∅ ↔ G = noEdge V(G) β := by
  refine ⟨fun h ↦ Graph.ext rfl ?_, fun h ↦ by rw [h, noEdge_edgeSet]⟩
  simp only [noEdge_isLink, iff_false]
  refine fun e x y he ↦ ?_
  have := h ▸ he.edge_mem
  simp at this

/-! ### Graphs with two vertices -/

/-- A graph with exactly two vertices and no loops. -/
@[simps (attr := grind =)]
def singleEdge (u v : α) (hne : a ≠ b) : Graph α β where
  vertexSet := {u, v}
  IsTwin c d := s(c, d) = s(a, b)
  IsTwin_symm _ _ := by simp [Sym2.eq_swap]
  IsTwin_irrefl := ⟨by grind⟩
  IsTwin_unique := by grind
  IsBase c w := (c = a ∧ w = u) ∨ (c = b ∧ w = v)
  IsBase_unique := by grind
  exists_isTwin_iff_exists_isBase _ := by simp; grind
  mem_vertexSet_of_isBase := by grind

@[simp]
lemma singleEdge_isStep (hne : a ≠ b) :
    (singleEdge u v hne).IsStep w c d w' ↔ (u = w ∧ c = a ∧ d = b ∧ v = w') ∨
    (u = w' ∧ c = b ∧ d = a ∧ v = w) := by
  simp only [isStep_iff, singleEdge_IsTwin, Sym2.eq, rel_iff', Prod.mk.injEq, Prod.swap_prod_mk,
    singleEdge_IsBase]
  grind

@[simp]
lemma singleEdge_isLink (hne : a ≠ b) :
    (singleEdge u v hne).IsLink e w w' ↔ e = s(a, b) ∧ s(u, v) = s(w, w') := by
  simp only [IsLink, singleEdge_isStep]
  grind

@[simp]
lemma singleEdge_inc (hne : a ≠ b) :
    (singleEdge u v hne).Inc e w ↔ e = s(a, b) ∧ (w = u ∨ w = v) := by
  simp [Inc, singleEdge_isLink, exists_and_left, and_congr_right_iff]
  aesop

lemma singleEdge_comm (u v : α) (hne : a ≠ b) : singleEdge u v hne = singleEdge v u hne :=
  Graph.ext_inc (pair_comm ..) <| by simp [or_comm]

@[simp]
lemma banana_isNonloopAt :
    (banana u v edgeSet).IsNonloopAt e x ↔ e ∈ edgeSet ∧ (x = u ∨ x = v) ∧ u ≠ v := by
  simp_rw [isNonloopAt_iff_inc_not_isLoopAt, ← isLink_self_iff, banana_isLink, banana_inc]
  aesop

@[simp]
lemma banana_isLoopAt : (banana u v edgeSet).IsLoopAt e x ↔ e ∈ edgeSet ∧ x = u ∧ u = v := by
  simp only [← isLink_self_iff, banana_isLink, and_congr_right_iff]
  aesop

@[simp]
lemma banana_adj : (banana u v edgeSet).Adj x y ↔ edgeSet.Nonempty ∧ s(x, y) = s(u, v) := by
  simp only [Adj, banana_isLink, exists_and_right, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
    Prod.swap_prod_mk, and_congr_left_iff]
  exact fun _ ↦ Iff.rfl

@[simp]
lemma banana_empty : banana u v ∅ = Graph.noEdge {u, v} β := by
  ext <;> simp

end Graph
