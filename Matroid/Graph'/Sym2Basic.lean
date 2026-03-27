/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Jun Kwon
-/
module

public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Sym.Sym2
public import Matroid.Graph.GraphLike.Basic

/-!
# Multigraphs

A multigraph is a set of vertices and a set of edges,
together with incidence data that associates each edge `e`
with an unordered pair `s(x,y)` of vertices called the *ends* of `e`.
The pair of `e` and `s(x,y)` is called a *link*.
The vertices `x` and `y` may be equal, in which case `e` is a *loop*.
There may be more than one edge wih the same ends.

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

variable {α β : Type*} {x y z u v w : α} {a b c d : β} {e f : Sym2 β}

open Set Sym2 GraphLike

/-- A multigraph with vertices of type `α` and edges of type `β`,
as described by vertex and edge sets `vertexSet : Set α` and `edgeSet : Set β`,
and a predicate `IsLink` describing whether an edge `e : β` has vertices `x y : α` as its ends.

The `edgeSet` structure field can be inferred from `IsLink`
via `edge_mem_iff_exists_isLink` (and this structure provides default values
for `edgeSet` and `edge_mem_iff_exists_isLink` that use `IsLink`).
While the field is not strictly necessary, when defining a graph we often
immediately know what the edge set should be,
and furthermore having `edgeSet` separate can be convenient for
definitional equality reasons. -/
structure Graph (α β : Type*) where
  /-- The vertex set. -/
  vertexSet : Set α
  /-- The edge set. -/
  edgeSet : Set (Sym2 β)
  /-- The edge set is pairwise disjoint. -/
  edgeSet_pairwise_disjoint :
    ∀ ⦃e f : Sym2 β⦄, e ∈ edgeSet → f ∈ edgeSet → e ≠ f → ∀ ⦃x y : β⦄, x ∈ e → y ∈ f → x ≠ y
  /-- The edge set does not contain any edges with one half-edge. -/
  edgeSet_not_isDiag : ∀ ⦃e : Sym2 β⦄, e ∈ edgeSet → ¬IsDiag e
  /-- The attach function attaches a half-edge to a vertex. -/
  attach : {d : β | ∃ e ∈ edgeSet, d ∈ e} → α
  /-- the vertex set contains all the vertices with at least one half-edge attached to it. -/
  attach_mem : range attach ⊆ vertexSet

namespace Graph

variable {G G₁ G₂ H : Graph α β}

/-- `E(G)` denotes the `edgeSet` of a graph `G`. -/
scoped notation "E(" G ")" => Graph.edgeSet G

/-- The set of darts (half-edges) appearing in some edge of `G`. -/
def halfEdgeSet (G : Graph α β) : Set β :=
  {d | ∃ e ∈ G.edgeSet, d ∈ e}

/-- `H(G)` denotes the `halfEdgeSet` of a graph `G`. -/
scoped notation "H(" G ")" => Graph.halfEdgeSet G

@[simp] theorem halfEdgeSet_eq (G : Graph α β) : G.halfEdgeSet = {d | ∃ e ∈ G.edgeSet, d ∈ e} := rfl

@[simp] theorem mem_halfEdgeSet_iff : d ∈ H(G) ↔ ∃ e ∈ G.edgeSet, d ∈ e := by simp [halfEdgeSet]

/-! ### Unique edge through a half-edge -/

theorem edge_eq_of_mem_darts (he : e ∈ G.edgeSet) (hf : f ∈ G.edgeSet) (hd : d ∈ e) (hd' : d ∈ f) :
    e = f := by_contra (G.edgeSet_pairwise_disjoint he hf · hd hd' rfl)

theorem exists_unique_edge_of_mem_halfEdgeSet (hd : d ∈ H(G)) : ∃! e, e ∈ G.edgeSet ∧ d ∈ e := by
  rcases mem_halfEdgeSet_iff.mp hd with ⟨e₀, he₀, hd₀⟩
  exact ⟨e₀, ⟨he₀, hd₀⟩, fun e₁ ⟨he₁, hd₁⟩ ↦ (edge_eq_of_mem_darts he₀ he₁ hd₀ hd₁).symm⟩

noncomputable def edge (G : Graph α β) (a : H(G)) : Sym2 β :=
  (exists_unique_edge_of_mem_halfEdgeSet a.property).choose

theorem edge_mem_edgeSet (a : H(G)) : G.edge a ∈ G.edgeSet :=
  (exists_unique_edge_of_mem_halfEdgeSet a.property).choose_spec.1.1

theorem mem_edge (a : H(G)) : a.val ∈ G.edge a :=
  (exists_unique_edge_of_mem_halfEdgeSet a.property).choose_spec.1.2

theorem edge_eq_of_mem (a : H(G)) (he : e ∈ G.edgeSet) (ha : a.val ∈ e) : e = G.edge a :=
  (exists_unique_edge_of_mem_halfEdgeSet a.property).unique ⟨he, ha⟩
    (exists_unique_edge_of_mem_halfEdgeSet a.property).choose_spec.1

theorem edge_congr {a b : H(G)} (h : a.val = b.val) : G.edge a = G.edge b :=
  edge_eq_of_mem b (edge_mem_edgeSet a) (h.symm ▸ mem_edge a)

theorem edge_not_isDiag (b : H(G)) : ¬(G.edge b).IsDiag :=
  G.edgeSet_not_isDiag (edge_mem_edgeSet b)

/-! ### Partner dart `inv'` -/

noncomputable def inv' (G : Graph α β) (b : H(G)) : H(G) :=
  ⟨Mem.other (mem_edge b),
    mem_halfEdgeSet_iff.mpr ⟨G.edge b, edge_mem_edgeSet b, other_mem (mem_edge b)⟩⟩

@[simp] theorem inv'_val (b : H(G)) : (G.inv' b).val = Mem.other (mem_edge b) := rfl

theorem edge_eq_mk (b : H(G)) : G.edge b = s(b.val, (G.inv' b).val) :=
  (other_spec (mem_edge b)).symm.trans (congrArg (s(b.val, ·)) (inv'_val b).symm)

theorem mem_edge_iff (b : H(G)) (c : β) : c ∈ G.edge b ↔ c = b.val ∨ c = (G.inv' b).val := by
  rw [edge_eq_mk, mem_iff]

theorem inv_mem (b : H(G)) : (G.inv' b).val ∈ H(G) := (G.inv' b).property

@[simp] theorem inv_mem_iff : d ∈ H(G) ↔ ∃ e ∈ G.edgeSet, d ∈ e := mem_halfEdgeSet_iff

theorem inv_ne (b : H(G)) : (G.inv' b).val ≠ b.val :=
  Sym2.other_ne (G.edgeSet_not_isDiag (edge_mem_edgeSet b)) (mem_edge b)

@[simp]
theorem edge_inv (b : H(G)) : G.edge (G.inv' b) = G.edge b :=
  (edge_eq_of_mem (G.inv' b) (edge_mem_edgeSet b) (other_mem (mem_edge b))).symm

theorem inv'_inv' (b : H(G)) : G.inv' (G.inv' b) = b := by
  have hpair := (other_spec <| edge_inv _ ▸ mem_edge (G.inv' b)).trans (edge_eq_mk b)
  rcases Sym2.eq_iff.mp hpair with ⟨h1, _⟩ | ⟨_, hmem⟩
  · exact (inv_ne b h1).elim
  rw [Subtype.ext_iff, inv'_val]
  convert hmem using 2
  exact edge_inv b

@[simp]
theorem forall_mem_edge_iff {P : β → Prop} (b : H(G)) :
    (∀ c ∈ G.edge b, P c) ↔ P b.val ∧ P (G.inv' b).val := by
  rw [edge_eq_mk, Sym2.ball]

theorem mem_halfEdgeSet_of_mem_edge (ha : a ∈ H(G)) (hb : b ∈ G.edge ⟨a, ha⟩) : b ∈ H(G) := by
  obtain rfl | rfl := mem_edge_iff ⟨a, ha⟩ b |>.mp hb
  · exact ha
  exact inv_mem ⟨a, ha⟩

theorem edge_eq_edge_iff (a b : H(G)) :
    G.edge a = G.edge b ↔ a.val = b.val ∨ a.val = (G.inv' b).val := by
  refine ⟨fun he ↦ ?_, ?_⟩
  · have ha : a.val ∈ G.edge b := he ▸ mem_edge a
    rwa [mem_edge_iff] at ha
  rintro (hab | hab)
  · exact edge_congr hab
  rw [(show a = G.inv' b from Subtype.ext hab), edge_inv]

noncomputable def attach' (G : Graph α β) : H(G) → G.vertexSet :=
  fun h ↦⟨G.attach h, G.attach_mem (mem_range_self h)⟩

@[simp] theorem attach'_coe (b : H(G)) : (G.attach' b).val = G.attach b := rfl

/-! ### The graph-like structure -/

/-- The dart oriented from the half-edge `b` toward `G.inv' b`. -/
noncomputable def dartOf (G : Graph α β) (b : H(G)) : (β × α) × (β × α) :=
  ((b.val, (G.attach' b).val), ((G.inv' b).val, (G.attach' (G.inv' b)).val))

instance : DartLike α ((β × α) × (β × α)) where
  fst a := a.1.2
  snd a := a.2.2

noncomputable instance : GraphLike α ((β × α) × (β × α)) (Graph α β) where
  verts G := G.vertexSet
  darts G := Set.range (dartOf G)
  fst_mem_of_darts {G d} h := by
    obtain ⟨b, rfl⟩ := h
    simpa [dartOf, DartLike.fst] using (G.attach' b).property
  snd_mem_of_darts {G d} h := by
    obtain ⟨b, rfl⟩ := h
    simpa [dartOf, DartLike.snd] using (G.attach' (G.inv' b)).property
  Adj G u v := ∃ b : H(G), (G.attach' b).val = u ∧ (G.attach' (G.inv' b)).val = v
  exists_darts_iff_adj {G u v} := by
    constructor
    · rintro ⟨d, ⟨b, rfl⟩, rfl, rfl⟩
      refine ⟨b, ?_, ?_⟩ <;> simp [dartOf, DartLike.fst, DartLike.snd]
    · rintro ⟨b, rfl, rfl⟩
      refine ⟨dartOf G b, ⟨b, rfl⟩, ?_, ?_⟩ <;> simp [dartOf, DartLike.fst, DartLike.snd]

@[simp] lemma verts_eq (G : Graph α β) : V(G) = G.vertexSet := rfl
@[simp] lemma darts_eq (G : Graph α β) : darts G = Set.range (dartOf G) := rfl

/-! ### Binary incidence -/

def isLink (G : Graph α β) (e : Sym2 β) (x y : α) : Prop :=
  ∃ a : H(G), G.edge a = e ∧ G.attach a = x ∧ G.attach (G.inv' a) = y

/-! ### The edge set (primitive `edgeSet`) -/

theorem mem_edgeSet_iff : e ∈ G.edgeSet ↔ ∃ a : H(G), G.edge a = e := by
  refine ⟨fun he ↦ ?_, fun ⟨a, ha⟩ ↦ ha ▸ edge_mem_edgeSet a⟩
  have hdH : e.out.1 ∈ H(G) := mem_halfEdgeSet_iff.mpr ⟨e, he, e.out_fst_mem⟩
  exact ⟨⟨e.out.1, hdH⟩, (edge_eq_of_mem ⟨e.out.1, hdH⟩ he e.out_fst_mem).symm⟩

/-! ### Incidence predicate `isLink` -/

instance : Std.Symm (G.isLink e) where
  symm x y h := by
    obtain ⟨a, he, hx, hy⟩ := h
    refine ⟨G.inv' a, ?_, hy, ?_⟩
    · rw [← he, edge_inv]
    · simpa [inv'_inv'] using hx

theorem isLink.edge_mem (h : G.isLink e x y) : e ∈ E(G) := by
  obtain ⟨a, rfl, -, -⟩ := h
  exact edge_mem_edgeSet a

@[simp]
lemma not_isLink_of_notMem_edgeSet (he : e ∉ E(G)) : ¬ G.isLink e x y :=
  mt isLink.edge_mem he

@[symm] theorem isLink.symm (h : G.isLink e x y) : G.isLink e y x := symm_of (G.isLink e) h

theorem isLink.left_mem (h : G.isLink e x y) : x ∈ G.vertexSet := by
  obtain ⟨a, -, rfl, -⟩ := h
  exact G.attach_mem (mem_range_self a)

theorem isLink.right_mem (h : G.isLink e x y) : y ∈ G.vertexSet := h.symm.left_mem

lemma isLink_comm : G.isLink e x y ↔ G.isLink e y x := ⟨.symm, .symm⟩

theorem isLink_of_mem_halfEdge (ha : a ∈ H(G)) :
    G.isLink (G.edge ⟨a, ha⟩) (G.attach ⟨a, ha⟩) (G.attach (G.inv' ⟨a, ha⟩)) :=
  ⟨⟨a, ha⟩, rfl, rfl, rfl⟩

theorem mem_edgeSet_iff_exists_isLink : e ∈ E(G) ↔ ∃ x y, G.isLink e x y := by
  refine ⟨fun he ↦ ?_, fun ⟨x, y, h⟩ ↦ h.edge_mem⟩
  obtain ⟨a, rfl⟩ := mem_edgeSet_iff.mp he
  exact ⟨_, _, isLink_of_mem_halfEdge a.property⟩

lemma edgeSet_eq_setOf_exists_isLink : E(G) = {e | ∃ x y, G.isLink e x y} :=
  Set.ext fun _ ↦ mem_edgeSet_iff_exists_isLink

theorem halfEdgeSet_eq_setOf_exists_isLink :
    H(G) = {a : β | ∃ (ha : a ∈ H(G)) (x y : α), G.isLink (G.edge ⟨a, ha⟩) x y} := by
  ext a
  exact ⟨fun ha ↦ ⟨ha, _, _, isLink_of_mem_halfEdge ha⟩, fun ⟨ha, _, _, h⟩ ↦ ha⟩

theorem isLink.left_eq_or_eq (h : G.isLink e x y) (h' : G.isLink e z w) : x = z ∨ x = w := by
  obtain ⟨a, hab, rfl, rfl⟩ := h
  obtain ⟨b, rfl, rfl, rfl⟩ := h'
  rw [edge_eq_edge_iff] at hab
  rcases hab with hab | hab
  · left
    simpa using congrArg G.attach (Subtype.ext hab)
  · right
    simpa [inv'_inv'] using congrArg G.attach (Subtype.ext hab)

theorem isLink.right_eq_or_eq (h : G.isLink e x y) (h' : G.isLink e z w) : y = z ∨ y = w :=
  h.symm.left_eq_or_eq h'

theorem isLink.left_eq_of_right_ne (h : G.isLink e x y) (h' : G.isLink e z w) (hzx : x ≠ z) :
    x = w :=
  (h.left_eq_or_eq h').elim (False.elim ∘ hzx) id

theorem isLink.right_unique (h : G.isLink e x y) (h' : G.isLink e x z) : y = z := by
  obtain rfl | rfl := h.right_eq_or_eq h'.symm
  · rfl
  obtain rfl | rfl := h'.right_eq_or_eq h.symm <;> rfl

theorem isLink.left_unique (h : G.isLink e x z) (h' : G.isLink e y z) : x = y :=
  h.symm.right_unique h'.symm

theorem isLink.eq_and_eq_or_eq_and_eq {x' y' : α} (h : G.isLink e x y) (h' : G.isLink e x' y') :
    (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  obtain rfl | rfl := h.left_eq_or_eq h'
  · simp [h.right_unique h']
  · simp [h'.symm.right_unique h]

theorem isLink.isLink_iff (h : G.isLink e x y) {x' y' : α} :
    G.isLink e x' y' ↔ (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  refine ⟨h.eq_and_eq_or_eq_and_eq, ?_⟩
  rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · assumption
  · exact h.symm

theorem isLink.isLink_iff_sym2_eq (h : G.isLink e x y) {x' y' : α} :
    G.isLink e x' y' ↔ s(x, y) = s(x', y') := by
  rw [h.isLink_iff, Sym2.eq_iff]

lemma isLink_attach {a : H(G)} : G.isLink (G.edge a) (G.attach a) (G.attach (G.inv' a)) :=
  ⟨a, rfl, rfl, rfl⟩

/-! ### Edge-vertex incidence -/

/-- The unary incidence predicate of `G`. `G.Inc e x` means that the vertex `x`
is one or both of the ends of the edge `e`.
In the `Inc` namespace, we use `edge` and `vertex` to refer to `e` and `x`. -/
def Inc (G : Graph α β) (e : Sym2 β) (x : α) : Prop :=
  ∃ y, G.isLink e x y

lemma Inc.edge_mem (h : G.Inc e x) : e ∈ E(G) := h.choose_spec.edge_mem

@[simp] lemma not_inc_of_notMem_edgeSet (he : e ∉ E(G)) : ¬G.Inc e x := mt Inc.edge_mem he

lemma Inc.vertex_mem (h : G.Inc e x) : x ∈ V(G) := h.choose_spec.left_mem

lemma isLink.inc_left (h : G.isLink e x y) : G.Inc e x := ⟨y, h⟩

lemma isLink.inc_right (h : G.isLink e x y) : G.Inc e y := ⟨x, h.symm⟩

lemma Inc.eq_or_eq_of_isLink (h : G.Inc e x) (h' : G.isLink e y z) : x = y ∨ x = z :=
  h.choose_spec.left_eq_or_eq h'

lemma Inc.eq_of_isLink_of_ne_left (h : G.Inc e x) (h' : G.isLink e y z) (hxy : x ≠ y) : x = z :=
  (h.eq_or_eq_of_isLink h').elim (False.elim ∘ hxy) id

lemma isLink.isLink_iff_eq (h : G.isLink e x y) : G.isLink e x z ↔ z = y :=
  ⟨fun h' ↦ h'.right_unique h, fun h' ↦ h' ▸ h⟩

lemma isLink_iff_inc : G.isLink e x y ↔ G.Inc e x ∧ G.Inc e y ∧ ∀ z, G.Inc e z → z = x ∨ z = y := by
  refine ⟨fun h ↦ ⟨h.inc_left, h.inc_right, fun z h' ↦ h'.choose_spec.left_eq_or_eq h⟩, ?_⟩
  rintro ⟨⟨x', hx'⟩, ⟨y', hy'⟩, h⟩
  obtain rfl | rfl := h _ hx'.inc_right
  · obtain rfl | rfl := hx'.left_eq_or_eq hy'
    · assumption
    exact hy'.symm
  assumption

/-- Given a proof that the edge `e` is incident with the vertex `x` in `G`,
noncomputably find the other end of `e`. (If `e` is a loop, this is equal to `x` itself). -/
protected noncomputable def Inc.other (h : G.Inc e x) : α := h.choose

@[simp] lemma Inc.isLink_other (h : G.Inc e x) : G.isLink e x h.other := h.choose_spec

@[simp] lemma Inc.inc_other (h : G.Inc e x) : G.Inc e h.other := h.isLink_other.inc_right

lemma Inc.eq_or_eq_or_eq (hx : G.Inc e x) (hy : G.Inc e y) (hz : G.Inc e z) :
    x = y ∨ x = z ∨ y = z := by
  by_contra! ⟨hxy, hxz, hyz⟩
  obtain ⟨x', hx'⟩ := hx
  obtain rfl := hy.eq_of_isLink_of_ne_left hx' hxy.symm
  obtain rfl := hz.eq_of_isLink_of_ne_left hx' hxz.symm
  exact hyz rfl

lemma inc_eq_inc_iff_isLink_eq_isLink :
    (∀ x, G₁.Inc e x ↔ G₂.Inc f x) ↔ (∀ x y, G₁.isLink e x y ↔ G₂.isLink f x y) := by
  refine ⟨fun h x y ↦ ?_, fun h x ↦ exists_congr (h x)⟩
  simp_rw [isLink_iff_inc, h]

lemma inc_attach {a : H(G)} : G.Inc (G.edge a) (G.attach a) :=
  ⟨G.attach (G.inv' a), isLink_attach⟩

/-! ### Loops and non-loops -/

/-- `G.IsLoopAt e x` means that both ends of the edge `e` are equal to the vertex `x`. -/
def IsLoopAt (G : Graph α β) (e : Sym2 β) (x : α) : Prop := G.isLink e x x

@[simp] lemma isLink_self_iff : G.isLink e x x ↔ G.IsLoopAt e x := Iff.rfl

lemma IsLoopAt.inc (h : G.IsLoopAt e x) : G.Inc e x := isLink.inc_left h

lemma IsLoopAt.eq_of_inc (h : G.IsLoopAt e x) (h' : G.Inc e y) : x = y := by
  obtain rfl | rfl := h'.eq_or_eq_of_isLink h <;> rfl

lemma IsLoopAt.edge_mem (h : G.IsLoopAt e x) : e ∈ E(G) := h.inc.edge_mem

lemma IsLoopAt.vertex_mem (h : G.IsLoopAt e x) : x ∈ Graph.vertexSet G := h.inc.vertex_mem

/-- `G.IsNonloopAt e x` means that the vertex `x` is one but not both of the ends of the edge =`e`,
or equivalently that `e` is incident with `x` but not a loop at `x` -
see `Graph.isNonloopAt_iff_inc_not_isLoopAt`. -/
def IsNonloopAt (G : Graph α β) (e : Sym2 β) (x : α) : Prop := ∃ y ≠ x, G.isLink e x y

lemma IsNonloopAt.inc (h : G.IsNonloopAt e x) : G.Inc e x := h.choose_spec.2.inc_left

lemma IsNonloopAt.edge_mem (h : G.IsNonloopAt e x) : e ∈ E(G) := h.inc.edge_mem

lemma IsNonloopAt.vertex_mem (h : G.IsNonloopAt e x) : x ∈ Graph.vertexSet G := h.inc.vertex_mem

lemma IsLoopAt.not_isNonloopAt (h : G.IsLoopAt e x) (y : α) : ¬G.IsNonloopAt e y := by
  rintro ⟨z, hyz, hy⟩
  rw [← h.eq_of_inc hy.inc_left, ← h.eq_of_inc hy.inc_right] at hyz
  exact hyz rfl

lemma IsNonloopAt.not_isLoopAt (h : G.IsNonloopAt e x) (y : α) : ¬G.IsLoopAt e y :=
  fun h' ↦ h'.not_isNonloopAt x h

lemma isNonloopAt_iff_inc_not_isLoopAt : G.IsNonloopAt e x ↔ G.Inc e x ∧ ¬G.IsLoopAt e x :=
  ⟨fun h ↦ ⟨h.inc, h.not_isLoopAt _⟩, fun ⟨⟨y, hy⟩, hn⟩ ↦ ⟨y, mt (fun h' ↦ h' ▸ hy) hn, hy⟩⟩

lemma Inc.isLoopAt_or_isNonloopAt (h : G.Inc e x) : G.IsLoopAt e x ∨ G.IsNonloopAt e x := by
  rw [isNonloopAt_iff_inc_not_isLoopAt]
  by_cases hl : G.IsLoopAt e x
  · exact Or.inl hl
  · exact Or.inr ⟨h, hl⟩

lemma isLoopAt_iff_inc_not_isNonloopAt : G.IsLoopAt e x ↔ G.Inc e x ∧ ¬ G.IsNonloopAt e x := by
  refine ⟨fun h ↦ ⟨h.inc, fun h' ↦ h'.not_isLoopAt x h⟩, fun ⟨hinc, hn⟩ ↦ ?_⟩
  obtain hl | hnl := hinc.isLoopAt_or_isNonloopAt
  · assumption
  exact absurd hnl hn

instance (G : Graph α β) : Std.Symm (Adj G) where
  symm _ _ := fun ⟨b, hu, hv⟩ ↦ ⟨G.inv' b, hv, by rw [inv'_inv']; exact hu⟩

theorem adj_iff_exists_isLink_edge : Adj G u v ↔ ∃ b : H(G), G.isLink (G.edge b) u v := by
  refine ⟨fun ⟨b, hu, hv⟩ ↦ ⟨b, hu ▸ hv ▸ isLink_of_mem_halfEdge b.property⟩, fun ⟨b, h⟩ ↦ ?_⟩
  obtain ⟨a, he, rfl, rfl⟩ := h
  obtain hae | hae := (edge_eq_edge_iff a b).mp he
  · obtain rfl : a = b := Subtype.ext hae
    exact ⟨a, rfl, rfl⟩
  obtain rfl : a = G.inv' b := Subtype.ext hae
  use G.inv' b
  simp

theorem adj_iff_exists_isLink : Adj G u v ↔ ∃ e, G.isLink e u v := by
  rw [adj_iff_exists_isLink_edge]
  exact ⟨fun ⟨a, h⟩ ↦ ⟨_, h⟩, fun ⟨e, a, he, hu, hv⟩ ↦
    ⟨a, by simpa [he, hu, hv] using isLink_of_mem_halfEdge a.property⟩⟩

theorem isLink.adj (h : G.isLink e x y) : Adj G x y := by
  obtain ⟨a, _, rfl, rfl⟩ := h
  refine ⟨a, ?_, ?_⟩ <;> simp [attach'_coe]

lemma Adj.left_mem (h : Adj G x y) : x ∈ G.vertexSet := by
  rcases adj_iff_exists_isLink.mp h with ⟨e, hlink⟩
  exact hlink.left_mem

lemma Adj.right_mem (h : Adj G x y) : y ∈ G.vertexSet := by
  rcases adj_iff_exists_isLink.mp h with ⟨e, hlink⟩
  exact hlink.right_mem

lemma adj_symm (h : Adj G x y) : Adj G y x := by
  obtain ⟨b, hu, hv⟩ := h
  exact ⟨G.inv' b, hv, by rw [inv'_inv']; exact hu⟩

lemma adj_comm (x y : α) : Adj G x y ↔ Adj G y x := ⟨adj_symm, adj_symm⟩

/-! ### Extensionality and compatibility -/

lemma edgeSet_eq_of_isLink_iff (h : ∀ e x y, G₁.isLink e x y ↔ G₂.isLink e x y) :
    G₁.edgeSet = G₂.edgeSet := by
  ext e
  rw [mem_edgeSet_iff_exists_isLink, mem_edgeSet_iff_exists_isLink]
  exact exists₂_congr (h e)

lemma halfEdgeSet_eq_of_isLink_iff (h : ∀ e x y, G₁.isLink e x y ↔ G₂.isLink e x y) :
    G₁.halfEdgeSet = G₂.halfEdgeSet := by
  ext d
  refine ⟨fun ⟨e, he, hd⟩ ↦ ⟨e, (edgeSet_eq_of_isLink_iff h) ▸ he, hd⟩, fun ⟨e, he, hd⟩ ↦ ?_⟩
  exact ⟨e, (edgeSet_eq_of_isLink_iff h).symm ▸ he, hd⟩

@[ext]
lemma ext (hV : G₁.vertexSet = G₂.vertexSet) (hE : G₁.edgeSet = G₂.edgeSet)
    (hA : ∀ (d : β) (h₁ : d ∈ G₁.halfEdgeSet) (h₂ : d ∈ G₂.halfEdgeSet),
      G₁.attach ⟨d, h₁⟩ = G₂.attach ⟨d, h₂⟩) : G₁ = G₂ := by
  rcases G₁ with ⟨V₁, E₁, p₁, nd₁, a₁, m₁⟩
  rcases G₂ with ⟨V₂, E₂, p₂, nd₂, a₂, m₂⟩
  subst hV hE
  obtain rfl : p₁ = p₂ := Subsingleton.elim _ _
  obtain rfl : nd₁ = nd₂ := Subsingleton.elim _ _
  obtain rfl : a₁ = a₂ := by
    funext ⟨d, hd⟩
    exact hA d hd (by simpa [halfEdgeSet, Set.mem_setOf] using hd)
  exact congrArg (Graph.mk V₁ E₁ p₁ nd₁ a₁) (Subsingleton.elim m₁ m₂)

lemma edge_eq_across_graphs (hE : G₁.edgeSet = G₂.edgeSet) (h₁ : d ∈ G₁.halfEdgeSet)
    (h₂ : d ∈ G₂.halfEdgeSet) : G₁.edge ⟨d, h₁⟩ = G₂.edge ⟨d, h₂⟩ := by
  have he₂ : G₂.edge ⟨d, h₂⟩ ∈ G₁.edgeSet := hE.symm ▸ edge_mem_edgeSet ⟨d, h₂⟩
  exact (edge_eq_of_mem ⟨d, h₁⟩ he₂ <| mem_edge ⟨d, h₂⟩).symm

/-- Equality from vertex set, binary incidence, and agreement of `attach` on each dart.
Unary `Inc` alone does not determine the dart–vertex assignment `attach`. -/
lemma ext_isLink_attach (hV : G₁.vertexSet = G₂.vertexSet)
    (h : ∀ e x y, G₁.isLink e x y ↔ G₂.isLink e x y)
    (hA : ∀ (d : β) (h₁ : d ∈ G₁.halfEdgeSet) (h₂ : d ∈ G₂.halfEdgeSet),
      G₁.attach ⟨d, h₁⟩ = G₂.attach ⟨d, h₂⟩) : G₁ = G₂ :=
  ext hV (edgeSet_eq_of_isLink_iff h) hA

/-- `Graph.copy` produces a graph equal to `G` but with provided definitional choices
for `vertexSet`, `edgeSet`, and `IsLink`. This is mainly useful for improving
definitional equalities while keeping the same underlying graph. -/
@[simps]
def copy (G : Graph α β) {vertexSet : Set α} {edgeSet : Set (Sym2 β)}
    (hvertexSet : V(G) = vertexSet) (hedgeSet : E(G) = edgeSet) : Graph α β where
  vertexSet := vertexSet
  edgeSet := edgeSet
  edgeSet_pairwise_disjoint := by
    simp_rw [← hedgeSet]
    exact G.edgeSet_pairwise_disjoint
  edgeSet_not_isDiag := by
    simp_rw [← hedgeSet]
    exact G.edgeSet_not_isDiag
  attach := fun ⟨a, ha⟩ ↦ G.attach ⟨a, hedgeSet ▸ ha⟩
  attach_mem := by
    rintro _ ⟨⟨a, ha⟩, rfl⟩
    exact hvertexSet ▸ G.attach_mem ⟨⟨a, hedgeSet ▸ ha⟩, rfl⟩

@[simp]
lemma copy_eq (G : Graph α β) {V : Set α} {E : Set (Sym2 β)} (hV : V(G) = V) (hE : E(G) = E) :
    G.copy hV hE = G := by
  subst hV hE
  ext <;> simp_all

/-! ### Sets of edges or loops incident to a vertex -/

/-- `G.incidenceSet x` is the set of edges incident to `x` in `G`. -/
def incidenceSet (G : Graph α β) (x : α) : Set (Sym2 β) :=
  {e | G.Inc e x}

@[simp] theorem mem_incidenceSet (x : α) (e : Sym2 β) : e ∈ G.incidenceSet x ↔ G.Inc e x := Iff.rfl

theorem incidenceSet_subset_edgeSet (x : α) : G.incidenceSet x ⊆ E(G) := fun _ h ↦ Inc.edge_mem h

/-- `G.loopSet x` is the set of loops at `x` in `G`. -/
def loopSet (G : Graph α β) (x : α) : Set (Sym2 β) := {e | G.IsLoopAt e x}

@[simp] theorem mem_loopSet (x : α) (e : Sym2 β) : e ∈ G.loopSet x ↔ IsLoopAt G e x := Iff.rfl

theorem loopSet_subset_incidenceSet (x : α) : G.loopSet x ⊆ G.incidenceSet x := fun _ he ↦ ⟨x, he⟩

/-!
### Compatibility of Graphs

We define two graphs to be `Compatible` if for each edge belonging to their shared edge set,
the incidence relation (i.e., which pairs of vertices it links) is the same in both graphs.
-/

/-- Two graphs are compatible if their shared edges have the same ends in both graphs. -/
def Compatible (G H : Graph α β) : Prop :=
  ∀ ⦃e⦄, e ∈ E(G) → e ∈ E(H) → ∀ x y, G.isLink e x y ↔ H.isLink e x y

lemma Compatible.isLink_congr (heG : e ∈ E(G)) (heH : e ∈ E(H)) (h : G.Compatible H) :
    G.isLink e x y ↔ H.isLink e x y := h heG heH x y

lemma Compatible.refl (G : Graph α β) : G.Compatible G := fun _ _ _ _ _ => .rfl

@[simp] lemma Compatible.rfl : G.Compatible G := .refl G

instance : Std.Refl (Compatible : Graph α β → Graph α β → Prop) where
  refl _ := .rfl

@[symm]
lemma Compatible.symm (h : G.Compatible H) : H.Compatible G :=
  fun _ heH heG x y => (h heG heH x y).symm

instance : Std.Symm (Compatible : Graph α β → Graph α β → Prop) where
  symm _ _ := Compatible.symm

lemma isLink.of_compatible (hGH : G.Compatible H) (heH : e ∈ E(H)) (h : G.isLink e x y) :
    H.isLink e x y :=
  (hGH h.edge_mem heH x y).mp h

lemma Compatible.of_disjoint_edgeSet (h : Disjoint E(G) E(H)) : G.Compatible H :=
  fun _ heG heH _ _ ↦ absurd heH (disjoint_left.mp h heG)

lemma Inc.of_compatible (hGH : G.Compatible H) (heH : e ∈ E(H)) (h : G.Inc e x) : H.Inc e x := by
  obtain ⟨y, hy⟩ := h
  exact ⟨y, hy.of_compatible hGH heH⟩

lemma IsLoopAt.of_compatible (hGH : G.Compatible H) (heH : e ∈ E(H)) (h : G.IsLoopAt e x) :
    H.IsLoopAt e x :=
  isLink.of_compatible hGH heH h

lemma IsNonloopAt.of_compatible (hGH : G.Compatible H) (heH : e ∈ E(H)) (h : G.IsNonloopAt e x) :
    H.IsNonloopAt e x := by
  obtain ⟨y, hne, hy⟩ := h
  exact ⟨y, hne, hy.of_compatible hGH heH⟩

/-! ### Graphs with no edges -/

/-- The graph with vertex set `vertexSet` and no edges -/
@[simps (attr := grind =)]
def noEdge (vertexSet : Set α) (β : Type*) : Graph α β where
  vertexSet := vertexSet
  edgeSet := ∅
  edgeSet_pairwise_disjoint := by simp
  edgeSet_not_isDiag := by simp
  attach := by
    simp only [mem_empty_iff_false, false_and, exists_false, setOf_false]
    rintro ⟨i, hi⟩
    simp at hi
  attach_mem i hi := by simp at hi

variable {vertexSet : Set α} {edgeSet : Set β}

lemma edgeSet_eq_empty : E(G) = ∅ ↔ G = noEdge V(G) β :=
  ⟨fun h ↦ Graph.ext (by simp) h (by simp), fun h ↦ by rw [h, noEdge_edgeSet]⟩

end Graph
