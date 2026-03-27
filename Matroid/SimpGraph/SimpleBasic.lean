/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Sym.Sym2
public import Matroid.Graph.GraphLike.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.PFun

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
* `G.IsLink e x y` means that the edge `e : Sym2 β` has vertices `x : α` and `y : α` as its ends.
* `G.Inc e x` means that the edge `e` has `x` as one of its ends.
* `Adj G x y` means that the vertices `x` and `y` are adjacent in `G` (via `GraphLike`).
* `G.Adj d d'` is the `SimpleGraph β` adjacency on half-edges; it is not vertex adjacency.
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

variable {α β γ δ : Type*} {x y z u v w : α} {a b c d : β} {e f : Sym2 β}

open Set Sym2 GraphLike SimpleGraph

/-- A multigraph with vertices of type `α` and half-edges of type `β`,
specified by a simple graph on `β` (encoding which unordered pairs of half-edges form links),
a vertex set, and an `attach` map sending each half-edge that participates in some link to a vertex.
-/
structure Graph (α β : Type*) where
  /-- The vertex set. -/
  vertexSet : Set α
  /-- The relation pairing two half-edges. -/
  rel : β → β → Prop
  /-- The relation is symmetric. -/
  rel_symm : Std.Symm rel
  /-- The relation is irreflexive. -/
  rel_irrefl : Std.Irrefl rel
  /-- The relation is unique. -/
  rel_unique : ∀ ⦃a b c : β⦄, rel a b → rel a c → b = c
  /-- halfedge-vertex incidence -/
  IsBase : β → α → Prop
  /-- A half-edge is based on at most one vertex. -/
  IsBase_le_one : ∀ ⦃a x y⦄, IsBase a x → IsBase a y → x = y
  /-- A half-edge is based on a vertex must be paired with another half-edge. -/
  exists_rel_of_isBase : ∀ ⦃a⦄, (∃ x, IsBase a x) ↔ ∃ b, rel a b
  /-- Vertex set contains all base points of half-edges. -/
  mem_vertexSet_of_isBase : ∀ ⦃a x⦄, IsBase a x → x ∈ vertexSet


namespace Graph

variable {G G₁ G₂ H : Graph α β}

/-- `E(G)` is the set of links, as in `SimpleGraph.edgeSet` on the underlying half-edge graph. -/
def edgeSet (G : Graph α β) : Set (Sym2 β) := {s : Sym2 β | ∃ u v, G.rel u v ∧ s = s(u, v)}
@[inherit_doc edgeSet] scoped notation "E(" G ")" => Graph.edgeSet G

/-- `H(G)` denotes the `halfEdgeSet` of a graph `G`. -/
def halfEdgeSet (G : Graph α β) : Set β := SetRel.dom {(a, b) : β × β | G.rel a b}
@[inherit_doc halfEdgeSet] scoped notation "H(" G ")" => Graph.halfEdgeSet G

@[symm] lemma rel.symm (h : G.rel a b) : G.rel b a := G.rel_symm.symm _ _ h

@[mk_iff]
structure IsDart (G : Graph α β) (u : α) (a b : β) (v : α) : Prop where
  rel : G.rel a b
  left_base : u = G.base ⟨a, b, rel⟩
  right_base : v = G.base ⟨b, a, rel.symm⟩

lemma rel.isDart (h : G.rel a b) : G.IsDart (G.base ⟨a, b, h⟩) a b (G.base ⟨b, a, h.symm⟩) :=
  ⟨h, rfl, rfl⟩

lemma rel_eq_of_isDart_eq (h : ∀ u a b v, G₁.IsDart u a b v ↔ G₂.IsDart u a b v) :
    ∀ a b, G₁.rel a b ↔ G₂.rel a b := by
  simp_rw [isDart_iff] at h
  refine fun a b ↦ ⟨fun hrel ↦ ?_, fun hrel ↦ ?_⟩
  · obtain ⟨hrel', _, _⟩ := (h (G₁.base ⟨a, b, hrel⟩) a b (G₁.base ⟨b, a, hrel.symm⟩)).mp
      ⟨hrel, rfl, rfl⟩
    exact hrel'
  obtain ⟨hrel', _, _⟩ := (h (G₂.base ⟨a, b, hrel⟩) a b (G₂.base ⟨b, a, hrel.symm⟩)).mpr
    ⟨hrel, rfl, rfl⟩
  exact hrel'

@[ext]
lemma ext (G₁ G₂ : Graph α β) (hV : G₁.vertexSet = G₂.vertexSet)
    (hdart : ∀ u a b v, G₁.IsDart u a b v ↔ G₂.IsDart u a b v) : G₁ = G₂ := by
  have := rel_eq_of_isDart_eq hdart
  match G₁, G₂ with | .mk vertexSet_1 rel_1 rel_symm_1 base_1 base_mem_1 rel_irrefl_1, .mk vertexSet_2 rel_2 rel_symm_2 base_2 base_mem_2 rel_irrefl_2 => _
  subst hV
  obtain rfl : rel_1 = rel_2 := by
    funext a b
    grind
  simp [mk.injEq, coe_setOf, true_and]
  ext d
  obtain ⟨a, b, h⟩ := d
  sorry

def map (G : Graph α β) (f : α → γ) : Graph γ β where
  vertexSet := f '' G.vertexSet
  rel := G.rel
  rel_symm := G.rel_symm
  base := f ∘ G.base
  base_mem := range_comp _ _ ▸ (image_mono G.base_mem)
  rel_irrefl := G.rel_irrefl

structure Hom {α β γ δ : Type*} (G : Graph α β) (H : Graph γ δ) where
  fᵥ : α → γ
  fₑ : β → δ
  rel_le : ∀ {a b : β}, G.rel a b → H.rel (fₑ a) (fₑ b)
  base_comm : ∀ {a b : β} {ha : G.rel a b}, H.base ⟨fₑ a, fₑ b, rel_le ha⟩ = fᵥ (G.base ⟨a, b, ha⟩)

-- def Equiv' : Graph α β ≃ Graph' α (β × β) where
--   toFun G := {
--     vertexSet := G.vertexSet,
--     rel a b := G.rel a.fst b.fst ∧ a.swap = b
--     rel_symm := ⟨fun a b h ↦ ⟨h.1.symm, by grind⟩⟩
--     base := fun ⟨d, h⟩ ↦ G.base ⟨d.fst, d.snd, by simpa using h⟩
--     base_mem v := by grind [G.base_mem]
--     rel_irrefl := ⟨by simp [G.rel_irrefl.irrefl]⟩
--     rel_unique := by
--       rintro a b c ⟨hrel, rfl⟩ ⟨hrel', rfl⟩
--       rfl}
--   invFun G := {
--     vertexSet := G.vertexSet,
--     rel a b := G.rel (a, b) (b, a)
--     rel_symm := ⟨fun a b h ↦ G.rel_symm.symm _ _ h⟩
--     base := fun ⟨a, h⟩ ↦ G.base ⟨(a, h.choose), (h.choose, a), h.choose_spec⟩
--     base_mem v := by grind [G.base_mem]
--     rel_irrefl := ⟨by simp [G.rel_irrefl.irrefl]⟩}
--   left_inv G := by
--     ext
--     · simp
--     simp
--     sorry
--   right_inv G := by
--     cases G
--     simp
--     sorry



-- @[simp] theorem mem_halfEdgeSet_iff : d ∈ H(G) ↔ ∃ d', G.Adj d d' := G.mem_support

-- theorem Adj.left_mem (h : G.Adj a b) : a ∈ H(G) :=
--   mem_halfEdgeSet_iff.mpr ⟨b, h⟩

-- theorem Adj.right_mem (h : G.Adj a b) : b ∈ H(G) :=
--   mem_halfEdgeSet_iff.mpr ⟨a, G.adj_symm h⟩

-- /-- `attach` does not depend on which adjacent half-edge witnesses `d ∈ H(G)`. -/
-- lemma attach_eq_attach (G : Graph α β) (d : β) (h₁ h₂ : d ∈ H(G)) :
--     G.attach ⟨d, h₁⟩ = G.attach ⟨d, h₂⟩ :=
--   congrArg G.attach (Subtype.ext rfl)

-- @[simp] theorem inv_mem_iff : d ∈ H(G) ↔ ∃ e ∈ G.edgeSet, d ∈ e := by
--   rw [mem_halfEdgeSet_iff]
--   constructor
--   · rintro ⟨d', h⟩
--     refine ⟨s(d, d'), (SimpleGraph.mem_edgeSet (G := G.toSimpleGraph)).2 h, mem_mk_left d d'⟩
--   · rintro ⟨e, he, hd⟩
--     refine ⟨Mem.other hd, (SimpleGraph.mem_edgeSet (G := G.toSimpleGraph)).1 ?_⟩
--     simpa [Sym2.other_spec hd] using he

-- noncomputable def attach' (G : Graph α β) : H(G) → G.vertexSet :=
--   fun h ↦ ⟨G.attach h, G.attach_mem (mem_range_self h)⟩

-- @[simp] theorem attach'_coe (b : H(G)) : (G.attach' b).val = G.attach b := rfl

-- /-! ### The graph-like structure -/

-- /-- The dart oriented from the half-edge `b` toward `G.inv' b`. -/
-- noncomputable def dartOf (G : Graph α β) (h : G.Adj a b) : (β × α) × (β × α) :=
--   ((a, (G.attach' ⟨a, b, h⟩).val), (b, (G.attach' ⟨b, a, h.symm⟩)))

-- instance : DartLike α ((β × α) × (β × α)) where
--   fst d := d.1.2
--   snd d := d.2.2

-- noncomputable instance : GraphLike α ((β × α) × (β × α)) (Graph α β) where
--   verts G := G.vertexSet
--   darts G := {d | ∃ (a b : β) (h : G.Adj a b), d = G.dartOf h}
--   fst_mem_of_darts {G d} h := by
--     obtain ⟨a, b, h, rfl⟩ := h
--     simp only [DartLike.fst, dartOf, attach'_coe]
--     exact G.attach_mem (mem_range_self _)
--   snd_mem_of_darts {G d} h := by
--     obtain ⟨a, b, h, rfl⟩ := h
--     simp only [DartLike.snd, dartOf, attach'_coe]
--     exact G.attach_mem (mem_range_self _)
--   Adj G u v := ∃ (a b : β) (h : G.Adj a b), u = G.attach ⟨a, b, h⟩ ∧ v = G.attach ⟨b, a, h.symm⟩
--   exists_darts_iff_adj {G u v} := by
--     constructor
--     · rintro ⟨d, ⟨a, b, h, rfl⟩, rfl, rfl⟩
--       exact ⟨a, b, h, rfl, rfl⟩
--     · rintro ⟨a, b, h, rfl, rfl⟩
--       exact ⟨dartOf G h, ⟨a, b, h, rfl⟩, rfl, rfl⟩

-- @[simp] lemma verts_eq (G : Graph α β) : G.vertexSet = V(G) := rfl
-- @[simp] lemma darts_eq (G : Graph α β) :
--   darts G = {d | ∃ (a b : β) (h : G.Adj a b), d = G.dartOf h} := rfl

-- /-! ### Binary incidence -/

-- def IsLink (G : Graph α β) (e : Sym2 β) (x y : α) : Prop :=
--   ∃ (a b : β) (h : G.Adj a b), e = s(a, b) ∧ x = G.attach ⟨a, b, h⟩ ∧ y = G.attach ⟨b, a, h.symm⟩

-- /-! ### The edge set (primitive `edgeSet`) -/

-- theorem mem_edgeSet_iff_exists_adj : e ∈ G.edgeSet ↔ ∃ (a b : β), G.Adj a b ∧ e = s(a, b) := by
--   refine Sym2.ind (fun x y => ?_) e
--   constructor
--   · intro hxy
--     exact ⟨x, y, (SimpleGraph.mem_edgeSet (G := G.toSimpleGraph)).1 hxy, rfl⟩
--   · rintro ⟨a, b, hab, he⟩
--     rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
--     · exact G.mem_edgeSet.2 hab
--     · exact G.mem_edgeSet.2 hab.symm

-- /-! ### Incidence predicate `isLink` -/

-- instance : Std.Symm (G.IsLink e) where
--   symm x y h := by
--     obtain ⟨a, b, hab, he, hx, hy⟩ := h
--     refine ⟨b, a, hab.symm, ?_, ?_, ?_⟩
--     · rw [he, eq_swap]
--     · exact hy
--     · exact hx

-- theorem IsLink.edge_mem (h : G.IsLink e x y) : e ∈ E(G) := by
--   obtain ⟨a, b, hab, rfl, -, -⟩ := h
--   exact (SimpleGraph.mem_edgeSet (G := G.toSimpleGraph)).2 hab

-- @[simp]
-- lemma not_isLink_of_notMem_edgeSet (he : e ∉ E(G)) : ¬ G.IsLink e x y :=
--   mt IsLink.edge_mem he

-- @[symm] theorem IsLink.symm (h : G.IsLink e x y) : G.IsLink e y x := symm_of (G.IsLink e) h

-- theorem IsLink.left_mem (h : G.IsLink e x y) : x ∈ G.vertexSet := by
--   obtain ⟨a, b, hab, -, rfl, -⟩ := h
--   let ha : H(G) := ⟨a, Adj.left_mem hab⟩
--   exact G.attach_mem (mem_range_self ha)

-- theorem IsLink.right_mem (h : G.IsLink e x y) : y ∈ G.vertexSet := h.symm.left_mem

-- lemma isLink_comm : G.IsLink e x y ↔ G.IsLink e y x := ⟨.symm, .symm⟩

-- theorem isLink_of_adj (h : G.Adj a b) :
--     G.IsLink (s(a, b)) (G.attach ⟨a, Adj.left_mem h⟩)
--       (G.attach ⟨b, Adj.right_mem h⟩) :=
--   ⟨a, b, h, rfl, rfl, rfl⟩

-- theorem mem_edgeSet_iff_exists_isLink : e ∈ E(G) ↔ ∃ x y, G.IsLink e x y := by
--   constructor
--   · intro he
--     obtain ⟨a, b, hab, rfl⟩ := (mem_edgeSet_iff_exists_adj).1 he
--     exact ⟨_, _, isLink_of_adj hab⟩
--   · rintro ⟨x, y, h⟩; exact h.edge_mem

-- lemma exists_isLink_of_mem_edgeSet (he : e ∈ E(G)) : ∃ x y, G.IsLink e x y :=
--   mem_edgeSet_iff_exists_isLink.1 he

-- lemma edgeSet_eq_setOf_exists_isLink : E(G) = {e | ∃ x y, G.IsLink e x y} :=
--   Set.ext fun _ ↦ mem_edgeSet_iff_exists_isLink

-- theorem IsLink.left_eq_or_eq (h : G.IsLink e x y) (h' : G.IsLink e z w) : x = z ∨ x = w := by
--   obtain ⟨a, b, hab, rfl, rfl, rfl⟩ := h
--   obtain ⟨c, d, hcd, hs, rfl, rfl⟩ := h'
--   grind

-- theorem IsLink.right_eq_or_eq (h : G.IsLink e x y) (h' : G.IsLink e z w) : y = z ∨ y = w :=
--   h.symm.left_eq_or_eq h'

-- theorem IsLink.left_eq_of_right_ne (h : G.IsLink e x y) (h' : G.IsLink e z w) (hzx : x ≠ z) :
--     x = w :=
--   (h.left_eq_or_eq h').elim (False.elim ∘ hzx) id

-- theorem IsLink.right_unique (h : G.IsLink e x y) (h' : G.IsLink e x z) : y = z := by
--   obtain rfl | rfl := h.right_eq_or_eq h'.symm
--   · rfl
--   obtain rfl | rfl := h'.right_eq_or_eq h.symm <;> rfl

-- theorem IsLink.left_unique (h : G.IsLink e x z) (h' : G.IsLink e y z) : x = y :=
--   h.symm.right_unique h'.symm

-- theorem IsLink.eq_and_eq_or_eq_and_eq {x' y' : α} (h : G.IsLink e x y) (h' : G.IsLink e x' y') :
--     (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
--   obtain rfl | rfl := h.left_eq_or_eq h'
--   · simp [h.right_unique h']
--   · simp [h'.symm.right_unique h]

-- theorem IsLink.isLink_iff (h : G.IsLink e x y) {x' y' : α} :
--     G.IsLink e x' y' ↔ (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
--   refine ⟨h.eq_and_eq_or_eq_and_eq, ?_⟩
--   rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
--   · assumption
--   · exact h.symm

-- theorem IsLink.isLink_iff_sym2_eq (h : G.IsLink e x y) {x' y' : α} :
--     G.IsLink e x' y' ↔ s(x, y) = s(x', y') := by
--   rw [h.isLink_iff, Sym2.eq_iff]

-- lemma isLink_attach {a b : β} (hab : G.Adj a b) :
--     G.IsLink (s(a, b)) (G.attach ⟨a, b, hab⟩) (G.attach ⟨b, a, hab.symm⟩) :=
--   ⟨a, b, hab, rfl, rfl, rfl⟩

-- /-! ### Edge-vertex incidence -/

-- /-- The unary incidence predicate of `G`. `G.Inc e x` means that the vertex `x`
-- is one or both of the ends of the edge `e`.
-- In the `Inc` namespace, we use `edge` and `vertex` to refer to `e` and `x`. -/
-- def Inc (G : Graph α β) (e : Sym2 β) (x : α) : Prop :=
--   ∃ y, G.IsLink e x y

-- lemma Inc.edge_mem (h : G.Inc e x) : e ∈ E(G) := h.choose_spec.edge_mem

-- @[simp] lemma not_inc_of_notMem_edgeSet (he : e ∉ E(G)) : ¬G.Inc e x := mt Inc.edge_mem he

-- lemma Inc.vertex_mem (h : G.Inc e x) : x ∈ V(G) := h.choose_spec.left_mem

-- lemma IsLink.inc_left (h : G.IsLink e x y) : G.Inc e x := ⟨y, h⟩

-- lemma IsLink.inc_right (h : G.IsLink e x y) : G.Inc e y := ⟨x, h.symm⟩

-- lemma Inc.eq_or_eq_of_isLink (h : G.Inc e x) (h' : G.IsLink e y z) : x = y ∨ x = z :=
--   h.choose_spec.left_eq_or_eq h'

-- lemma Inc.eq_of_isLink_of_ne_left (h : G.Inc e x) (h' : G.IsLink e y z) (hxy : x ≠ y) : x = z :=
--   (h.eq_or_eq_of_isLink h').elim (False.elim ∘ hxy) id

-- lemma IsLink.IsLink_iff_eq (h : G.IsLink e x y) : G.IsLink e x z ↔ z = y :=
--   ⟨fun h' ↦ h'.right_unique h, fun h' ↦ h' ▸ h⟩

-- lemma isLink_iff_inc : G.IsLink e x y ↔ G.Inc e x ∧ G.Inc e y ∧ ∀ z, G.Inc e z → z = x ∨ z = y := by
--   refine ⟨fun h ↦ ⟨h.inc_left, h.inc_right, fun z h' ↦ h'.choose_spec.left_eq_or_eq h⟩, ?_⟩
--   rintro ⟨⟨x', hx'⟩, ⟨y', hy'⟩, h⟩
--   obtain rfl | rfl := h _ hx'.inc_right
--   · obtain rfl | rfl := hx'.left_eq_or_eq hy'
--     · assumption
--     exact hy'.symm
--   assumption

-- /-- Given a proof that the edge `e` is incident with the vertex `x` in `G`,
-- noncomputably find the other end of `e`. (If `e` is a loop, this is equal to `x` itself). -/
-- protected noncomputable def Inc.other (h : G.Inc e x) : α := h.choose

-- @[simp] lemma Inc.IsLink_other (h : G.Inc e x) : G.IsLink e x h.other := h.choose_spec

-- @[simp] lemma Inc.inc_other (h : G.Inc e x) : G.Inc e h.other := h.IsLink_other.inc_right

-- lemma Inc.eq_or_eq_or_eq (hx : G.Inc e x) (hy : G.Inc e y) (hz : G.Inc e z) :
--     x = y ∨ x = z ∨ y = z := by
--   by_contra! ⟨hxy, hxz, hyz⟩
--   obtain ⟨x', hx'⟩ := hx
--   obtain rfl := hy.eq_of_isLink_of_ne_left hx' hxy.symm
--   obtain rfl := hz.eq_of_isLink_of_ne_left hx' hxz.symm
--   exact hyz rfl

-- lemma inc_eq_inc_iff_isLink_eq_isLink :
--     (∀ x, G₁.Inc e x ↔ G₂.Inc f x) ↔ (∀ x y, G₁.IsLink e x y ↔ G₂.IsLink f x y) := by
--   refine ⟨fun h x y ↦ ?_, fun h x ↦ exists_congr (h x)⟩
--   simp_rw [isLink_iff_inc, h]

-- /-! ### Loops and non-loops -/

-- /-- `G.IsLoopAt e x` means that both ends of the edge `e` are equal to the vertex `x`. -/
-- def IsLoopAt (G : Graph α β) (e : Sym2 β) (x : α) : Prop := G.IsLink e x x

-- @[simp] lemma isLink_self_iff : G.IsLink e x x ↔ G.IsLoopAt e x := Iff.rfl

-- lemma IsLoopAt.inc (h : G.IsLoopAt e x) : G.Inc e x := IsLink.inc_left h

-- lemma IsLoopAt.eq_of_inc (h : G.IsLoopAt e x) (h' : G.Inc e y) : x = y := by
--   obtain rfl | rfl := h'.eq_or_eq_of_isLink h <;> rfl

-- lemma IsLoopAt.edge_mem (h : G.IsLoopAt e x) : e ∈ E(G) := h.inc.edge_mem

-- lemma IsLoopAt.vertex_mem (h : G.IsLoopAt e x) : x ∈ Graph.vertexSet G := h.inc.vertex_mem

-- /-- `G.IsNonloopAt e x` means that the vertex `x` is one but not both of the ends of the edge `e`,
-- as witnessed by some `isLink` to a vertex different from `x`. -/
-- def IsNonloopAt (G : Graph α β) (e : Sym2 β) (x : α) : Prop := ∃ y ≠ x, G.IsLink e x y

-- lemma IsNonloopAt.inc (h : G.IsNonloopAt e x) : G.Inc e x := h.choose_spec.2.inc_left

-- lemma IsNonloopAt.edge_mem (h : G.IsNonloopAt e x) : e ∈ E(G) := h.inc.edge_mem

-- lemma IsNonloopAt.vertex_mem (h : G.IsNonloopAt e x) : x ∈ Graph.vertexSet G := h.inc.vertex_mem

-- lemma IsLoopAt.not_isNonloopAt (h : G.IsLoopAt e x) (y : α) : ¬G.IsNonloopAt e y := by
--   rintro ⟨z, hyz, hy⟩
--   rw [← h.eq_of_inc hy.inc_left, ← h.eq_of_inc hy.inc_right] at hyz
--   exact hyz rfl

-- lemma IsNonloopAt.not_isLoopAt (h : G.IsNonloopAt e x) (y : α) : ¬G.IsLoopAt e y :=
--   fun h' ↦ h'.not_isNonloopAt x h

-- lemma isNonloopAt_iff_inc_not_isLoopAt : G.IsNonloopAt e x ↔ G.Inc e x ∧ ¬G.IsLoopAt e x :=
--   ⟨fun h ↦ ⟨h.inc, h.not_isLoopAt _⟩, fun ⟨⟨y, hy⟩, hn⟩ ↦ ⟨y, mt (fun h' ↦ h' ▸ hy) hn, hy⟩⟩

-- lemma Inc.isLoopAt_or_isNonloopAt (h : G.Inc e x) : G.IsLoopAt e x ∨ G.IsNonloopAt e x := by
--   rw [isNonloopAt_iff_inc_not_isLoopAt]
--   by_cases hl : G.IsLoopAt e x
--   · exact Or.inl hl
--   · exact Or.inr ⟨h, hl⟩

-- lemma isLoopAt_iff_inc_not_isNonloopAt : G.IsLoopAt e x ↔ G.Inc e x ∧ ¬ G.IsNonloopAt e x := by
--   refine ⟨fun h ↦ ⟨h.inc, fun h' ↦ h'.not_isLoopAt x h⟩, fun ⟨hinc, hn⟩ ↦ ?_⟩
--   obtain hl | hnl := hinc.isLoopAt_or_isNonloopAt
--   · assumption
--   exact absurd hnl hn

-- instance (G : Graph α β) : Std.Symm (Adj G) where
--   symm _ _ := fun ⟨a, b, h, hu, hv⟩ ↦ ⟨b, a, h.symm, hv, hu⟩

-- theorem adj_iff_exists_isLink : Adj G u v ↔ ∃ e, G.IsLink e u v := by
--   rw [← exists_darts_iff_adj]
--   constructor
--   · rintro ⟨d, ⟨a, b, hab, rfl⟩, rfl, rfl⟩
--     exact ⟨s(a, b), isLink_of_adj hab⟩
--   · rintro ⟨e, a, b, hab, he, rfl, rfl⟩
--     exact ⟨dartOf G hab, ⟨a, b, hab, rfl⟩, rfl, rfl⟩

-- theorem IsLink.adj (h : G.IsLink e x y) : Adj G x y := by
--   rw [adj_iff_exists_isLink]
--   exact ⟨e, h⟩

-- /-! ### Extensionality and compatibility -/

-- lemma edgeSet_eq_of_isLink_iff (h : ∀ e x y, G₁.IsLink e x y ↔ G₂.IsLink e x y) :
--     G₁.edgeSet = G₂.edgeSet := by
--   ext e
--   rw [mem_edgeSet_iff_exists_isLink, mem_edgeSet_iff_exists_isLink]
--   exact exists₂_congr (h e)

-- lemma halfEdgeSet_eq_of_isLink_iff (h : ∀ e x y, G₁.IsLink e x y ↔ G₂.IsLink e x y) :
--     G₁.halfEdgeSet = G₂.halfEdgeSet := by
--   have hE := edgeSet_eq_of_isLink_iff h
--   ext d
--   simp_rw [mem_halfEdgeSet_iff, ← SimpleGraph.mem_edgeSet, hE]

-- @[ext]
-- lemma ext (hV : G₁.vertexSet = G₂.vertexSet) (hE : G₁.edgeSet = G₂.edgeSet)
--     (hA : ∀ (d : β) (h₁ : d ∈ G₁.halfEdgeSet) (h₂ : d ∈ G₂.halfEdgeSet),
--       G₁.attach ⟨d, h₁⟩ = G₂.attach ⟨d, h₂⟩) : G₁ = G₂ := by
--   obtain ⟨sg₁, V₁, a₁, m₁⟩ := G₁
--   obtain ⟨sg₂, V₂, a₂, m₂⟩ := G₂
--   cases SimpleGraph.edgeSet_injective hE
--   subst hV
--   congr
--   · funext ⟨d, hd⟩
--     exact hA d hd (by simpa using hd)

-- /-- Equality from vertex set, binary incidence, and agreement of `attach` on each dart.
-- Unary `Inc` alone does not determine the dart–vertex assignment `attach`. -/
-- lemma ext_isLink_attach (hV : G₁.vertexSet = G₂.vertexSet)
--     (h : ∀ e x y, G₁.IsLink e x y ↔ G₂.IsLink e x y)
--     (hA : ∀ (d : β) (h₁ : d ∈ G₁.halfEdgeSet) (h₂ : d ∈ G₂.halfEdgeSet),
--       G₁.attach ⟨d, h₁⟩ = G₂.attach ⟨d, h₂⟩) : G₁ = G₂ :=
--   ext hV (edgeSet_eq_of_isLink_iff h) hA

-- /-- `Graph.copy` produces a graph equal to `G` but with provided definitional choices for
-- `vertexSet` and `edgeSet` (the latter only as a proposition; the underlying `SimpleGraph` is
-- unchanged). This is mainly useful for improving definitional equalities while keeping the same
-- underlying graph. -/
-- def copy (G : Graph α β) {vertexSet : Set α}
--     (hvertexSet : V(G) = vertexSet) : Graph α β where
--   toSimpleGraph := G.toSimpleGraph
--   vertexSet := vertexSet
--   attach := fun ⟨d, ha⟩ ↦ G.attach ⟨d, ha⟩
--   attach_mem := by
--     intro x hx
--     rcases Set.mem_range.mp hx with ⟨y, rfl⟩
--     rcases y with ⟨d, ha⟩
--     exact hvertexSet ▸ G.attach_mem (mem_range_self (f := G.attach) ⟨d, ha⟩)

-- @[simp]
-- lemma copy_eq (G : Graph α β) {V : Set α} (hV : V(G) = V):
--     G.copy hV = G :=
--   ext hV.symm rfl fun _ _ _ ↦ rfl

-- /-! ### Sets of edges or loops incident to a vertex -/

-- /-- `G.incidenceSet x` is the set of edges incident to `x` in `G`. -/
-- def incidenceSet (G : Graph α β) (x : α) : Set (Sym2 β) :=
--   {e | G.Inc e x}

-- @[simp] theorem mem_incidenceSet (x : α) (e : Sym2 β) : e ∈ G.incidenceSet x ↔ G.Inc e x := Iff.rfl

-- theorem incidenceSet_subset_edgeSet (x : α) : G.incidenceSet x ⊆ E(G) := fun _ ↦ Inc.edge_mem

-- /-- `G.loopSet x` is the set of loops at `x` in `G`. -/
-- def loopSet (G : Graph α β) (x : α) : Set (Sym2 β) := {e | G.IsLoopAt e x}

-- @[simp] theorem mem_loopSet (x : α) (e : Sym2 β) : e ∈ G.loopSet x ↔ IsLoopAt G e x := Iff.rfl

-- theorem loopSet_subset_incidenceSet (x : α) : G.loopSet x ⊆ G.incidenceSet x := fun _ he ↦ ⟨x, he⟩

-- /-!
-- ### Compatibility of Graphs

-- We define two graphs to be `Compatible` if for each edge belonging to their shared edge set,
-- the incidence relation (i.e., which pairs of vertices it links) is the same in both graphs.
-- -/

-- /-- Two graphs are compatible if their shared edges have the same ends in both graphs. -/
-- def Compatible (G H : Graph α β) : Prop :=
--   ∀ ⦃e⦄, e ∈ E(G) → e ∈ E(H) → ∀ x y, G.IsLink e x y ↔ H.IsLink e x y

-- lemma Compatible.IsLink_congr (heG : e ∈ E(G)) (heH : e ∈ E(H)) (h : G.Compatible H) :
--     G.IsLink e x y ↔ H.IsLink e x y := h heG heH x y

-- lemma Compatible.refl (G : Graph α β) : G.Compatible G := fun _ _ _ _ _ => .rfl

-- @[simp] lemma Compatible.rfl : G.Compatible G := .refl G

-- instance : Std.Refl (Compatible : Graph α β → Graph α β → Prop) where
--   refl _ := .rfl

-- @[symm]
-- lemma Compatible.symm (h : G.Compatible H) : H.Compatible G :=
--   fun _ heH heG x y => (h heG heH x y).symm

-- instance : Std.Symm (Compatible : Graph α β → Graph α β → Prop) where
--   symm _ _ := Compatible.symm

-- lemma IsLink.of_compatible (hGH : G.Compatible H) (heH : e ∈ E(H)) (h : G.IsLink e x y) :
--     H.IsLink e x y :=
--   (hGH h.edge_mem heH x y).mp h

-- lemma Compatible.of_disjoint_edgeSet (h : Disjoint E(G) E(H)) : G.Compatible H :=
--   fun _ heG heH _ _ ↦ absurd heH (disjoint_left.mp h heG)

-- lemma Inc.of_compatible (hGH : G.Compatible H) (heH : e ∈ E(H)) (h : G.Inc e x) : H.Inc e x := by
--   obtain ⟨y, hy⟩ := h
--   exact ⟨y, hy.of_compatible hGH heH⟩

-- lemma IsLoopAt.of_compatible (hGH : G.Compatible H) (heH : e ∈ E(H)) (h : G.IsLoopAt e x) :
--     H.IsLoopAt e x :=
--   IsLink.of_compatible hGH heH h

-- lemma IsNonloopAt.of_compatible (hGH : G.Compatible H) (heH : e ∈ E(H)) (h : G.IsNonloopAt e x) :
--     H.IsNonloopAt e x := by
--   obtain ⟨y, hne, hy⟩ := h
--   exact ⟨y, hne, hy.of_compatible hGH heH⟩

-- /-! ### Graphs with no edges -/

-- /-- The graph with vertex set `vertexSet` and no edges -/
-- def noEdge (vertexSet : Set α) (β : Type*) : Graph α β where
--   toSimpleGraph := ⊥
--   vertexSet := vertexSet
--   attach := fun ⟨d, hd⟩ ↦ False.elim (by simp at hd)
--   attach_mem := by
--     intro x hx
--     rcases Set.mem_range.mp hx with ⟨y, rfl⟩
--     rcases y with ⟨d, hd⟩
--     exact False.elim (by simp at hd)

-- @[simp]
-- lemma noEdge_edgeSet (vertexSet : Set α) (β : Type*) : E(noEdge vertexSet β) = ∅ := by
--   simp [edgeSet, noEdge, SimpleGraph.edgeSet_bot]

-- variable {vertexSet : Set α}

-- lemma edgeSet_eq_empty : E(G) = ∅ ↔ G = noEdge V(G) β := by
--   refine ⟨fun h ↦ ?_, fun he ↦ ?_⟩
--   · have hbot : G.toSimpleGraph = ⊥ :=
--       (SimpleGraph.edgeSet_eq_empty (G := G.toSimpleGraph)).1 (by simpa [edgeSet] using h)
--     refine ext rfl (by simp [edgeSet, hbot, noEdge, SimpleGraph.edgeSet_bot]) ?_
--     intro d h₁ h₂
--     exact False.elim (by simp [hbot] at h₁)
--   rw [he, noEdge_edgeSet]

-- end Graph
