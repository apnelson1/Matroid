/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Jun Kwon
-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sym.Sym2
import Matroid.ForMathlib.Partition.Set

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

## Vertex and Label

The vertex set of a multigraph is a term in `Partition (Set α)`.
Hence a vertex has a type `Set α` and the elements inside are called *labels* of that vertex.
The fact that the vertices form a partition means that a label only represents one vertex.

Although the `Set α` are vertices not labels, most of the API is written in terms of labels.
This is because, when it comes to contraction/minors, vertices may be merged to some larger
set and become a different object, your favorite label for that vertex still represents the
supervertex so you can 'pretend' that they are 'the same' vertex.

`Partition (Set α)` can be cast to both `Set (Set α)` and `α → α → Prop`.
The former can be interpreted as the set of vertices.
The latter as a relation on labels whether they represent the same vertex or not.
In other words, whether they are `dup`licate labels or not.

## Main definitions

For `G : Graph α β`, ...

* `V(G)` denotes the vertex set of `G` as a term in `Partition (Set α)`.
* `E(G)` denotes the edge set of `G` as a term in `Set β`.
* `G.IsLink e x y` means that the edge `e : β` has vertices `x : α` and `y : α` as its ends.
* `G.Inc e x` means that the edge `e : β` has `x` as one of its ends.
* `G.Adj x y` means that there is an edge `e` having `x` and `y` as its ends.
* `G.IsLoopAt e x` means that `e` is a loop edge with both ends equal to `x`.
* `G.IsNonloopAt e x` means that `e` is a non-loop edge with one end equal to `x`.

## Implementation notes

Unlike the design of `SimpleGraph`, the vertex and edge sets of `G` are modelled as sets
`V(G) : Partition (Set α)` and `E(G) : Set β`, within ambient types,
rather than being types themselves.
This mimics the 'embedded set' design used in `Matroid`, which seems to be more convenient for
formalizing real-world proofs in combinatorics.

A specific advantage is that this allows subgraphs of `G : Graph α β` to also exist on
an equal footing with `G` as terms in `Graph α β`,
and so there is no need for a `Graph.subgraph` type and all the associated
definitions and canonical coercion maps. The same will go for minors and the various other
partial orders on multigraphs.

The main tradeoff is that parts of the API will need to care about whether a term
`a : α`, `v : Set α`, or `e : β` is a 'real' label, vertex, or edge of the graph,
rather than something outside the vertex or edge set.
This is an issue, but is likely amenable to automation.

## Notation

Reflecting written mathematics, we use the compact notations `V(G)` and `E(G)` to
refer to the `vertexSet` and `edgeSet` of `G : Graph α β`.
If `G.IsLink e x y` then we refer to `e` as `edge` and `x` and `y` as `left` and `right` in names.
-/

variable {α β : Type*} {a b c x y z u v w : α} {e f : β} {P Q : Partition (Set α)} {S : Set α}

open Set Relation Partition

def btwVx (P : Partition (Set α)) (l : α → α → Prop) : Prop :=
  ∀ ⦃a b c d⦄, l a b → l c d → P a c ∨ P a d

lemma btwVx_mono_left (hP : P ≤ Q) {l : α → α → Prop} (h : btwVx P l) :
    btwVx Q l := fun _ _ _ _ hab hcd ↦ (h hab hcd).imp (rel_le_of_le hP _ _) (rel_le_of_le hP _ _)

lemma btwVx_anti_right {l l' : α → α → Prop} (hle : l ≤ l')
    (h : btwVx P l') : btwVx P l := fun _ _ _ _ hab hcd ↦ h (hle _ _ hab) (hle _ _ hcd)

@[simp]
lemma btwVx_induce_iff {l : α → α → Prop} [IsSymm α l] :
    btwVx (P.induce S) l ↔ btwVx P l ∧ ∀ ⦃a b⦄, l a b → a ∈ S ∧ b ∈ S := by
  refine ⟨fun h => ⟨fun a b c d hab hcd ↦ (h hab hcd).imp (by simp) (by simp), fun a b hab ↦ ?_⟩,
    fun ⟨h, h'⟩ a b c d hab hcd => ?_⟩
  · obtain ha | ha := h hab hab <;> obtain hb | hb := h (symm hab) (symm hab) <;> simp_all
  have ⟨ha, hb⟩ := h' hab
  have ⟨hc, hd⟩ := h' hcd
  apply (h hab hcd).imp <;> simp_all

lemma btwVx_restrict {l : α → α → Prop} [IsSymm α l] (hbtw : btwVx P l) :
    btwVx (P.induce S) (restrict l S) := fun a b c d ⟨hab, ha, hb⟩ ⟨hcd, hc, hd⟩ ↦
  (hbtw hab hcd).imp (by simp [ha, hc]) (by simp [ha, hd])

/-- A multigraph with vertices of type `α` and edges of type `β`,
as described by vertex and edge sets `vertexSet : Partition (Set α)` and `edgeSet : Set β`,
and a predicate `IsLink` describing whether an edge `e : β` has labels `x y : α` as its ends.

The `edgeSet` structure field can be inferred from `IsLink`
via `edge_mem_iff_exists_isLink` (and this structure provides default values
for `edgeSet` and `edge_mem_iff_exists_isLink` that use `IsLink`).
While the field is not strictly necessary, when defining a graph we often
immediately know what the edge set should be,
and furthermore having `edgeSet` separate can be convenient for
definitional equality reasons.
-/
structure Graph (α β : Type*) where
  /-- The vertex set. -/
  vertexSet : Partition (Set α)
  /-- The binary incidence predicate, stating that `x` and `y` are the ends of an edge `e`.
  If `G.IsLink e x y` then we refer to `e` as `edge` and `x` and `y` as `left` and `right`. -/
  IsLink : β → α → α → Prop
  /-- The edge set. -/
  edgeSet : Set β := {e | ∃ x y, IsLink e x y}
  /-- If `e` goes from `x` to `y`, it goes from `y` to `x`. -/
  isLink_symm : ∀ ⦃e⦄, e ∈ edgeSet → (Symmetric <| IsLink e)
  /-- An edge is incident with at most one pair of vertices. -/
  dup_or_dup_of_isLink_of_isLink : ∀ ⦃e⦄, btwVx vertexSet (IsLink e)
  /-- An edge `e` is incident to something if and only if `e` is in the edge set. -/
  edge_mem_iff_exists_isLink : ∀ ⦃e⦄, e ∈ edgeSet ↔ ∃ x y, IsLink e x y := by exact fun _ ↦ Iff.rfl
  /-- If some edge `e` is incident to `x`, then `x` is a label of some vertex. -/
  mem_vertexSet_of_isLink : ∀ ⦃e x y⦄, IsLink e x y → ∃ v ∈ vertexSet, x ∈ v
  /-- If `x` and `y` represent the same vertex, it has the same incidence relation. -/
  isLink_of_dup : ∀ ⦃e x y z⦄, vertexSet x y → IsLink e y z → IsLink e x z

initialize_simps_projections Graph (IsLink → isLink)

namespace Graph

variable {G : Graph α β}

/-- `V(G)` denotes the `vertexSet` of a graph `G`. -/
scoped notation "V(" G ")" => Graph.vertexSet G

/-- `E(G)` denotes the `edgeSet` of a graph `G`. -/
scoped notation "E(" G ")" => Graph.edgeSet G

/-- `L(G)` denotes the `labelSet` of a graph `G`. -/
scoped notation "L(" G ")" => Partition.supp V(G)

/-! ### Edge-vertex-vertex incidence -/

lemma IsLink.edge_mem (h : G.IsLink e x y) : e ∈ E(G) :=
  (edge_mem_iff_exists_isLink ..).2 ⟨x, y, h⟩

@[simp] protected lemma IsLink.symm (h : G.IsLink e x y) : G.IsLink e y x :=
  G.isLink_symm h.edge_mem h

instance : IsSymm α (G.IsLink e) where
  symm _ _ huv := huv.symm

lemma IsLink.dup_left (h : G.IsLink e x y) (hrel : V(G) x z) : G.IsLink e z y :=
  G.isLink_of_dup (symm hrel) h

lemma IsLink.dup_right (h : G.IsLink e x y) (hrel : V(G) y z) : G.IsLink e x z :=
  h.symm.dup_left hrel |>.symm

instance : Trans V(G) (G.IsLink e) (G.IsLink e) where
  trans hxy := G.isLink_of_dup hxy

lemma isLink_left_rw (h : V(G) x y) : G.IsLink e x z ↔ G.IsLink e y z :=
  left_rw _ h

lemma isLink_right_rw (h : V(G) x y) : G.IsLink e z x ↔ G.IsLink e z y :=
  right_rw _ h

@[simp] lemma IsLink.left_mem_vertex (h : G.IsLink e x y) : ∃ v ∈ V(G), x ∈ v :=
  G.mem_vertexSet_of_isLink h

@[simp] lemma IsLink.right_mem_vertex (h : G.IsLink e x y) : ∃ v ∈ V(G), y ∈ v :=
  h.symm.left_mem_vertex

@[simp] lemma IsLink.left_mem (h : G.IsLink e x y) : x ∈ L(G) :=
  mem_supp_iff.mpr h.left_mem_vertex

@[simp] lemma IsLink.right_mem (h : G.IsLink e x y) : y ∈ L(G) :=
  mem_supp_iff.mpr h.right_mem_vertex

@[simp] lemma IsLink.left_refl (h : G.IsLink e x y) : V(G) x x := by
  obtain ⟨v, hv, hx⟩ := h.left_mem_vertex
  use v

@[simp] lemma IsLink.right_refl (h : G.IsLink e x y) : V(G) y y := h.symm.left_refl

lemma isLink_comm : G.IsLink e x y ↔ G.IsLink e y x :=
  comm

lemma exists_isLink_of_mem_edgeSet (h : e ∈ E(G)) : ∃ x y, G.IsLink e x y :=
  (edge_mem_iff_exists_isLink ..).1 h

lemma edgeSet_eq_setOf_exists_isLink : E(G) = {e | ∃ x y, G.IsLink e x y} :=
  Set.ext G.edge_mem_iff_exists_isLink

lemma IsLink.left_dup_or_dup (h : G.IsLink e x y) (h' : G.IsLink e z w) :
    V(G) x z ∨ V(G) x w := G.dup_or_dup_of_isLink_of_isLink h h'

lemma IsLink.right_dup_or_dup (h : G.IsLink e x y) (h' : G.IsLink e z w) :
    V(G) y z ∨ V(G) y w := h.symm.left_dup_or_dup h'

lemma IsLink.left_dup_of_right_ndup (h : G.IsLink e x y) (h' : G.IsLink e z w)
    (hzx : ¬ V(G) x z) : V(G) x w :=
  (h.left_dup_or_dup h').elim (False.elim ∘ hzx) id

lemma IsLink.right_unique_dup (h : G.IsLink e x y) (h' : G.IsLink e x z) : V(G) y z := by
  obtain hyz | hyx := h.right_dup_or_dup h'.symm
  · exact hyz
  obtain hzy | hzx := h'.right_dup_or_dup h.symm
  · exact symm hzy
  exact trans' hyx <| symm hzx

instance : Trans (G.IsLink e) (G.IsLink e) V(G) where
  trans hxy hxz := (symm hxy).right_unique_dup hxz

lemma IsLink.left_unique_dup (h : G.IsLink e x z) (h' : G.IsLink e y z) : V(G) x y :=
  h.symm.right_unique_dup h'.symm

lemma IsLink.dup_and_dup_or_dup_and_dup {x' y' : α} (h : G.IsLink e x y) (h' : G.IsLink e x' y') :
    V(G) x x' ∧ V(G) y y' ∨ V(G) x y' ∧ V(G) y x' := by
  obtain hx | hx := h.left_dup_or_dup h'
  · simp [h.right_unique_dup <| h'.dup_left (symm hx), hx]
  simp [symm (h'.symm.right_unique_dup <| h.dup_left hx), hx]

lemma IsLink.isLink_iff_dup_and_dup_or_dup_and_dup (h : G.IsLink e x y) {x' y' : α} :
    G.IsLink e x' y' ↔ V(G) x x' ∧ V(G) y y' ∨ V(G) x y' ∧ V(G) y x' := by
  refine ⟨h.dup_and_dup_or_dup_and_dup, ?_⟩
  rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
  · rwa [isLink_left_rw hx, isLink_right_rw hy] at h
  rwa [isLink_comm, isLink_left_rw hy, isLink_right_rw hx] at h

instance : Dompeq V(G) (G.IsLink e) where
  dompeq := by
    ext x y
    simp only [Domp, Comp, flip_apply]
    exact ⟨fun ⟨a, hxa, b, hlba, hby⟩ => trans' (trans' hxa hlba.symm) hby,
      fun h => ⟨x, h.left_refl, y, h.symm, h.right_refl⟩⟩

/-! ### Edge-vertex incidence -/

/-- The unary incidence predicate of `G`. `G.Inc e x` means that the vertex `x`
is one or both of the ends of the edge `e`.
In the `Inc` namespace, we use `edge` and `vertex` to refer to `e` and `x`. -/
def Inc (G : Graph α β) (e : β) (x : α) : Prop := ∃ y, G.IsLink e x y

instance : Trans G.Inc V(G) G.Inc where
  trans := fun ⟨y, hy⟩ hbc => ⟨y, trans' (symm hbc) hy⟩

-- Cannot be @[simp] because `x` can not be inferred by `simp`.
lemma Inc.edge_mem (h : G.Inc e x) : e ∈ E(G) :=
  h.choose_spec.edge_mem

-- Cannot be @[simp] because `e` can not be inferred by `simp`.
lemma Inc.mem_vertex (h : G.Inc e x) : ∃ v ∈ V(G), x ∈ v :=
  h.choose_spec.left_mem_vertex

lemma Inc.label_mem (h : G.Inc e x) : x ∈ L(G) :=
  h.choose_spec.left_mem

-- Cannot be @[simp] because `y` can not be inferred by `simp`.
lemma IsLink.inc_left (h : G.IsLink e x y) : G.Inc e x :=
  ⟨y, h⟩

-- Cannot be @[simp] because `x` can not be inferred by `simp`.
lemma IsLink.inc_right (h : G.IsLink e x y) : G.Inc e y :=
  ⟨x, h.symm⟩

@[simp]
lemma inc_right_rw (h : V(G) x y) : G.Inc e x ↔ G.Inc e y :=
  right_rw _ h

lemma Inc.dup (hi : G.Inc e x) (h : V(G) x y) : G.Inc e y :=
  trans' hi h

lemma Inc.dup_or_dup_of_isLink (h : G.Inc e x) (h' : G.IsLink e y z) : V(G) x y ∨ V(G) x z :=
  h.choose_spec.left_dup_or_dup h'

lemma Inc.dup_of_isLink_of_ndup_left (h : G.Inc e x) (h' : G.IsLink e y z) (hxy : ¬ V(G) x y) :
    V(G) x z := (h.dup_or_dup_of_isLink h').elim (False.elim ∘ hxy) id

lemma IsLink.isLink_iff_dup (h : G.IsLink e x y) : G.IsLink e x z ↔ V(G) z y :=
  ⟨fun h' ↦ h'.right_unique_dup h, fun h' ↦ h.dup_right (symm h')⟩

/-- The binary incidence predicate can be expressed in terms of the unary one. -/
lemma isLink_iff_inc_dup :
    G.IsLink e x y ↔ G.Inc e x ∧ G.Inc e y ∧ ∀ z, G.Inc e z → V(G) z x ∨ V(G) z y := by
  refine ⟨fun h ↦ ⟨h.inc_left, h.inc_right, fun z h' ↦ h'.dup_or_dup_of_isLink h⟩, ?_⟩
  rintro ⟨⟨x', hx'⟩, ⟨y', hy'⟩, h⟩
  obtain hx | hy := h _ hx'.inc_right
  · obtain hy | hxy' := hx'.left_dup_or_dup hy'
    · rwa [isLink_right_rw (symm hy), ← isLink_right_rw hx]
    rwa [isLink_comm, isLink_right_rw hxy']
  rwa [← isLink_right_rw hy]

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
    V(G) x y ∨ V(G) x z ∨ V(G) y z := by
  by_contra! hcon
  obtain ⟨x', hx'⟩ := hx
  obtain hy := hy.dup_of_isLink_of_ndup_left hx' <| not_symm_not hcon.1
  obtain hz := hz.dup_of_isLink_of_ndup_left hx' <| not_symm_not hcon.2.1
  exact hcon.2.2 <| trans' hy <| symm hz

/-- `G.IsLoopAt e x` means that both ends of the edge `e` are equal to the vertex `x`. -/
def IsLoopAt (G : Graph α β) (e : β) (x : α) : Prop := G.IsLink e x x

@[simp]
lemma isLink_self_iff : G.IsLink e x x ↔ G.IsLoopAt e x := Iff.rfl

lemma IsLoopAt.inc (h : G.IsLoopAt e x) : G.Inc e x :=
  IsLink.inc_left h

lemma IsLoopAt.dup_of_inc (h : G.IsLoopAt e x) (h' : G.Inc e y) : V(G) x y := by
  obtain hy | hy := h'.dup_or_dup_of_isLink h <;> exact symm hy

lemma IsLoopAt.dup (h : G.IsLoopAt e x) (h' : V(G) x y) : G.IsLoopAt e y :=
  h.dup_left h' |>.dup_right h'

lemma dup_isLoopAt (h : V(G) x y) : G.IsLoopAt e x ↔ G.IsLoopAt e y :=
  ⟨fun h' ↦ h'.dup h, fun h' ↦ h'.dup (symm h)⟩

-- Cannot be @[simp] because `x` can not be inferred by `simp`.
lemma IsLoopAt.edge_mem (h : G.IsLoopAt e x) : e ∈ E(G) :=
  h.inc.edge_mem

-- Cannot be @[simp] because `e` can not be inferred by `simp`.
lemma IsLoopAt.mem_vertex (h : G.IsLoopAt e x) : ∃ v ∈ V(G), x ∈ v :=
  h.inc.mem_vertex

/-- `G.IsNonloopAt e x` means that the vertex `x` is one but not both of the ends of the edge =`e`,
or equivalently that `e` is incident with `x` but not a loop at `x` -
see `Graph.isNonloopAt_iff_inc_not_isLoopAt`. -/
def IsNonloopAt (G : Graph α β) (e : β) (x : α) : Prop := ∃ y, ¬ V(G) x y ∧ G.IsLink e x y

lemma IsNonloopAt.inc (h : G.IsNonloopAt e x) : G.Inc e x :=
  h.choose_spec.2.inc_left

-- Cannot be @[simp] because `x` can not be inferred by `simp`.
lemma IsNonloopAt.edge_mem (h : G.IsNonloopAt e x) : e ∈ E(G) :=
  h.inc.edge_mem

-- Cannot be @[simp] because `e` can not be inferred by `simp`.
lemma IsNonloopAt.mem_vertex (h : G.IsNonloopAt e x) : ∃ v ∈ V(G), x ∈ v :=
  h.inc.mem_vertex

lemma IsNonloopAt.dup (h : G.IsNonloopAt e x) (h' : V(G) x y) : G.IsNonloopAt e y := by
  obtain ⟨z, hxz, hy⟩ := h
  use z, fun hyz => hxz <| trans' h' hyz, hy.dup_left h'

lemma dup_isNonloopAt (h : V(G) x y) : G.IsNonloopAt e x ↔ G.IsNonloopAt e y :=
  ⟨(·.dup h), (·.dup (symm h))⟩

lemma IsLoopAt.not_isNonloopAt (h : G.IsLoopAt e x) (y : α) : ¬ G.IsNonloopAt e y := by
  rintro ⟨z, hyz, hy⟩
  refine hyz ?_
  rw [← left_rw V(G) (h.dup_of_inc hy.inc_left)]
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

instance : Trans V(G) G.Adj G.Adj where
  trans := by
    rintro x y z hDxy ⟨f, hlyz⟩
    exact ⟨f, hlyz.dup_left <| symm hDxy⟩

protected lemma Adj.symm (h : G.Adj x y) : G.Adj y x :=
  ⟨_, h.choose_spec.symm⟩

instance : IsSymm α G.Adj where
  symm _ _ := Adj.symm

lemma adj_comm (x y) : G.Adj x y ↔ G.Adj y x :=
  comm

-- Cannot be @[simp] because `y` can not be inferred by `simp`.
lemma Adj.left_mem_vertex (h : G.Adj x y) : ∃ v ∈ V(G), x ∈ v :=
  h.choose_spec.left_mem_vertex

-- Cannot be @[simp] because `x` can not be inferred by `simp`.
lemma Adj.right_mem_vertex (h : G.Adj x y) : ∃ v ∈ V(G), y ∈ v :=
  h.symm.left_mem_vertex

lemma IsLink.adj (h : G.IsLink e x y) : G.Adj x y :=
  ⟨e, h⟩

lemma Adj.dup_left (h : G.Adj x y) (h' : V(G) x z) : G.Adj z y := by
  obtain ⟨e, he⟩ := h
  use e, he.dup_left h'

lemma Adj.dup_right (h : G.Adj x y) (h' : V(G) y z) : G.Adj x z := by
  obtain ⟨e, he⟩ := h
  use e, he.dup_right h'

lemma adj_left_rw (h : V(G) x y) : G.Adj x z ↔ G.Adj y z :=
  left_rw G.Adj h

lemma adj_right_rw (h : V(G) x y) : G.Adj z x ↔ G.Adj z y :=
  right_rw G.Adj h

/-! ### Extensionality -/

/-- `edgeSet` can be determined using `IsLink`, so the graph constructed from `G.vertexSet` and
`G.IsLink` using any value for `edgeSet` is equal to `G` itself. -/
@[simp]
lemma mk_eq_self (G : Graph α β) {E : Set β} (hE : ∀ e, e ∈ E ↔ ∃ x y, G.IsLink e x y) :
    Graph.mk V(G) G.IsLink E
    (by simpa [show E = E(G) by simp [Set.ext_iff, hE, G.edge_mem_iff_exists_isLink]]
      using G.isLink_symm)
    (fun _ _ _ _ _ h h' ↦ h.left_dup_or_dup h') hE
    G.mem_vertexSet_of_isLink G.isLink_of_dup = G := by
  obtain rfl : E = E(G) := by simp [Set.ext_iff, hE, G.edge_mem_iff_exists_isLink]
  cases G with | _ _ _ _ _ _ h _ => simp

/-- Two graphs with the same vertex set and binary incidences are equal.
(We use this as the default extensionality lemma rather than adding `@[ext]`
to the definition of `Graph`, so it doesn't require equality of the edge sets.) -/
@[ext]
protected lemma ext {G₁ G₂ : Graph α β} (hD : V(G₁) = V(G₂))
    (h : ∀ e x y, G₁.IsLink e x y ↔ G₂.IsLink e x y) : G₁ = G₂ := by
  rw [← G₁.mk_eq_self G₁.edge_mem_iff_exists_isLink, ← G₂.mk_eq_self G₂.edge_mem_iff_exists_isLink]
  convert rfl using 2
  · exact hD.symm
  · simp [funext_iff, h]
  simp [edgeSet_eq_setOf_exists_isLink, h]

/-- Two graphs with the same vertex set and unary incidences are equal. -/
lemma ext_inc {G₁ G₂ : Graph α β} (hV : V(G₁) = V(G₂)) (h : ∀ e x, G₁.Inc e x ↔ G₂.Inc e x) :
    G₁ = G₂ :=
  Graph.ext hV fun _ _ _ ↦ by simp_rw [isLink_iff_inc_dup, h, hV]

end Graph
