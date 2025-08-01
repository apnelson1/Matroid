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

open Set Relation Partition

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
  Dup : Partition (Set α)
  /-- The vertex set. -/
  vertexSet : Set α := Dup.supp
  /-- The vertex set is the support of the vertex relation. -/
  vertexSet_eq : vertexSet = Dup.supp := by rfl
  /-- The binary incidence predicate, stating that `x` and `y` are the ends of an edge `e`.
  If `G.IsLink e x y` then we refer to `e` as `edge` and `x` and `y` as `left` and `right`. -/
  IsLink : β → α → α → Prop
  /-- The edge set. -/
  edgeSet : Set β := {e | ∃ x y, IsLink e x y}
  /-- If `e` goes from `x` to `y`, it goes from `y` to `x`. -/
  isLink_symm : ∀ ⦃e⦄, e ∈ edgeSet → (Symmetric <| IsLink e)
  /-- An edge is incident with at most one pair of vertices. -/
  dup_or_dup_of_isLink_of_isLink : ∀ ⦃e x y v w⦄, IsLink e x y → IsLink e v w → Dup x v ∨ Dup x w
  /-- An edge `e` is incident to something if and only if `e` is in the edge set. -/
  edge_mem_iff_exists_isLink : ∀ ⦃e⦄, e ∈ edgeSet ↔ ∃ x y, IsLink e x y := by exact fun _ ↦ Iff.rfl
  /-- If some edge `e` is incident to `x`, then `x ∈ V`. -/
  mem_vertexSet_of_isLink : ∀ ⦃e x y⦄, IsLink e x y → x ∈ vertexSet
  /-- If `x` and `y` represent the same vertex, it has the same incidence relation. -/
  isLink_of_dup : ∀ ⦃e x y z⦄, Dup x y → IsLink e y z → IsLink e x z

initialize_simps_projections Graph (IsLink → isLink, Dup → dup)

namespace Graph

variable {G : Graph α β}

/-- `V(G)` denotes the `vertexSet` of a graph `G`. -/
scoped notation "V(" G ")" => Graph.vertexSet G

@[simp] lemma vertexSet_def : G.Dup.supp = V(G) := G.vertexSet_eq.symm

lemma mem_supp (hx : x ∈ V(G)) : x ∈ G.Dup.supp := G.vertexSet_eq ▸ hx

/-- `E(G)` denotes the `edgeSet` of a graph `G`. -/
scoped notation "E(" G ")" => Graph.edgeSet G

instance : IsSymm α (G.IsLink e) where
  symm u v huv := G.isLink_symm (G.edge_mem_iff_exists_isLink.mpr ⟨u, v, huv⟩) huv

instance : Trans G.Dup (G.IsLink e) (G.IsLink e) where
  trans hxy := G.isLink_of_dup hxy

/-! ### Vertex relation -/

lemma dup_refl_iff : G.Dup x x ↔ x ∈ V(G) :=
  vertexSet_def ▸ rel_self_iff_mem_supp

lemma dup_of_mem_vertexSet (hx : x ∈ V(G)) : G.Dup x x :=
  dup_refl_iff.mpr hx

lemma dup_left_mem (hx : G.Dup x y) : x ∈ V(G) :=
  vertexSet_def ▸ hx.left_mem

lemma dup_right_mem (hy : G.Dup x y) : y ∈ V(G) :=
  vertexSet_def ▸ hy.right_mem

lemma dup_left_self (hx : G.Dup x y) : G.Dup x x :=
  refl_of_left hx

lemma dup_right_self (hy : G.Dup x y) : G.Dup y y :=
  refl_of_right hy

@[deprecated not_symm_not (since := "2025-07-19")]
lemma not_dup_symm (h : ¬ G.Dup x y) : ¬ G.Dup y x := fun hyx ↦ h (symm hyx)

@[deprecated not_comm_not (since := "2025-07-19")]
lemma not_dup_comm : ¬ G.Dup x y ↔ ¬ G.Dup y x := ⟨not_symm_not, not_symm_not⟩

lemma dup_left_rw (h : G.Dup x y) : G.Dup x z ↔ G.Dup y z :=
  left_rw G.Dup h

lemma dup_right_rw (h : G.Dup x y) : G.Dup z x ↔ G.Dup z y :=
  right_rw G.Dup h

@[simp] lemma not_dup_of_not_left_mem (h : ¬ x ∈ V(G)) : ¬ G.Dup x y :=
  fun h' ↦ h <| vertexSet_def ▸ h'.left_mem

@[simp] lemma not_dup_of_not_right_mem (h : ¬ y ∈ V(G)) : ¬ G.Dup x y :=
  fun h' ↦ h <| vertexSet_def ▸ h'.right_mem

def NodupAt (G : Graph α β) (x : α) : Prop := ∀ ⦃y⦄, G.Dup x y → x = y

lemma NodupAt.dup_iff (h : G.NodupAt x) : G.Dup x y ↔ x = y ∧ x ∈ V(G) := by
  refine ⟨fun hdup ↦ ⟨h hdup, vertexSet_def ▸ hdup.left_mem⟩, ?_⟩
  rintro ⟨rfl, hx⟩
  exact dup_of_mem_vertexSet hx

lemma dup_of_NodupAt (hdup : G.Dup x y) (h : G.NodupAt x) : x = y := h hdup

class Nodup (G : Graph α β) : Prop where
  atomic_dup : Atomic G.Dup

lemma dup_atomic (G : Graph α β) [G.Nodup] : Atomic G.Dup := Nodup.atomic_dup

lemma eq_of_dup [G.Nodup] (hdup : G.Dup x y) : x = y :=
  G.dup_atomic.eq_of_rel hdup

@[simp]
lemma dup_iff_eq [G.Nodup] : G.Dup x y ↔ x = y ∧ x ∈ V(G) := by
  rw [G.dup_atomic.rel_eq, G.vertexSet_eq]

@[simp]
lemma dup_eq_discrete [G.Nodup] : G.Dup = Partition.discrete V(G) := by
  ext x y
  rw [dup_iff_eq, rel_discrete_iff, and_comm]

lemma eq_or_eq_of_isLink_of_isLink [G.Nodup] (huv : G.IsLink e u v) (hxy : G.IsLink e x y) :
    u = x ∨ u = y := by
  obtain h | h := G.dup_or_dup_of_isLink_of_isLink huv hxy <;> rw [dup_iff_eq] at h <;> tauto

/-! ### Edge-vertex-vertex incidence -/

lemma IsLink.edge_mem (h : G.IsLink e x y) : e ∈ E(G) :=
  (edge_mem_iff_exists_isLink ..).2 ⟨x, y, h⟩

@[simp] protected lemma IsLink.symm (h : G.IsLink e x y) : G.IsLink e y x :=
  G.isLink_symm h.edge_mem h

lemma IsLink.dup_left (h : G.IsLink e x y) (hrel : G.Dup x z) : G.IsLink e z y :=
  G.isLink_of_dup (symm hrel) h

lemma IsLink.dup_right (h : G.IsLink e x y) (hrel : G.Dup y z) : G.IsLink e x z :=
  h.symm.dup_left hrel |>.symm

lemma isLink_left_rw (h : G.Dup x y) : G.IsLink e x z ↔ G.IsLink e y z :=
  left_rw _ h

lemma isLink_right_rw (h : G.Dup x y) : G.IsLink e z x ↔ G.IsLink e z y :=
  right_rw _ h

@[simp] lemma IsLink.left_mem (h : G.IsLink e x y) : x ∈ V(G) := G.mem_vertexSet_of_isLink h

@[simp] lemma IsLink.right_mem (h : G.IsLink e x y) : y ∈ V(G) := h.symm.left_mem

@[simp] lemma IsLink.left_mem_supp (h : G.IsLink e x y) : x ∈ G.Dup.supp :=
  vertexSet_def ▸ h.left_mem

@[simp] lemma IsLink.right_mem_supp (h : G.IsLink e x y) : y ∈ G.Dup.supp :=
  vertexSet_def ▸ h.right_mem

@[simp] lemma IsLink.left_refl (h : G.IsLink e x y) : G.Dup x x := dup_of_mem_vertexSet h.left_mem

@[simp] lemma IsLink.right_refl (h : G.IsLink e x y) : G.Dup y y := h.symm.left_refl

lemma isLink_comm : G.IsLink e x y ↔ G.IsLink e y x :=
  comm

lemma exists_isLink_of_mem_edgeSet (h : e ∈ E(G)) : ∃ x y, G.IsLink e x y :=
  (edge_mem_iff_exists_isLink ..).1 h

lemma edgeSet_eq_setOf_exists_isLink : E(G) = {e | ∃ x y, G.IsLink e x y} :=
  Set.ext G.edge_mem_iff_exists_isLink

lemma IsLink.left_dup_or_dup (h : G.IsLink e x y) (h' : G.IsLink e z w) :
    G.Dup x z ∨ G.Dup x w := G.dup_or_dup_of_isLink_of_isLink h h'

lemma IsLink.right_dup_or_dup (h : G.IsLink e x y) (h' : G.IsLink e z w) :
    G.Dup y z ∨ G.Dup y w := h.symm.left_dup_or_dup h'

lemma IsLink.left_eq_or_eq [G.Nodup] (h : G.IsLink e x y) (h' : G.IsLink e z w) :
    x = z ∨ x = w := G.eq_or_eq_of_isLink_of_isLink h h'

lemma IsLink.right_eq_or_eq [G.Nodup] (h : G.IsLink e x y) (h' : G.IsLink e z w) :
    y = z ∨ y = w := h.symm.left_eq_or_eq h'

lemma IsLink.left_dup_of_right_ndup (h : G.IsLink e x y) (h' : G.IsLink e z w)
    (hzx : ¬ G.Dup x z) : G.Dup x w :=
  (h.left_dup_or_dup h').elim (False.elim ∘ hzx) id

lemma IsLink.right_unique_dup (h : G.IsLink e x y) (h' : G.IsLink e x z) : G.Dup y z := by
  obtain hyz | hyx := h.right_dup_or_dup h'.symm
  · exact hyz
  obtain hzy | hzx := h'.right_dup_or_dup h.symm
  · exact symm hzy
  exact trans' hyx <| symm hzx

instance : Trans (G.IsLink e) (G.IsLink e) G.Dup where
  trans hxy hxz := (symm hxy).right_unique_dup hxz

lemma IsLink.left_unique_dup (h : G.IsLink e x z) (h' : G.IsLink e y z) : G.Dup x y :=
  h.symm.right_unique_dup h'.symm

lemma IsLink.left_eq_of_right_ne [G.Nodup] (h : G.IsLink e x y) (h' : G.IsLink e z w)
    (hne : x ≠ z) : x = w := by
  obtain hx | hx := h.left_dup_or_dup h' <;> rw [dup_iff_eq] at hx <;> tauto

lemma IsLink.right_unique [G.Nodup] (h : G.IsLink e x y) (h' : G.IsLink e x z) : y = z :=
  eq_of_dup <| h.right_unique_dup h'

lemma IsLink.left_unique [G.Nodup] (h : G.IsLink e x z) (h' : G.IsLink e y z) : x = y :=
  h.symm.right_unique h'.symm

lemma IsLink.dup_and_dup_or_dup_and_dup {x' y' : α} (h : G.IsLink e x y) (h' : G.IsLink e x' y') :
    G.Dup x x' ∧ G.Dup y y' ∨ G.Dup x y' ∧ G.Dup y x' := by
  obtain hx | hx := h.left_dup_or_dup h'
  · simp [h.right_unique_dup <| h'.dup_left (symm hx), hx]
  simp [symm (h'.symm.right_unique_dup <| h.dup_left hx), hx]

lemma IsLink.eq_and_eq_or_eq_and_eq [G.Nodup] {x' y' : α} (h : G.IsLink e x y)
    (h' : G.IsLink e x' y') : x = x' ∧ y = y' ∨ x = y' ∧ y = x' := by
  obtain rfl | rfl := h.left_eq_or_eq h'
  · simp [h.right_unique h']
  simp [h'.symm.right_unique h]

lemma IsLink.isLink_iff_dup_and_dup_or_dup_and_dup (h : G.IsLink e x y) {x' y' : α} :
    G.IsLink e x' y' ↔ G.Dup x x' ∧ G.Dup y y' ∨ G.Dup x y' ∧ G.Dup y x' := by
  refine ⟨h.dup_and_dup_or_dup_and_dup, ?_⟩
  rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
  · rwa [isLink_left_rw hx, isLink_right_rw hy] at h
  rwa [isLink_comm, isLink_left_rw hy, isLink_right_rw hx] at h

lemma IsLink.isLink_iff [G.Nodup] (h : G.IsLink e x y) {x' y' : α} :
    G.IsLink e x' y' ↔ (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  refine ⟨h.eq_and_eq_or_eq_and_eq, ?_⟩
  rintro (⟨rfl, rfl⟩ | ⟨rfl,rfl⟩)
  · assumption
  exact h.symm

lemma IsLink.isLink_iff_sym2_eq [G.Nodup] (h : G.IsLink e x y) {x' y' : α} :
    G.IsLink e x' y' ↔ s(x,y) = s(x',y') := by
  rw [h.isLink_iff, Sym2.eq_iff]

instance : Dompeq G.Dup (G.IsLink e) where
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

instance : Trans G.Inc G.Dup G.Inc where
  trans := fun ⟨y, hy⟩ hbc => ⟨y, trans' (symm hbc) hy⟩

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
lemma inc_right_rw (h : G.Dup x y) : G.Inc e x ↔ G.Inc e y :=
  right_rw _ h

lemma Inc.dup (hi : G.Inc e x) (h : G.Dup x y) : G.Inc e y :=
  trans' hi h

lemma Inc.dup_or_dup_of_isLink (h : G.Inc e x) (h' : G.IsLink e y z) : G.Dup x y ∨ G.Dup x z :=
  h.choose_spec.left_dup_or_dup h'

lemma Inc.dup_of_isLink_of_ndup_left (h : G.Inc e x) (h' : G.IsLink e y z) (hxy : ¬ G.Dup x y) :
    G.Dup x z := (h.dup_or_dup_of_isLink h').elim (False.elim ∘ hxy) id

lemma IsLink.isLink_iff_dup (h : G.IsLink e x y) : G.IsLink e x z ↔ G.Dup z y :=
  ⟨fun h' ↦ h'.right_unique_dup h, fun h' ↦ h.dup_right (symm h')⟩

/-- The binary incidence predicate can be expressed in terms of the unary one. -/
lemma isLink_iff_inc_dup :
    G.IsLink e x y ↔ G.Inc e x ∧ G.Inc e y ∧ ∀ z, G.Inc e z → G.Dup z x ∨ G.Dup z y := by
  refine ⟨fun h ↦ ⟨h.inc_left, h.inc_right, fun z h' ↦ h'.dup_or_dup_of_isLink h⟩, ?_⟩
  rintro ⟨⟨x', hx'⟩, ⟨y', hy'⟩, h⟩
  obtain hx | hy := h _ hx'.inc_right
  · obtain hy | hxy' := hx'.left_dup_or_dup hy'
    · rwa [isLink_right_rw (symm hy), ← isLink_right_rw hx]
    rwa [isLink_comm, isLink_right_rw hxy']
  rwa [← isLink_right_rw hy]

lemma Inc.eq_or_eq_of_isLink [G.Nodup] (h : G.Inc e x) (h' : G.IsLink e y z) :
    x = y ∨ x = z := h.choose_spec.left_eq_or_eq h'

lemma Inc.eq_of_isLink_of_ne_left [G.Nodup] (h : G.Inc e x) (h' : G.IsLink e y z)
    (hxy : x ≠ y) : x = z :=
  (h.eq_or_eq_of_isLink h').elim (False.elim ∘ hxy) id

lemma IsLink.isLink_iff_eq [G.Nodup] (h : G.IsLink e x y) : G.IsLink e x z ↔ z = y :=
  ⟨fun h' ↦ h'.right_unique h, fun h' ↦ h' ▸ h⟩

/-- The binary incidence predicate can be expressed in terms of the unary one. -/
lemma isLink_iff_inc [G.Nodup] :
    G.IsLink e x y ↔ G.Inc e x ∧ G.Inc e y ∧ ∀ z, G.Inc e z → z = x ∨ z = y := by
  refine ⟨fun h ↦ ⟨h.inc_left, h.inc_right, fun z h' ↦ h'.eq_or_eq_of_isLink h⟩, ?_⟩
  rintro ⟨⟨x', hx'⟩, ⟨y', hy'⟩, h⟩
  obtain rfl | rfl := h _ hx'.inc_right
  · obtain rfl | rfl := hx'.left_eq_or_eq hy'
    · assumption
    exact hy'.symm
  assumption

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
    G.Dup x y ∨ G.Dup x z ∨ G.Dup y z := by
  by_contra! hcon
  obtain ⟨x', hx'⟩ := hx
  obtain hy := hy.dup_of_isLink_of_ndup_left hx' <| not_symm_not hcon.1
  obtain hz := hz.dup_of_isLink_of_ndup_left hx' <| not_symm_not hcon.2.1
  exact hcon.2.2 <| trans' hy <| symm hz

lemma Inc.eq_or_eq_or_eq [G.Nodup] (hx : G.Inc e x) (hy : G.Inc e y) (hz : G.Inc e z) :
    x = y ∨ x = z ∨ y = z := by
  by_contra! hcon
  obtain ⟨x', hx'⟩ := hx
  obtain rfl := hy.eq_of_isLink_of_ne_left hx' hcon.1.symm
  obtain rfl := hz.eq_of_isLink_of_ne_left hx' hcon.2.1.symm
  exact hcon.2.2 rfl

/-- `G.IsLoopAt e x` means that both ends of the edge `e` are equal to the vertex `x`. -/
def IsLoopAt (G : Graph α β) (e : β) (x : α) : Prop := G.IsLink e x x

@[simp]
lemma isLink_self_iff : G.IsLink e x x ↔ G.IsLoopAt e x := Iff.rfl

lemma IsLoopAt.inc (h : G.IsLoopAt e x) : G.Inc e x :=
  IsLink.inc_left h

lemma IsLoopAt.dup_of_inc (h : G.IsLoopAt e x) (h' : G.Inc e y) : G.Dup x y := by
  obtain hy | hy := h'.dup_or_dup_of_isLink h <;> exact symm hy

lemma IsLoopAt.eq_of_inc [G.Nodup] (h : G.IsLoopAt e x) (h' : G.Inc e y) : x = y := by
  obtain rfl | rfl := h'.eq_or_eq_of_isLink h <;> rfl

lemma IsLoopAt.dup (h : G.IsLoopAt e x) (h' : G.Dup x y) : G.IsLoopAt e y :=
  h.dup_left h' |>.dup_right h'

lemma dup_isLoopAt (h : G.Dup x y) : G.IsLoopAt e x ↔ G.IsLoopAt e y :=
  ⟨fun h' ↦ h'.dup h, fun h' ↦ h'.dup (symm h)⟩

-- Cannot be @[simp] because `x` can not be inferred by `simp`.
lemma IsLoopAt.edge_mem (h : G.IsLoopAt e x) : e ∈ E(G) :=
  h.inc.edge_mem

-- Cannot be @[simp] because `e` can not be inferred by `simp`.
lemma IsLoopAt.vertex_mem (h : G.IsLoopAt e x) : x ∈ V(G) :=
  h.inc.vertex_mem

/-- `G.IsNonloopAt e x` means that the vertex `x` is one but not both of the ends of the edge =`e`,
or equivalently that `e` is incident with `x` but not a loop at `x` -
see `Graph.isNonloopAt_iff_inc_not_isLoopAt`. -/
def IsNonloopAt (G : Graph α β) (e : β) (x : α) : Prop := ∃ y, ¬ G.Dup x y ∧ G.IsLink e x y

lemma IsNonloopAt.inc (h : G.IsNonloopAt e x) : G.Inc e x :=
  h.choose_spec.2.inc_left

-- Cannot be @[simp] because `x` can not be inferred by `simp`.
lemma IsNonloopAt.edge_mem (h : G.IsNonloopAt e x) : e ∈ E(G) :=
  h.inc.edge_mem

-- Cannot be @[simp] because `e` can not be inferred by `simp`.
lemma IsNonloopAt.vertex_mem (h : G.IsNonloopAt e x) : x ∈ V(G) :=
  h.inc.vertex_mem

lemma IsNonloopAt.dup (h : G.IsNonloopAt e x) (h' : G.Dup x y) : G.IsNonloopAt e y := by
  obtain ⟨z, hxz, hy⟩ := h
  use z, fun hyz => hxz <| trans' h' hyz, hy.dup_left h'

lemma dup_isNonloopAt (h : G.Dup x y) : G.IsNonloopAt e x ↔ G.IsNonloopAt e y :=
  ⟨(·.dup h), (·.dup (symm h))⟩

lemma IsLoopAt.not_isNonloopAt (h : G.IsLoopAt e x) (y : α) : ¬ G.IsNonloopAt e y := by
  rintro ⟨z, hyz, hy⟩
  refine hyz ?_
  rw [← left_rw G.Dup (h.dup_of_inc hy.inc_left)]
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

instance : Trans G.Dup G.Adj G.Adj where
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
lemma Adj.left_mem (h : G.Adj x y) : x ∈ V(G) :=
  h.choose_spec.left_mem

-- Cannot be @[simp] because `x` can not be inferred by `simp`.
lemma Adj.right_mem (h : G.Adj x y) : y ∈ V(G) :=
  h.symm.left_mem

lemma IsLink.adj (h : G.IsLink e x y) : G.Adj x y :=
  ⟨e, h⟩

lemma Adj.dup_left (h : G.Adj x y) (h' : G.Dup x z) : G.Adj z y := by
  obtain ⟨e, he⟩ := h
  use e, he.dup_left h'

lemma Adj.dup_right (h : G.Adj x y) (h' : G.Dup y z) : G.Adj x z := by
  obtain ⟨e, he⟩ := h
  use e, he.dup_right h'

lemma adj_left_rw (h : G.Dup x y) : G.Adj x z ↔ G.Adj y z :=
  left_rw G.Adj h

lemma adj_right_rw (h : G.Dup x y) : G.Adj z x ↔ G.Adj z y :=
  right_rw G.Adj h

/-! ### Extensionality -/

@[simps]
def mk_of_unique (V : Set α) (IsLink : β → α → α → Prop)
    (edgeSet : Set β := {e | ∃ x y, IsLink e x y})
    (isLink_symm : ∀ ⦃e : β⦄, e ∈ edgeSet → Symmetric (IsLink e))
    (dup_or_dup_of_isLink_of_isLink : ∀ ⦃e x y v w⦄, IsLink e x y → IsLink e v w → x = v ∨ x = w)
    (edge_mem_iff_exists_isLink : ∀ e, e ∈ edgeSet ↔ ∃ x y, IsLink e x y := by
      exact fun _ ↦ Iff.rfl)
    (left_mem_of_isLink : ∀ ⦃e x y⦄, IsLink e x y → x ∈ V) : Graph α β where
  edgeSet := edgeSet
  edge_mem_iff_exists_isLink := edge_mem_iff_exists_isLink
  Dup := Partition.discrete V
  vertexSet := V
  vertexSet_eq := supp_discrete V |>.symm
  IsLink := IsLink
  isLink_symm := isLink_symm
  dup_or_dup_of_isLink_of_isLink e x y v w hl hl' := by
    simp_rw [rel_discrete_iff]
    obtain rfl | rfl := dup_or_dup_of_isLink_of_isLink hl hl'
    · exact Or.inl ⟨rfl, left_mem_of_isLink hl⟩
    exact Or.inr ⟨rfl, left_mem_of_isLink hl⟩
  mem_vertexSet_of_isLink e x y hl := (supp_discrete V).symm ▸ left_mem_of_isLink hl
  isLink_of_dup e x y z hxy hl := by
    obtain ⟨rfl, hx⟩ := rel_discrete_iff.mp hxy
    exact hl

instance (V : Set α) (IsLink : β → α → α → Prop) (edgeSet : Set β)
    (isLink_symm : ∀ ⦃e : β⦄, e ∈ edgeSet → Symmetric (IsLink e))
    (dup_or_dup_of_isLink_of_isLink : ∀ ⦃e x y v w⦄, IsLink e x y → IsLink e v w → x = v ∨ x = w)
    (edge_mem_iff_exists_isLink : ∀ e, e ∈ edgeSet ↔ ∃ x y, IsLink e x y)
    (left_mem_of_isLink : ∀ ⦃e x y⦄, IsLink e x y → x ∈ V) :
    Nodup (mk_of_unique V IsLink edgeSet isLink_symm dup_or_dup_of_isLink_of_isLink
    edge_mem_iff_exists_isLink left_mem_of_isLink) where
  atomic_dup := by simp

-- @[simps]
-- def mk_of_unique' (V : Set α) (IsLink : β → α → α → Prop)
--     (isLink_symm : ∀ ⦃e x y⦄, IsLink e x y → IsLink e y x)
--     (dup_or_dup_of_isLink_of_isLink : ∀ ⦃e x y v w⦄, IsLink e x y → IsLink e v w → x = v ∨ x = w)
--     (left_mem_of_isLink : ∀ ⦃e x y⦄, IsLink e x y → x ∈ V) : Graph α β where
--   Dup := Partition.discrete V
--   vertexSet := V
--   vertexSet_eq := supp_discrete V |>.symm
--   IsLink := IsLink
--   isLink_symm e he x y hl := isLink_symm hl
--   dup_or_dup_of_isLink_of_isLink e x y v w hl hl' := by
--     simp_rw [rel_discrete_iff]
--     obtain rfl | rfl := dup_or_dup_of_isLink_of_isLink hl hl'
--     · exact Or.inl ⟨left_mem_of_isLink hl, rfl⟩
--     exact Or.inr ⟨left_mem_of_isLink hl, rfl⟩
--   mem_vertexSet_of_isLink e x y hl := (supp_discrete V).symm ▸ left_mem_of_isLink hl
--   isLink_of_dup e x y z hxy hl := by
--     obtain ⟨hx, rfl⟩ := rel_discrete_iff.mp hxy
--     exact hl

-- instance (V : Set α) (IsLink : β → α → α → Prop)
--     (isLink_symm : ∀ ⦃e x y⦄, IsLink e x y → IsLink e y x)
--     (dup_or_dup_of_isLink_of_isLink : ∀ ⦃e x y v w⦄, IsLink e x y → IsLink e v w → x = v ∨ x = w)
--     (left_mem_of_isLink : ∀ ⦃e x y⦄, IsLink e x y → x ∈ V) :
--     Nodup (mk_of_unique' V IsLink isLink_symm dup_or_dup_of_isLink_of_isLink
--     left_mem_of_isLink) where
--   le_eq a b := by simp

@[simps]
def mk_of_domp (P : Partition (Set α)) (l : β → α → α → Prop) [∀ e, IsSymm α (l e)]
    (h : ∀ {e a b c d}, l e a b → l e c d → P a c ∨ P a d) : Graph α β where
  Dup := P
  IsLink e := Domp P (l e)
  isLink_symm e he := IsSymm.symm
  dup_or_dup_of_isLink_of_isLink := by
    rintro e x y a b ⟨w, hPxw, z, hlzw, hPzy⟩ ⟨d, hPad, c, hlcd, hPcb⟩
    obtain hPzc | hPzd := h (symm hlzw) (symm hlcd)
    · left
      rwa [left_rw P hPxw, left_rw P hPzc, comm_of P]
    right
    rwa [← right_rw P hPcb, ← right_rw P hPzd]
  mem_vertexSet_of_isLink e x y := by
    rw [domp_def']
    rintro ⟨z, hxz, hzy⟩
    exact hxz.left_mem
  isLink_of_dup e x y z := trans'

lemma isLink_mk_of_domp_of_mem {P : Partition (Set α)} {l : β → α → α → Prop} [∀ e, IsSymm α (l e)]
    (h : ∀ {e a b c d}, l e a b → l e c d → P a c ∨ P a d) (hl : l e x y) (hx : x ∈ P.supp)
    (hy : y ∈ P.supp) : (mk_of_domp P l h).IsLink e x y := by
  rw [mk_of_domp_isLink]
  exact ⟨x, Partition.rel_self_of_mem_supp hx, y, symm hl, Partition.rel_self_of_mem_supp hy⟩

/-- `edgeSet` can be determined using `IsLink`, so the graph constructed from `G.vertexSet` and
`G.IsLink` using any value for `edgeSet` is equal to `G` itself. -/
@[simp]
lemma mk_eq_self (G : Graph α β) {E : Set β} (hE : ∀ e, e ∈ E ↔ ∃ x y, G.IsLink e x y) :
    Graph.mk G.Dup V(G) G.vertexSet_eq G.IsLink E
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
protected lemma ext {G₁ G₂ : Graph α β} (hD : G₁.Dup = G₂.Dup)
    (h : ∀ e x y, G₁.IsLink e x y ↔ G₂.IsLink e x y) : G₁ = G₂ := by
  rw [← G₁.mk_eq_self G₁.edge_mem_iff_exists_isLink, ← G₂.mk_eq_self G₂.edge_mem_iff_exists_isLink]
  convert rfl using 2
  · exact hD.symm
  · rw [G₁.vertexSet_eq, G₂.vertexSet_eq, hD]
  · simp [funext_iff, h]
  simp [edgeSet_eq_setOf_exists_isLink, h]

/-- Two graphs with the same vertex set and unary incidences are equal. -/
lemma ext_inc {G₁ G₂ : Graph α β} (hV : G₁.Dup = G₂.Dup) (h : ∀ e x, G₁.Inc e x ↔ G₂.Inc e x) :
    G₁ = G₂ :=
  Graph.ext hV fun _ _ _ ↦ by simp_rw [isLink_iff_inc_dup, h, hV]

end Graph
