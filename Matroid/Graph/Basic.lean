import Mathlib.Combinatorics.Graph.Basic
import Mathlib.Data.Set.Card.Arithmetic

/-!
# Basic Graph Theory

This file extends `Mathlib.Combinatorics.Graph.Basic` with additional definitions and lemmas
for multigraphs with type `Graph α β` (where `α` is the vertex type and `β` is the edge type).

## Main definitions

* `endSet`: The set of endpoints of an edge.
* `incVertexSet`: The set of vertices incident to a set of edges.
* `parallel`: Two edges are parallel if they have the same endpoints.
* `Neighbor`: The (open) neighborhood of a vertex.
* `SetNeighbor`: The external neighborhood of a set of vertices.
* `IncEdges`: The set of edges incident to a vertex.
* `SetIncEdges`: The set of edges incident to a set of vertices.
* `LinkEdges`: The set of edges linking two vertices.
* `SetLinkEdges`: The set of edges with endpoints in two given sets.
* `Isolated`: A vertex with no incident edges.
* `IsPendant`: An edge that is the unique edge incident to one of its endpoints.
* `IsLeaf`: A vertex with exactly one incident edge.
* `IsLeafEdge`: An edge that is pendant at some vertex.

-/

variable {α β : Type*} {x y z u v w : α} {e f : β} {G H : Graph α β} {F : Set β} {S T X Y : Set α}

open Set

namespace Graph

initialize_simps_projections Graph (IsLink → isLink)

/-! ## Additional lemmas for `Graph`

This section contains auxiliary lemmas and definitions for the `Graph` structure from Mathlib,
extending basic graph functionality for use in matroid theory.
-/

@[simp]
lemma IsLink.other_eq (h : G.IsLink e x y) : Inc.other ⟨y, h⟩ = y := by
  have := h.inc_left.choose_spec
  rwa [h.isLink_iff_eq] at this

@[simp]
lemma IsLoopAt.other_eq (h : G.IsLoopAt e x) : h.inc.other = x :=
  IsLink.other_eq h

@[simp]
lemma IsNonloopAt.other_ne (h : G.IsNonloopAt e x) : h.inc.other ≠ x := by
  obtain ⟨y, hne, h⟩ := h
  exact ne_of_eq_of_ne h.other_eq hne

@[simp]
lemma Inc.other_mem (h : G.Inc e x) : h.other ∈ V(G) :=
  h.choose_spec.right_mem

lemma IsLoopAt.eq_of_isLink (h : G.IsLoopAt e v) (h' : G.IsLink e x y) : v = x ∧ v = y :=
  ⟨h.eq_of_inc h'.inc_left, h.eq_of_inc h'.inc_right⟩

instance : Std.Symm G.Adj where
  symm _ _ := Adj.symm

-- TODO: These attributes should ideally be incorporated directly into the declarations
-- of `Adj.symm` and `IsLink.symm` in Mathlib when upstreaming.
attribute [grind →] IsLink.edge_mem IsLink.left_mem IsLink.right_mem IsLink.inc_left
  IsLink.inc_right Inc.edge_mem Inc.vertex_mem IsNonloopAt.edge_mem IsNonloopAt.vertex_mem
  Adj.left_mem Adj.right_mem
attribute [grind .] Inc.eq_or_eq_of_isLink exists_isLink_of_mem_edgeSet
attribute [symm] Adj.symm IsLink.symm

@[simp]
lemma not_isLink_of_notMem_edgeSet (he : e ∉ E(G)) : ¬ G.IsLink e x y :=
  mt IsLink.edge_mem he

@[simp]
lemma not_inc_of_notMem_edgeSet (he : e ∉ E(G)) : ¬ G.Inc e x :=
  mt Inc.edge_mem he

/-- Two graphs `G` and `H` have the same `IsLink` function for edge `e` if and only if
there exist vertices `x` and `y` such that both graphs agree that `e` links `x` and `y`. -/
lemma isLink_eq_isLink_iff_exists_isLink_of_mem_edgeSet (heG : e ∈ E(G)) :
    G.IsLink e = H.IsLink e ↔ ∃ x y, G.IsLink e x y ∧ H.IsLink e x y := by
  refine ⟨fun h ↦ ?_, fun ⟨x, y, hG, hH⟩ ↦ ?_⟩
  · simp only [← h, and_self]
    exact (G.edge_mem_iff_exists_isLink e).mp heG
  · ext u v
    rw [hG.isLink_iff_sym2_eq, hH.isLink_iff_sym2_eq]

/-- The set of ends of an edge `e`. -/
@[grind]
def endSet (G : Graph α β) (e : β) : Set α := {x | G.Inc e x}

notation "V(" G ", " e ")" => Graph.endSet G e

@[simp, grind =]
lemma mem_endSet_iff : x ∈ V(G, e) ↔ G.Inc e x := Iff.rfl

@[grind →]
lemma IsLink.endSet_eq (h : G.IsLink e x y) : V(G, e) = {x, y} := by
  ext a
  grind

@[grind →]
lemma IsLoopAt.endSet_eq (h : G.IsLoopAt e x) : V(G, e) = {x} := by
  rw [IsLink.endSet_eq h, pair_eq_singleton]

@[grind →]
lemma endSet_eq_of_notMem (he : e ∉ E(G)) : V(G, e) = ∅ := by
  simp only [endSet, eq_empty_iff_forall_notMem, mem_setOf_eq]
  exact fun x hx ↦ he hx.edge_mem

lemma inc_iff_isLoopAt_or_isNonloopAt : G.Inc e x ↔ G.IsLoopAt e x ∨ G.IsNonloopAt e x :=
  ⟨Inc.isLoopAt_or_isNonloopAt, fun h ↦ h.elim IsLoopAt.inc IsNonloopAt.inc⟩

@[simp, grind! .]
lemma endSet_encard_le_two (G : Graph α β) (e : β) : V(G, e).encard ≤ 2 := by
  by_cases heE : e ∈ E(G)
  · obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet heE
    rw [h.endSet_eq]
    by_cases hxy : x = y <;> simp [hxy, encard_pair]
  simp [endSet_eq_of_notMem heE]

/-- The set of vertices incident to at least one edge in `F`.
Also known as the vertex set of the edge set `F`. -/
@[grind]
def incVertexSet (G : Graph α β) (F : Set β) : Set α := {x | ∃ e ∈ F, G.Inc e x}

notation "V(" G ", " F ")" => Graph.incVertexSet G F

@[simp, grind =]
lemma mem_incVertexSet_iff : x ∈ V(G, F) ↔ ∃ e ∈ F, G.Inc e x := Iff.rfl

@[simp, grind! .]
lemma incVertexSet_subset (G : Graph α β) (F : Set β) : V(G, F) ⊆ V(G) := by
  rintro x ⟨e, hS, he⟩
  exact he.vertex_mem

lemma incVertexSet_eq_sUnion (G : Graph α β) (F : Set β) : V(G, F) = ⋃ e ∈ F, V(G, e) := by
  ext x
  simp

lemma incVertexSet_encard_le (G : Graph α β) (F : Set β) : V(G, F).encard ≤ 2 * F.encard := by
  rw [incVertexSet_eq_sUnion]
  obtain hinf | hfin := F.finite_or_infinite.symm
  · simp [hinf]
  have : Fintype F := hfin.fintype
  refine (hfin.encard_biUnion_le (V(G, ·))).trans ?_
  grw [finsum_mem_eq_sum _ (hfin.inter_of_left _), Finset.sum_le_card_nsmul _ _ 2 (by simp)]
  simp only [nsmul_eq_mul, mul_comm, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    ENat.ofNat_ne_top, ENat.mul_le_mul_left_iff]
  refine le_trans ?_ (encard_eq_coe_toFinset_card F).ge
  refine ENat.coe_le_coe.mpr <| Finset.card_le_card <| by simp

lemma incVertexSet_inter_edgeSet (G : Graph α β) (F : Set β) : V(G, F ∩ E(G)) = V(G, F) := by
  ext x
  simp only [mem_incVertexSet_iff, mem_inter_iff]
  refine exists_congr fun e ↦ and_congr_left fun he ↦ and_iff_left_of_imp fun _ ↦ he.edge_mem

/-- The function mapping an edge of `G` to an unordered pair of its endpoints
(as elements of the vertex subtype).
Used mostly as an implementation detail. -/
@[grind]
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

lemma inc_eq_inc_iff {G₁ G₂ : Graph α β} : G₁.Inc e = G₂.Inc f ↔ G₁.IsLink e = G₂.IsLink f := by
  constructor <;> rintro h
  · ext x y
    rw [isLink_iff_inc, isLink_iff_inc, h]
  · simp [funext_iff, Inc, h]

section parallel

/-- Two edges `e` and `f` are parallel in `G` if they are both in the edge set of `G`
and have the same endpoints (i.e., the same `IsLink` function). -/
@[grind]
def parallel (G : Graph α β) (e f : β) : Prop :=
  e ∈ E(G) ∧ f ∈ E(G) ∧ G.IsLink e = G.IsLink f

lemma parallel.left_mem (h : G.parallel e f) : e ∈ E(G) := h.1

lemma parallel.right_mem (h : G.parallel e f) : f ∈ E(G) := h.2.1

lemma parallel.isLink_eq (h : G.parallel e f) : G.IsLink e = G.IsLink f := h.2.2

@[simp]
lemma parallel_refl (he : e ∈ E(G)) : G.parallel e e := ⟨he, he, rfl⟩

@[simp]
lemma parallel_refl_iff : G.parallel e e ↔ e ∈ E(G) :=
  ⟨fun h => h.left_mem, parallel_refl⟩

lemma parallel_iff_inc_eq (G : Graph α β) (e f : β) :
    G.parallel e f ↔ e ∈ E(G) ∧ f ∈ E(G) ∧ G.Inc e = G.Inc f := by
  refine ⟨fun ⟨he, hf, h⟩ ↦ ⟨he, hf, ?_⟩, fun ⟨he, hf, h⟩ ↦ ⟨he, hf, ?_⟩⟩
  · rwa [inc_eq_inc_iff]
  · rwa [inc_eq_inc_iff] at h

lemma inc_eq_inc_iff_parallel (G : Graph α β) {e f : β} (he : e ∈ E(G)) (hf : f ∈ E(G)) :
    G.Inc e = G.Inc f ↔ G.parallel e f := by
  simp [parallel_iff_inc_eq, he, hf]

lemma parallel.inc_eq (h : G.parallel e f) : G.Inc e = G.Inc f := by
  obtain ⟨he, hf, h⟩ := G.parallel_iff_inc_eq e f |>.mp h
  exact h

@[symm]
lemma parallel.symm (h : G.parallel e f) : G.parallel f e := by
  obtain ⟨he, hf, h⟩ := h
  exact ⟨hf, he, h.symm⟩

instance : Std.Symm G.parallel where
  symm _ _ := parallel.symm

lemma parallel_comm : G.parallel e f ↔ G.parallel f e := ⟨(·.symm), (·.symm)⟩

lemma parallel.trans {g : β} (h : G.parallel e f) (h' : G.parallel f g) : G.parallel e g := by
  obtain ⟨he, hf, h⟩ := h
  obtain ⟨hf, hg, h'⟩ := h'
  exact ⟨he, hg, h.trans h'⟩

instance : IsTrans _ G.parallel where
  trans _ _ _ := parallel.trans

end parallel

section Neighborhood

/-- The set of vertices adjacent to `x` in `G`. Also called the (open) neighborhood of `x`. -/
@[grind]
def Neighbor (G : Graph α β) (x : α) : Set α := {y | G.Adj x y}

notation "N(" G ", " x ")" => Neighbor G x

@[simp]
lemma neighbor_subset (G : Graph α β) (x : α) : N(G, x) ⊆ V(G) := by grind

@[simp]
lemma notMem_neighbor_of_not_adj (hadj : ¬ G.Adj x y) : y ∉ N(G, x) := by grind

lemma neighbor_subset_of_ne_not_adj (hne : x ≠ y) (hadj : ¬ G.Adj x y) :
    N(G, x) \ {x} ⊆ V(G) \ {x, y} := by
  rintro z ⟨hz, hne⟩
  rw [mem_singleton_iff] at hne
  simp only [mem_diff, hz.right_mem, mem_insert_iff, hne, mem_singleton_iff, false_or,
    true_and]
  rintro rfl
  exact hadj hz

/-- The set of vertices outside `S` that are adjacent to at least one vertex in `S`.
Also called the (external) neighborhood of `S`. -/
@[grind]
def SetNeighbor (G : Graph α β) (S : Set α) : Set α := {y | y ∉ S ∧ ∃ x ∈ S, G.Adj x y}

notation "N(" G ", " S ")" => SetNeighbor G S

@[simp]
lemma setNeighbor_subset (G : Graph α β) (S : Set α) : N(G, S) ⊆ V(G) := by
  rintro y ⟨hyS, x, hxS, hadj⟩
  exact hadj.right_mem

@[simp]
lemma setNeighbor_disjoint (G : Graph α β) (S : Set α) : Disjoint S N(G, S) := by
  rw [disjoint_iff_forall_ne]
  rintro a haS y ⟨hyS, x, hxS, hxy⟩
  exact ne_of_mem_of_not_mem haS hyS

@[simp]
lemma notMem_setNeighbor_of_not_adj (hadj : ¬ G.Adj x y) : y ∉ N(G, {x}) := by
  simp [SetNeighbor, hadj]

/-- The set of edges incident to vertex `v` in `G`. -/
@[grind]
def IncEdges (G : Graph α β) (v : α) : Set β := {e | G.Inc e v}

notation "E(" G ", " v ")" => IncEdges G v

@[simp]
lemma incEdges_subset (G : Graph α β) (v : α) : E(G, v) ⊆ E(G) := by
  rintro e he
  exact he.edge_mem

@[simp, grind =]
lemma mem_incEdges_iff (G : Graph α β) (v : α) (e : β) : e ∈ E(G, v) ↔ G.Inc e v := Iff.rfl

/-- The set of edges incident to at least one vertex in `S`. -/
@[grind]
def SetIncEdges (G : Graph α β) (S : Set α) : Set β := {e | ∃ x ∈ S, G.Inc e x}

notation "E(" G ", " S ")" => SetIncEdges G S

@[simp, grind .]
lemma setIncEdges_subset (G : Graph α β) (S : Set α) : E(G, S) ⊆ E(G) := by
  rintro e ⟨x, hxS, he⟩
  exact he.edge_mem

lemma setIncEdges_mono_right (G : Graph α β) {S T : Set α} (hST : S ⊆ T) : E(G, S) ⊆ E(G, T) := by
  rintro e ⟨x, hxS, he⟩
  exact ⟨x, hST hxS, he⟩

@[simp, grind =]
lemma mem_setIncEdges_iff (G : Graph α β) (S : Set α) : e ∈ E(G, S) ↔ ∃ x ∈ S, G.Inc e x := by
  simp [SetIncEdges]

@[simp, grind =]
lemma setIncEdges_singleton (G : Graph α β) (x : α) : E(G, {x}) = E(G, x) := by
  simp [SetIncEdges, IncEdges]

lemma incEdge_subset_setIncEdges (G : Graph α β) {S : Set α} (hx : x ∈ S) : E(G, x) ⊆ E(G, S) := by
  rw [← setIncEdges_singleton]
  exact G.setIncEdges_mono_right <| by simpa

/-- The set of edges linking vertices `u` and `v` in `G`.
When `u = v`, this is the set of loops at `u`. -/
@[grind]
def LinkEdges (G : Graph α β) (u v : α) : Set β := {e | G.IsLink e u v}

notation "E(" G ", " u ", " v ")" => LinkEdges G u v

@[simp]
lemma linkEdges_empty (G : Graph α β) (u v : α) : E(G, u, v) = ∅ ↔ ¬ G.Adj u v := by
  simp [LinkEdges, Adj, Set.ext_iff]

@[simp]
lemma linkEdges_self (G : Graph α β) (u : α) : E(G, u, u) = {e | G.IsLoopAt e u} := rfl

@[simp, grind =]
lemma mem_linkEdges_iff (G : Graph α β) (u v : α) (e : β) : e ∈ E(G, u, v) ↔ G.IsLink e u v :=
  Iff.rfl

lemma linkEdges_subset_incEdges_left (G : Graph α β) (u v : α) : E(G, u, v) ⊆ E(G, u) :=
  fun _ hxy ↦ ⟨v, hxy⟩

lemma linkEdges_subset_incEdges_right (G : Graph α β) (u v : α) : E(G, u, v) ⊆ E(G, v) :=
  fun _ hxy ↦ ⟨u, hxy.symm⟩

@[simp]
lemma linkEdges_eq_empty_of_left_not_mem (hu : u ∉ V(G)) (v) : E(G, u, v) = ∅ := by
  rw [linkEdges_empty]
  exact mt Adj.left_mem hu

@[simp]
lemma linkEdges_eq_empty_of_right_not_mem (u) (hv : v ∉ V(G)) : E(G, u, v) = ∅ := by
  rw [linkEdges_empty]
  exact mt Adj.right_mem hv

lemma linkEdges_comm (G : Graph α β) (u v : α) : E(G, u, v) = E(G, v, u) := by
  ext e
  simp [isLink_comm]

/-- The set of edges with one endpoint in `S` and one endpoint in `T`. -/
@[grind]
def SetLinkEdges (G : Graph α β) (S T : Set α) : Set β := {e | ∃ x ∈ S, ∃ y ∈ T, G.IsLink e x y}

notation "E(" G ", " S ", " T ")" => SetLinkEdges G S T

/-- The edge boundary (or cut) of `S`: edges with one endpoint in `S`
and one endpoint outside `S`. -/
notation "δ(" G ", " S ")" => SetLinkEdges G S (V(G) \ S)

@[grind =]
lemma mem_setLinkEdges_iff (G : Graph α β) (S T : Set α) (e : β) :
  e ∈ E(G, S, T) ↔ ∃ x ∈ S, ∃ y ∈ T, G.IsLink e x y := Iff.rfl

lemma IsLink.mem_setLinkEdges_iff (h : G.IsLink e x y) :
    e ∈ E(G, S, T) ↔ x ∈ S ∧ y ∈ T ∨ x ∈ T ∧ y ∈ S := by
  refine ⟨fun ⟨a, haS, b, hbT, hab⟩ => ?_, ?_⟩
  · grind [h.eq_and_eq_or_eq_and_eq hab]
  rintro (⟨hxS, hyT⟩ | ⟨hxT, hyS⟩) <;> simp only [G.mem_setLinkEdges_iff]
  · use x, hxS, y, hyT, h
  use y, hyS, x, hxT, h.symm

lemma setLinkEdges_subset (G : Graph α β) (S T : Set α) : E(G, S, T) ⊆ E(G) := by
  rintro e ⟨x, hxS, y, hyT, he⟩
  exact he.edge_mem

lemma setLinkEdges_mono_left (G : Graph α β) (hST : S ⊆ X) : E(G, S, T) ⊆ E(G, X, T) := by
  rintro e ⟨x, hxS, y, hyT, he⟩
  exact ⟨x, hST hxS, y, hyT, he⟩

lemma setLinkEdges_mono_right (G : Graph α β) (hST : T ⊆ Y) : E(G, S, T) ⊆ E(G, S, Y) := by
  rintro e ⟨x, hxS, y, hyT, he⟩
  exact ⟨x, hxS, y, hST hyT, he⟩

lemma setLinkEdges_comm (G : Graph α β) (S T : Set α) : E(G, S, T) = E(G, T, S) := by
  ext e
  exact ⟨fun ⟨x, hxS, y, hyT, hxy⟩ => ⟨y, hyT, x, hxS, hxy.symm⟩,
    fun ⟨y, hyT, x, hxS, hxy⟩ => ⟨x, hxS, y, hyT, hxy.symm⟩⟩

lemma setLinkEdges_vertexSet_inter_left (G : Graph α β) (S T : Set α) :
    E(G, V(G) ∩ S, T) = E(G, S, T) := by
  ext e
  exact ⟨fun ⟨x, ⟨hx, hxS⟩, y, hyT, hxy⟩ => ⟨x, hxS, y, hyT, hxy⟩,
    fun ⟨x, hxS, y, hyT, hxy⟩ => ⟨x, ⟨hxy.left_mem, hxS⟩, y, hyT, hxy⟩⟩

lemma setLinkEdges_vertexSet_inter_right (G : Graph α β) (S T : Set α) :
    E(G, S, V(G) ∩ T) = E(G, S, T) := by
  ext e
  exact ⟨fun ⟨x, hxS, y, ⟨hy, hyT⟩, hxy⟩ => ⟨x, hxS, y, hyT, hxy⟩,
    fun ⟨x, hxS, y, hyT, hxy⟩ => ⟨x, hxS, y, ⟨hxy.right_mem, hyT⟩, hxy⟩⟩

lemma setLinkEdges_subset_setIncEdges_left (G : Graph α β) (S T : Set α) :
    E(G, S, T) ⊆ E(G, S) := by
  rintro e ⟨x, hxS, y, hyT, hxy⟩
  exact ⟨x, hxS, hxy.inc_left⟩

lemma setLinkEdges_subset_setIncEdges_right (G : Graph α β) (S T : Set α) :
    E(G, S, T) ⊆ E(G, T) := by
  rintro e ⟨x, hxS, y, hyT, hxy⟩
  exact ⟨y, hyT, hxy.inc_right⟩

end Neighborhood


/-! ### Isolated vertices

An isolated vertex is a vertex that is incident with no edges.
-/

/-- An `Isolated` vertex is one that is incident with no edge but is in the vertex set. -/
@[mk_iff, grind]
structure Isolated (G : Graph α β) (x : α) : Prop where
  not_inc : ∀ ⦃e⦄, ¬ G.Inc e x
  mem : x ∈ V(G)

@[simp]
lemma Isolated.not_adj (h : G.Isolated x) : ¬ G.Adj x y :=
  fun ⟨_, he⟩ ↦ h.not_inc he.inc_left

@[simp]
lemma Isolated.not_isLink (h : G.Isolated x) : ¬ G.IsLink e x y :=
  fun he ↦ h.not_inc he.inc_left

lemma isolated_or_exists_isLink (hx : x ∈ V(G)) : G.Isolated x ∨ ∃ e y, G.IsLink e x y := by
  simp [isolated_iff, Inc, ← not_exists, hx, em']

/-- The set of isolated vertices in `G`. -/
@[grind]
def IsolatedSet (G : Graph α β) : Set α := {x | G.Isolated x}

notation "I(" G ")" => IsolatedSet G

@[simp]
lemma mem_isolatedSet_iff (G : Graph α β) (x : α) : x ∈ I(G) ↔ G.Isolated x := Iff.rfl

@[simp]
lemma isolatedSet_subset (G : Graph α β) : I(G) ⊆ V(G) := by
  rintro x ⟨h, hx⟩
  exact hx

@[simp]
lemma setincEdges_isolatedSet (G : Graph α β) : E(G, I(G)) = ∅ := by
  simp +contextual [Set.ext_iff, isolated_iff]

@[simp]
lemma not_isolated_iff (hv : v ∈ V(G)) : ¬ G.Isolated v ↔ ∃ e, G.Inc e v := by
  simp [isolated_iff, hv]

@[simp]
lemma incEdges_empty_iff (hv : v ∈ V(G)) : E(G, v) = ∅ ↔ G.Isolated v := by
  simp [IncEdges, isolated_iff, hv, eq_empty_iff_forall_notMem]

@[simp]
lemma SetIncEdges_empty_iff {S} (hS : S ⊆ V(G)) : E(G, S) = ∅ ↔ S ⊆ I(G) := by
  simp only [SetIncEdges, eq_empty_iff_forall_notMem, mem_setOf_eq, not_exists, not_and]
  refine ⟨fun h x hxS ↦ ?_, fun h e x hxS ↦ (h hxS |>.not_inc ·)⟩
  simp only [mem_isolatedSet_iff, isolated_iff, hS hxS, and_true]
  exact fun e ↦ h e x hxS

@[simp]
lemma IsLink.left_not_isolated (h : G.IsLink e x y) : ¬ G.Isolated x :=
  fun h' ↦ h'.not_inc h.inc_left

@[simp]
lemma IsLink.right_not_isolated (h : G.IsLink e x y) : ¬ G.Isolated y :=
  fun h' ↦ h'.not_inc h.inc_right

/-! ### Leaves

A leaf (or degree-one vertex) is a vertex with exactly one incident edge,
and that edge is a nonloop.
A pendant edge is an edge that is the unique edge incident to one of its endpoints.
-/

/-- `G.IsPendant e x` means that `e` is a nonloop edge at `x`,
and is the unique edge incident to `x`. -/
@[mk_iff, grind]
structure IsPendant (G : Graph α β) (e : β) (x : α) : Prop where
  isNonloopAt : G.IsNonloopAt e x
  edge_unique : ∀ ⦃f⦄, G.Inc f x → f = e

lemma IsPendant.not_isLoopAt (h : G.IsPendant e x) (f : β) : ¬ G.IsLoopAt f x := by
  refine fun h' ↦ h.isNonloopAt.not_isLoopAt x ?_
  rwa [← h.edge_unique h'.inc]

/-- A leaf (or degree-one vertex) is a vertex that has exactly one incident edge,
which is a nonloop. -/
@[grind]
def IsLeaf (G : Graph α β) (v : α) : Prop := ∃ e, G.IsPendant e v

lemma IsPendant.isLeaf (h : G.IsPendant e x) : G.IsLeaf x :=
  ⟨e, h⟩

lemma IsLeaf.mem (h : G.IsLeaf v) : v ∈ V(G) :=
  h.choose_spec.isNonloopAt.vertex_mem

lemma IsLeaf.vertexSet_nontrivial (h : G.IsLeaf v) : V(G).Nontrivial := by
  obtain ⟨e, he⟩ := h
  exact he.isNonloopAt.vertexSet_nontrivial

lemma IsLeaf.exists_unique_inc (h : G.IsLeaf x) : ∃! e, G.Inc e x :=
  ⟨h.choose, h.choose_spec.isNonloopAt.inc, h.choose_spec.edge_unique⟩

lemma IsLeaf.exists_unique_adj (h : G.IsLeaf x) : ∃! y, G.Adj x y := by
  obtain ⟨e, ⟨y, he⟩, hunique⟩ := h.exists_unique_inc
  refine ⟨y, he.adj, fun z ⟨f, hz⟩ ↦ ?_⟩
  rw [hunique f hz.inc_left] at hz
  exact hz.right_unique he

lemma IsLeaf.eq_of_adj_adj (h : G.IsLeaf x) (hu : G.Adj x u) (hv : G.Adj x v) :
    u = v := by
  obtain ⟨y, hy, hun⟩ := h.exists_unique_adj
  rw [hun u hu, hun v hv]

lemma IsLeaf.eq_of_inc_inc (h : G.IsLeaf x) (he : G.Inc e x) (hf : G.Inc f x) :
    e = f := by
  obtain ⟨g, hg, hun⟩ := h.exists_unique_inc
  rw [hun e he, hun f hf]

lemma IsLeaf.not_adj_self (h : G.IsLeaf x) : ¬ G.Adj x x := by
  rintro ⟨e, he : G.IsLoopAt e x⟩
  obtain ⟨f, h⟩ := h
  exact h.not_isLoopAt e he

lemma IsLeaf.ne_of_adj (h : G.IsLeaf x) (hxy : G.Adj x y) : x ≠ y :=
  fun h' ↦ h.not_adj_self <| h' ▸ hxy

lemma IsLeaf.not_isLoopAt (h : G.IsLeaf x) (e) : ¬ G.IsLoopAt e x :=
  fun h' ↦ h.not_adj_self h'.adj

/-- A leaf edge (or pendant edge) is an edge that is the unique edge incident to (at least)
one of its endpoints. -/
@[grind]
def IsLeafEdge (G : Graph α β) (e : β) := ∃ x, G.IsPendant e x
