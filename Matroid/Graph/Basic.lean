import Mathlib.Combinatorics.Graph.Basic
import Mathlib.Data.Set.Card.Arithmetic

variable {α β : Type*} {x y z u v w : α} {e f : β} {G H : Graph α β} {F : Set β} {S T X Y : Set α}

open Set

namespace Graph

initialize_simps_projections Graph (IsLink → isLink)

/-
For mathlib
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

/- these two commands should be incorporated directly into the declarations
of `Adj.symm` and `IsLink.symm`, like so:
```
@[symm]
protected lemma Adj.symm (h : G.Adj x y) : G.Adj y x :=
  ⟨_, h.choose_spec.symm⟩
```
-/
attribute [grind →] IsLink.edge_mem IsLink.left_mem IsLink.right_mem Inc.edge_mem Inc.vertex_mem
  IsNonloopAt.edge_mem IsNonloopAt.vertex_mem Adj.left_mem Adj.right_mem
attribute [symm] Adj.symm IsLink.symm

@[simp]
lemma not_isLink_of_notMem_edgeSet (he : e ∉ E(G)) : ¬ G.IsLink e x y :=
  mt IsLink.edge_mem he

@[simp]
lemma not_inc_of_notMem_edgeSet (he : e ∉ E(G)) : ¬ G.Inc e x :=
  mt Inc.edge_mem he

-- A graph G and H has the same IsLink iff there is a pair of vertices they agree on.
lemma isLink_eq_isLink_iff_exists_isLink_of_mem_edgeSet (heG : e ∈ E(G)) :
    G.IsLink e = H.IsLink e ↔ ∃ x y, G.IsLink e x y ∧ H.IsLink e x y := by
  refine ⟨fun h ↦ ?_, fun ⟨x, y, hG, hH⟩ ↦ ?_⟩
  · simp only [← h, and_self]
    exact (G.edge_mem_iff_exists_isLink e).mp heG
  · ext u v
    rw [hG.isLink_iff_sym2_eq, hH.isLink_iff_sym2_eq]

/-- The set of ends of an edge `e`. -/
def endSet (G : Graph α β) (e : β) : Set α := {x | G.Inc e x}

notation "V(" G ", " e ")" => Graph.endSet G e

@[simp]
lemma mem_endSet_iff : x ∈ V(G, e) ↔ G.Inc e x := Iff.rfl

lemma IsLink.endSet_eq (h : G.IsLink e x y) : V(G, e) = {x,y} := by
  ext a
  simp only [mem_endSet_iff, mem_insert_iff, mem_singleton_iff]
  refine ⟨fun h' ↦ h'.eq_or_eq_of_isLink h, ?_⟩
  rintro (rfl | rfl)
  · exact h.inc_left
  exact h.inc_right

lemma IsLoopAt.endSet_eq (h : G.IsLoopAt e x) : V(G, e) = {x} := by
  rw [IsLink.endSet_eq h, pair_eq_singleton]

lemma endSet_eq_of_notMem_edgeSet (he : e ∉ E(G)) : V(G, e) = ∅ := by
  simp only [endSet, eq_empty_iff_forall_notMem, mem_setOf_eq]
  exact fun x hx ↦ he hx.edge_mem

lemma inc_iff_isLoopAt_or_isNonloopAt : G.Inc e x ↔ G.IsLoopAt e x ∨ G.IsNonloopAt e x :=
  ⟨Inc.isLoopAt_or_isNonloopAt, fun h ↦ h.elim IsLoopAt.inc IsNonloopAt.inc⟩

@[simp]
lemma endSet_encard_le_two (G : Graph α β) (e : β) : V(G, e).encard ≤ 2 := by
  by_cases heE : e ∈ E(G)
  · obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet heE
    rw [h.endSet_eq]
    by_cases hxy : x = y <;> simp [hxy, encard_pair]
  simp [endSet_eq_of_notMem_edgeSet heE]

-- Terrible name
def endSetSet (G : Graph α β) (F : Set β) : Set α := {x | ∃ e ∈ F, G.Inc e x}

notation "V(" G ", " F ")" => Graph.endSetSet G F

@[simp]
lemma mem_endSetSet_iff : x ∈ V(G, F) ↔ ∃ e ∈ F, G.Inc e x := Iff.rfl

@[simp]
lemma endSetSet_subset (G : Graph α β) (F : Set β) : V(G, F) ⊆ V(G) := by
  rintro x ⟨e, hS, he⟩
  exact he.vertex_mem

lemma endSetSet_eq_sUnion (G : Graph α β) (F : Set β) : V(G, F) = ⋃ e ∈ F, V(G, e) := by
  ext x
  simp

lemma endSetSet_encard_le (G : Graph α β) (F : Set β) : V(G, F).encard ≤ 2 * F.encard := by
  rw [endSetSet_eq_sUnion]
  obtain hinf | hfin := F.finite_or_infinite.symm
  · simp [hinf]
  have : Fintype F := hfin.fintype
  refine (hfin.encard_biUnion_le (V(G, ·))).trans ?_
  grw [finsum_mem_eq_sum _ (hfin.inter_of_left _), Finset.sum_le_card_nsmul _ _ 2 (by simp)]
  simp only [nsmul_eq_mul, mul_comm, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    ENat.ofNat_ne_top, ENat.mul_le_mul_left_iff]
  refine le_trans ?_ (encard_eq_coe_toFinset_card F).ge
  refine ENat.coe_le_coe.mpr <| Finset.card_le_card <| by simp

lemma endSetSet_inter_edgeSet (G : Graph α β) (F : Set β) : V(G, F ∩ E(G)) = V(G, F) := by
  ext x
  simp only [mem_endSetSet_iff, mem_inter_iff]
  refine exists_congr fun e ↦ and_congr_left fun he ↦ and_iff_left_of_imp fun _ ↦ he.edge_mem

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


lemma inc_eq_inc_iff {G₁ G₂ : Graph α β} : G₁.Inc e = G₂.Inc f ↔ G₁.IsLink e = G₂.IsLink f := by
  constructor <;> rintro h
  · ext x y
    rw [isLink_iff_inc, isLink_iff_inc, h]
  · simp [funext_iff, Inc, h]

section parallel

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

def Neighbor (G : Graph α β) (x : α) : Set α := {y | G.Adj x y}

notation "N(" G ", " x ")" => Neighbor G x

@[simp]
lemma neighbor_subset (G : Graph α β) (x : α) : N(G, x) ⊆ V(G) := by
  rintro y ⟨hne, hy⟩
  exact hy.right_mem

@[simp]
lemma notMem_neighbor_of_not_adj (hadj : ¬ G.Adj x y) : y ∉ N(G, x) := by
  simp [Neighbor, hadj]

lemma neighbor_subset_of_ne_not_adj (hne : x ≠ y) (hadj : ¬ G.Adj x y) :
    N(G, x) \ {x} ⊆ V(G) \ {x, y} := by
  rintro z ⟨hz, hne⟩
  rw [mem_singleton_iff] at hne
  simp only [mem_diff, hz.right_mem, mem_insert_iff, hne, mem_singleton_iff, false_or,
    true_and]
  rintro rfl
  exact hadj hz

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

def IncEdges (G : Graph α β) (v : α) : Set β := {e | G.Inc e v}

notation "E(" G ", " v ")" => IncEdges G v

@[simp]
lemma incEdges_subset (G : Graph α β) (v : α) : E(G, v) ⊆ E(G) := by
  rintro e he
  exact he.edge_mem

@[simp]
lemma mem_incEdges_iff (G : Graph α β) (v : α) (e : β) : e ∈ E(G, v) ↔ G.Inc e v := Iff.rfl

def SetIncEdges (G : Graph α β) (S : Set α) : Set β := {e | ∃ x ∈ S, G.Inc e x}

notation "E(" G ", " S ")" => SetIncEdges G S

@[simp]
lemma setIncEdges_subset (G : Graph α β) (S : Set α) : E(G, S) ⊆ E(G) := by
  rintro e ⟨x, hxS, he⟩
  exact he.edge_mem

lemma setIncEdges_mono_right (G : Graph α β) {S T : Set α} (hST : S ⊆ T) : E(G, S) ⊆ E(G, T) := by
  rintro e ⟨x, hxS, he⟩
  exact ⟨x, hST hxS, he⟩

@[simp]
lemma mem_setIncEdges_iff (G : Graph α β) (S : Set α) : e ∈ E(G, S) ↔ ∃ x ∈ S, G.Inc e x := by
  simp [SetIncEdges]

@[simp]
lemma setIncEdges_singleton (G : Graph α β) (x : α) : E(G, {x}) = E(G, x) := by
  simp [SetIncEdges, IncEdges]

lemma incEdge_subset_setIncEdges (G : Graph α β) {S : Set α} (hx : x ∈ S) : E(G, x) ⊆ E(G, S) := by
  rw [← setIncEdges_singleton]
  exact G.setIncEdges_mono_right <| by simpa

def LinkEdges (G : Graph α β) (u v : α) : Set β := {e | G.IsLink e u v}

notation "E(" G ", " u ", " v ")" => LinkEdges G u v

@[simp]
lemma linkEdges_empty (G : Graph α β) (u v : α) : E(G, u, v) = ∅ ↔ ¬ G.Adj u v := by
  simp [LinkEdges, Adj, Set.ext_iff]

@[simp]
lemma linkEdges_self (G : Graph α β) (u : α) : E(G, u, u) = {e | G.IsLoopAt e u} := by
  simp [LinkEdges]

@[simp]
lemma mem_linkEdges_iff (G : Graph α β) (u v : α) (e : β) : e ∈ E(G, u, v) ↔ G.IsLink e u v := by
  simp [LinkEdges]

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

def LinkEdgesSet (G : Graph α β) (S T : Set α) : Set β := {e | ∃ x ∈ S, ∃ y ∈ T, G.IsLink e x y}

notation "E(" G ", " S ", " T ")" => LinkEdgesSet G S T

notation "δ(" G ", " S ")" => LinkEdgesSet G S (V(G) \ S)

@[grind =]
lemma mem_linkEdgesSet_iff (G : Graph α β) (S T : Set α) (e : β) :
  e ∈ E(G, S, T) ↔ ∃ x ∈ S, ∃ y ∈ T, G.IsLink e x y := Iff.rfl

lemma IsLink.mem_linkEdgesSet_iff (h : G.IsLink e x y) :
    e ∈ E(G, S, T) ↔ x ∈ S ∧ y ∈ T ∨ x ∈ T ∧ y ∈ S := by
  refine ⟨fun ⟨a, haS, b, hbT, hab⟩ => ?_, ?_⟩
  · grind [h.eq_and_eq_or_eq_and_eq hab]
  rintro (⟨hxS, hyT⟩ | ⟨hxT, hyS⟩) <;> simp only [G.mem_linkEdgesSet_iff]
  · use x, hxS, y, hyT, h
  use y, hyS, x, hxT, h.symm

lemma linkEdgesSet_subset (G : Graph α β) (S T : Set α) : E(G, S, T) ⊆ E(G) := by
  rintro e ⟨x, hxS, y, hyT, he⟩
  exact he.edge_mem

lemma linkEdgesSet_mono_left (G : Graph α β) (hST : S ⊆ X) : E(G, S, T) ⊆ E(G, X, T) := by
  rintro e ⟨x, hxS, y, hyT, he⟩
  exact ⟨x, hST hxS, y, hyT, he⟩

lemma linkEdgesSet_mono_right (G : Graph α β) (hST : T ⊆ Y) : E(G, S, T) ⊆ E(G, S, Y) := by
  rintro e ⟨x, hxS, y, hyT, he⟩
  exact ⟨x, hxS, y, hST hyT, he⟩

lemma linkEdgesSet_comm (G : Graph α β) (S T : Set α) : E(G, S, T) = E(G, T, S) := by
  ext e
  exact ⟨fun ⟨x, hxS, y, hyT, hxy⟩ => ⟨y, hyT, x, hxS, hxy.symm⟩,
    fun ⟨y, hyT, x, hxS, hxy⟩ => ⟨x, hxS, y, hyT, hxy.symm⟩⟩

lemma linkEdgesSet_vertexSet_inter_left (G : Graph α β) (S T : Set α) :
    E(G, V(G) ∩ S, T) = E(G, S, T) := by
  ext e
  exact ⟨fun ⟨x, ⟨hx, hxS⟩, y, hyT, hxy⟩ => ⟨x, hxS, y, hyT, hxy⟩,
    fun ⟨x, hxS, y, hyT, hxy⟩ => ⟨x, ⟨hxy.left_mem, hxS⟩, y, hyT, hxy⟩⟩

lemma linkEdgesSet_vertexSet_inter_right (G : Graph α β) (S T : Set α) :
    E(G, S, V(G) ∩ T) = E(G, S, T) := by
  ext e
  exact ⟨fun ⟨x, hxS, y, ⟨hy, hyT⟩, hxy⟩ => ⟨x, hxS, y, hyT, hxy⟩,
    fun ⟨x, hxS, y, hyT, hxy⟩ => ⟨x, hxS, y, ⟨hxy.right_mem, hyT⟩, hxy⟩⟩

end Neighborhood


/-! ### Isolated vertices -/

/-- An `Isolated` vertex is one that is incident with no edge. -/
@[mk_iff]
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

/-! ### Leaves -/

/-- `G.IsPendant e x` means that `e` is a nonloop edge at `x`, and is also the only edge at `x`. -/
@[mk_iff]
structure IsPendant (G : Graph α β) (e : β) (x : α) : Prop where
  isNonloopAt : G.IsNonloopAt e x
  edge_unique : ∀ ⦃f⦄, G.Inc f x → f = e

lemma IsPendant.not_isLoopAt (h : G.IsPendant e x) (f : β) : ¬ G.IsLoopAt f x := by
  refine fun h' ↦ h.isNonloopAt.not_isLoopAt x ?_
  rwa [← h.edge_unique h'.inc]

/-- A leaf is a degree-one vertex. -/
def IsLeaf (G : Graph α β) (v : α) : Prop := ∃ e, G.IsPendant e v

lemma IsPendant.isLeaf (h : G.IsPendant e x) : G.IsLeaf x :=
  ⟨e, h⟩

lemma IsLeaf.mem (h : G.IsLeaf v) : v ∈ V(G) :=
  h.choose_spec.isNonloopAt.vertex_mem

lemma IsLeaf.vertexSet_nontrivial (h : G.IsLeaf v) : V(G).Nontrivial := by
  obtain ⟨e, he⟩ := h
  exact he.isNonloopAt.vertexSet_nontrivial

/-- Maybe not needed with `IsPendant`. -/
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

/-- A leaf edge is an edge incident with a degree-one vertex. -/
def IsLeafEdge (G : Graph α β) (e : β) := ∃ x, G.IsPendant e x
