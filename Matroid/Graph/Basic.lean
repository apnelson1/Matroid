import Mathlib.Combinatorics.Graph.Basic

variable {α β : Type*} {x y z u v w : α} {e f : β} {G H : Graph α β}

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

instance : IsSymm _ G.Adj where
  symm _ _ := Adj.symm

/- these two commands should be incorporated directly into the declarations
of `Adj.symm` and `IsLink.symm`, like so:
```
@[symm]
protected lemma Adj.symm (h : G.Adj x y) : G.Adj y x :=
  ⟨_, h.choose_spec.symm⟩
```
-/
attribute [symm] Adj.symm
attribute [symm] IsLink.symm

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

instance : IsSymm _ G.parallel where
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

def Neighbor (G : Graph α β) (x : α) : Set α := {y | y ≠ x ∧ G.Adj x y}

notation "N(" G ", " x ")" => Neighbor G x

@[simp]
lemma neighbor_subset (G : Graph α β) (x : α) : N(G, x) ⊆ V(G) := by
  rintro y ⟨hne, hy⟩
  exact hy.right_mem

@[simp]
lemma self_notMem_Neighbor (G : Graph α β) (x : α) : x ∉ N(G, x) := by
  simp [Neighbor]

@[simp]
lemma notMem_neighbor_of_not_adj (hadj : ¬ G.Adj x y) : y ∉ N(G, x) := by
  simp [Neighbor, hadj]

lemma neighbor_subset_of_ne_not_adj (hne : x ≠ y) (hadj : ¬ G.Adj x y) :
    N(G, x) ⊆ V(G) \ {x, y} := by
  rintro z ⟨hne, hz⟩
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

def IncidentEdges (G : Graph α β) (v : α) : Set β := {e | G.Inc e v}

notation "E(" G ", " v ")" => IncidentEdges G v

@[simp]
lemma incidentEdges_subset (G : Graph α β) (v : α) : E(G, v) ⊆ E(G) := by
  rintro e he
  exact he.edge_mem

def SetIncidentEdges (G : Graph α β) (S : Set α) : Set β := {e | ∃ x ∈ S, G.Inc e x}

notation "E(" G ", " S ")" => SetIncidentEdges G S

@[simp]
lemma setIncidentEdges_subset (G : Graph α β) (S : Set α) : E(G, S) ⊆ E(G) := by
  rintro e ⟨x, hxS, he⟩
  exact he.edge_mem

@[simp]
lemma mem_setIncidentEdges_iff (G : Graph α β) (S : Set α) :
    e ∈ E(G, S) ↔ ∃ x ∈ S, G.Inc e x := by
  simp [SetIncidentEdges]

end Neighborhood

@[simps]
def LineGraph (G : Graph α β) : Graph β (Sym2 β) where
  vertexSet := E(G)
  edgeSet := Sym2.mk '' { (e, f) | ∃ x, G.Inc e x ∧ G.Inc f x }
  IsLink a e f := (∃ x, G.Inc e x ∧ G.Inc f x) ∧ s(e, f) = a
  edge_mem_iff_exists_isLink a := by simp only [mem_image, mem_setOf_eq, Prod.exists]
  isLink_symm a ha e f hef := by
    simp_all only [mem_image, mem_setOf_eq, Prod.exists]
    simp_rw [and_comm, ← hef.2]
    simp [hef.1]
  eq_or_eq_of_isLink_of_isLink := by
    rintro a e f g h ⟨hef, rfl⟩ ⟨hgf, heq⟩
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at heq
    tauto
  left_mem_of_isLink := by
    rintro a e f ⟨⟨x, he, hf⟩, rfl⟩
    exact he.edge_mem

def IsStable (G : Graph α β) (S : Set α) : Prop :=
  S.Pairwise (¬ G.Adj · ·)
