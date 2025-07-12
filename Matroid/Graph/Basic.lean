-- import Mathlib.Combinatorics.Graph.Basic
import Matroid.Graph.Basic'
import Matroid.ForMathlib.SetPartition

variable {α β : Type*} {x y z u v w : α} {e f : β} {G H : Graph α β}


open Set

namespace Graph


/-
For mathlib
-/

@[simp]
lemma not_isLink_of_notMem_edgeSet (he : e ∉ E(G)) : ¬ G.IsLink e x y :=
  mt IsLink.edge_mem he

@[simp]
lemma not_inc_of_notMem_edgeSet (he : e ∉ E(G)) : ¬ G.Inc e x :=
  mt Inc.edge_mem he

/-- The set of ends of an edge `e`. -/
def endSet (G : Graph α β) (e : β) : Set α := {x | G.Inc e x}

@[simp]
lemma mem_endSet_iff : x ∈ G.endSet e ↔ G.Inc e x := Iff.rfl

-- lemma IsLink.endSet_eq (h : G.IsLink e x y) : G.endSet e = {x,y} := by
--   ext a
--   simp only [mem_endSet_iff, mem_insert_iff, mem_singleton_iff]
--   refine ⟨fun h' ↦ h'.dup_or_dup_of_isLink h, ?_⟩
--   rintro (rfl | rfl)
--   · exact h.inc_left
--   exact h.inc_right

-- lemma IsLoopAt.endSet_eq (h : G.IsLoopAt e x) : G.endSet e = {x} := by
--   rw [IsLink.endSet_eq h, pair_eq_singleton]

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

-- lemma IsLink.ends_eq (h : G.IsLink e x y) :
--     G.ends ⟨e, h.edge_mem⟩ = s(⟨x, h.left_mem⟩,⟨y, h.right_mem⟩) := by
--   simp only [Graph.ends, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Subtype.mk.injEq, Prod.swap_prod_mk]
--   generalize_proofs h₁ h₂
--   exact h₁.choose_spec.choose_spec.dup_and_dup_or_dup_and_dup h

lemma IsNonloopAt.vertexSet_nontrivial (h : G.IsNonloopAt e x) : G.vertexSet.Nontrivial := by
  obtain ⟨y, hne, h⟩ := h
  refine nontrivial_of_mem_mem_ne h.left_mem h.right_mem ?_
  rintro rfl
  exact hne <| dup_of_mem_vertexSet h.left_mem

lemma inc_eq_inc_iff {G₁ G₂ : Graph α β} [G₁.LabelUnique] [G₂.LabelUnique] :
    G₁.Inc e = G₂.Inc f ↔ G₁.IsLink e = G₂.IsLink f := by
  constructor <;> rintro h
  · ext x y
    rw [isLink_iff_inc, isLink_iff_inc, h]
  · simp [funext_iff, Inc, eq_iff_iff, h]

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

-- lemma parallel_iff_inc_eq (G : Graph α β) (e f : β) :
--     G.parallel e f ↔ e ∈ E(G) ∧ f ∈ E(G) ∧ G.Inc e = G.Inc f := by
--   refine ⟨fun ⟨he, hf, h⟩ ↦ ⟨he, hf, ?_⟩, fun ⟨he, hf, h⟩ ↦ ⟨he, hf, ?_⟩⟩
--   · rwa [inc_eq_inc_iff]
--   · rwa [inc_eq_inc_iff] at h

-- lemma inc_eq_inc_iff_parallel (G : Graph α β) {e f : β} (he : e ∈ E(G)) (hf : f ∈ E(G)) :
--     G.Inc e = G.Inc f ↔ G.parallel e f := by
--   simp [parallel_iff_inc_eq, he, hf]

-- lemma parallel.inc_eq (h : G.parallel e f) : G.Inc e = G.Inc f := by
--   obtain ⟨he, hf, h⟩ := G.parallel_iff_inc_eq e f |>.mp h
--   exact h

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

def parallelClasses (G : Graph α β) : Partition E(G) :=
  Partition.ofRel' G.parallel <| by simp


end parallel
