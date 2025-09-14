-- import Mathlib.Combinatorics.Graph.Basic
import Matroid.Graph.Basic
import Matroid.ForMathlib.Partition.Set

variable {α β : Type*} {x y z u v w : Set α} {e f : β} {G H : Graph α β}


open Set Partition

namespace Graph


-- lemma IsLink.endSet_eq (h : G.IsLink e x y) : G.endSet e = {x,y} := by
--   ext a
--   simp only [mem_endSet_iff, mem_insert_iff, mem_singleton_iff]
--   refine ⟨fun h' ↦ h'.dup_or_dup_of_isLink h, ?_⟩
--   rintro (rfl | rfl)
--   · exact h.inc_left
--   exact h.inc_right

-- lemma IsLoopAt.endSet_eq (h : G.IsLoopAt e x) : G.endSet e = {x} := by
--   rw [IsLink.endSet_eq h, pair_eq_singleton]



-- class Nodup (G : Graph α β) : Prop where
--   vertexSet_atomic : Atomic V(G)

-- lemma vertexSet_atomic (G : Graph α β) [G.Nodup] : Atomic V(G) := Nodup.vertexSet_atomic

-- lemma eq_of_dup [G.Nodup] (h : V(G) x y) : x = y :=
--   G.vertexSet_atomic.eq_of_rel h

-- lemma mem_labelSet_iff_singleton_vertex [G.Nodup] : x ∈ L(G) ↔ {x} ∈ V(G) := by
--   refine ⟨fun ⟨s, hs, hxs⟩ ↦ ?_, fun h ↦ ⟨{x}, h, rfl⟩⟩
--   obtain ⟨t, ht, hxt⟩ := G.vertexSet_atomic.exists_singleton_of_mem hs
--   subst x
--   exact hs

-- @[simp]
-- lemma dup_iff_eq [G.Nodup] : V(G) x y ↔ x = y ∧ ∃ v ∈ V(G), x ∈ v := by
--   simp [G.vertexSet_atomic.rel_eq, mem_supp_iff]

-- lemma vertexSet_eq_discrete [G.Nodup] : V(G) = Partition.discrete L(G) := by
--   ext x y
--   rw [dup_iff_eq, rel_discrete_iff, mem_supp_iff]

-- lemma eq_or_eq_of_isLink_of_isLink [G.Nodup] (huv : G.IsLink e u v) (hxy : G.IsLink e x y) :
--     u = x ∨ u = y := by
--   obtain h | h := G.dup_or_dup_of_isLink_of_isLink huv hxy
--   · change V(G) u x at h
--     rw [dup_iff_eq] at h
--     tauto
--   · change V(G) u y at h
--     rw [dup_iff_eq] at h
--     tauto

-- lemma IsLink.left_eq_or_eq [G.Nodup] (h : G.IsLink e x y) (h' : G.IsLink e z w) :
--     x = z ∨ x = w := G.eq_or_eq_of_isLink_of_isLink h h'

-- lemma IsLink.right_eq_or_eq [G.Nodup] (h : G.IsLink e x y) (h' : G.IsLink e z w) :
--     y = z ∨ y = w := h.symm.left_eq_or_eq h'

-- lemma IsLink.left_eq_of_right_ne [G.Nodup] (h : G.IsLink e x y) (h' : G.IsLink e z w)
--     (hne : x ≠ z) : x = w := by
--   obtain hx | hx := h.left_dup_or_dup h' <;> rw [dup_iff_eq] at hx <;> tauto

-- lemma IsLink.right_unique [G.Nodup] (h : G.IsLink e x y) (h' : G.IsLink e x z) : y = z :=
--   eq_of_dup <| h.right_unique_dup h'

-- lemma IsLink.left_unique [G.Nodup] (h : G.IsLink e x z) (h' : G.IsLink e y z) : x = y :=
--   h.symm.right_unique h'.symm

-- lemma IsLink.eq_and_eq_or_eq_and_eq [G.Nodup] {x' y' : α} (h : G.IsLink e x y)
--     (h' : G.IsLink e x' y') : x = x' ∧ y = y' ∨ x = y' ∧ y = x' := by
--   obtain rfl | rfl := h.left_eq_or_eq h'
--   · simp [h.right_unique h']
--   simp [h'.symm.right_unique h]

-- lemma IsLink.isLink_iff [G.Nodup] (h : G.IsLink e x y) {x' y' : α} :
--     G.IsLink e x' y' ↔ (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
--   refine ⟨h.eq_and_eq_or_eq_and_eq, ?_⟩
--   rintro (⟨rfl, rfl⟩ | ⟨rfl,rfl⟩)
--   · assumption
--   exact h.symm

-- lemma IsLink.isLink_iff_sym2_eq [G.Nodup] (h : G.IsLink e x y) {x' y' : α} :
--     G.IsLink e x' y' ↔ s(x,y) = s(x',y') := by
--   rw [h.isLink_iff, Sym2.eq_iff]

-- lemma Inc.eq_or_eq_of_isLink [G.Nodup] (h : G.Inc e x) (h' : G.IsLink e y z) :
--     x = y ∨ x = z := h.choose_spec.left_eq_or_eq h'

-- lemma Inc.eq_of_isLink_of_ne_left [G.Nodup] (h : G.Inc e x) (h' : G.IsLink e y z)
--     (hxy : x ≠ y) : x = z :=
--   (h.eq_or_eq_of_isLink h').elim (False.elim ∘ hxy) id

-- lemma IsLink.isLink_iff_eq [G.Nodup] (h : G.IsLink e x y) : G.IsLink e x z ↔ z = y :=
--   ⟨fun h' ↦ h'.right_unique h, fun h' ↦ h' ▸ h⟩

-- /-- The binary incidence predicate can be expressed in terms of the unary one. -/
-- lemma isLink_iff_inc [G.Nodup] :
--     G.IsLink e x y ↔ G.Inc e x ∧ G.Inc e y ∧ ∀ z, G.Inc e z → z = x ∨ z = y := by
--   refine ⟨fun h ↦ ⟨h.inc_left, h.inc_right, fun z h' ↦ h'.eq_or_eq_of_isLink h⟩, ?_⟩
--   rintro ⟨⟨x', hx'⟩, ⟨y', hy'⟩, h⟩
--   obtain rfl | rfl := h _ hx'.inc_right
--   · obtain rfl | rfl := hx'.left_eq_or_eq hy'
--     · assumption
--     exact hy'.symm
--   assumption

-- lemma Inc.eq_or_eq_or_eq [G.Nodup] (hx : G.Inc e x) (hy : G.Inc e y) (hz : G.Inc e z) :
--     x = y ∨ x = z ∨ y = z := by
--   by_contra! hcon
--   obtain ⟨x', hx'⟩ := hx
--   obtain rfl := hy.eq_of_isLink_of_ne_left hx' hcon.1.symm
--   obtain rfl := hz.eq_of_isLink_of_ne_left hx' hcon.2.1.symm
--   exact hcon.2.2 rfl

-- lemma IsLoopAt.eq_of_inc [G.Nodup] (h : G.IsLoopAt e x) (h' : G.Inc e y) : x = y := by
--   obtain rfl | rfl := h'.eq_or_eq_of_isLink h <;> rfl

-- lemma endSet_eq_of_notMem_edgeSet (he : e ∉ E(G)) : G.endSet e = ∅ := by
--   simp only [endSet, eq_empty_iff_forall_notMem, mem_setOf_eq]
--   exact fun x hx ↦ he hx.edge_mem

-- lemma inc_iff_isLoopAt_or_isNonloopAt : G.Inc e x ↔ G.IsLoopAt e x ∨ G.IsNonloopAt e x :=
--   ⟨Inc.isLoopAt_or_isNonloopAt, fun h ↦ h.elim IsLoopAt.inc IsNonloopAt.inc⟩

-- /-- The function which maps a term in the subtype of edges of `G` to an unordered pair of
-- elements in the subtype of vertices of `G`.
-- Used mostly as an implementation details. -/
-- protected noncomputable def ends (G : Graph α β) (e : E(G)) : Sym2 (L(G) : Set α) :=
--   have h := exists_isLink_of_mem_edgeSet e.2
--   s(⟨_, h.choose_spec.choose_spec.left_mem⟩,
--     ⟨_, h.choose_spec.choose_spec.right_mem⟩)

-- -- lemma IsLink.ends_eq (h : G.IsLink e x y) :
-- --     G.ends ⟨e, h.edge_mem⟩ = s(⟨x, h.left_mem⟩,⟨y, h.right_mem⟩) := by
-- --   simp only [Graph.ends, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Subtype.mk.injEq,
-- --     Prod.swap_prod_mk]
-- --   generalize_proofs h₁ h₂
-- --   exact h₁.choose_spec.choose_spec.dup_and_dup_or_dup_and_dup h

-- lemma IsNonloopAt.vertexSet_nontrivial (h : G.IsNonloopAt e x) :
--     (V(G) : Set (Set α)).Nontrivial := by
--   obtain ⟨y, hne, h⟩ := h
--   obtain ⟨u, hu, hx⟩ := h.left_mem_vertex
--   obtain ⟨v, hv, hy⟩ := h.right_mem_vertex
--   refine nontrivial_of_mem_mem_ne hu hv ?_
--   rintro rfl
--   exact hne ⟨u, hu, hx, hy⟩

-- lemma inc_eq_inc_iff {G₁ G₂ : Graph α β} [G₁.Nodup] [G₂.Nodup] :
--     G₁.Inc e = G₂.Inc f ↔ G₁.IsLink e = G₂.IsLink f := by
--   constructor <;> rintro h
--   · ext x y
--     rw [isLink_iff_inc, isLink_iff_inc, h]
--   · simp [funext_iff, Inc, h]

-- section parallel

-- def parallel (G : Graph α β) (e f : β) : Prop :=
--   e ∈ E(G) ∧ f ∈ E(G) ∧ G.IsLink e = G.IsLink f

-- lemma parallel.left_mem (h : G.parallel e f) : e ∈ E(G) := h.1

-- lemma parallel.right_mem (h : G.parallel e f) : f ∈ E(G) := h.2.1

-- lemma parallel.isLink_eq (h : G.parallel e f) : G.IsLink e = G.IsLink f := h.2.2

-- @[simp]
-- lemma parallel_refl (he : e ∈ E(G)) : G.parallel e e := ⟨he, he, rfl⟩

-- @[simp]
-- lemma parallel_refl_iff : G.parallel e e ↔ e ∈ E(G) :=
--   ⟨fun h => h.left_mem, parallel_refl⟩

-- -- lemma parallel_iff_inc_eq (G : Graph α β) (e f : β) :
-- --     G.parallel e f ↔ e ∈ E(G) ∧ f ∈ E(G) ∧ G.Inc e = G.Inc f := by
-- --   refine ⟨fun ⟨he, hf, h⟩ ↦ ⟨he, hf, ?_⟩, fun ⟨he, hf, h⟩ ↦ ⟨he, hf, ?_⟩⟩
-- --   · rwa [inc_eq_inc_iff]
-- --   · rwa [inc_eq_inc_iff] at h

-- -- lemma inc_eq_inc_iff_parallel (G : Graph α β) {e f : β} (he : e ∈ E(G)) (hf : f ∈ E(G)) :
-- --     G.Inc e = G.Inc f ↔ G.parallel e f := by
-- --   simp [parallel_iff_inc_eq, he, hf]

-- -- lemma parallel.inc_eq (h : G.parallel e f) : G.Inc e = G.Inc f := by
-- --   obtain ⟨he, hf, h⟩ := G.parallel_iff_inc_eq e f |>.mp h
-- --   exact h

-- lemma parallel.symm (h : G.parallel e f) : G.parallel f e := by
--   obtain ⟨he, hf, h⟩ := h
--   exact ⟨hf, he, h.symm⟩

-- instance : IsSymm _ G.parallel where
--   symm _ _ := parallel.symm

-- lemma parallel_comm : G.parallel e f ↔ G.parallel f e := ⟨(·.symm), (·.symm)⟩

-- lemma parallel.trans {g : β} (h : G.parallel e f) (h' : G.parallel f g) : G.parallel e g := by
--   obtain ⟨he, hf, h⟩ := h
--   obtain ⟨hf, hg, h'⟩ := h'
--   exact ⟨he, hg, h.trans h'⟩

-- instance : IsTrans _ G.parallel where
--   trans _ _ _ := parallel.trans

-- def parallelClasses (G : Graph α β) : Partition (Set β) :=
--   Partition.ofRel G.parallel

-- @[simp]
-- lemma parallelClasses_supp (G : Graph α β) : (G.parallelClasses).supp = E(G) := by
--   simp only [parallelClasses, ofRel_supp, ]

-- end parallel
