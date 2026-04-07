/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/

import Mathlib.Order.Extension.Linear
-- import Mathlib.Combinatorics.Graph.Subgraph
import Matroid.Graph.Subgraph.Basic
import Mathlib.Data.Sym.Sym2.Order

/-!
# Arbitrary trichotomous relation on a type α

There are certain occasions where we would appreciate some sort of orientation on edges in a graph.
However, such choices cannot be made in individual graphs as that would lead to inconsistency issue
between related graphs. One solution is to impose a trichotomous relation any pair of vertices.
Then, the choice of orientation is made by 'towards the bigger vertex'.

This file introduces a centralised way to impose some trichotomous relation on any type α.
-/

namespace Graph

variable {α β : Type*} {e : β} {G H : Graph α β}

instance (α : Type*) : IsPartialOrder α Eq where
  refl _ := rfl
  trans _ _ _ := Eq.trans
  antisymm _ _ _ := Eq.symm

noncomputable def ArbRel (α : Type*) : α → α → Prop :=
  extend_partialOrder Eq |>.choose

instance : IsLinearOrder α (ArbRel α) := extend_partialOrder Eq |>.choose_spec.1

noncomputable instance (α : Type*) : DecidableRel (ArbRel α) :=
  Classical.decRel (ArbRel α)

-- noncomputable def toSym2 (he : e ∈ E(G)) : Sym2 α :=
--   let h := exists_isLink_of_mem_edgeSet he
--   s(h.choose, h.choose_spec.choose)

noncomputable def source (G : Graph α β) (e : β) (he : e ∈ E(G)) : α :=
  let h := exists_isLink_of_mem_edgeSet he
  if ArbRel α h.choose h.choose_spec.choose then h.choose else h.choose_spec.choose

noncomputable def target (G : Graph α β) (e : β) (he : e ∈ E(G)) : α :=
  let h := exists_isLink_of_mem_edgeSet he
  if ArbRel α h.choose h.choose_spec.choose then h.choose_spec.choose else h.choose

lemma isLink_source_target (he : e ∈ E(G)) : G.IsLink e (G.source e he) (G.target e he) := by
  let h := exists_isLink_of_mem_edgeSet he
  simp only [source, target, ArbRel]
  split_ifs with hRel
  · exact h.choose_spec.choose_spec
  · exact h.choose_spec.choose_spec.symm

@[simp]
lemma source_mem (he : e ∈ E(G)) : G.source e he ∈ V(G) :=
  (G.isLink_source_target he).left_mem

@[simp]
lemma target_mem (he : e ∈ E(G)) : G.target e he ∈ V(G) :=
  (G.isLink_source_target he).right_mem

-- lemma IsSubgraph.source (h : H ≤ G) (he : e ∈ E(H)) : source he = source (edgeSet_mono h he) :=
--by
--   simp only [Graph.source]
--   generalize_proofs hHxy hHy hGxy hGy
--   obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := (h.isLink_mono hHy.choose_spec).eq_and_eq_or_eq_and_eq
--     hGy.choose_spec
--   · simp_rw [h2, h1]
--   simp_rw [h2, h1]
--   have := total_of (ArbRel α) hGy.choose hGxy.choose
--   have := antisymm_of (ArbRel α) (a := hGy.choose) (b := hGxy.choose)
--   grind

-- lemma IsSubgraph.target (h : H ≤ G) (he : e ∈ E(H)) : target he = target (edgeSet_mono h he) :=
--by
--   simp only [Graph.target]
--   generalize_proofs hHxy hHy hGxy hGy
--   obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := (h.isLink_mono hHy.choose_spec).eq_and_eq_or_eq_and_eq
--     hGy.choose_spec
--   · simp_rw [h2, h1]
--   simp_rw [h2, h1]
--   have := total_of (ArbRel α) hGy.choose hGxy.choose
--   have := antisymm_of (ArbRel α) (a := hGy.choose) (b := hGxy.choose)
--   grind

@[simp]
lemma IsSubgraph.source (h : H ≤ G) (he : e ∈ E(H)) :
    G.source e (edgeSet_mono h he) = H.source e he := by
  simp only [Graph.source]
  generalize_proofs hGxy hGy hHxy hHy
  obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := (hHy.choose_spec.of_le h).eq_and_eq_or_eq_and_eq
    hGy.choose_spec
  · simp_rw [h2, h1]
  simp_rw [h2, h1]
  have := total_of (ArbRel α) hGy.choose hGxy.choose
  have := antisymm_of (ArbRel α) (a := hGy.choose) (b := hGxy.choose)
  grind

@[simp]
lemma IsSubgraph.target (h : H ≤ G) (he : e ∈ E(H)) :
    G.target e (edgeSet_mono h he) = H.target e he := by
  simp only [Graph.target]
  generalize_proofs hGxy hGy hHxy hHy
  obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := (hHy.choose_spec.of_le h).eq_and_eq_or_eq_and_eq
    hGy.choose_spec
  · simp_rw [h2, h1]
  simp_rw [h2, h1]
  have := total_of (ArbRel α) hGy.choose hGxy.choose
  have := antisymm_of (ArbRel α) (a := hGy.choose) (b := hGxy.choose)
  grind
