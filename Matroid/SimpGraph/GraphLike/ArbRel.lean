/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/

import Mathlib.Order.Extension.Linear
import Matroid.Graph.Basic
import Mathlib.Data.Sym.Sym2.Order

/-!
# Arbitrary trichotomous relation on a type α

There are certain occasions where we would appreciate some sort of orientation on edges in a graph.
However, such choices cannot be made in individual graphs as that would lead to inconsistency issue
between related graphs. One solution is to impose a trichotomous relation any pair of vertices.
Then, the choice of orientation is made by 'towards the bigger vertex'.

This file introduces a centralised way to impose some trichotomous relation on any type α.
-/

open Graph

variable {α β : Type*} {e : β} {G : Graph α β}

instance (α : Type*) : IsPartialOrder α Eq where
  refl _ := rfl
  trans _ _ _ := Eq.trans
  antisymm _ _ _ := Eq.symm

noncomputable def ArbRel (α : Type*) : α → α → Prop :=
  extend_partialOrder Eq |>.choose

instance : IsLinearOrder α (ArbRel α) := extend_partialOrder Eq |>.choose_spec.1

noncomputable instance (α : Type*) : DecidableRel (ArbRel α) :=
  Classical.decRel (ArbRel α)

noncomputable def Graph.toSym2 (G : Graph α β) (he : e ∈ E(G)) : Sym2 α :=
  let h := exists_isLink_of_mem_edgeSet he
  s(h.choose, h.choose_spec.choose)

noncomputable def Graph.src (G : Graph α β) (he : e ∈ E(G)) : α :=
  let h := exists_isLink_of_mem_edgeSet he
  if ArbRel α h.choose h.choose_spec.choose then h.choose else h.choose_spec.choose

noncomputable def Graph.tgt (G : Graph α β) (he : e ∈ E(G)) : α :=
  let h := exists_isLink_of_mem_edgeSet he
  if ArbRel α h.choose h.choose_spec.choose then h.choose_spec.choose else h.choose

lemma Graph.isLink_src_tgt (he : e ∈ E(G)) : G.IsLink e (G.src he) (G.tgt he) := by
  let h := exists_isLink_of_mem_edgeSet he
  simp only [src, tgt]
  split_ifs with hRel
  · exact h.choose_spec.choose_spec
  · exact h.choose_spec.choose_spec.symm

lemma Graph.src_mem (he : e ∈ E(G)) : G.src he ∈ V(G) := by
  exact (G.isLink_src_tgt he).left_mem

lemma Graph.tgt_mem (he : e ∈ E(G)) : G.tgt he ∈ V(G) := by
  exact (G.isLink_src_tgt he).right_mem
