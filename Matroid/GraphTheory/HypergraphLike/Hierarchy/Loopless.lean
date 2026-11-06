/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Matroid.GraphTheory.HypergraphLike.Basic

/-!
# Loopless hypergraph-like structures

`HypergraphLike.Loopless` requires distinct incidences of the same edge to attach to distinct
vertices. For graphs, this excludes loops; for hypergraphs, it excludes repeated incidences
between an edge and a vertex. This file develops the incidence, link, adjacency, and compatibility
API.
-/

@[expose] public section

open Set Function

namespace HypergraphLike

variable {V I E Gr : Type*} {G : Gr} [HypergraphLike V I E G] {u u' v v' w : V} {i j : I} {e f : E}
  {Gr₂ : Type*}

section Loopless

/-- A graph-like object `G` is loopless if distinct incidences of the same edge have distinct
endpoints. This is a property of `G`, rather than of every object of its type. -/
class Loopless (G : Gr) [HypergraphLike V I E G] : Prop where
  /-- Distinct incidences of the same edge have distinct endpoints. -/
  no_loops_of_mem_mem ⦃i j : I⦄ (hi : i ∈ I(G)) (hj : j ∈ I(G)) :
    edgeMap' ⟨i, hi⟩ = edgeMap' ⟨j, hj⟩ → i ≠ j →
      attach' ⟨i, hi⟩ ≠ attach' ⟨j, hj⟩

lemma loopless_iff_injOn [Nonempty V] [Nonempty E] :
    Loopless G ↔ InjOn (fun i ↦ (edgeMap G i, attach G i)) I(G) := by
  refine ⟨fun h i hi j hj hpair ↦ by_contra fun hne ↦ ?_, fun h ↦ ⟨fun i j hi hj he hne hv ↦ ?_⟩⟩
  · refine Loopless.no_loops_of_mem_mem hi hj (Subtype.ext ?_) hne (Subtype.ext ?_)
    · simpa only [val_edgeMap'] using congrArg Prod.fst hpair
    simpa only [val_attach'] using congrArg Prod.snd hpair
  refine hne <| h hi hj <| Prod.ext ?_ ?_
  · simpa only [val_edgeMap'] using congrArg Subtype.val he
  simpa only [val_attach'] using congrArg Subtype.val hv

variable [Loopless G]

lemma no_loops [Nonempty V] [Nonempty E] (hi : i ∈ I(G)) (hj : j ∈ I(G))
    (hij : edgeMap G i = edgeMap G j) (hne : i ≠ j) : attach G i ≠ attach G j :=
  fun huv ↦ hne ((loopless_iff_injOn.mp inferInstance) hi hj (Prod.ext hij huv))

lemma incidence_injective (G : Gr) [HypergraphLike V I E G] [Loopless G] :
    Injective fun i : I(G) ↦ (edgeMap' i, attach' i) := by
  intro i j hij
  by_contra hne
  exact Loopless.no_loops_of_mem_mem i.property j.property (congrArg Prod.fst hij)
    (fun h ↦ hne (Subtype.ext h)) (congrArg Prod.snd hij)

lemma IsLink.ne (h : IsLink G e u v) : u ≠ v := by
  let : Nonempty V := ⟨u⟩
  let : Nonempty E := ⟨e⟩
  obtain ⟨i, j, hij, hi, hj, hei, hej, hui, hvj⟩ := isLink_iff_exists_incidence.mp h
  exact fun huv ↦ no_loops hi.mem_incs hj.mem_incs (hei.trans hej.symm) hij
    (hui.trans (huv.trans hvj.symm))

lemma Adj.ne (h : Adj G u v) : u ≠ v := by
  obtain ⟨e, he⟩ := h
  exact he.ne

@[simp] lemma not_isLink_self : ¬ IsLink G e v v := fun h ↦ h.ne rfl

@[simp] lemma not_adj_self : ¬ Adj G v v := fun h ↦ h.ne rfl

/-
lemma Compatible.loopless {H : Gr₂} [HypergraphLike V I E H] (h : Compatible G H)
    (hI : I(H) ⊆ I(G)) : Loopless H where
  no_loops_of_mem_mem _ _ hi hj he hne hv :=
    Loopless.no_loops_of_mem_mem (hI hi) (hI hj)
      (Subtype.ext ((h.edgeMap'_eq (hI hi) hi).trans
        ((congrArg Subtype.val he).trans (h.edgeMap'_eq (hI hj) hj).symm))) hne
      (Subtype.ext ((h.attach'_eq (hI hi) hi).trans
        ((congrArg Subtype.val hv).trans (h.attach'_eq (hI hj) hj).symm)))
-/

end Loopless

end HypergraphLike
