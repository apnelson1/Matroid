/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Matroid.GraphTheory.HypergraphLike.Basic

/-!
# Directed/Undirected hypergraph-like structures

In a `HypergraphLike.Directed` structure, every incidence is directed either from its vertex
to its edge or from its edge to its vertex. In a `HypergraphLike.Undirected` structure, every
incidence is undirected, meaning it is both a source and a target. This file develops the source
and target incidence API for directed and undirected hypergraph-like structures.
-/

@[expose] public section

open Set

namespace HypergraphLike

variable {V I E Gr : Type*} {G : Gr} [HypergraphLike V I E G] {u v w : V} {i : I} {e : E}

/-- A graph-like structure is undirected if every incidence is both a source and a target.
For graphs, each edge can then be traversed in either direction. -/
class Undirected (G : Gr) [HypergraphLike V I E G] where
  /-- Source and target incidences coincide. -/
  isSource_iff ⦃i : I⦄ : IsSource G i ↔ IsTarget G i

section Undirected

variable [Undirected G]

@[simp, grind =] lemma isSource_iff (G : Gr) [HypergraphLike V I E G] [Undirected G] (i : I) :
    IsSource G i ↔ IsTarget G i := Undirected.isSource_iff (i := i)

@[grind →] lemma isSource_of_mem_incs (hi : i ∈ I(G)) : IsSource G i :=
  (mem_incs_iff.mp hi).elim id (isSource_iff G i).mpr

@[grind →] lemma isTarget_of_mem_incs (hi : i ∈ I(G)) : IsTarget G i :=
  (isSource_iff G i).mp (isSource_of_mem_incs hi)

private lemma isLink_iff_of_undirected : IsLink G e u v ↔
    ∃ i j : I(G), i ≠ j ∧ (edgeMap' i : E) = e ∧ (edgeMap' j : E) = e ∧
      (attach' i : V) = u ∧ (attach' j : V) = v :=
  ⟨fun ⟨l⟩ ↦ ⟨⟨l.source, l.isSource_source.mem_incs⟩, ⟨l.target, l.isTarget_target.mem_incs⟩,
    by simp [l.source_ne_target], l.edgeMap'_source, l.edgeMap'_target, l.attach'_source,
      l.attach'_target⟩,
    fun ⟨i, j, hij, hi, hj, hu, hv⟩ ↦ ⟨⟨i, j, (by grind), isSource_of_mem_incs i.property,
      isTarget_of_mem_incs j.property, hi, hj, hu, hv⟩⟩⟩

lemma isLink_iff_exists_incidence_of_undirected [Nonempty V] [Nonempty E] :
    IsLink G e u v ↔ ∃ i ∈ I(G), ∃ j ∈ I(G), i ≠ j ∧ edgeMap G i = e ∧
      edgeMap G j = e ∧ attach G i = u ∧ attach G j = v := by
  simp only [isLink_iff_of_undirected, ne_eq, Subtype.ext_iff, val_edgeMap', val_attach',
    Subtype.exists, exists_prop]

@[symm]
lemma IsLink.symm (h : IsLink G e u v) : IsLink G e v u := by
  obtain ⟨i, j, hne, hi, hj, hu, hv⟩ := isLink_iff_of_undirected.mp h
  exact isLink_iff_of_undirected.mpr ⟨j, i, hne.symm, hj, hi, hv, hu⟩

instance : Std.Symm (IsLink G e) where
  symm _ _ := IsLink.symm

lemma isLink_comm : IsLink G e u v ↔ IsLink G e v u := ⟨.symm, .symm⟩

instance : Std.Symm (Adj G) where
  symm _ _ := fun ⟨_, h⟩ ↦ h.symm.adj

@[symm] lemma Adj.symm (h : Adj G v w) : Adj G w v := symm_of (Adj G) h

lemma adj_comm : Adj G v w ↔ Adj G w v := ⟨.symm, .symm⟩

lemma isLink_iff_mem_incVerts (hne : u ≠ v) :
    IsLink G e u v ↔ u ∈ incVerts G e ∧ v ∈ incVerts G e := by
  refine ⟨fun h ↦ ⟨h.left_mem_incVerts, h.right_mem_incVerts⟩, ?_⟩
  rintro ⟨⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩⟩
  exact isLink_iff_of_undirected.mpr
    ⟨i, j, ne_of_apply_ne (fun i : I(G) ↦ (attach' i : V)) hne, hi, hj, rfl, rfl⟩

lemma isLink_iff_subset_incVerts_of_ne (hne : u ≠ v) : IsLink G e u v ↔ {u, v} ⊆ incVerts G e :=
  (isLink_iff_mem_incVerts hne).trans pair_subset_iff.symm

lemma adj_iff_exists_mem_incVerts (hne : u ≠ v) :
    Adj G u v ↔ ∃ e, u ∈ incVerts G e ∧ v ∈ incVerts G e := by
  simp only [Adj, isLink_iff_mem_incVerts hne]

lemma adj_iff_exists_subset_incVerts_of_ne (hne : u ≠ v) :
    Adj G u v ↔ ∃ e, {u, v} ⊆ incVerts G e := by
  simp only [Adj, isLink_iff_subset_incVerts_of_ne hne]

end Undirected

/-- A graph-like structure is directed if each incidence is either a source or a target, never both.
For graphs, each edge then has a specified direction. -/
class Directed (G : Gr) [HypergraphLike V I E G] where
  /-- A source incidence is not a target incidence. -/
  not_isTarget_of_isSource ⦃i : I⦄ : IsSource G i → ¬ IsTarget G i

section Directed

variable [Directed G]

@[grind →] lemma IsSource.not_isTarget (h : IsSource G i) : ¬ IsTarget G i :=
  Directed.not_isTarget_of_isSource h

lemma IsTarget.not_isSource (h : IsTarget G i) : ¬ IsSource G i :=
  fun hs ↦ hs.not_isTarget h

lemma isTarget_iff_not_isSource (hi : i ∈ I(G)) : IsTarget G i ↔ ¬ IsSource G i :=
  ⟨IsTarget.not_isSource, fun hs ↦ (mem_incs_iff.mp hi).resolve_left hs⟩

end Directed

end HypergraphLike
