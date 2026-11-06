/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Matroid.GraphTheory.HypergraphLike.Degree

/-!
# Compatibility of hypergraph-like structures

`HypergraphLike.Compatible G H` requires agreement of incidence maps and directions on shared
incidences. This file develops transport of incidence fibers, incident vertices and edges,
links, and adjacency between compatible graph-like structures.
-/

@[expose] public section

open Set Function

namespace HypergraphLike

variable {V I E Gr Gr₂ : Type*} {G : Gr} [HypergraphLike V I E G] {u v : V} {i : I} {e : E}
  {H : Gr₂} [HypergraphLike V I E H]

/-- Two graph-like structures are compatible when they agree on the edge, attached vertex, and
directedness of every shared incidence: it is a source in one exactly when it is in the other,
and likewise for targets. This only compares shared incidences; an edge with the same label
may have different incidence sets in the two structures. -/
structure Compatible (G : Gr) [HypergraphLike V I E G] (H : Gr₂) [HypergraphLike V I E H] :
    Prop where
  /-- Shared incidences belong to the same edge. -/
  edgeMap'_eq ⦃i : I⦄ (hiG : i ∈ I(G)) (hiH : i ∈ I(H)) : (edgeMap' ⟨i, hiG⟩ :E) = edgeMap' ⟨i, hiH⟩
  /-- Shared incidences attach to the same vertex. -/
  attach'_eq ⦃i : I⦄ (hiG : i ∈ I(G)) (hiH : i ∈ I(H)) : (attach' ⟨i, hiG⟩ : V) = attach' ⟨i, hiH⟩
  /-- A shared incidence is a source in one structure exactly when it is in the other. -/
  isSource_iff ⦃i : I⦄ (hiG : i ∈ I(G)) (hiH : i ∈ I(H)) : IsSource G i ↔ IsSource H i
  /-- A shared incidence is a target in one structure exactly when it is in the other. -/
  isTarget_iff ⦃i : I⦄ (hiG : i ∈ I(G)) (hiH : i ∈ I(H)) : IsTarget G i ↔ IsTarget H i

lemma Compatible.edgeMap_eq [Nonempty E] (h : Compatible G H) (hiG : i ∈ I(G)) (hiH : i ∈ I(H)) :
    edgeMap G i = edgeMap H i := by
  simpa only [val_edgeMap'] using h.edgeMap'_eq hiG hiH

lemma Compatible.attach_eq [Nonempty V] (h : Compatible G H) (hiG : i ∈ I(G)) (hiH : i ∈ I(H)) :
    attach G i = attach H i := by
  simpa only [val_attach'] using h.attach'_eq hiG hiH

lemma compatible_iff [Nonempty V] [Nonempty E] : Compatible G H ↔
    ∀ i ∈ I(G), i ∈ I(H) → edgeMap G i = edgeMap H i ∧ attach G i = attach H i ∧
      (IsSource G i ↔ IsSource H i) ∧ (IsTarget G i ↔ IsTarget H i) := by
  refine ⟨fun h i hiG hiH ↦ ⟨h.edgeMap_eq hiG hiH, h.attach_eq hiG hiH,
    h.isSource_iff hiG hiH, h.isTarget_iff hiG hiH⟩, fun h ↦ ?_⟩
  exact {
    edgeMap'_eq _ hiG hiH := by simpa only [val_edgeMap'] using (h _ hiG hiH).1
    attach'_eq _ hiG hiH := by simpa only [val_attach'] using (h _ hiG hiH).2.1
    isSource_iff _ hiG hiH := (h _ hiG hiH).2.2.1
    isTarget_iff _ hiG hiH := (h _ hiG hiH).2.2.2 }

@[simp]
lemma Compatible.rfl : Compatible G G where
  edgeMap'_eq _ _ _ := Eq.refl _
  attach'_eq _ _ _ := Eq.refl _
  isSource_iff _ _ _ := Iff.rfl
  isTarget_iff _ _ _ := Iff.rfl

lemma Compatible.refl (G : Gr) [HypergraphLike V I E G] : Compatible G G := .rfl

instance [∀ G : Gr, HypergraphLike V I E G] : Std.Refl (Compatible (Gr := Gr) (Gr₂ := Gr) · ·) where
  refl _ := .rfl

@[symm]
lemma Compatible.symm (h : Compatible G H) : Compatible H G where
  edgeMap'_eq _ hiH hiG := (h.edgeMap'_eq hiG hiH).symm
  attach'_eq _ hiH hiG := (h.attach'_eq hiG hiH).symm
  isSource_iff _ hiH hiG := (h.isSource_iff hiG hiH).symm
  isTarget_iff _ hiH hiG := (h.isTarget_iff hiG hiH).symm

instance [∀ G : Gr, HypergraphLike V I E G] : Std.Symm (Compatible (Gr := Gr) (Gr₂ := Gr) · ·) where
  symm _ _ := .symm

lemma compatible_comm : Compatible G H ↔ Compatible H G := ⟨.symm, .symm⟩

lemma Compatible.of_disjoint_incs (h : Disjoint I(G) I(H)) : Compatible G H where
  edgeMap'_eq _ hiG hiH := (disjoint_left.mp h hiG hiH).elim
  attach'_eq _ hiG hiH := (disjoint_left.mp h hiG hiH).elim
  isSource_iff _ hiG hiH := (disjoint_left.mp h hiG hiH).elim
  isTarget_iff _ hiG hiH := (disjoint_left.mp h hiG hiH).elim

lemma Compatible.disjoint_incs_of_disjoint_verts (h : Compatible G H) (hV : Disjoint V(G) V(H)) :
    Disjoint I(G) I(H) :=
  disjoint_left.mpr fun i hiG hiH ↦ disjoint_left.mp hV (attach' ⟨i, hiG⟩).property
    (h.attach'_eq hiG hiH ▸ (attach' ⟨i, hiH⟩).property)

lemma Compatible.disjoint_incs_of_disjoint_edges (h : Compatible G H) (hE : Disjoint E(G) E(H)) :
    Disjoint I(G) I(H) :=
  disjoint_left.mpr fun i hiG hiH ↦ disjoint_left.mp hE (edgeMap' ⟨i, hiG⟩).property
    (h.edgeMap'_eq hiG hiH ▸ (edgeMap' ⟨i, hiH⟩).property)

lemma Compatible.mem_edgeFiber_iff (h : Compatible G H) (hiG : i ∈ I(G)) (hiH : i ∈ I(H)) :
    i ∈ edgeFiber G e ↔ i ∈ edgeFiber H e := by
  let : Nonempty E := ⟨e⟩
  simp only [mem_edgeFiber, hiG, hiH, true_and, h.edgeMap_eq hiG hiH]

lemma Compatible.mem_vertexFiber_iff (h : Compatible G H) (hiG : i ∈ I(G)) (hiH : i ∈ I(H)) :
    i ∈ vertexFiber G v ↔ i ∈ vertexFiber H v := by
  let : Nonempty V := ⟨v⟩
  simp only [mem_vertexFiber, hiG, hiH, true_and, h.attach_eq hiG hiH]

lemma Compatible.edgeFiber_subset_of_edgeFiber_subset (h : Compatible G H)
    (hF : edgeFiber G e ⊆ I(H)) : edgeFiber G e ⊆ edgeFiber H e := fun _ hi ↦
  (h.mem_edgeFiber_iff (edgeFiber_subset_incs hi) (hF hi)).mp hi

lemma Compatible.vertexFiber_subset_of_vertexFiber_subset (h : Compatible G H)
    (hF : vertexFiber G v ⊆ I(H)) : vertexFiber G v ⊆ vertexFiber H v := fun _ hi ↦
  (h.mem_vertexFiber_iff (vertexFiber_subset_incs hi) (hF hi)).mp hi

lemma Compatible.edgeFiber_subset (h : Compatible G H) (hI : I(G) ⊆ I(H)) :
    edgeFiber G e ⊆ edgeFiber H e :=
  h.edgeFiber_subset_of_edgeFiber_subset (edgeFiber_subset_incs.trans hI)

lemma Compatible.vertexFiber_subset (h : Compatible G H) (hI : I(G) ⊆ I(H)) :
    vertexFiber G v ⊆ vertexFiber H v :=
  h.vertexFiber_subset_of_vertexFiber_subset (vertexFiber_subset_incs.trans hI)

/-- Retaining a finite edge fiber without increasing its eorder preserves the complete fiber. -/
lemma Compatible.edgeFiber_eq_of_eorder_le {H : Gr₂} [HypergraphLike V I E H]
    (h : Compatible G H)
    (hF : edgeFiber G e ⊆ I(H)) (hfin : eorder G e < ⊤) (hle : eorder H e ≤ eorder G e) :
    edgeFiber G e = edgeFiber H e :=
  (eorder_lt_top_iff.mp hfin).eq_of_subset_of_encard_le
    (h.edgeFiber_subset_of_edgeFiber_subset hF)
    (by simpa only [eorder_eq_encard_edgeFiber] using hle)

lemma Compatible.incVerts_subset_of_edgeFiber_subset (h : Compatible G H)
    (hF : edgeFiber G e ⊆ I(H)) : incVerts G e ⊆ incVerts H e := by
  intro v hv
  let : Nonempty V := ⟨v⟩
  let : Nonempty E := ⟨e⟩
  obtain ⟨i, hi, he, hv⟩ := mem_incVerts_iff_exists_incidence.mp hv
  have hiH := hF (mem_edgeFiber.mpr ⟨hi, he⟩)
  exact mem_incVerts_iff_exists_incidence.mpr ⟨i, hiH,
    (h.edgeMap_eq hi hiH).symm.trans he, (h.attach_eq hi hiH).symm.trans hv⟩

lemma Compatible.incEdges_subset_of_vertexFiber_subset (h : Compatible G H)
    (hF : vertexFiber G v ⊆ I(H)) : incEdges G v ⊆ incEdges H v := by
  intro e he
  let : Nonempty V := ⟨v⟩
  let : Nonempty E := ⟨e⟩
  obtain ⟨i, hi, hv, he⟩ := mem_incEdges_iff_exists_incidence.mp he
  have hiH := hF (mem_vertexFiber.mpr ⟨hi, hv⟩)
  exact mem_incEdges_iff_exists_incidence.mpr
    ⟨i, hiH, (h.attach_eq hi hiH).symm.trans hv, (h.edgeMap_eq hi hiH).symm.trans he⟩

lemma Compatible.incVerts_subset (h : Compatible G H) (hI : I(G) ⊆ I(H)) :
    incVerts G e ⊆ incVerts H e :=
  h.incVerts_subset_of_edgeFiber_subset (edgeFiber_subset_incs.trans hI)

lemma Compatible.incEdges_subset (h : Compatible G H) (hI : I(G) ⊆ I(H)) :
    incEdges G v ⊆ incEdges H v :=
  h.incEdges_subset_of_vertexFiber_subset (vertexFiber_subset_incs.trans hI)

lemma Compatible.incVerts_eq_of_edgeFiber_eq (h : Compatible G H)
    (hF : edgeFiber G e = edgeFiber H e) : incVerts G e = incVerts H e :=
  (h.incVerts_subset_of_edgeFiber_subset (hF.subset.trans edgeFiber_subset_incs)).antisymm
    (h.symm.incVerts_subset_of_edgeFiber_subset (hF.superset.trans edgeFiber_subset_incs))

lemma Compatible.incEdges_eq_of_vertexFiber_eq (h : Compatible G H)
    (hF : vertexFiber G v = vertexFiber H v) : incEdges G v = incEdges H v :=
  (h.incEdges_subset_of_vertexFiber_subset (hF.subset.trans vertexFiber_subset_incs)).antisymm
    (h.symm.incEdges_subset_of_vertexFiber_subset (hF.superset.trans vertexFiber_subset_incs))

lemma Compatible.incVerts_eq (h : Compatible G H) (hI : I(G) = I(H)) :
    incVerts G e = incVerts H e :=
  (h.incVerts_subset hI.subset).antisymm (h.symm.incVerts_subset hI.superset)

lemma Compatible.incEdges_eq (h : Compatible G H) (hI : I(G) = I(H)) :
    incEdges G v = incEdges H v :=
  (h.incEdges_subset hI.subset).antisymm (h.symm.incEdges_subset hI.superset)

/-- Transport a link when its incidences are retained in a compatible graph-like object. -/
lemma IsLink.of_compatible_of_edgeFiber_subset (h : IsLink G e u v)
    (hGH : Compatible G H) (hF : edgeFiber G e ⊆ I(H)) : IsLink H e u v := by
  let : Nonempty V := ⟨u⟩
  let : Nonempty E := ⟨e⟩
  obtain ⟨i, j, hne, hs, ht, hi, hj, hu, hv⟩ := isLink_iff_exists_incidence.mp h
  have hiH := hF (mem_edgeFiber.mpr ⟨hs.mem_incs, hi⟩)
  have hjH := hF (mem_edgeFiber.mpr ⟨ht.mem_incs, hj⟩)
  exact isLink_iff_exists_incidence.mpr ⟨i, j, hne,
    (hGH.isSource_iff hs.mem_incs hiH).mp hs, (hGH.isTarget_iff ht.mem_incs hjH).mp ht,
    (hGH.edgeMap_eq hs.mem_incs hiH).symm.trans hi, (hGH.edgeMap_eq ht.mem_incs hjH).symm.trans hj,
    (hGH.attach_eq hs.mem_incs hiH).symm.trans hu, (hGH.attach_eq ht.mem_incs hjH).symm.trans hv⟩

lemma IsLink.of_compatible (h : IsLink G e u v) (hGH : Compatible G H) (hI : I(G) ⊆ I(H)) :
    IsLink H e u v :=
  h.of_compatible_of_edgeFiber_subset hGH (edgeFiber_subset_incs.trans hI)

lemma Compatible.isLink_congr_of_edgeFiber_eq (h : Compatible G H)
    (hF : edgeFiber G e = edgeFiber H e) : IsLink G e u v ↔ IsLink H e u v :=
  ⟨fun he ↦ he.of_compatible_of_edgeFiber_subset h (hF.subset.trans edgeFiber_subset_incs),
    fun he ↦ he.of_compatible_of_edgeFiber_subset h.symm (hF.superset.trans edgeFiber_subset_incs)⟩

lemma Adj.of_compatible (h : Adj G u v) (hGH : Compatible G H) (hI : I(G) ⊆ I(H)) : Adj H u v :=
  h.elim fun _ he ↦ (he.of_compatible hGH hI).adj

lemma Compatible.isLink_congr (h : Compatible G H) (hI : I(G) = I(H)) :
    IsLink G e u v ↔ IsLink H e u v :=
  ⟨fun he ↦ he.of_compatible h hI.subset, fun he ↦ he.of_compatible h.symm hI.superset⟩

lemma Compatible.adj_congr (h : Compatible G H) (hI : I(G) = I(H)) : Adj G u v ↔ Adj H u v := by
  simp only [Adj, h.isLink_congr hI]

end HypergraphLike
