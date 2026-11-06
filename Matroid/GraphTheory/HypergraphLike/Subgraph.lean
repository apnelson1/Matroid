/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Matroid.GraphTheory.HypergraphLike.Basic

/-!
# Subgraphs of hypergraph-like structures

`HypergraphLike.IsSubgraph H G` is a general notion of sub(hyper)graph. Between two graphs or
between two digraphs, it is the expected subgraph relation. Incidences may be deleted independently
of edges, so walk footprints are subgraphs even when they use only part of an edge. It also permits
comparison between directed and undirected (hyper)graphs: a directed graph
with a single directed edge `e` from `u` to `v` is a subgraph of the undirected graph with an edge
`e` between `u` and `v`.
-/

@[expose] public section

open Set Function

namespace HypergraphLike

variable {V I E Gr Gr₂ Gr₃ : Type*} {H : Gr} {G : Gr₂} {K : Gr₃} {i : I} {e : E}
  [HypergraphLike V I E H] [HypergraphLike V I E G] [HypergraphLike V I E K] {u v : V}

/-- A subgraph retains subsets of vertices, edges, and incidences, preserving incidence maps
and permitted directions. A directed edge may become undirected in the larger graph. -/
structure IsSubgraph (H : Gr) [HypergraphLike V I E H] (G : Gr₂) [HypergraphLike V I E G] :
    Prop where
  /-- Every vertex of `H` is a vertex of `G`. -/
  verts_mono : V(H) ⊆ V(G)
  /-- Every edge of `H` is an edge of `G`. -/
  edges_mono : E(H) ⊆ E(G)
  /-- Every incidence of an edge of `H` belongs to that edge in `G`. -/
  edgeFiber_subset ⦃e : E⦄ : e ∈ E(H) → edgeFiber H e ⊆ edgeFiber G e
  /-- Every incidence of `H` has the same attached vertex in `G`. -/
  attach'_eq ⦃i : I⦄ (hiH : i ∈ I(H)) (hiG : i ∈ I(G)) :
    (attach' (G := H) ⟨i, hiH⟩ : V) = (attach' (G := G) ⟨i, hiG⟩ : V)
  /-- Every source incidence of `H` is a source incidence of `G`. -/
  isSource_mono ⦃i : I⦄ : IsSource H i → IsSource G i
  /-- Every target incidence of `H` is a target incidence of `G`. -/
  isTarget_mono ⦃i : I⦄ : IsTarget H i → IsTarget G i

namespace IsSubgraph

lemma incs_mono (hHG : IsSubgraph H G) : I(H) ⊆ I(G) :=
  fun _ hi ↦ (mem_incs_iff.mp hi).elim
    (fun hs ↦ (hHG.isSource_mono hs).mem_incs) (fun ht ↦ (hHG.isTarget_mono ht).mem_incs)

attribute [gcongr only, grind →] verts_mono edges_mono incs_mono

/-! ### The subgraph relation -/

@[simp]
protected lemma rfl : IsSubgraph H H where
  verts_mono := .rfl
  edges_mono := .rfl
  edgeFiber_subset _ _ := .rfl
  attach'_eq _ _ _ := rfl
  isSource_mono _ h := h
  isTarget_mono _ h := h

protected lemma refl (H : Gr) [HypergraphLike V I E H] : IsSubgraph H H := .rfl

/-- Subgraph inclusion composes across different representation types. -/
protected lemma trans (hHG : IsSubgraph H G) (hGK : IsSubgraph G K) : IsSubgraph H K where
  verts_mono := hHG.verts_mono.trans hGK.verts_mono
  edges_mono := hHG.edges_mono.trans hGK.edges_mono
  edgeFiber_subset _ he := (hHG.edgeFiber_subset he).trans
    (hGK.edgeFiber_subset (hHG.edges_mono he))
  attach'_eq _ hiH hiK := (hHG.attach'_eq hiH (hHG.incs_mono hiH)).trans
    (hGK.attach'_eq (hHG.incs_mono hiH) hiK)
  isSource_mono _ h := hGK.isSource_mono (hHG.isSource_mono h)
  isTarget_mono _ h := hGK.isTarget_mono (hHG.isTarget_mono h)

instance [∀ H : Gr, HypergraphLike V I E H] : IsPreorder Gr (fun H G : Gr ↦ IsSubgraph H G) where
  refl _ := .rfl
  trans _ _ _ := .trans

instance [∀ H : Gr, HypergraphLike V I E H] [∀ G : Gr₂, HypergraphLike V I E G]
    [∀ K : Gr₃, HypergraphLike V I E K] : Trans (fun (H : Gr) (G : Gr₂) ↦ IsSubgraph H G)
      (fun (G : Gr₂) (K : Gr₃) ↦ IsSubgraph G K) (fun (H : Gr) (K : Gr₃) ↦ IsSubgraph H K) where
  trans := .trans

/-! ### Incidence maps and orientation -/

variable (hHG : IsSubgraph H G)

include hHG

lemma edgeMap'_eq (hiH : i ∈ I(H)) (hiG : i ∈ I(G)) :
    (edgeMap' (G := H) ⟨i, hiH⟩ : E) = (edgeMap' (G := G) ⟨i, hiG⟩ : E) := by
  obtain ⟨_, he, rfl⟩ := (hHG.edgeFiber_subset (edgeMap' ⟨i, hiH⟩).property) ⟨⟨i, hiH⟩, rfl, rfl⟩
  exact he.symm

/-- Inclusion map of an incidence into the larger graph preserves the edge to which it belongs. -/
@[simp] lemma edgeMap'_inclusion (i : I(H)) :
    edgeMap' (G := G) (inclusion hHG.incs_mono i) = inclusion hHG.edges_mono (edgeMap' i) :=
  Subtype.ext (hHG.edgeMap'_eq i.property (hHG.incs_mono i.property)).symm

/-- Inclusion map of an incidence into the larger graph preserves its attached vertex. -/
@[simp]
lemma attach'_inclusion (i : I(H)) :
    attach' (G := G) (inclusion hHG.incs_mono i) = inclusion hHG.verts_mono (attach' (G := H) i) :=
  Subtype.ext (hHG.attach'_eq i.property (hHG.incs_mono i.property)).symm

lemma edgeMap_eq [Nonempty E] (hi : i ∈ I(H)) : edgeMap H i = edgeMap G i := by
  simpa using hHG.edgeMap'_eq hi (hHG.incs_mono hi)

lemma attach_eq [Nonempty V] (hi : i ∈ I(H)) : attach H i = attach G i := by
  simpa using hHG.attach'_eq hi (hHG.incs_mono hi)

end IsSubgraph

/-- A subgraph characterization using `attach`. -/
lemma isSubgraph_iff [Nonempty V] : IsSubgraph H G ↔ V(H) ⊆ V(G) ∧ E(H) ⊆ E(G) ∧
    (∀ e ∈ E(H), edgeFiber H e ⊆ edgeFiber G e) ∧ EqOn (attach H) (attach G) I(H) ∧
    (∀ i, IsSource H i → IsSource G i) ∧ (∀ i, IsTarget H i → IsTarget G i) :=
  ⟨fun h ↦ ⟨h.verts_mono, h.edges_mono, fun _ he ↦ h.edgeFiber_subset he, fun _ ↦ h.attach_eq,
    h.isSource_mono, h.isTarget_mono⟩,
    fun ⟨hV, hE, hF, hA, hS, hT⟩ ↦ ⟨hV, hE, hF, fun _ hi _ ↦ by simpa using hA hi, hS, hT⟩⟩

@[gcongr only]
lemma IsSource.monoSubgraph (hHG : IsSubgraph H G) (h : IsSource H i) : IsSource G i :=
  hHG.isSource_mono h

@[gcongr only]
lemma IsTarget.monoSubgraph (hHG : IsSubgraph H G) (h : IsTarget H i) : IsTarget G i :=
  hHG.isTarget_mono h

namespace Link

/-- A link in a subgraph gives a link in the larger graph with the same chosen incidences. -/
def mono (l : Link H e u v) (hHG : IsSubgraph H G) : Link G e u v where
  source := l.source
  target := l.target
  source_ne_target := l.source_ne_target
  isSource_source := hHG.isSource_mono l.isSource_source
  isTarget_target := hHG.isTarget_mono l.isTarget_target
  edgeMap'_source := (hHG.edgeMap'_eq l.isSource_source.mem_incs _).symm.trans l.edgeMap'_source
  edgeMap'_target := (hHG.edgeMap'_eq l.isTarget_target.mem_incs _).symm.trans l.edgeMap'_target
  attach'_source := (hHG.attach'_eq l.isSource_source.mem_incs _).symm.trans l.attach'_source
  attach'_target := (hHG.attach'_eq l.isTarget_target.mem_incs _).symm.trans l.attach'_target

@[simp]
lemma mono_source (l : Link H e u v) (hHG : IsSubgraph H G) : (l.mono hHG).source = l.source := rfl

@[simp]
lemma mono_target (l : Link H e u v) (hHG : IsSubgraph H G) : (l.mono hHG).target = l.target := rfl

@[simp] lemma mono_rfl (l : Link H e u v) : l.mono (.rfl : IsSubgraph H H) = l := rfl

@[simp] lemma mono_trans (l : Link H e u v) (hHG : IsSubgraph H G) (hGK : IsSubgraph G K) :
    (l.mono hHG).mono hGK = l.mono (hHG.trans hGK) := rfl

lemma mono_injective (hHG : IsSubgraph H G) : Injective (fun l : Link H e u v ↦ l.mono hHG) :=
  fun _ _ h ↦ Link.ext (congrArg (Link.source (G := G)) h) (congrArg (Link.target (G := G)) h)

@[simp] lemma mono_inj (hHG : IsSubgraph H G) {l₁ l₂ : Link H e u v} :
    l₁.mono hHG = l₂.mono hHG ↔ l₁ = l₂ := (mono_injective hHG).eq_iff

end Link

@[gcongr only]
lemma IsLink.monoSubgraph (hHG : IsSubgraph H G) (h : IsLink H e u v) : IsLink G e u v :=
  h.map (·.mono hHG)

@[gcongr only] lemma Adj.monoSubgraph (hHG : IsSubgraph H G) (h : Adj H u v) : Adj G u v :=
  h.elim fun _ he ↦ (he.monoSubgraph hHG).adj

/-! ### Fibers and incident vertices and edges -/

namespace IsSubgraph

variable (hHG : IsSubgraph H G)

include hHG

@[gcongr only] lemma edgeFiber_mono : edgeFiber H e ⊆ edgeFiber G e :=
  fun _ hi ↦ hHG.edgeFiber_subset (mem_edges_of_mem_edgeFiber hi) hi

@[gcongr only] lemma vertexFiber_mono : vertexFiber H v ⊆ vertexFiber G v := by
  rintro i ⟨j, hj, rfl⟩
  exact ⟨inclusion hHG.incs_mono j, (hHG.attach'_eq j.property _).symm.trans hj, rfl⟩

lemma edgeFiber_eq_inter : edgeFiber H e = I(H) ∩ edgeFiber G e := by
  let : Nonempty E := ⟨e⟩
  ext i
  simp only [mem_inter_iff, mem_edgeFiber]
  refine and_congr_right fun hi ↦ ?_
  rw [hHG.edgeMap_eq hi, and_iff_right (hHG.incs_mono hi)]

lemma vertexFiber_eq_inter : vertexFiber H v = I(H) ∩ vertexFiber G v := by
  let : Nonempty V := ⟨v⟩
  ext i
  simp only [mem_inter_iff, mem_vertexFiber]
  refine and_congr_right fun hi ↦ ?_
  rw [hHG.attach_eq hi, and_iff_right (hHG.incs_mono hi)]

@[gcongr only]
lemma incVerts_mono : incVerts H e ⊆ incVerts G e := by
  rintro v ⟨i, hi, rfl⟩
  exact ⟨inclusion hHG.incs_mono i, (hHG.edgeMap'_eq i.property _).symm.trans hi,
    (hHG.attach'_eq i.property _).symm⟩

@[gcongr only]
lemma incEdges_mono : incEdges H v ⊆ incEdges G v :=
  fun _ he ↦ mem_incEdges.mpr (hHG.incVerts_mono (mem_incEdges.mp he))

/-- Retaining a whole fiber preserves the incident vertices of that edge. -/
lemma incVerts_eq_of_edgeFiber_eq (hF : edgeFiber H e = edgeFiber G e) :
    incVerts H e = incVerts G e := by
  ext v
  let : Nonempty V := ⟨v⟩
  rw [incVerts_eq_image, incVerts_eq_image, ← hF,
    image_congr (fun _ hi ↦ hHG.attach_eq (edgeFiber_subset_incs hi))]

/-- When all retained edges keep their incidences, incident edges are restricted by the edge set. -/
lemma incEdges_eq_inter (hF : ∀ e ∈ E(H), edgeFiber H e = edgeFiber G e) :
    incEdges H v = E(H) ∩ incEdges G v :=
  Set.ext fun e ↦ (and_iff_right_of_imp (incEdges_subset_edges ·)).symm.trans
    (and_congr_right fun he ↦ by
      simp only [mem_incEdges, hHG.incVerts_eq_of_edgeFiber_eq (hF e he)])

/-- For complete retained fibers, incidence membership is determined by the edge set. -/
lemma mem_incs_iff [Nonempty E] (hF : ∀ e ∈ E(H), edgeFiber H e = edgeFiber G e) (hi : i ∈ I(G)) :
    i ∈ I(H) ↔ edgeMap G i ∈ E(H) :=
  ⟨fun hiH ↦ hHG.edgeMap_eq hiH ▸ edgeMap_mem_edges hiH,
    fun he ↦ edgeFiber_subset_incs ((hF _ he).superset (mem_edgeFiber.mpr ⟨hi, rfl⟩))⟩

lemma incs_eq_inter_preimage [Nonempty E] (hF : ∀ e ∈ E(H), edgeFiber H e = edgeFiber G e) :
    I(H) = I(G) ∩ edgeMap G ⁻¹' E(H) :=
  Set.ext fun _ ↦ (and_iff_right_of_imp (hHG.incs_mono ·)).symm.trans
    (and_congr_right fun hi ↦ hHG.mem_incs_iff hF hi)

omit hHG in
lemma incs_eq_of_edges_eq (hE : E(H) = E(G))
    (hF : ∀ e ∈ E(H), edgeFiber H e = edgeFiber G e) : I(H) = I(G) := by
  rw [← biUnion_edgeFiber H, ← biUnion_edgeFiber G, ← hE]
  exact iUnion₂_congr hF

lemma edgeFiber_eq_iff : edgeFiber H e = edgeFiber G e ↔ edgeFiber G e ⊆ I(H) := by
  rw [hHG.edgeFiber_eq_inter, inter_eq_right]

lemma vertexFiber_eq_iff : vertexFiber H v = vertexFiber G v ↔ vertexFiber G v ⊆ I(H) := by
  rw [hHG.vertexFiber_eq_inter, inter_eq_right]

/-- Reverse inclusion holds exactly when the vertex and edge sets and directedness agree. -/
lemma antisymm_iff : IsSubgraph G H ↔ V(H) = V(G) ∧ E(H) = E(G) ∧
    (∀ i, IsSource H i ↔ IsSource G i) ∧ (∀ i, IsTarget H i ↔ IsTarget G i) := by
  refine ⟨fun hGH ↦ ⟨hHG.verts_mono.antisymm hGH.verts_mono,
    hHG.edges_mono.antisymm hGH.edges_mono, fun _ ↦ ⟨(hHG.isSource_mono ·), (hGH.isSource_mono ·)⟩,
    fun _ ↦ ⟨(hHG.isTarget_mono ·), (hGH.isTarget_mono ·)⟩⟩, fun ⟨hV, hE, hS, hT⟩ ↦ ?_⟩
  have hI : I(H) = I(G) := Set.ext fun i ↦ by
    simp only [HypergraphLike.mem_incs_iff, hS i, hT i]
  refine ⟨hV.superset, hE.superset, fun e he ↦ ?_, fun _ hiG hiH ↦ (hHG.attach'_eq hiH hiG).symm,
    fun _ h ↦ (hS _).mpr h, fun _ h ↦ (hT _).mpr h⟩
  rw [hHG.edgeFiber_eq_inter, hI, inter_eq_right.mpr edgeFiber_subset_incs]

omit hHG in
/-- Build inclusion from inclusions of all three sets and preservation of incidence maps. -/
lemma of_incidenceMaps (hV : V(H) ⊆ V(G)) (hE : E(H) ⊆ E(G)) (hI : I(H) ⊆ I(G))
    (hEdge : ∀ i (hiH : i ∈ I(H)) (hiG : i ∈ I(G)), (edgeMap' ⟨i, hiH⟩ : E) = edgeMap' ⟨i, hiG⟩)
    (hAttach : ∀ i (hiH : i ∈ I(H)) (hiG : i ∈ I(G)), (attach' ⟨i, hiH⟩ : V) = attach' ⟨i, hiG⟩)
    (hS : ∀ i, IsSource H i → IsSource G i) (hT : ∀ i, IsTarget H i → IsTarget G i) :
    IsSubgraph H G where
  verts_mono := hV
  edges_mono := hE
  edgeFiber_subset _ _ i hi := by
    obtain ⟨j, hj, rfl⟩ := hi
    exact ⟨inclusion hI j, (hEdge j j.property (hI j.property)).symm.trans hj, rfl⟩
  attach'_eq := hAttach
  isSource_mono := hS
  isTarget_mono := hT

end IsSubgraph

end HypergraphLike
