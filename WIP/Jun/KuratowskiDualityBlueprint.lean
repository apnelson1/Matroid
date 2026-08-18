/-
Copyright (c) 2026 Jun Kwon.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon

THIS FILE IS A PROOF BLUEPRINT, NOT A CLAIMED-COMPILING MODULE.

Purpose
=======

This file is a complete scaffold for the remaining finite planar-duality/Kuratowski project.
It deliberately contains many `sorry`s.  The goal is to expose the mathematical dependency graph
at a granularity where each obligation can be attacked locally, while keeping the final theorem
maximally representation-independent.

Public endpoint
===============

For a finite graph G, the intended public theorem is the equivalence of:

  (A) G has an abstract dual;
  (B) G contains neither K_5 nor K_{3,3} as a topological minor;
  (C) G is planar.

Internally it is useful to insert a fourth proposition:

  (W) G contains neither K_5 nor K_{3,3} as an ordinary minor.

The intended proof graph is

      HasAbstractDual
            |
            | matroid minor closure + K5/K33 have no abstract dual
            v
        WagnerFree
         ^       |
         |       | 3-connected Kuratowski + maximal-extension reduction
         |       v
  KuratowskiFree ---> Planar
         ^              |
         |              | geometric dual = matroid dual
         +--------------+

with

  WagnerFree -> KuratowskiFree

being immediate from `topological minor -> minor`, and

  KuratowskiFree -> WagnerFree

being the special graph-theoretic fact that a K5/K33 minor forces a TK5/TK33.

The final theorem can expose only A/B/C, while W remains a useful public corollary.

Generality policy
=================

Every declaration below is tagged in comments with one of:

  PUBLIC-GENERAL     intended mathematical API at the strongest natural level;
  PUBLIC-SPECIALIZED mathematically stable specialization worth exposing;
  PRIVATE-BRIDGE     proof-route-specific restriction; keep private unless it later proves useful;
  PRIVATE-TACTICAL   local proof decomposition only.

The standing policy is:

* aggressively weaken hypotheses and strengthen conclusions;
* unused structure is evidence of overspecialization;
* lack of a current consumer is not an argument against generalization;
* deliberately restricted bootstrap lemmas should usually be private;
* representation/canonicity issues should be solved by isomorphism transport, not by weakening the
  mathematical theorem statement.

Transport architecture
======================

The intended implementation uses the `Family` / `IsoAction` / `Equivariant` / `Invariant` /
`Relabel` / `Transfer` architecture from the accompanying design files.  In particular, the
finite hard direction should be proved on canonical infinite carriers and transferred back.
The exact graph arity below follows the current production `Graph α β` notation for readability;
when the half-edge graph redesign lands, the same declarations should be lifted mechanically to
`Graph V E`.
-/

module

-- Proposed imports, intentionally schematic while this remains a WIP blueprint.
public import Matroid.Graph.Planarity.PLDrawing
public import Matroid.Graph.Planarity.PLReduction
public import Matroid.Graph.Planarity.FaceCycle
public import Matroid.Graph.TopologicalMinor
-- public import Matroid.Graph.Minor.Iso
public import Matroid.Graph.Connected.Bond
public import Matroid.Graph.Connected.Ear
public import Matroid.Graph.Planarity.Obstructions
public import Matroid.Graph.Planarity.StarLemma
public import Matroid.Graph.Planarity.ThetaCurve
public import Matroid.Graphic
public import Matroid.Equiv
-- public import Matroid.Graph.Iso.Transfer

open Set Function
open scoped Sym2

namespace Graph

universe uV uE uV' uE'

variable {α : Type uV} {β : Type uE} {γ : Type uV'} {δ : Type uE'}
variable {G : Graph α β} {H : Graph γ δ}

/-! ###########################################################################
    0. THE FOUR CENTRAL PROPOSITIONS AND ISO-TRANSPORT
    ########################################################################### -/

/-- PUBLIC-GENERAL.
`G` contains neither Kuratowski obstruction as a topological minor.

Do not build finiteness into this definition. -/
def KuratowskiFree (G : Graph α β) : Prop :=
  ¬ (CompleteGraph 5).IsTopologicalMinor G ∧
  ¬ (CompleteBipartiteGraph 3 3).IsTopologicalMinor G

/-- PUBLIC-GENERAL.
The ordinary-minor version.  This is the useful internal strengthening because it is manifestly
minor-closed and therefore survives contractions in the 3-connected induction. -/
def WagnerFree (G : Graph α β) : Prop :=
  ¬ (CompleteGraph 5).IsMinor G ∧
  ¬ (CompleteBipartiteGraph 3 3).IsMinor G

/-- PUBLIC-GENERAL.
Data witnessing abstract duality.  This is intentionally a matroid isomorphism, rather than an
identity of edge-labelled matroids.  The edge correspondence is mathematical data and must survive
relabeling.

If the exact syntax of `Matroid.Iso` is inconvenient, keep the same conceptual interface:
`G.cycleMatroid✶ ≂ H.cycleMatroid`. -/
abbrev AbstractDualIso (G : Graph α β) (H : Graph γ δ) :=
  G.cycleMatroid✶ ≂ H.cycleMatroid

/-- PUBLIC-GENERAL.
Prop-valued relation obtained by forgetting the chosen edge equivalence. -/
def IsAbstractDual (G : Graph α β) (H : Graph γ δ) : Prop :=
  Nonempty (AbstractDualIso G H)

/-- PUBLIC-GENERAL.
A carrier-independent witness family.  Keeping the witness as data is what lets `IsoAction`
transport an actual dual graph, not just the proposition that one exists.

In the future 3-carrier graph definition, include all three carrier types here. -/
structure AbstractDualWitness (G : Graph α β) where
  Vertex : Type uV
  Edge : Type uE
  graph : Graph Vertex Edge
  iso : AbstractDualIso G graph

/-- PUBLIC-GENERAL.
Existence of an abstract dual. -/
def HasAbstractDual (G : Graph α β) : Prop := Nonempty (AbstractDualWitness G)

/-- PUBLIC-SPECIALIZED.
The equal-edge-carrier relation from the old WIP.  This is useful whenever primal and dual edges
are literally the same labels, especially for geometric duals.  It should be a specialization of
`IsAbstractDual`, not the primary definition. -/
def matroidalDual {γ : Type*} (G : Graph α β) (H : Graph γ β) : Prop :=
  G.cycleMatroid✶ = H.cycleMatroid

/-- PUBLIC-GENERAL.
Graph isomorphism induces an isomorphism of cycle matroids.  This is a foundational bridge for the
whole project and belongs below planarity. -/
noncomputable def Iso.cycleMatroidIso {G₁ : Graph α β} {G₂ : Graph γ δ}
    (i : G₁.Iso G₂) : G₁.cycleMatroid ≂ G₂.cycleMatroid := by
  sorry

/-- PUBLIC-GENERAL.
Dualizing a matroid isomorphism.  This may already exist in the matroid API; if so, use it instead. -/
noncomputable def Matroid.Iso.dual {M : Matroid β} {N : Matroid δ} (i : M ≂ N) : M✶ ≂ N✶ := by
  sorry

/-- PUBLIC-GENERAL.
Transport an abstract-dual witness along an isomorphism of the primal graph.  In the 3-carrier
redesign this should be the `IsoAction AbstractDualWitness` implementation. -/
noncomputable def AbstractDualWitness.mapIso {G₁ : Graph α β} {G₂ : Graph γ δ}
    (i : G₁.Iso G₂) (D : AbstractDualWitness G₁) : AbstractDualWitness G₂ := by
  sorry

/-- PUBLIC-GENERAL.
`HasAbstractDual` is representation-invariant.  Prefer obtaining this automatically from the
`IsoAction` instance on `AbstractDualWitness`. -/
instance instInvariantHasAbstractDual :
    Invariant (fun {α β} (G : Graph α β) => G.HasAbstractDual) := by
  sorry

/-- PUBLIC-GENERAL. -/
instance instInvariantKuratowskiFree :
    Invariant (fun {α β} (G : Graph α β) => G.KuratowskiFree) := by
  sorry

/-- PUBLIC-GENERAL. -/
instance instInvariantWagnerFree :
    Invariant (fun {α β} (G : Graph α β) => G.WagnerFree) := by
  sorry

/-- PUBLIC-GENERAL.
Planarity should be registered as invariant, preferably because drawings themselves form an
`IsoAction` family. -/
instance instInvariantPlanar :
    Invariant (fun {α β} (G : Graph α β) => G.Planar) := by
  sorry

/-! ###########################################################################
    1. ABSTRACT DUALITY: BASIC MATROID CONSEQUENCES
    ########################################################################### -/

namespace IsAbstractDual

/-- PUBLIC-GENERAL.  Abstract duality is symmetric. -/
theorem symm (h : G.IsAbstractDual H) : H.IsAbstractDual G := by
  sorry

/-- PUBLIC-GENERAL. -/
theorem edgeEquiv (h : G.IsAbstractDual H) : Nonempty (E(G) ≃ E(H)) := by
  sorry

/-- PUBLIC-SPECIALIZED.
Recover the general abstract-dual relation from literal equality on a common edge carrier. -/
theorem of_matroidalDual {H : Graph γ β} (h : G.matroidalDual H) : G.IsAbstractDual H := by
  sorry

/-- PUBLIC-SPECIALIZED.
After relabeling the dual edges through the chosen matroid isomorphism, every abstract dual can be
represented as a literal `matroidalDual` on the primal edge carrier.

This is the right bridge for reusing the old WIP arithmetic without making edge equality part of
the primary definition. -/
theorem exists_equalGround_copy (h : G.IsAbstractDual H) :
    ∃ H' : Graph γ β, G.matroidalDual H' ∧ H'.IsIsoTo H := by
  sorry

/-- PUBLIC-GENERAL.
If `G` has finite edge set then every abstract dual does too. -/
theorem edgeFinite_right [G.EdgeFinite] (h : G.IsAbstractDual H) : H.EdgeFinite := by
  sorry

/-- PUBLIC-GENERAL.
Connectedify a dual witness without changing its cycle matroid.  This is the generalized form of
`matroidalDual.exists_connected_matroidalDual` from the old WIP.

No finiteness should be needed; only enough room in the target vertex carrier, which can be solved
by changing carriers rather than adding a mathematical hypothesis. -/
theorem exists_connected_dual (h : G.IsAbstractDual H) :
    ∃ (γ' : Type uV) (H' : Graph γ' δ), G.IsAbstractDual H' ∧ H'.Connected := by
  sorry

/-- PUBLIC-GENERAL.
Finite connected witness when the primal edge set is finite. -/
theorem exists_connected_finite_dual [G.EdgeFinite] (h : G.IsAbstractDual H) :
    ∃ (γ' : Type uV) (H' : Graph γ' δ),
      G.IsAbstractDual H' ∧ H'.Finite ∧ H'.Connected := by
  sorry

end IsAbstractDual

namespace matroidalDual

variable {H₀ : Graph γ β}

/-- PUBLIC-SPECIALIZED.
Keep and finish the old WIP theorem.  This is already near the mathematically strongest ENat/cardinal
form and should not be weakened merely because finite Euler is the first consumer. -/
theorem euler_rank_identity (h : G.matroidalDual H₀) :
    V(G).encard + V(H₀).encard = E(G).encard + c(G) + c(H₀) := by
  sorry

/-- PUBLIC-SPECIALIZED. -/
theorem euler_rank_identity_of_connected (h : G.matroidalDual H₀)
    (hG : G.Connected) (hH : H₀.Connected) :
    V(G).encard + V(H₀).encard = E(G).encard + 2 := by
  sorry

/-- PUBLIC-SPECIALIZED.
Bridges of one graph correspond to matroid loops of the other. -/
theorem isBridge_iff_isLoop (h : G.matroidalDual H₀) {e : β} :
    G.IsBridge e ↔ ∃ v, H₀.IsLoopAt e v := by
  sorry

/-- PUBLIC-SPECIALIZED.
If the dual graph has at most one active vertex, the primal is a forest. -/
theorem isForest_of_dual_vertexSet_subsingleton (h : G.matroidalDual H₀)
    (hV : V(H₀).Subsingleton) : G.IsForest := by
  sorry

/-- PUBLIC-SPECIALIZED.
This is the key reusable inequality from the old WIP.  It is more general than the planar girth
bound: it assumes only matroidal duality.

Generality audit:
* do not assume G connected;
* do not assume H finite beyond what is forced by the cardinal arithmetic implementation;
* `H.Preconnected` is the natural graph hypothesis used to turn cocircuit girth into minimum degree.
-/
theorem girth_mul_dual_vertices_le_two_mul_edges (h : G.matroidalDual H₀)
    (hG : ¬ G.IsForest) (hH : H₀.Preconnected) :
    G.cycleMatroid.girth * V(H₀).encard ≤ 2 * E(G).encard := by
  sorry

/-- PUBLIC-SPECIALIZED.
A combined primal edge-connectivity / dual-girth inequality.  Preserve the old WIP theorem in its
strong form; K5/K33 are only tiny corollaries. -/
theorem girth_edgeConn_bound (h : G.matroidalDual H₀) {k g : ℕ}
    (hk : G.EdgeConnGE k) (hg : g ≤ G.cycleMatroid.girth)
    (hGF : ¬ G.IsForest) (hG : G.Connected) (hH : H₀.Connected)
    (hVG : V(G).Nontrivial) :
    8 + k * V(G).encard + g * V(H₀).encard ≤
      4 * (V(G).encard + V(H₀).encard) := by
  sorry

end matroidalDual

/-- PUBLIC-GENERAL.
K5 has no abstract dual.  The proof should immediately relabel a hypothetical abstract dual to an
equal-ground connected finite witness and invoke the general rank/girth bound. -/
theorem completeGraph_five_not_hasAbstractDual :
    ¬ (CompleteGraph 5).HasAbstractDual := by
  sorry

/-- PUBLIC-GENERAL. -/
theorem completeBipartiteGraph_three_three_not_hasAbstractDual :
    ¬ (CompleteBipartiteGraph 3 3).HasAbstractDual := by
  sorry

/-! ###########################################################################
    2. ABSTRACT DUALITY UNDER GRAPH MINORS
    ########################################################################### -/

namespace IsAbstractDual

/-- PUBLIC-GENERAL.
Deleting primal edges corresponds to contracting the corresponding dual edges.

The statement should be made through the chosen edge equivalence, not under a fake equality of
edge carriers.  The exact graph-contraction witness type is schematic here. -/
theorem delete_contract
    (h : G.IsAbstractDual H) (D : Set E(G)) :
    ∃ H', (G.deleteEdges (↑D)).IsAbstractDual H' := by
  sorry

/-- PUBLIC-GENERAL.
Contracting primal edges corresponds to deleting the corresponding dual edges. -/
theorem contract_delete
    (h : G.IsAbstractDual H) (C : Set E(G)) :
    ∃ H', (G.contractEdges (↑C)).IsAbstractDual H' := by
  sorry

/-- PUBLIC-GENERAL.
The previous two operations commute with an arbitrary delete/contract minor specification. -/
theorem minor
    (h : G.IsAbstractDual H) {K : Graph α β} (hKG : K.IsMinor G) :
    K.HasAbstractDual := by
  sorry

end IsAbstractDual

/-- PUBLIC-GENERAL.
Existence of an abstract dual is minor-closed.

This is the actual API theorem callers should use; the relation-level delete/contract lemmas above
are its implementation. -/
theorem HasAbstractDual.minor_closed {K : Graph α β}
    (hG : G.HasAbstractDual) (hKG : K.IsMinor G) : K.HasAbstractDual := by
  sorry

/-- PUBLIC-GENERAL.
A topological model gives an ordinary graph minor.  If the fully general statement causes an
infinite-minor dependency problem, first prove it for finite pattern H as a PRIVATE-BRIDGE and then
return to the general statement later. -/
theorem IsTopologicalMinor.isMinor {K : Graph γ δ}
    (h : K.IsTopologicalMinor G) : K.IsMinor G := by
  sorry

/-- PUBLIC-GENERAL. -/
theorem HasAbstractDual.topologicalMinor_closed {K : Graph γ δ}
    (hG : G.HasAbstractDual) (hKG : K.IsTopologicalMinor G) : K.HasAbstractDual := by
  exact hG.minor_closed hKG.isMinor

/-- PUBLIC-GENERAL.
First major arrow, proved wholly through matroid/minor theory. -/
theorem HasAbstractDual.wagnerFree (hG : G.HasAbstractDual) : G.WagnerFree := by
  constructor
  · intro hK5
    exact completeGraph_five_not_hasAbstractDual (hG.minor_closed hK5)
  · intro hK33
    exact completeBipartiteGraph_three_three_not_hasAbstractDual (hG.minor_closed hK33)

/-- PUBLIC-GENERAL. -/
theorem WagnerFree.kuratowskiFree (hG : G.WagnerFree) : G.KuratowskiFree := by
  constructor
  · exact fun h => hG.1 h.isMinor
  · exact fun h => hG.2 h.isMinor

/-! ###########################################################################
    3. KURATOWSKI-FREE <-> WAGNER-FREE
    ########################################################################### -/

/-- PUBLIC-GENERAL.
A K5 minor forces either a TK5 or a TK3,3.  This is Diestel's special K5 branch-set reduction.
Do not assume host finiteness unless the minor API genuinely requires it. -/
theorem isTopologicalMinor_K5_or_K33_of_isMinor_K5
    (h : (CompleteGraph 5).IsMinor G) :
    (CompleteGraph 5).IsTopologicalMinor G ∨
    (CompleteBipartiteGraph 3 3).IsTopologicalMinor G := by
  sorry

/-- PUBLIC-GENERAL.
A K3,3 minor forces a TK3,3.  If the cleanest actual theorem naturally allows a TK5 alternative,
state the stronger/easier disjunction and let the final corollary consume it. -/
theorem isTopologicalMinor_K33_or_K5_of_isMinor_K33
    (h : (CompleteBipartiteGraph 3 3).IsMinor G) :
    (CompleteBipartiteGraph 3 3).IsTopologicalMinor G ∨
    (CompleteGraph 5).IsTopologicalMinor G := by
  sorry

/-- PUBLIC-GENERAL. -/
theorem KuratowskiFree.wagnerFree (hG : G.KuratowskiFree) : G.WagnerFree := by
  constructor
  · intro h
    exact (isTopologicalMinor_K5_or_K33_of_isMinor_K5 h).elim hG.1 hG.2
  · intro h
    exact (isTopologicalMinor_K33_or_K5_of_isMinor_K33 h).elim hG.2 hG.1

/-- PUBLIC-GENERAL.
This equivalence is independently useful and should be exported even though the headline theorem
mentions only topological minors. -/
theorem kuratowskiFree_iff_wagnerFree : G.KuratowskiFree ↔ G.WagnerFree :=
  ⟨KuratowskiFree.wagnerFree, WagnerFree.kuratowskiFree⟩

/-! ###########################################################################
    4. GEOMETRIC DUAL: LOCAL EDGE-SIDE CONSTRUCTION
    ###########################################################################

The current practical implementation target is a finite loopless PL drawing.  This is a deliberate
bootstrap restriction because the existing local-star API is polygonal.  The final theorem
`Planar -> HasAbstractDual` below removes the restriction by normalization and PL reduction.

A future public `Drawing.geometricDual` for arbitrary tame drawings is desirable, but it should not
block the finite Kuratowski project.
-/

namespace PLDrawing

variable [G.Finite] [G.Loopless] (D : PLDrawing G ℝ²)

/-- PUBLIC-SPECIALIZED.
The face type on the sphere.  Keep the one-point compactification internal to the implementation
when possible. -/
abbrev Face := D.toDrawing.onePoint.Face

/-- PRIVATE-TACTICAL.
Use the midpoint only as a convenient deterministic point in the edge interior.  The geometric dual
must eventually be proved independent of this choice. -/
noncomputable def edgeMidpoint (e : E(G)) : OnePoint ℝ² :=
  D.edgeInteriorPoint e (1 / 2)

/-- PUBLIC-GENERAL CANDIDATE, currently proved in the PL setting.
Every interior point of a simple polygonal edge has a sufficiently small two-ray local star, and no
other edge/vertex of the finite drawing enters the ball. -/
theorem exists_edgeInterior_local_two_star (e : E(G)) :
    ∃ q ρ Y,
      q ∈ D.edgeInterior e ∧ 0 < ρ ∧ Y.card = 2 ∧
      closedBall q ρ ∩ D.toDrawing.support =
        {q} ∪ ⋃ y ∈ Y, segment ℝ q y := by
  sorry

/-- PRIVATE-TACTICAL.
Exactly two local sectors occur around an edge interior. -/
theorem edgeInterior_two_sectors (e : E(G)) :
    ∃ S : Fin 2 → Set ℝ²,
      Pairwise (Disjoint on S) ∧
      (∀ i, IsConnected (S i)) ∧
      (∀ i, S i ⊆ D.toDrawing.supportᶜ) := by
  sorry

/-- PRIVATE-BRIDGE.
Each local sector lies in a unique global face. -/
noncomputable def edgeSideFace (e : E(G)) (i : Fin 2) : D.Face := by
  sorry

/-- PUBLIC-SPECIALIZED.
The unordered pair of faces seen from the two local sides of the primal edge.  Both entries may be
equal; this is exactly how a primal bridge becomes a dual loop. -/
noncomputable def dualEnds (e : E(G)) : Sym2 D.Face :=
  s(D.edgeSideFace e 0, D.edgeSideFace e 1)

/-- PUBLIC-SPECIALIZED.
Changing the local star/radius/midpoint does not change the unordered pair of global side faces.
This is the canonicity theorem behind `dualEnds`. -/
theorem dualEnds_eq_of_other_local_choice (e : E(G)) :
    -- schematic quantified statement over any valid two-sector local model
    True := by
  sorry

/-- PUBLIC-SPECIALIZED.
The geometric dual graph.  Dual vertices are global faces; dual edges are literally primal edges. -/
noncomputable def geometricDual : Graph D.Face β where
  vertexSet := Set.univ
  edgeSet := E(G)
  IsLink e F₁ F₂ := e ∈ E(G) ∧ s(F₁, F₂) = D.dualEnds ⟨e, by assumption⟩
  isLink_symm := by sorry
  eq_or_eq_of_isLink_of_isLink := by sorry
  edge_mem_iff_exists_isLink := by sorry
  left_mem_of_isLink := by sorry

@[simp] theorem edgeSet_geometricDual : E(D.geometricDual) = E(G) := by
  sorry

@[simp] theorem geometricDual_isLink_iff (e : β) (F₁ F₂ : D.Face) :
    D.geometricDual.IsLink e F₁ F₂ ↔
      e ∈ E(G) ∧ s(F₁, F₂) = D.dualEnds ⟨e, by assumption⟩ := by
  sorry

/-- PUBLIC-SPECIALIZED.
Bridge-loop correspondence at the geometric level.  This should eventually be a corollary of the
matroid-duality theorem too, but proving it directly is a valuable sanity check for `dualEnds`. -/
theorem isBridge_iff_geometricDual_isLoop (e : β) :
    G.IsBridge e ↔ ∃ F, D.geometricDual.IsLoopAt e F := by
  sorry

/-! ---------------------------------------------------------------------------
    4A. A reusable face-adjacency / region-connectivity theorem
    --------------------------------------------------------------------------- -/

/-- PUBLIC-GENERAL CANDIDATE.
Given selected faces and selected primal edges, form the corresponding open 2-dimensional region:
face interiors together with the interiors of selected edges. -/
def dualRegion (F : Set D.Face) (E₀ : Set β) : Set (OnePoint ℝ²) :=
  (⋃ f ∈ F, D.toDrawing.onePoint.faceSet f) ∪
  (⋃ e ∈ E₀ ∩ E(G), D.toDrawing.onePoint.edgeInterior e)

/-- PUBLIC-GENERAL CANDIDATE.
This is the finite-drawing replacement for the old CW theorem `dualGraph_preconnected`:
connectivity in the chosen dual subgraph is equivalent to topological connectedness of the union of
the corresponding faces and open edges.

Try to formulate this for any drawing for which the local edge-side theorem is available, not
specifically for plane graphs. -/
theorem dual_restrict_preconnected_iff_region_preconnected
    (F : Set D.Face) (E₀ : Set β) :
    (D.geometricDual.induce F).restrict E₀ |>.Preconnected ↔
      IsPreconnected (D.dualRegion F E₀) := by
  sorry

/-- PUBLIC-SPECIALIZED.
The full geometric dual is connected.  Prove geometrically from the previous theorem; do not assume
primal connectedness. -/
theorem geometricDual_connected : D.geometricDual.Connected := by
  sorry

end PLDrawing

/-! ###########################################################################
    5. GEOMETRIC DUAL: CYCLE <-> BOND, THEN MATROID DUALITY
    ########################################################################### -/

namespace PLDrawing

variable [G.Finite] [G.Loopless] (D : PLDrawing G ℝ²)

/-- PUBLIC-GENERAL CANDIDATE.
A graph cycle in a PL drawing traces a Jordan curve on the sphere, and its support is exactly the
image of that curve.  This should require only the cycle subgraph, not connectivity of G. -/
theorem cycle_support_isJordanCurve
    {C : Set β} (hC : G.IsCycleSet C) :
    ∃ J : Path (D.toDrawing.onePoint.somePoint) (D.toDrawing.onePoint.somePoint),
      J.IsSimpleLoop ∧ range J = D.toDrawing.onePoint.edgeSupport C := by
  sorry

/-- PRIVATE-BRIDGE.
For a primal cycle C, classify every primal face as lying on one of the two Jordan sides. -/
noncomputable def cycleSideFaces {C : Set β} (hC : G.IsCycleSet C) :
    Bool → Set D.Face := by
  sorry

/-- PRIVATE-BRIDGE.
Every cycle edge has one dual endpoint on each Jordan side. -/
theorem cycle_edge_crosses_side_partition
    {C : Set β} (hC : G.IsCycleSet C) {e : β} (he : e ∈ C) :
    -- schematic: the two endpoints of dual edge e lie in opposite side-face sets
    True := by
  sorry

/-- PRIVATE-BRIDGE.
Every non-cycle edge has both local side faces on the same Jordan side. -/
theorem noncycle_edge_stays_in_side
    {C : Set β} (hC : G.IsCycleSet C) {e : β} (he : e ∈ E(G) \ C) :
    True := by
  sorry

/-- PRIVATE-BRIDGE.
The dual vertices on each Jordan side remain connected using only dual edges outside C.
This is the place to use `dual_restrict_preconnected_iff_region_preconnected`. -/
theorem cycle_side_dual_preconnected
    {C : Set β} (hC : G.IsCycleSet C) (i : Bool) :
    -- schematic induced/restricted graph
    True := by
  sorry

/-- PUBLIC-SPECIALIZED.
Every primal cycle is a dual bond.  This is one half of abstract duality and should be independently
exported. -/
theorem isCycleSet_iff_geometricDual_isBond_forward
    {C : Set β} (hC : G.IsCycleSet C) :
    D.geometricDual.IsBond C := by
  sorry

/-! ---------------------------------------------------------------------------
    5A. Forests do not separate the sphere
    --------------------------------------------------------------------------- -/

/-- PUBLIC-GENERAL CANDIDATE.
The complement of the support of a finite embedded forest in the sphere is preconnected.

Generality target: this theorem should live outside planarity if its proof only uses an injective
realization of a finite forest in S².  Do not state it specifically for `PLDrawing` unless required
by the current proof route.

Suggested induction:
1. empty edge set / isolated points;
2. choose a leaf edge;
3. remove a small terminal arc at the leaf;
4. show adding that arc back cannot disconnect the complement.
Alternative: induct by attaching an embedded arc at one endpoint to a nonseparating compactum.
-/
theorem forest_support_compl_preconnected
    {F : Set β} (hF : G.IsAcyclicSet F) :
    IsPreconnected (D.toDrawing.onePoint.edgeSupport F)ᶜ := by
  sorry

/-- PUBLIC-GENERAL CANDIDATE.
The region consisting of all primal faces plus all non-S edge interiors differs from the complement
of the geometric support of S only by finitely many primal vertices.  State the exact equality or
sandwich that the connectivity proof actually uses. -/
theorem dualRegion_allFaces_complEdges_vs_edgeSupport_compl
    (S : Set β) : True := by
  sorry

/-- PUBLIC-GENERAL CANDIDATE.
Removing or restoring finitely many graph-vertex points in the relevant 2-dimensional open region
does not change preconnectedness.  Generalize to finite subsets of a 2-manifold/open connected set
if the proof does not use graph structure. -/
theorem finite_vertex_punctures_preserve_preconnected : True := by
  sorry

/-- PRIVATE-BRIDGE.
If a dual bond S contained no primal cycle, then S would be a forest and its geometric support would
not separate the sphere. -/
theorem dualBond_not_acyclic
    {S : Set β} (hS : D.geometricDual.IsBond S) :
    ¬ G.IsAcyclicSet S := by
  sorry

/-- PRIVATE-BRIDGE.
Every non-acyclic edge set contains a primal cycle set.  This should be a pure graph/matroid lemma,
probably already available. -/
theorem exists_cycleSet_subset_of_not_acyclic
    {S : Set β} (hS : ¬ G.IsAcyclicSet S) :
    ∃ C ⊆ S, G.IsCycleSet C := by
  sorry

/-- PUBLIC-SPECIALIZED.
Every dual bond is exactly a primal cycle.  Use bond minimality after extracting a cycle subset and
applying the forward direction. -/
theorem geometricDual_isBond_iff_isCycleSet_backward
    {S : Set β} (hS : D.geometricDual.IsBond S) : G.IsCycleSet S := by
  obtain ⟨C, hCS, hC⟩ := D.exists_cycleSet_subset_of_not_acyclic (D.dualBond_not_acyclic hS)
  have hCb : D.geometricDual.IsBond C := D.isCycleSet_iff_geometricDual_isBond_forward hC
  exact by
    sorry

/-- PUBLIC-SPECIALIZED.
The central graph-theoretic geometric-duality theorem. -/
theorem isCycleSet_iff_geometricDual_isBond (S : Set β) :
    G.IsCycleSet S ↔ D.geometricDual.IsBond S := by
  constructor
  · exact D.isCycleSet_iff_geometricDual_isBond_forward
  · exact D.geometricDual_isBond_iff_isCycleSet_backward

/-- PUBLIC-SPECIALIZED.
Geometric duality realizes matroid duality.  Because the geometric dual literally reuses the primal
edge labels, this should be literal equality of matroids, not merely an isomorphism.

Proof: characterize circuits of the left side as dual bonds, then use
`cycleMatroid_cocircuit` on G. -/
theorem cycleMatroid_geometricDual :
    D.geometricDual.cycleMatroid = G.cycleMatroid✶ := by
  sorry

/-- PUBLIC-SPECIALIZED. -/
theorem geometricDual_matroidalDual : G.matroidalDual D.geometricDual := by
  simpa [matroidalDual] using D.cycleMatroid_geometricDual.symm

end PLDrawing

/-! ###########################################################################
    6. EULER AND PLANAR NUMERICAL CONSEQUENCES
    ########################################################################### -/

namespace PLDrawing

variable [G.Finite] [G.Loopless] (D : PLDrawing G ℝ²)

/-- PUBLIC-SPECIALIZED.
General Euler formula for a possibly disconnected primal plane graph.  Derive this from matroid rank
duality rather than by geometric induction. -/
theorem euler_formula :
    V(G).encard + V(D.geometricDual).encard = E(G).encard + c(G) + 1 := by
  have hdual : G.matroidalDual D.geometricDual := D.geometricDual_matroidalDual
  rw [hdual.euler_rank_identity, D.geometricDual_connected.numberOfComponents]

/-- PUBLIC-SPECIALIZED. -/
theorem euler_formula_of_connected (hG : G.Connected) :
    V(G).encard + V(D.geometricDual).encard = E(G).encard + 2 := by
  sorry

/-- PUBLIC-SPECIALIZED.
The usual simple-planar girth bound, obtained from the abstract-dual inequality.  State the stronger
girth form first; triangle-free and bipartite bounds are corollaries. -/
theorem edge_bound_of_girth {g : ℕ}
    (hg : g ≤ G.cycleMatroid.girth) (hforest : ¬ G.IsForest) :
    -- exact finite-cardinality version chosen after ENat normalization
    True := by
  sorry

end PLDrawing

/-! ###########################################################################
    7. PLANAR -> HAS ABSTRACT DUAL FOR ARBITRARY FINITE GRAPHS
    ########################################################################### -/

This section intentionally separates the clean loopless PL geometric theorem from the arbitrary
finite graph theorem.  Loops should be restored matroidally as dual bridges/coloops rather than
forcing the current polygonal local-side machinery to handle wild loop parametrizations.
-/

/-- PUBLIC-GENERAL.
Deleting graph-theoretic loops deletes exactly the matroid loops.  Prefer an existing theorem if the
API already states this. -/
theorem cycleMatroid_deleteLoops (G : Graph α β) :
    -- schematic equality/decomposition of matroids
    True := by
  sorry

/-- PUBLIC-GENERAL.
A graph constructor which adjoins one bridge/coloop for each label in L, without changing any
existing cycle.  Use a `Sum` vertex carrier rather than demanding fresh labels in the old carrier. -/
noncomputable def addColoopsFor (H : Graph γ β) (L : Set β) : Graph (γ ⊕ L) β := by
  sorry

/-- PUBLIC-GENERAL.
Cycle matroid of `addColoopsFor` is the original cycle matroid with the selected labels adjoined as
coloops. -/
theorem cycleMatroid_addColoopsFor (H : Graph γ β) (L : Set β) :
    True := by
  sorry

/-- PUBLIC-GENERAL.
If the loopless core has an abstract dual, then so does the original graph. -/
theorem hasAbstractDual_of_deleteLoops_hasAbstractDual
    (h : (G.deleteEdges G.loopSet).HasAbstractDual) : G.HasAbstractDual := by
  sorry

/-- PUBLIC-GENERAL.
Main geometric-duality existence theorem for finite graphs.

Suggested proof:
1. delete loops;
2. restrict the given drawing;
3. use `Planar.plPlanar` on the finite loopless core;
4. use `PLDrawing.geometricDual_matroidalDual`;
5. restore deleted primal loops as dual bridges using `addColoopsFor`.

No connectedness or simplicity assumption belongs in the final statement. -/
theorem Planar.hasAbstractDual [G.Finite] (hG : G.Planar) : G.HasAbstractDual := by
  sorry

/-! ###########################################################################
    7A. JORDAN-CURVE ASSUMPTION BOUNDARY
    ###########################################################################

The project intentionally assumes the Jordan Curve Theorem rather than formalizing it from first
principles.  There should nevertheless be exactly one licensed axiom/opaque assumption.  Every
sphere/one-point/polygonal consequence must be proved from it, not introduced as another `sorry`.
-/

namespace JordanCurveBoundary

/-- PUBLIC-GENERAL / LICENSED AXIOM.
This is the only theorem in the completed project that is allowed to remain axiomatic.  Choose the
most general Mathlib-natural formulation (preferably a Jordan embedding of `Circle` into an
abstract topological plane / sphere if that does not create a dependency cycle). -/
axiom jordan_curve_theorem : True

/-- PUBLIC-GENERAL.
Plane complement form: a Jordan curve has exactly two connected components, both with frontier the
curve. -/
theorem plane_complement_two_components : True := by
  -- derive only from `jordan_curve_theorem`
  sorry

/-- PUBLIC-GENERAL.
One-point compactification / sphere form used by `Drawing.Face`. -/
theorem onePoint_complement_two_components : True := by
  sorry

/-- PUBLIC-GENERAL.
Polygonal simple-loop specialization.  This should be a theorem, never an extra axiom. -/
theorem polygonal_simpleLoop_jordan : True := by
  sorry

/-- PRIVATE-TACTICAL.
Final repository audit target: all headline planarity/duality theorems should print exactly the one
licensed JCT axiom (plus standard classical choice/propext/quotient axioms as expected), not stray
`sorryAx`s.  This is a CI/checklist obligation rather than mathematical content. -/
private theorem axiom_audit_placeholder : True := by
  trivial

end JordanCurveBoundary

/-! ###########################################################################
    8. LOCAL POLYGONAL TOPOLOGY NEEDED BY THE 3-CONNECTED HARD DIRECTION
    ########################################################################### -/

namespace PolygonalPath

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- PUBLIC-GENERAL.
Every nonendpoint point of a simple polygonal arc has a two-ray local star, with an arbitrary upper
bound on the radius.  This should remain dimension-free. -/
theorem IsSimple.exists_local_star_two
    {x y q : V} {P : PolygonalPath x y} (hP : P.IsSimple)
    (hqP : q ∈ P.toSet) (hqx : q ≠ x) (hqy : q ≠ y)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ, 0 < ρ ∧ ρ ≤ ε ∧
      ∃ Y : Finset V, Y.card = 2 ∧
        (Y : Set V) ⊆ sphere q ρ ∧
        closedBall q ρ ∩ P.toSet =
          {q} ∪ ⋃ z ∈ Y, segment ℝ q z := by
  sorry

/-- PRIVATE-TACTICAL.  Subdivide P at q without changing `toSet`. -/
private theorem localStarTwo_subdivide_at_point : True := by sorry

/-- PRIVATE-TACTICAL.  Break the subdivided path into two simple arcs meeting only at q. -/
private theorem localStarTwo_breakAt : True := by sorry

/-- PRIVATE-TACTICAL.  Choose a ball in which each half is contained in its first segment. -/
private theorem localStarTwo_firstSegment_ball : True := by sorry

/-- PRIVATE-TACTICAL.  Apply `IsSegmentFigure.exists_radius` below the chosen epsilon. -/
private theorem localStarTwo_choose_radius : True := by sorry

/-- PRIVATE-TACTICAL.  Obtain the lower cardinal bound 2 from the two path halves. -/
private theorem localStarTwo_two_le_card_radii : True := by sorry

/-- PRIVATE-TACTICAL.  Obtain the upper cardinal bound 2 from the two-segment cover. -/
private theorem localStarTwo_card_radii_le_two : True := by sorry

end PolygonalPath

/-! ---------------------------------------------------------------------------
    8A. Theta curve: exact three-component theorem
    --------------------------------------------------------------------------- -/

namespace PolygonalPath

variable {a b : ℝ²}

/-- PRIVATE-BRIDGE.
The union of the three theta arms is a finite segment figure. -/
private theorem theta_isSegmentFigure
    (A : Fin 3 → PolygonalPath a b) : True := by
  sorry

/-- PRIVATE-BRIDGE.
At endpoint a, choose one common radius at which all three arms are exactly their first radial
segments.  Localize each arm with `closedBall a ρ`; do NOT claim the global arm intersections are
`{a}` because all arms also meet at b. -/
private theorem theta_endpoint_common_radius
    (hab : a ≠ b) (A : Fin 3 → PolygonalPath a b)
    (hsimple : ∀ i, (A i).IsSimple)
    (hmeet : ∀ i j, i ≠ j → (A i).toSet ∩ (A j).toSet = {a, b}) :
    True := by
  sorry

/-- PRIVATE-BRIDGE.  Three distinct localized arms give at least three radii. -/
private theorem theta_endpoint_three_le_radii : True := by sorry

/-- PRIVATE-BRIDGE.  The three-arm cover gives at most three radii. -/
private theorem theta_endpoint_radii_le_three : True := by sorry

/-- PRIVATE-BRIDGE.
Endpoint local star with exactly three sectors. -/
private theorem exists_theta_endpoint_star_three : True := by
  sorry

/-- PUBLIC-GENERAL CANDIDATE.
An interior point of exactly one theta arm has a local two-ray star, and the other two arms can be
excluded by shrinking the radius. -/
theorem exists_theta_arm_interior_star_two : True := by
  sorry

/-- PRIVATE-BRIDGE.
For each omitted arm i, the other two arms concatenate to a simple Jordan loop. -/
private theorem theta_other_two_simpleLoop : True := by sorry

/-- PRIVATE-BRIDGE.  Its support is exactly the union of those two arms. -/
private theorem theta_other_two_support_eq : True := by sorry

/-- PRIVATE-BRIDGE.
The interior of the omitted arm is nonempty, connected, and disjoint from that Jordan loop. -/
private theorem theta_omitted_interior_properties : True := by sorry

/-- PRIVATE-BRIDGE.
Choose the Jordan side opposite the omitted arm. -/
private noncomputable def thetaCandidateRegion : Fin 3 → Set (OnePoint ℝ²) := by
  sorry

/-- PRIVATE-BRIDGE.  Candidate region lies in the theta complement. -/
private theorem thetaCandidateRegion_subset_compl : True := by sorry

/-- PRIVATE-BRIDGE.
Each candidate is an entire connected component of the theta complement, not merely a connected
subset. -/
private theorem thetaCandidateRegion_eq_component : True := by sorry

/-- PRIVATE-BRIDGE.  The three candidates are distinct, hence pairwise disjoint. -/
private theorem thetaCandidateRegion_pairwise_disjoint : True := by sorry

/-- PUBLIC-GENERAL CANDIDATE.
For an arbitrary complement component K, its frontier is nonempty and lies in theta.  This is
mostly generic topology and should be split out of PolygonalPath if possible. -/
theorem theta_component_frontier_nonempty_subset : True := by
  sorry

/-- PRIVATE-BRIDGE.
Any frontier point is either endpoint a/b or lies in the interior of a unique arm. -/
private theorem theta_frontier_point_cases : True := by sorry

/-- PRIVATE-BRIDGE.
Endpoint classification: the three candidate components occupy the three local sectors, so any
component with endpoint in its frontier equals one candidate. -/
private theorem theta_component_eq_candidate_of_endpoint_frontier : True := by
  sorry

/-- PRIVATE-BRIDGE.
Interior-arm classification: the two candidate components adjacent to that arm occupy the two local
sectors, so any component with that point in its frontier equals one of them. -/
private theorem theta_component_eq_candidate_of_arm_frontier : True := by
  sorry

/-- PRIVATE-BRIDGE. -/
private theorem theta_every_component_is_candidate : True := by
  sorry

/-- PUBLIC-GENERAL.
The exact three-region theta theorem.  Keep this graph-free. -/
theorem exists_three_regions_theta
    (hab : a ≠ b) (A : Fin 3 → PolygonalPath a b)
    (hsimple : ∀ i, (A i).IsSimple)
    (hmeet : ∀ i j, i ≠ j → (A i).toSet ∩ (A j).toSet = {a, b}) :
    ∃ W : Fin 3 → Set (OnePoint ℝ²),
      (∀ i, IsOpen (W i)) ∧
      (∀ i, IsConnected (W i)) ∧
      Pairwise (fun i j => Disjoint (W i) (W j)) ∧
      (⋃ i, W i) = ((↑) '' ⋃ i, (A i).toSet)ᶜ ∧
      ∀ i, frontier (W i) =
        (↑) '' ⋃ j ∈ ({i}ᶜ : Set (Fin 3)), (A j).toSet := by
  sorry

end PolygonalPath

/-! ---------------------------------------------------------------------------
    8B. Crosscut
    --------------------------------------------------------------------------- -/

namespace Polygon

/-- PRIVATE-BRIDGE.  Split the boundary polygon at the two crosscut endpoints into two simple arcs. -/
private theorem crosscut_boundary_two_arcs : True := by sorry

/-- PRIVATE-BRIDGE.  The two boundary arcs and the crosscut satisfy theta hypotheses. -/
private theorem crosscut_forms_theta : True := by sorry

/-- PRIVATE-BRIDGE.
Identify the theta region outside the original Jordan polygon. -/
private theorem crosscut_theta_exterior_eq_original_exterior : True := by sorry

/-- PUBLIC-GENERAL.
A simple crosscut of a Jordan polygon splits its interior into exactly two connected regions with
the expected frontiers. -/
theorem IsSimple.exists_two_regions_crosscut : True := by
  sorry

/-- PUBLIC-GENERAL.
Two disjoint crosscuts in the same Jordan region cannot have alternating endpoints.
Not needed for the preferred K5 nonduality proof, but mathematically valuable. -/
theorem IsSimple.not_alternating_crosscut : True := by
  sorry

end Polygon

/-! ###########################################################################
    9. FACE CYCLES BY EAR INDUCTION
    ########################################################################### -/

namespace PLDrawing

variable [G.Finite] [G.Loopless] (D : PLDrawing G ℝ²)

/-- PUBLIC-SPECIALIZED.
Trace a graph path by a polygonal path with exactly the support of its drawing restriction. -/
theorem exists_polygonalPath_toSet_eq_support_of_isPath : True := by
  sorry

/-- PUBLIC-SPECIALIZED. -/
theorem exists_isSimpleLoop_toSet_eq_support_of_isCyclicWalk : True := by
  sorry

/-- PUBLIC-SPECIALIZED. -/
theorem exists_polygon_isSimple_of_isCycle : True := by
  sorry

/-- PRIVATE-BRIDGE.
Base case of the ear induction: every face of a drawn cycle has the whole cycle as frontier, with
the correct component identity. -/
private theorem faceCycle_base_cycle : True := by
  sorry

/-- PRIVATE-BRIDGE.
For an ear P added to H, its interior lies in a unique face F of the drawing of H. -/
private theorem ear_interior_subset_unique_old_face : True := by
  sorry

/-- PRIVATE-BRIDGE.
Restricting the drawing to the old graph and to the ear has exactly the expected support
intersection. -/
private theorem support_restrict_inter_support_restrict_of_isEar : True := by
  sorry

/-- PRIVATE-BRIDGE.
By the induction hypothesis, the old face F is bounded by a cycle C. -/
private theorem ear_old_face_boundary_cycle : True := by
  sorry

/-- PRIVATE-BRIDGE.
The two ear endpoints split the old boundary cycle into two simple boundary paths. -/
private theorem ear_boundary_cycle_split_paths : True := by
  sorry

/-- PRIVATE-BRIDGE.
Apply the crosscut theorem to obtain the two new faces inside F and identify their boundary cycles. -/
private theorem ear_crosscut_new_faces : True := by
  sorry

/-- PRIVATE-BRIDGE.
All old faces other than F are unchanged by adding the ear. -/
private theorem ear_other_faces_unchanged : True := by
  sorry

/-- PUBLIC-SPECIALIZED.
Every face of a finite 2-connected loopless PL drawing is bounded by a graph cycle, and the face is
exactly the corresponding component of the cycle complement.

Keep the full component equality: it is stronger and is what later insertion/contraction arguments
actually want. -/
theorem exists_isCycle_frontier_faceSet_eq
    (hG : G.ConnGE 2) (F : D.toDrawing.onePoint.Face) :
    ∃ (C : Graph α β) (hC : C ≤ G), C.IsCycle ∧
      frontier (D.toDrawing.onePoint.faceSet F) =
        (D.toDrawing.onePoint.restrict hC).support ∧
      ∀ ⦃q⦄, q ∈ D.toDrawing.onePoint.faceSet F →
        D.toDrawing.onePoint.faceSet F =
          connectedComponentIn ((D.toDrawing.onePoint.restrict hC).support)ᶜ q := by
  sorry

end PLDrawing

/-! ###########################################################################
    10. FACIAL CYCLES AROUND DELETED / CONTRACTED VERTICES
    ########################################################################### -/

namespace PLDrawing

variable [G.Finite] [G.Simple] (D : PLDrawing G ℝ²)

/-- PRIVATE-BRIDGE.
Deleting one vertex from a 3-connected graph leaves a 2-connected graph.  Use the existing graph
connectivity theorem rather than reproving it geometrically. -/
private theorem delete_vertex_connGE_two : True := by sorry

/-- PRIVATE-BRIDGE.
All neighbors of the deleted vertex lie on the frontier of the unique old face containing its
former point. -/
private theorem neighbors_on_deleted_vertex_face_frontier : True := by
  sorry

/-- PUBLIC-SPECIALIZED.
Deleting a vertex from a 3-connected PL drawing exposes a facial cycle containing all its former
neighbors. -/
theorem exists_facial_cycle_of_delete_vertex
    (hG : G.ConnGE 3) (u : V(G)) :
    -- exact production statement to be filled from current API
    True := by
  sorry

/-- PRIVATE-BRIDGE.
In a drawing of G/e, deleting the contracted vertex exposes the facial cycle used to split the
vertex back. -/
private theorem contracted_vertex_deleted_face : True := by
  sorry

/-- PUBLIC-SPECIALIZED.
Facial cycle around the contracted supervertex. -/
theorem exists_facial_cycle_of_contract : True := by
  sorry

/-! ---------------------------------------------------------------------------
    10A. Local insertion and vertex splitting
    --------------------------------------------------------------------------- -/

/-- PUBLIC-GENERAL CANDIDATE.
Two boundary points/vertices of one face can be joined by a new embedded polygonal arc whose
interior lies in that face.

This is the basic local insertion theorem.  It is deliberately much weaker geometrically than
`Drawing.union` and is all the general Kuratowski reduction should need. -/
theorem exists_arc_in_face_between_boundary_vertices : True := by
  sorry

/-- PUBLIC-SPECIALIZED.
Add one new edge inside a face. -/
theorem planar_add_edge_of_common_face : True := by
  sorry

/-- PRIVATE-BRIDGE.
Given a facial cycle C and two complementary boundary paths P₁,P₂, construct disjoint small
neighborhood wedges in which the contracted vertex can be split into u and v. -/
private theorem exists_split_vertex_neighborhoods : True := by
  sorry

/-- PRIVATE-BRIDGE.  Route all u-neighbor edges through the P₁ wedge. -/
private theorem reroute_u_edges_after_split : True := by sorry

/-- PRIVATE-BRIDGE.  Route all v-neighbor edges through the P₂ wedge. -/
private theorem reroute_v_edges_after_split : True := by sorry

/-- PRIVATE-BRIDGE.  Insert the edge uv between the two new points. -/
private theorem insert_split_edge : True := by sorry

/-- PRIVATE-BRIDGE.  Verify pairwise support/interior disjointness after the local surgery. -/
private theorem split_vertex_drawing_axioms : True := by sorry

/-- PUBLIC-SPECIALIZED.
The geometric uncontraction theorem consumed by the 3-connected Kuratowski induction. -/
theorem planar_of_contract_of_facial_cycle_two_paths : True := by
  sorry

end PLDrawing

/-! ###########################################################################
    11. THE COMBINATORIAL K33/K5 DICHOTOMY AROUND A FACIAL CYCLE
    ########################################################################### -/

/-- PUBLIC-SPECIALIZED.
This is the existing `K33_K5_lemma` from WIP/Jun/Planarity/K33.lean.  Finish the current auxiliary
branches, but keep the final theorem at this clean level.

It is stronger than needed for the minor-free induction because the obstruction alternative gives
a topological minor. -/
theorem K33_K5_lemma
    {C : Graph α β} {u v : α}
    (hCG : C ≤ G) (hC : C.IsCycle)
    (hu : u ∉ V(C)) (hv : v ∉ V(C)) (huv : u ≠ v)
    (hadj : G.Adj u v)
    (hu2 : (N(G, u) ∩ V(C)).Nontrivial)
    (hv2 : (N(G, v) ∩ V(C)).Nontrivial) :
    (∃ P₁ P₂ : WList α β,
      C.IsPath P₁ ∧ C.IsPath P₂ ∧
      (∀ x ∈ P₁.vertex.tail.dropLast, ¬ G.Adj u x) ∧
      (∀ x ∈ P₂.vertex.tail.dropLast, ¬ G.Adj v x) ∧
      C.IsCyclicWalk (P₁ ++ P₂)) ∨
    (CompleteBipartiteGraph 3 3).IsTopologicalMinor G ∨
    (CompleteGraph 5).IsTopologicalMinor G := by
  sorry

/-! ###########################################################################
    12. 3-CONNECTED MINOR-FREE -> PLANAR
    ########################################################################### -/

/-- PUBLIC-GENERAL.
A suitable edge of a finite simple 3-connected graph can be contracted while preserving
3-connectivity, after whatever simplification of parallel edges the graph API regards as standard.
This likely already exists; expose the exact theorem needed by the induction. -/
theorem exists_contractible_edge_threeConnected
    [G.Finite] [G.Simple] (hG : G.ConnGE 3) (hcard : 4 < V(G).ncard) :
    ∃ e : E(G), True := by
  sorry

/-- PRIVATE-BRIDGE.
The contracted/simplified graph has strictly fewer vertices or edges, whichever measure the chosen
strong induction uses. -/
private theorem contract_measure_lt : True := by sorry

/-- PUBLIC-GENERAL.
`WagnerFree` is preserved by deletion and contraction.  This should be a one-line minor-transitivity
corollary, not a special Kuratowski lemma. -/
theorem WagnerFree.minor {K : Graph α β} (hG : G.WagnerFree) (hKG : K.IsMinor G) :
    K.WagnerFree := by
  sorry

/-- PRIVATE-BRIDGE.
Base cases: finite simple 3-connected graphs with at most four vertices are planar. -/
private theorem threeConnected_small_planar : True := by
  sorry

/-- PRIVATE-BRIDGE.
After applying IH to G/e, choose a PL drawing rather than an arbitrary drawing. -/
private theorem contract_has_PLDrawing_of_IH : True := by
  sorry

/-- PRIVATE-BRIDGE.
Use `exists_facial_cycle_of_contract` to obtain C around the contracted vertex and prove the two
original endpoint neighbor sets meet C nontrivially in the way required by `K33_K5_lemma`. -/
private theorem contract_facial_cycle_neighbor_data : True := by
  sorry

/-- PRIVATE-BRIDGE.
If the K33_K5 dichotomy returns an obstruction, contradict `WagnerFree` through
`topologicalMinor -> minor`. -/
private theorem contract_dichotomy_obstruction_impossible : True := by
  sorry

/-- PRIVATE-BRIDGE.
If it returns the two clean boundary paths, feed them directly into the uncontraction theorem. -/
private theorem contract_dichotomy_clean_paths_planar : True := by
  sorry

/-- PUBLIC-GENERAL.
The hard 3-connected theorem.  Note that the logically natural hypothesis here is ordinary
minor-freeness, because that is what survives contraction. -/
theorem WagnerFree.planar_of_connGE_three
    [G.Finite] [G.Simple] (hW : G.WagnerFree) (h3 : G.ConnGE 3) : G.Planar := by
  sorry

/-- PUBLIC-GENERAL.
Topological-minor-free specialization, obtained through the K/W equivalence. -/
theorem KuratowskiFree.planar_of_connGE_three
    [G.Finite] [G.Simple] (hK : G.KuratowskiFree) (h3 : G.ConnGE 3) : G.Planar :=
  hK.wagnerFree.planar_of_connGE_three h3

/-! ###########################################################################
    13. GENERAL KURATOWSKI REDUCTION WITHOUT DRAWING UNION
    ###########################################################################

The intended route is Diestel 4.4.4--4.4.5: extend to an edge-maximal topological-obstruction-free
simple graph and prove that such a graph is 3-connected.  Do not revive general two-drawing gluing.

Use the `Transfer` architecture to carry out all fresh-label constructions on canonical infinite
carriers.
-/

/-- PUBLIC-GENERAL CANDIDATE.
A graph property P is edge-maximal on the fixed active vertex set.  The exact definition should be
factored out if useful for other extremal arguments. -/
def EdgeMaximalOnVertexSet
    (P : ∀ {α β}, Graph α β → Prop) (G : Graph α β) : Prop :=
  P G ∧ ∀ H, G < H → V(H) = V(G) → H.Simple → ¬ P H

/-- PRIVATE-BRIDGE.
On canonical infinite carriers, every finite simple Kuratowski-free graph has an edge-maximal
Kuratowski-free simple supergraph with the same active vertex set. -/
private theorem exists_edgeMaximal_kuratowskiFree_extension_natCarrier : True := by
  sorry

/-- PUBLIC-GENERAL.
Transferred representation-independent existence theorem.  If the witness graph itself must be
transported, use `IsoAction.nonempty_of_forall_finite_natCarrier`, not merely invariant Prop
transfer. -/
theorem exists_edgeMaximal_kuratowskiFree_extension
    [G.Finite] [G.Simple] (hG : G.KuratowskiFree) :
    ∃ H, G ≤ H ∧ V(H) = V(G) ∧ H.KuratowskiFree ∧
      EdgeMaximalOnVertexSet KuratowskiFree H := by
  sorry

/-! ---------------------------------------------------------------------------
    13A. Diestel 4.4.4: low-order separations of edge-maximal graphs
    --------------------------------------------------------------------------- -/

/-- PUBLIC-GENERAL CANDIDATE.
A topological model of a 3-connected pattern cannot have branch vertices genuinely on both sides
of a separation of order at most two.  All branch vertices lie on one side; the model meets the
other side in at most a segment of one routed edge.

State this for an arbitrary 3-connected pattern X, not just K5/K33.  This is a reusable topological
minor theorem. -/
theorem TopologicalModel.branchVertices_one_side_of_separation
    {X : Graph γ δ} (hX : X.ConnGE 3)
    (M : X.TopologicalModel G)
    -- separation data A,B, order <= 2
    : True := by
  sorry

/-- PRIVATE-BRIDGE.
Every separator vertex in a minimum separation has a neighbor in every relevant side component. -/
private theorem minimum_separator_vertex_has_neighbors_both_sides : True := by
  sorry

/-- PRIVATE-BRIDGE.
Separation of order 0 contradicts edge maximality by adding a cross-edge and localizing the newly
created topological obstruction. -/
private theorem edgeMaximal_kfree_no_order_zero_separation : True := by
  sorry

/-- PRIVATE-BRIDGE.
Separation of order 1 contradicts edge maximality by adding an edge between neighbors on opposite
sides and rerouting the unique excursion of the obstruction. -/
private theorem edgeMaximal_kfree_no_order_one_separation : True := by
  sorry

/-- PRIVATE-BRIDGE.
For a separation of order 2 with separator {x,y}, maximality forces xy to be an edge.  Otherwise add
xy and replace it in the resulting obstruction by an x-y path through the opposite side. -/
private theorem edgeMaximal_kfree_order_two_separator_is_edge : True := by
  sorry

/-- PRIVATE-BRIDGE.
Each induced side of the order-2 separation is itself edge-maximal Kuratowski-free. -/
private theorem edgeMaximal_kfree_separation_sides_maximal : True := by
  sorry

/-- PUBLIC-GENERAL CANDIDATE.
Diestel 4.4.4, stated for any family X of 3-connected forbidden topological minors if the API makes
that abstraction natural.  A K5/K33 specialization can then be tiny. -/
theorem edgeMaximal_kfree_low_separation_structure : True := by
  sorry

/-! ---------------------------------------------------------------------------
    13B. Local planar facts used in Diestel 4.4.5
    --------------------------------------------------------------------------- -/

/-- PRIVATE-BRIDGE.
In each smaller side G_i sharing edge xy, choose a face incident with xy. -/
private theorem exists_face_incident_shared_edge : True := by
  sorry

/-- PRIVATE-BRIDGE.
Unless the side is exactly a triangle, the chosen face has a boundary vertex z distinct from x,y.
For a triangle choose its third vertex directly. -/
private theorem exists_third_boundary_vertex_on_shared_edge_face : True := by
  sorry

/-- PRIVATE-BRIDGE.
Adding xz or yz inside that face preserves planarity.  Reduce to
`PLDrawing.planar_add_edge_of_common_face`. -/
private theorem side_augmented_by_boundary_chord_planar : True := by
  sorry

/-- PRIVATE-BRIDGE.
If the new obstruction in G + z1z2 has all branch vertices on one side, reroute it into one of the
planar side augmentations, contradiction. -/
private theorem maximal_threeConn_branches_one_side_impossible : True := by
  sorry

/-- PRIVATE-BRIDGE.
G + z1z2 has too few independent cross-separation paths for a TK5 to have branch vertices on both
sides, or for a TK3,3 to have two branch vertices on each side. -/
private theorem maximal_threeConn_cross_side_branch_count : True := by
  sorry

/-- PRIVATE-BRIDGE.
The only remaining cross-side case is a TK3,3 with one branch vertex v on one side.  Reroute it into
the planar graph obtained by adjoining v with the three edges vx, vy, vz1 to the opposite side. -/
private theorem maximal_threeConn_last_K33_case_impossible : True := by
  sorry

/-- PUBLIC-GENERAL.
Diestel 4.4.5: a finite edge-maximal Kuratowski-free simple graph with at least four vertices is
3-connected.

The proof is induction on the active vertex count.  Smaller separation sides are either triangles
or 3-connected by IH; convert their Kuratowski-freeness to Wagner-freeness and invoke the already
proved 3-connected theorem to draw them. -/
theorem edgeMaximal_kuratowskiFree_connGE_three
    [G.Finite] [G.Simple]
    (hmax : EdgeMaximalOnVertexSet KuratowskiFree G)
    (hcard : 4 ≤ V(G).ncard) : G.ConnGE 3 := by
  sorry

/-! ---------------------------------------------------------------------------
    13C. Simple finite graphs
    --------------------------------------------------------------------------- -/

/-- PRIVATE-BRIDGE.  Graphs with fewer than four active vertices are planar. -/
private theorem finite_simple_small_planar : True := by
  sorry

/-- PUBLIC-GENERAL.
General hard direction for finite simple graphs. -/
theorem KuratowskiFree.planar_of_simple
    [G.Finite] [G.Simple] (hK : G.KuratowskiFree) : G.Planar := by
  by_cases hsmall : V(G).ncard < 4
  · exact by sorry
  obtain ⟨H, hGH, hV, hHK, hmax⟩ := exists_edgeMaximal_kuratowskiFree_extension hK
  have hH3 : H.ConnGE 3 := edgeMaximal_kuratowskiFree_connGE_three hmax (by omega)
  have hHp : H.Planar := hHK.planar_of_connGE_three hH3
  exact hHp.mono hGH

/-! ###########################################################################
    14. NORMALIZATION: LOOPS, PARALLEL EDGES, ISOLATED VERTICES
    ########################################################################### -/

The headline theorem should be for the natural finite `Graph`, not just simple graphs.  Therefore
normalization belongs in an explicit layer rather than being silently assumed everywhere.
-/

/-- PUBLIC-GENERAL.
A chosen simplification: delete loops and keep one representative from each parallel class.
The exact existing graph API may already provide this object under another name. -/
noncomputable def simplification (G : Graph α β) : Graph α β := by
  sorry

/-- PUBLIC-GENERAL. -/
theorem simplification_simple : G.simplification.Simple := by
  sorry

/-- PUBLIC-GENERAL.
K5/K33 topological-minor exclusion is unchanged by simplification.  Prove both directions if true;
do not settle for the one implication needed immediately. -/
theorem kuratowskiFree_simplification_iff :
    G.simplification.KuratowskiFree ↔ G.KuratowskiFree := by
  sorry

/-- PUBLIC-GENERAL.
Planarity descends to simplification. -/
theorem Planar.simplification (hG : G.Planar) : G.simplification.Planar := by
  sorry

/-- PUBLIC-GENERAL CANDIDATE.
Insert one extra edge parallel to an already drawn edge inside a thin tube. -/
theorem planar_add_parallel_edge : True := by
  sorry

/-- PUBLIC-GENERAL CANDIDATE.
Insert one loop in a sufficiently small local sector at a vertex. -/
theorem planar_add_loop : True := by
  sorry

/-- PUBLIC-GENERAL.
If the simplification is planar, restore all finitely many deleted parallel edges and loops. -/
theorem planar_of_simplification_planar [G.Finite]
    (h : G.simplification.Planar) : G.Planar := by
  sorry

/-- PUBLIC-GENERAL.
General finite hard direction. -/
theorem KuratowskiFree.planar [G.Finite] (hK : G.KuratowskiFree) : G.Planar := by
  have hsK : G.simplification.KuratowskiFree := kuratowskiFree_simplification_iff.mpr hK
  have hsP : G.simplification.Planar := hsK.planar_of_simple
  exact planar_of_simplification_planar hsP

/-! ###########################################################################
    15. OPTIONAL DIRECT DRAWING-MINOR THEOREMS
    ###########################################################################

These are useful API results but no longer prerequisites for the headline equivalence, because
`Planar -> HasAbstractDual -> WagnerFree -> KuratowskiFree` already proves the easy obstruction
direction.  Keep them out of the critical dependency chain.
-/

/-- PUBLIC-GENERAL.
Planarity descends to ordinary graph minors. -/
theorem Planar.minor {K : Graph γ δ} (hG : G.Planar) (hKG : K.IsMinor G) : K.Planar := by
  sorry

/-- PUBLIC-GENERAL.
Planarity descends to topological minors. -/
theorem Planar.topologicalMinor {K : Graph γ δ}
    (hG : G.Planar) (hKG : K.IsTopologicalMinor G) : K.Planar := by
  exact hG.minor hKG.isMinor

/-! ###########################################################################
    16. FINAL THEOREMS
    ########################################################################### -/

/-- PUBLIC-GENERAL.
The requested three-way theorem.  Exact `List.TFAE` syntax can be replaced by named iff theorems if
that is more ergonomic for Mathlib. -/
theorem finite_kuratowski_abstractDual_tfae [G.Finite] :
    List.TFAE [G.HasAbstractDual, G.KuratowskiFree, G.Planar] := by
  tfae_have 1 -> 2 := fun h => h.wagnerFree.kuratowskiFree
  tfae_have 2 -> 3 := fun h => h.planar
  tfae_have 3 -> 1 := fun h => h.hasAbstractDual
  tfae_finish

/-- PUBLIC-GENERAL.
Four-way strengthening including ordinary minors.  This is probably the most useful theorem for
internal mathematics even if the project headline remains the three-way statement. -/
theorem finite_planar_duality_wagner_kuratowski_tfae [G.Finite] :
    List.TFAE [G.HasAbstractDual, G.WagnerFree, G.KuratowskiFree, G.Planar] := by
  tfae_have 1 -> 2 := HasAbstractDual.wagnerFree
  tfae_have 2 -> 3 := WagnerFree.kuratowskiFree
  tfae_have 3 -> 2 := KuratowskiFree.wagnerFree
  tfae_have 3 -> 4 := KuratowskiFree.planar
  tfae_have 4 -> 1 := Planar.hasAbstractDual
  tfae_finish

/-- PUBLIC-GENERAL. -/
theorem hasAbstractDual_iff_planar [G.Finite] : G.HasAbstractDual ↔ G.Planar := by
  sorry

/-- PUBLIC-GENERAL. -/
theorem kuratowskiFree_iff_planar [G.Finite] : G.KuratowskiFree ↔ G.Planar := by
  sorry

/-- PUBLIC-GENERAL. -/
theorem wagnerFree_iff_planar [G.Finite] : G.WagnerFree ↔ G.Planar := by
  sorry

/-! ###########################################################################
    17. GENERALITY / API AUDIT AFTER THE FIRST COMPLETE PROOF
    ###########################################################################

Do not regard the first completion of Section 16 as the end of the project.  Before upstreaming,
audit every declaration against the following list.

A. Remove accidental finiteness
------------------------------

* Abstract dual symmetry, minor closure, bridge/loop correspondence: no finiteness.
* Topological-minor-to-minor: seek arbitrary pattern/host if minor API permits.
* Cycle/bond direction for a single finite cycle may not need global graph finiteness; inspect where
  finiteness is genuinely used (closed support, local isolation of edges, dual-region theorem).
* `exists_local_star_two` is dimension-free and should remain so.

B. Remove accidental connectivity
----------------------------------

* Abstract duality and the final Euler rank identity should naturally account for component counts.
* Geometric dual is connected even when primal is disconnected; do not assume primal connectedness.
* Face-cycle theorem genuinely needs a 2-connected hypothesis for a single cycle boundary.

C. Separate representation choices
----------------------------------

* Edge equality is a specialization; primary abstract duality uses `Matroid.Iso`.
* Fresh carrier labels are solved through `Relabel`/`Transfer`.
* Geometric dual can reuse primal edge labels because it is a canonical construction from one
  drawing; this is a feature, not a restriction on abstract duality.

D. Promote graph-free topology
------------------------------

Candidates to move to `ForMathlib`/geometry/topology:

* connected-component frontier lemmas;
* simple polygonal arc local two-star theorem;
* theta exact three-region theorem;
* crosscut theorem;
* finite embedded forest complement connectedness, if it can be stated without graph-specific
  drawing structure;
* region adjacency theorem, if it can be phrased for finite 1-complex decompositions.

E. Keep proof-route scaffolding private
---------------------------------------

Likely private forever:

* candidate theta region choices;
* common radii selected only for one proof;
* particular maximal-extension construction on Nat carriers;
* rerouting subcases inside Diestel 4.4.4/4.4.5;
* local split-vertex neighborhood choices.

F. Do not stop at the first existential result
----------------------------------------------

Where a proof naturally gives stronger structure, expose it:

* exact component/frontier equalities rather than merely existence of faces;
* literal `cycleMatroid_geometricDual` equality rather than only `HasAbstractDual`;
* generalized Euler with component counts rather than only V-E+F=2;
* full `KuratowskiFree <-> WagnerFree`, not merely the one implication needed by induction;
* deletion/contraction duality, not merely minor closure.

-/

end Graph
