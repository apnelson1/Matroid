/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Matroid.Graph.Walk.Iso
-- public import Mathlib.Combinatorics.Graph.Simple

/-!
# `irw` registrations for Mathlib graph declarations

Project-owned graph isomorphisms, walk transport, and their naturality laws are registered beside
their definitions. This adapter contains the remaining rules for graph predicates owned by
Mathlib.
-/

@[expose] public section

open Set

namespace Graph

universe uV uE uV' uE'

variable {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
  {G : Graph V E} {H : Graph V' E'}

/-! ## Atomic graph relations -/

-- Naturality facts use the same canonical equivalences registered above.  Thus the binder
-- transport and the public graph API share one expression, allowing cleanup to recognize the
-- usual `e (e.symm y)` cancellation.

/-! ## Primitive and derived local graph relations -/

/-- Unary edge/vertex incidence. -/
theorem Iso.irw_inc (i : Iso G H) (e : E(G)) (x : V(G)) :
    G.Inc e.1 x.1 ↔ H.Inc (i.edgeEquiv e).1 (i.vertexEquiv x).1 := by
  constructor
  · rintro ⟨y, hxy⟩
    let yG : V(G) := ⟨y, hxy.right_mem⟩
    refine ⟨(i.vertexEquiv yG).1, ?_⟩
    exact (i.isLink_edgeEquiv_vertexEquiv e x yG).mp hxy
  · rintro ⟨y, hxy⟩
    let eH : E(H) := i.edgeEquiv e
    let xH : V(H) := i.vertexEquiv x
    let yH : V(H) := ⟨y, hxy.right_mem⟩
    have hG := (i.symm.isLink_edgeEquiv_vertexEquiv eH xH yH).mp hxy
    refine ⟨(i.symm.vertexEquiv yH).1, ?_⟩
    simpa [eH, xH, yH] using hG

/-- A loop at a specified vertex. -/
theorem Iso.irw_isLoopAt (i : Iso G H) (e : E(G)) (x : V(G)) :
    G.IsLoopAt e.1 x.1 ↔
      H.IsLoopAt (i.edgeEquiv e).1 (i.vertexEquiv x).1 := by
  simpa only [IsLoopAt] using i.isLink_edgeEquiv_vertexEquiv e x x

/-- A non-loop edge incident with a specified vertex. -/
theorem Iso.irw_isNonloopAt (i : Iso G H) (e : E(G)) (x : V(G)) :
    G.IsNonloopAt e.1 x.1 ↔
      H.IsNonloopAt (i.edgeEquiv e).1 (i.vertexEquiv x).1 := by
  rw [isNonloopAt_iff_inc_not_isLoopAt, isNonloopAt_iff_inc_not_isLoopAt,
    i.irw_inc e x, i.irw_isLoopAt e x]

/-! ## Named graph-dependent sets, used propositionally through membership -/

/-- Membership in the incidence set transports with both the edge and vertex. -/
theorem Iso.irw_mem_incidenceSet (i : Iso G H) (e : E(G)) (x : V(G)) :
    e.1 ∈ G.incidenceSet x.1 ↔
      (i.edgeEquiv e).1 ∈ H.incidenceSet (i.vertexEquiv x).1 := by
  simpa only [mem_incidenceSet] using i.irw_inc e x

/-- Membership in the loop set transports with both the edge and vertex. -/
theorem Iso.irw_mem_loopSet (i : Iso G H) (e : E(G)) (x : V(G)) :
    e.1 ∈ G.loopSet x.1 ↔
      (i.edgeEquiv e).1 ∈ H.loopSet (i.vertexEquiv x).1 := by
  simpa only [mem_loopSet] using i.irw_isLoopAt e x

/-! ## Whole-graph properties -/

/-- Nonemptiness of the active vertex set. -/
theorem Iso.irw_vertexSet_nonempty (i : Iso G H) : V(G).Nonempty ↔ V(H).Nonempty := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨(i.vertexEquiv ⟨x, hx⟩).1, (i.vertexEquiv ⟨x, hx⟩).2⟩
  · rintro ⟨y, hy⟩
    exact ⟨((i.vertexEquiv).symm ⟨y, hy⟩).1,
      ((i.vertexEquiv).symm ⟨y, hy⟩).2⟩

/-- Nonemptiness of the active edge set. -/
theorem Iso.irw_edgeSet_nonempty (i : Iso G H) : E(G).Nonempty ↔ E(H).Nonempty := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨(i.edgeEquiv ⟨e, he⟩).1, (i.edgeEquiv ⟨e, he⟩).2⟩
  · rintro ⟨f, hf⟩
    exact ⟨((i.edgeEquiv).symm ⟨f, hf⟩).1,
      ((i.edgeEquiv).symm ⟨f, hf⟩).2⟩

/-- Finiteness of the active vertex set. -/
theorem Iso.irw_vertexSet_finite (i : Iso G H) : V(G).Finite ↔ V(H).Finite := by
  constructor
  · intro h
    have := h.to_subtype
    exact Set.finite_coe_iff.mp (Finite.of_equiv _ i.vertexEquiv)
  · intro h
    have := h.to_subtype
    exact Set.finite_coe_iff.mp (Finite.of_equiv _ (i.vertexEquiv).symm)

/-- Finiteness of the active edge set. -/
theorem Iso.irw_edgeSet_finite (i : Iso G H) : E(G).Finite ↔ E(H).Finite := by
  constructor
  · intro h
    have := h.to_subtype
    exact Set.finite_coe_iff.mp (Finite.of_equiv _ i.edgeEquiv)
  · intro h
    have := h.to_subtype
    exact Set.finite_coe_iff.mp (Finite.of_equiv _ (i.edgeEquiv).symm)

/-- Looplessness is invariant under graph isomorphism. -/
theorem Iso.irw_loopless (i : Iso G H) : G.Loopless ↔ H.Loopless := by
  constructor
  · intro hG
    refine ⟨?_⟩
    intro e x hloop
    let eH : E(H) := ⟨e, hloop.edge_mem⟩
    let xH : V(H) := ⟨x, hloop.vertex_mem⟩
    have hloopG := (i.symm.irw_isLoopAt eH xH).mp hloop
    exact hG.not_isLoopAt _ _ hloopG
  · intro hH
    refine ⟨?_⟩
    intro e x hloop
    let eG : E(G) := ⟨e, hloop.edge_mem⟩
    let xG : V(G) := ⟨x, hloop.vertex_mem⟩
    have hloopH := (i.irw_isLoopAt eG xG).mp hloop
    exact hH.not_isLoopAt _ _ hloopH

/-- Simplicity (loopless and no parallel edges with the same ends) is invariant under graph
isomorphism. -/
theorem Iso.irw_simple (i : Iso G H) : G.Simple ↔ H.Simple := by
  constructor
  · intro hG
    refine { toLoopless := (i.irw_loopless).mp hG.toLoopless, eq_of_isLink := ?_ }
    intro e f x y he hf
    let eH : E(H) := ⟨e, he.edge_mem⟩
    let fH : E(H) := ⟨f, hf.edge_mem⟩
    let xH : V(H) := ⟨x, he.left_mem⟩
    let yH : V(H) := ⟨y, he.right_mem⟩
    have heG := (i.symm.isLink_edgeEquiv_vertexEquiv eH xH yH).mp he
    have hfG := (i.symm.isLink_edgeEquiv_vertexEquiv fH xH yH).mp hf
    have hval : (i.symm.edgeEquiv eH).1 = (i.symm.edgeEquiv fH).1 :=
      hG.eq_of_isLink heG hfG
    have hsub : i.symm.edgeEquiv eH = i.symm.edgeEquiv fH := Subtype.ext hval
    have hef : eH = fH := (i.symm.edgeEquiv).injective hsub
    exact congrArg Subtype.val hef
  · intro hH
    refine { toLoopless := (i.irw_loopless).mpr hH.toLoopless, eq_of_isLink := ?_ }
    intro e f x y he hf
    let eG : E(G) := ⟨e, he.edge_mem⟩
    let fG : E(G) := ⟨f, hf.edge_mem⟩
    let xG : V(G) := ⟨x, he.left_mem⟩
    let yG : V(G) := ⟨y, he.right_mem⟩
    have heH := (i.isLink_edgeEquiv_vertexEquiv eG xG yG).mp he
    have hfH := (i.isLink_edgeEquiv_vertexEquiv fG xG yG).mp hf
    have hval : (i.edgeEquiv eG).1 = (i.edgeEquiv fG).1 :=
      hH.eq_of_isLink heH hfH
    have hsub : i.edgeEquiv eG = i.edgeEquiv fG := Subtype.ext hval
    have hef : eG = fG := i.edgeEquiv.injective hsub
    exact congrArg Subtype.val hef




attribute [irw_naturality]
  Iso.isLink_edgeEquiv_vertexEquiv
  Iso.adj_vertexEquiv
  Iso.irw_mem_loopSet
  Iso.irw_mem_incidenceSet
  Iso.irw_isLoopAt
  Iso.irw_isNonloopAt
  Iso.irw_inc
  Iso.irw_loopless
  Iso.irw_simple
  Iso.irw_vertexSet_nonempty
  Iso.irw_edgeSet_nonempty
  Iso.irw_vertexSet_finite
  Iso.irw_edgeSet_finite



end Graph
