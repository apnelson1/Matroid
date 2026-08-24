/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Matroid.Graph.Hom

/-!
# Canonical transport under graph isomorphism

Project-owned IRw domains and equivalences for Mathlib's ambient graph carriers.
-/

@[expose] public section

open Set

namespace Graph

universe uV uE uV' uE'

variable {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
  {G : Graph V E} {H : Graph V' E'}

/-! ## Binder equivalences -/

/-- Primitive supported action on ambient graph vertices. -/
@[irw_domain]
def Iso.vertexDomain (i : Iso G H) : IRw.SupportedDomain V V' where
  sourceSupport x := x ∈ V(G)
  targetSupport y := y ∈ V(H)
  equiv := i.vertexEquiv

/-- Primitive supported action on ambient graph edges. -/
@[irw_domain]
def Iso.edgeDomain (i : Iso G H) : IRw.SupportedDomain E E' where
  sourceSupport e := e ∈ E(G)
  targetSupport f := f ∈ E(H)
  equiv := i.edgeEquiv

@[irw_equiv]
def Iso.supportedVertexSetEquiv (i : Iso G H) :
    {X : Set V // X ⊆ V(G)} ≃ {Y : Set V' // Y ⊆ V(H)} :=
  i.vertexDomain.set.equiv

@[irw_equiv]
def Iso.supportedEdgeSetEquiv (i : Iso G H) :
    {X : Set E // X ⊆ E(G)} ≃ {Y : Set E' // Y ⊆ E(H)} :=
  i.edgeDomain.set.equiv


end Graph
