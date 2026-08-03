/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Data.PFun

@[expose] public section

variable {V I E : Type*} {x y z u v w : V} {a b c d : I} {e f : E}

open Set Sym2 PFun

/-- A multigraph with vertices of type `α` and darts of type `β`.

Edges are non-diagonal unordered pairs of darts (`edgeSet : Set (Sym2 β)`), required to be
pairwise dart-disjoint. Incidence is recorded by `attach`, which sends each half-edge appearing
in some edge to a vertex of `G`. -/
structure Graph (V I E : Type*) where
  /-- The vertex set. -/
  vertexSet : Set V
  /-- Attach each half-edge to its incident vertex. -/
  attach : I →. V
  attach_mem : PFun.ran attach ⊆ vertexSet
  /-- Edge linking map-/
  edgeMap : I →. E
  edgeMap_order_two : ∀ e : E, e ∈ edgeMap.ran → Set.encard (edgeMap.preimage {e}) = 2
  attach_dom_eq_edgeMap_dom : attach.Dom = edgeMap.Dom

