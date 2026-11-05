/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Matroid.GraphTheory.Graph.Basic
public import Matroid.GraphTheory.Pseudograph.Basic

/-!
# Bridge between pseudographs and graphs

This file provides a bridge between pseudographs and graphs.

To be precise, it shows that `Graph` is quotient of `Pseudograph` by incidence relabelling.
-/

@[expose] public section

open Set HypergraphLike

namespace Pseudograph

variable {V I J E : Type*} {G : Pseudograph V I E}

/-- Forget the names of incidences and retain only the ordinary undirected graph. -/
@[simps]
def toGraph (G : Pseudograph V I E) : Graph V E where
  vertexSet := V(G)
  IsLink := IsLink G
  edgeSet := E(G)
  isLink_symm := fun _ _ ↦ ⟨fun _ _ h ↦ h.symm⟩
  eq_or_eq_of_isLink_of_isLink := fun _ _ _ _ _ h h' ↦ h.left_eq_or_eq h'
  edge_mem_iff_exists_isLink _ := mem_edges_iff_exists_isLink
  left_mem_of_isLink _ _ _ hxy := IsLink.left_mem_vertexSet hxy

def incidenceRelabeling (G : Pseudograph V I E) (f : J → I) : Pseudograph V J E where
  vertexSet := V(G)
  incidenceSet := f ⁻¹' I(G)
  edgeSet := E(G)
  edgeMap' i := edgeMap' (f i)
  attach' := fun i ↦ f i
  other' := fun i ↦ f (other G i)
  other'_ne := fun i ↦ f.injective.ne (other_ne i)
  edgeMap'_other' := fun i ↦ f.injective.ne (edgeMap_other i)
  edgeMap'_eq := fun i j hij ↦ f.injective.ne (edgeMap_eq_iff i j hij)
  edgeMap_range := by
    simp [edgeMap_range]
