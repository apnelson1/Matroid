/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Matroid.Graph.Iso.Invariant
public import Matroid.Graph.Iso.Relabel

/-!
# Transferring results between carriers

The two-class API makes carrier transfer split cleanly:

* `IsoAction` moves graph-dependent data/witnesses;
* `IsoInvariant` says an observable is unchanged after that move.

There is no separate homogeneous/cross-universe or proposition/data-valued hierarchy here.
-/

@[expose] public section

open Set Function

namespace Graph

universe uV uE uV' uE' uO uO'

variable {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'} {G : Graph V E}

/-! ### Finiteness and carrier copies -/

theorem Iso.vertexSet_finite {H : Graph V' E'} (i : Iso G H) (h : V(G).Finite) : V(H).Finite :=
  have := h.to_subtype
  Set.finite_coe_iff.mp (Finite.of_equiv _ i.vertexEquiv)

theorem Iso.edgeSet_finite {H : Graph V' E'} (i : Iso G H) (h : E(G).Finite) : E(H).Finite :=
  have := h.to_subtype
  Set.finite_coe_iff.mp (Finite.of_equiv _ i.edgeEquiv)

theorem FitsOn.of_finite [Infinite V'] [Infinite E'] (hV : V(G).Finite) (hE : E(G).Finite) :
    G.FitsOn V' E' := by
  have := hV.to_subtype
  have := hE.to_subtype
  obtain ⟨f, hf⟩ := exists_injective_nat V(G)
  obtain ⟨g, hg⟩ := exists_injective_nat E(G)
  exact ⟨⟨(⟨f, hf⟩ : V(G) ↪ ℕ).trans (Infinite.natEmbedding V')⟩,
    ⟨(⟨g, hg⟩ : E(G) ↪ ℕ).trans (Infinite.natEmbedding E')⟩⟩

theorem FitsOn.of_finite_nat (hV : V(G).Finite) (hE : E(G).Finite) : G.FitsOn ℕ ℕ :=
  FitsOn.of_finite hV hE

theorem FitsOn.fin {n k : ℕ} (hV : V(G).ncard ≤ n) (hE : E(G).ncard ≤ k)
    (hVfin : V(G).Finite) (hEfin : E(G).Finite) : G.FitsOn (Fin n) (Fin k) := by
  have := hVfin.fintype
  have := hEfin.fintype
  refine ⟨Function.Embedding.nonempty_of_card_le ?_, Function.Embedding.nonempty_of_card_le ?_⟩ <;>
    simpa [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, Nat.card_fin]

/-! ### Witness/data transfer -/

namespace IsoAction

/-- If every graph on the target carriers has a witness in `F'`, then every source graph that fits
there has a witness in `F`. -/
theorem nonempty_of_forall_on
    {F : Family.{uV, uE, uO}} {F' : Family.{uV', uE', uO'}} [IsoAction F F']
    (h : ∀ H : Graph V' E', Nonempty (F' H)) (hfit : G.FitsOn V' E') : Nonempty (F G) :=
  ⟨(IsoAction.map (F := F) hfit.copyOn.iso).symm (h _).some⟩

/-- Finite-graph specialization to `Graph ℕ ℕ`. -/
theorem nonempty_of_forall_finite_nat
    {F : Family.{uV, uE, uO}}
    {F₀ : {V : Type} → {E : Type} → Graph V E → Sort uO'} [IsoAction F F₀]
    (h : ∀ H : Graph ℕ ℕ, V(H).Finite → E(H).Finite → Nonempty (F₀ H))
    (hV : V(G).Finite) (hE : E(G).Finite) : Nonempty (F G) :=
  let i := (FitsOn.of_finite_nat hV hE).copyOn.iso
  ⟨(IsoAction.map (F := F) i).symm (h _ (i.vertexSet_finite hV) (i.edgeSet_finite hE)).some⟩

end IsoAction

/-! ### Fixed-codomain observable transfer -/

namespace IsoInvariant

/-- A fixed-codomain invariant established on every target-carrier graph transfers back to `G`. -/
theorem eq_of_forall_on
    {R : Sort uO}
    {f : {V : Type uV} → {E : Type uE} → Graph V E → R}
    {f' : {V : Type uV'} → {E : Type uE'} → Graph V E → R}
    [IsoInvariant f f'] {r : R}
    (h : ∀ H : Graph V' E', f' H = r) (hfit : G.FitsOn V' E') : f G = r :=
  (IsoInvariant.eq_of_iso (f := f) (f' := f') hfit.copyOn.iso).trans (h _)

/-- Predicate on a fixed-codomain invariant value. -/
theorem holds_of_forall_on
    {R : Sort uO}
    {f : {V : Type uV} → {E : Type uE} → Graph V E → R}
    {f' : {V : Type uV'} → {E : Type uE'} → Graph V E → R}
    [IsoInvariant f f'] (Q : R → Prop)
    (h : ∀ H : Graph V' E', Q (f' H)) (hfit : G.FitsOn V' E') : Q (f G) := by
  rw [IsoInvariant.eq_of_iso (f := f) (f' := f') hfit.copyOn.iso]
  exact h _

/-- A property proved for every graph on target carriers holds for any source graph fitting there. -/
theorem of_forall_on
    {P : Property.{uV, uE}} {P' : Property.{uV', uE'}} [IsoInvariant P P']
    (h : ∀ H : Graph V' E', P' H) (hfit : G.FitsOn V' E') : P G :=
  IsoInvariant.comap hfit.copyOn.iso (h _)

/-- To prove an invariant property for every finite graph, it is enough to prove its `Type 0`
incarnation on finite `Graph ℕ ℕ`. -/
theorem of_forall_finite_nat
    {P : Property.{uV, uE}}
    {P₀ : {V : Type} → {E : Type} → Graph V E → Prop} [IsoInvariant P P₀]
    (h : ∀ H : Graph ℕ ℕ, V(H).Finite → E(H).Finite → P₀ H)
    (hV : V(G).Finite) (hE : E(G).Finite) : P G :=
  let i := (FitsOn.of_finite_nat hV hE).copyOn.iso
  IsoInvariant.comap i (h _ (i.vertexSet_finite hV) (i.edgeSet_finite hE))

/-- Bounded finite carriers, cross-universe. -/
theorem of_forall_fin {n k : ℕ}
    {P : Property.{uV, uE}}
    {P₀ : {V : Type} → {E : Type} → Graph V E → Prop} [IsoInvariant P P₀]
    (h : ∀ H : Graph (Fin n) (Fin k), P₀ H)
    (hV : V(G).ncard ≤ n) (hE : E(G).ncard ≤ k)
    (hVfin : V(G).Finite) (hEfin : E(G).Finite) : P G :=
  of_forall_on h (FitsOn.fin hV hE hVfin hEfin)

/-- Naturality square for a canonical copy. -/
theorem map_eq_copyOn
    {F : Family.{uV, uE, uO}} {F' : Family.{uV', uE', uO'}} [IsoAction F F']
    {f : Observable F} {f' : Observable F'} [IsoInvariant f f']
    (hfit : G.FitsOn V' E') :
    IsoAction.map (F := F) hfit.copyOn.iso (f G) = f' hfit.copyOn.graph :=
  IsoInvariant.map_eq _

/-! ### Relabel-first proof interfaces -/

/-- Register a fixed-codomain invariant by checking canonical relabelled copies. -/
theorem of_relabel_eq
    {R : Sort uO}
    {f : {V : Type uV} → {E : Type uE} → Graph V E → R}
    {f' : {V : Type uV'} → {E : Type uE'} → Graph V E → R}
    (h : ∀ {V : Type uV} {E : Type uE} {G : Graph V E}
      {V' : Type uV'} {E' : Type uE'}
      (fv : V(G) ↪ V') (fe : E(G) ↪ E'), f G = f' (G.relabel fv fe)) :
    IsoInvariant f f' :=
  IsoInvariant.of_eq fun i ↦ by
    rw [h i.vertexEmbeddingInto i.edgeEmbeddingInto, i.relabel_eq]

/-- Proposition-valued relabel-first constructor. -/
theorem of_relabel_iff
    {P : Property.{uV, uE}} {P' : Property.{uV', uE'}}
    (h : ∀ {V : Type uV} {E : Type uE} {G : Graph V E}
      {V' : Type uV'} {E' : Type uE'}
      (fv : V(G) ↪ V') (fe : E(G) ↪ E'), P G ↔ P' (G.relabel fv fe)) :
    IsoInvariant P P' :=
  IsoInvariant.of_iff fun i ↦ by
    rw [h i.vertexEmbeddingInto i.edgeEmbeddingInto, i.relabel_eq]

end IsoInvariant

end Graph
