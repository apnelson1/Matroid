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

`FitsOn` produces an isomorphic copy of a graph on chosen ambient carriers.  There are now two
levels of transfer:

* `Invariant` / `IsoAction` transfer inside one carrier-universe pair;
* `IsoTransport` transfer across unrelated carrier universes.

The second point removes the old reason for a universe-indexed `NatCarrier`: a finite graph whose
carriers live in arbitrary universes can be copied to `Graph ℕ ℕ`, and a cross-universe
`IsoTransport` moves the property or witness back.  Thus `Graph ℕ ℕ` really is the canonical
finite proving ground whenever the object being transferred has an `IsoTransport` instance.
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

/-- Every finite graph fits on `ℕ, ℕ`, regardless of the universes of its original carriers. -/
theorem FitsOn.of_finite_nat (hV : V(G).Finite) (hE : E(G).Finite) : G.FitsOn ℕ ℕ :=
  FitsOn.of_finite hV hE

theorem FitsOn.fin {n k : ℕ} (hV : V(G).ncard ≤ n) (hE : E(G).ncard ≤ k)
    (hVfin : V(G).Finite) (hEfin : E(G).Finite) : G.FitsOn (Fin n) (Fin k) := by
  have := hVfin.fintype
  have := hEfin.fintype
  refine ⟨Function.Embedding.nonempty_of_card_le ?_, Function.Embedding.nonempty_of_card_le ?_⟩ <;>
    simpa [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, Nat.card_fin]

/-! ### Same-universe transfer -/

namespace Invariant

variable {V₁ V₂ : Type uV} {E₁ E₂ : Type uE} {G : Graph V₁ E₁}
  {R : Sort uO} {f : {V : Type uV} → {E : Type uE} → Graph V E → R}

/-- A fixed-codomain invariant takes on `G` whatever value it takes on every graph on carriers
that `G` fits on. -/
theorem eq_of_forall_on [Invariant f] {r : R} (h : ∀ H : Graph V₂ E₂, f H = r)
    (hfit : G.FitsOn V₂ E₂) : f G = r :=
  (Invariant.eq_of_iso (f := f) hfit.copyOn.iso).trans (h _)

/-- Predicate-valued version of `eq_of_forall_on`. -/
theorem holds_of_forall_on [Invariant f] (Q : R → Prop) (h : ∀ H : Graph V₂ E₂, Q (f H))
    (hfit : G.FitsOn V₂ E₂) : Q (f G) := by
  rw [Invariant.eq_of_iso (f := f) hfit.copyOn.iso]
  exact h _

end Invariant

namespace IsoAction

variable {V₁ V₂ : Type uV} {E₁ E₂ : Type uE} {G : Graph V₁ E₁}
  {F : {V : Type uV} → {E : Type uE} → Graph V E → Sort uO} [IsoAction F]

/-- Same-universe witness transfer. -/
theorem nonempty_of_forall_on (h : ∀ H : Graph V₂ E₂, Nonempty (F H))
    (hfit : G.FitsOn V₂ E₂) : Nonempty (F G) :=
  ⟨(IsoAction.map (F := F) hfit.copyOn.iso).symm (h _).some⟩

end IsoAction

/-! ### Cross-universe transfer

These are the versions used by constructions such as incidence graphs, where the canonical copy
or comparison graph naturally lands in a different carrier universe. -/

namespace IsoTransport

variable
  {P : {V : Type uV} → {E : Type uE} → Graph V E → Prop}
  {P' : {V : Type uV'} → {E : Type uE'} → Graph V E → Prop}
  [IsoTransport P P']

/-- A cross-universe invariant property proved on every graph on target carriers holds on `G`. -/
theorem of_forall_on (h : ∀ H : Graph V' E', P' H) (hfit : G.FitsOn V' E') : P G :=
  (IsoTransport.map hfit.copyOn.iso).symm (h _)

/-- To prove a transportable property for every finite graph in arbitrary carrier universes, it is
enough to prove its `Type 0` incarnation for finite `Graph ℕ ℕ`. -/
theorem of_forall_finite_nat
    {P₀ : {V : Type} → {E : Type} → Graph V E → Prop} [IsoTransport P P₀]
    (h : ∀ H : Graph ℕ ℕ, V(H).Finite → E(H).Finite → P₀ H)
    (hV : V(G).Finite) (hE : E(G).Finite) : P G :=
  let i := (FitsOn.of_finite_nat hV hE).copyOn.iso
  (IsoTransport.map i).symm (h _ (i.vertexSet_finite hV) (i.edgeSet_finite hE))

/-- Bounded finite carriers, now also cross-universe. -/
theorem of_forall_fin
    {n k : ℕ} {P₀ : {V : Type} → {E : Type} → Graph V E → Prop}
    [IsoTransport P P₀] (h : ∀ H : Graph (Fin n) (Fin k), P₀ H)
    (hV : V(G).ncard ≤ n) (hE : E(G).ncard ≤ k)
    (hVfin : V(G).Finite) (hEfin : E(G).Finite) : P G :=
  of_forall_on h (FitsOn.fin hV hE hVfin hEfin)

/-- Cross-universe witness transfer. -/
theorem nonempty_of_forall_on
    {F : {V : Type uV} → {E : Type uE} → Graph V E → Sort uO}
    {F' : {V : Type uV'} → {E : Type uE'} → Graph V E → Sort uO'}
    [IsoTransport F F'] (h : ∀ H : Graph V' E', Nonempty (F' H))
    (hfit : G.FitsOn V' E') : Nonempty (F G) :=
  ⟨(IsoTransport.map hfit.copyOn.iso).symm (h _).some⟩

/-- Finite witness transfer from the canonical `Graph ℕ ℕ` universe. -/
theorem nonempty_of_forall_finite_nat
    {F : {V : Type uV} → {E : Type uE} → Graph V E → Sort uO}
    {F₀ : {V : Type} → {E : Type} → Graph V E → Sort uO'}
    [IsoTransport F F₀]
    (h : ∀ H : Graph ℕ ℕ, V(H).Finite → E(H).Finite → Nonempty (F₀ H))
    (hV : V(G).Finite) (hE : E(G).Finite) : Nonempty (F G) :=
  let i := (FitsOn.of_finite_nat hV hE).copyOn.iso
  ⟨(IsoTransport.map i).symm (h _ (i.vertexSet_finite hV) (i.edgeSet_finite hE)).some⟩

end IsoTransport

/-! ### Equivariant functions -/

theorem Equivariant.map_eq_copyOn
    {V₁ V₂ : Type uV} {E₁ E₂ : Type uE} {G : Graph V₁ E₁}
    {F : {V : Type uV} → {E : Type uE} → Graph V E → Sort uO} [IsoAction F]
    {f : {V : Type uV} → {E : Type uE} → (G : Graph V E) → F G}
    [Equivariant F f] (hfit : G.FitsOn V₂ E₂) :
    IsoAction.map hfit.copyOn.iso (f G) = f hfit.copyOn.graph :=
  Equivariant.map_eq _

theorem Equivariant.isoRelated_of_isIsoTo
    {V₁ V₂ : Type uV} {E₁ E₂ : Type uE} {G : Graph V₁ E₁} {H : Graph V₂ E₂}
    {F : {V : Type uV} → {E : Type uE} → Graph V E → Sort uO} [IsoAction F]
    {f : {V : Type uV} → {E : Type uE} → (G : Graph V E) → F G}
    [Equivariant F f] (h : G.IsIsoTo H) : IsoRelated (f G) (f H) :=
  ⟨h.some, Equivariant.map_eq _⟩

end Graph
