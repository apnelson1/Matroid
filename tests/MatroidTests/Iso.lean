/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Matroid.Graph.Iso.Invariant

/-!
# Regression tests for `IsoAction`, `IsoTransport`, and `Invariant`

The public API is expression-first.  None of the fixtures below are declared through a bundled
`Family`, `TypeFamily`, `Property`, or `Family.Section`; ordinary universe-polymorphic declarations
and lambdas are elaborated directly at the universes demanded by `IsoAction`, `IsoTransport`, and
`Invariant`.

Atomic graph properties register one `IsoTransport` instance.  The same-universe `IsoAction` and
`Invariant` are then recovered by the low-priority bridges.  Compound same-universe propositions
continue to resolve through the specialized logical `Invariant` instances, while compound
cross-universe propositions resolve through the logical `IsoTransport` instances.

The `f ⧉ e` tests are particularly important: `⧉` duplicates the syntax of `e` before
elaboration.  If it were replaced by an ordinary function taking one already-elaborated family,
the explicit cross-universe checks below would stop typechecking.
-/

@[expose] public section

open Set

namespace Graph
namespace GFCheck

universe uV uE uV' uE' uV'' uE''

/-! ### Atomic properties: one cross-universe registration -/

/-- Vertex-side test atom. -/
def IsBig {V : Type uV} {E : Type uE} (G : Graph V E) : Prop := 3 ≤ V(G).encard

theorem isBig_iff_of_iso
    {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) : IsBig G ↔ IsBig H := by
  simp only [IsBig, IsIsoTo.vertexSet_encard_eq ⟨i⟩]

instance instIsBigTransport : IsoTransport ⧉ IsBig :=
  IsoTransport.of_iff isBig_iff_of_iso isBig_iff_of_iso isBig_iff_of_iso

/-- Edge-side test atom. -/
def IsDense {V : Type uV} {E : Type uE} (G : Graph V E) : Prop := 3 ≤ E(G).encard

theorem isDense_iff_of_iso
    {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) : IsDense G ↔ IsDense H := by
  simp only [IsDense, IsIsoTo.edgeSet_encard_eq ⟨i⟩]

instance instIsDenseTransport : IsoTransport ⧉ IsDense :=
  IsoTransport.of_iff isDense_iff_of_iso isDense_iff_of_iso isDense_iff_of_iso

/-- Parameterized atom, modeling `K.IsTopologicalMinor G` with `K` fixed. -/
def HasOrder (n : ℕ∞) {V : Type uV} {E : Type uE} (G : Graph V E) : Prop :=
  V(G).encard = n

theorem hasOrder_iff_of_iso (n : ℕ∞)
    {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) : HasOrder n G ↔ HasOrder n H := by
  simp only [HasOrder, IsIsoTo.vertexSet_encard_eq ⟨i⟩]

instance instHasOrderTransport (n : ℕ∞) : IsoTransport ⧉ HasOrder n :=
  IsoTransport.of_iff (hasOrder_iff_of_iso n) (hasOrder_iff_of_iso n) (hasOrder_iff_of_iso n)

/-! The atomic registration is enough for all three layers. -/

/-- info: instIsBigTransport -/
#guard_msgs (whitespace := lax) in
#synth IsoTransport ⧉ IsBig
#synth IsoAction IsBig
#synth Invariant IsBig

#synth IsoTransport ⧉ IsDense
#synth IsoAction IsDense
#synth Invariant IsDense

#synth IsoTransport ⧉ HasOrder 5
#synth Invariant (HasOrder 5)

/-! ### Fixtures for same-universe equivariance -/

/-- A section of `fun G ↦ V(G) → Prop`, written as its ordinary Lean type. -/
def bigAtVertex :
    {V : Type uV} → {E : Type uE} → (G : Graph V E) → V(G) → Prop :=
  fun G _ ↦ IsBig G

instance instBigAtVertex :
    Equivariant (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ V(G) → Prop)
      bigAtVertex where
  map_eq i := funext fun _ ↦ Invariant.eq_of_iso (f := IsBig) i

/-- Ambient-label predicate for membership bridge checks. -/
def bigAtLabel : {V : Type uV} → {E : Type uE} → Graph V E → V → Prop :=
  fun G _ ↦ IsBig G

instance instBigAtLabel :
    Equivariant (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ V(G) → Prop)
      (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦
        fun x : V(G) ↦ bigAtLabel G x.1) where
  map_eq i := funext fun _ ↦ Invariant.eq_of_iso (f := IsBig) i

/-- Edge-side ambient-label predicate. -/
def denseAtLabel : {V : Type uV} → {E : Type uE} → Graph V E → E → Prop :=
  fun G _ ↦ IsDense G

instance instDenseAtLabel :
    Equivariant (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ E(G) → Prop)
      (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦
        fun e : E(G) ↦ denseAtLabel G e.1) where
  map_eq i := funext fun _ ↦ Invariant.eq_of_iso (f := IsDense) i

/-- Equivariant empty vertex set. -/
def emptyVertexSet :
    {V : Type uV} → {E : Type uE} → (G : Graph V E) → Set V(G) :=
  fun _ ↦ ∅

instance instEmptyVertexSet :
    Equivariant (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ Set V(G))
      emptyVertexSet where
  map_eq i := by simp [emptyVertexSet, IsoAction.map, Equiv.Set.congr]

/-- Equivariant empty edge set. -/
def emptyEdgeSet :
    {V : Type uV} → {E : Type uE} → (G : Graph V E) → Set E(G) :=
  fun _ ↦ ∅

instance instEmptyEdgeSet :
    Equivariant (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ Set E(G))
      emptyEdgeSet where
  map_eq i := by simp [emptyEdgeSet, IsoAction.map, Equiv.Set.congr]

/-! ### Same-universe structural `IsoAction` -/

/-- info: instConst Nat -/
#guard_msgs (whitespace := lax) in
set_option pp.explicit true in
#synth IsoAction (fun {V : Type uV} {E : Type uE} (_ : Graph V E) ↦ ℕ)

/-- info: instVertices -/
#guard_msgs (whitespace := lax) in
set_option pp.explicit true in
#synth IsoAction (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ V(G))

/-- info: instEdges -/
#guard_msgs (whitespace := lax) in
set_option pp.explicit true in
#synth IsoAction (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ E(G))

#synth IsoAction (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ Set V(G))
#synth IsoAction (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ V(G) × E(G))
#synth IsoAction (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ V(G) ⊕ E(G))
#synth IsoAction (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ Option V(G))
#synth IsoAction (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ E(G) → V(G) → Prop)
#synth IsoAction (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦
  {x : V(G) // bigAtVertex G x})

/-! ### Cross-universe structural `IsoTransport` -/

/-- info: instTransportVertices -/
#guard_msgs (whitespace := lax) in
#synth IsoTransport
  (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ V(G))
  (fun {V : Type uV'} {E : Type uE'} (G : Graph V E) ↦ V(G))

/-- info: instTransportEdges -/
#guard_msgs (whitespace := lax) in
#synth IsoTransport
  (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ E(G))
  (fun {V : Type uV'} {E : Type uE'} (G : Graph V E) ↦ E(G))

#synth IsoTransport
  (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ Set V(G))
  (fun {V : Type uV'} {E : Type uE'} (G : Graph V E) ↦ Set V(G))

#synth IsoTransport
  (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ V(G) × E(G))
  (fun {V : Type uV'} {E : Type uE'} (G : Graph V E) ↦ V(G) × E(G))

#synth IsoTransport
  (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ E(G) → V(G) → Prop)
  (fun {V : Type uV'} {E : Type uE'} (G : Graph V E) ↦ E(G) → V(G) → Prop)

/-! The syntax-level duplication form should infer the same structural transports without the
caller writing any universe annotations. -/
#synth IsoTransport ⧉ fun G ↦ Set V(G)
#synth IsoTransport ⧉ fun G ↦ V(G) × E(G)
#synth IsoTransport ⧉ fun G ↦ E(G) → V(G) → Prop

/-! A genuinely heterogeneous isomorphism can be used immediately. -/
example {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) : V(G) ≃ V(H) :=
  IsoTransport.map (F := fun G ↦ V(G)) i

example {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) : IsBig G ↔ IsBig H :=
  IsoTransport.iff_of_iso (P := IsBig) (P' := IsBig) i

/-- The universe shape forced by an incidence graph: its vertex carrier `V ⊕ E` lives in
`Type (max uV uE)`, with no assumption that `uV = uE`. -/
example {V : Type uV} {E : Type uE} {I : Type uE'}
    {G : Graph V E} {H : Graph (V ⊕ E) I} (i : Iso G H) : IsBig G ↔ IsBig H :=
  IsoTransport.iff_of_iso (P := IsBig) (P' := IsBig) i

example {V : Type uV} {E : Type uE} {I : Type uE'}
    {G : Graph V E} {H : Graph (V ⊕ E) I} (i : Iso G H) : V(G) ≃ V(H) :=
  IsoTransport.map (F := fun G ↦ V(G)) i

/-! Source and target coherence are not documentation only: pin both laws on vertices across three
universe slices. -/
example {V₀ V₁ : Type uV} {E₀ E₁ : Type uE} {V₂ : Type uV'} {E₂ : Type uE'} {G₀ : Graph V₀ E₀}
    {G₁ : Graph V₁ E₁} {H : Graph V₂ E₂} (i : Iso G₀ G₁) (j : Iso G₁ H) (x : V(G₀)) :
    IsoTransport.map (F := fun G ↦ V(G)) (i.comp j) x =
      IsoTransport.map (F := fun G ↦ V(G)) j (IsoAction.map (F := fun G ↦ V(G)) i x) :=
  IsoTransport.map_pre (F := fun G ↦ V(G)) i j x

example {V₀ : Type uV} {E₀ : Type uE} {V₁ V₂ : Type uV'} {E₁ E₂ : Type uE'}
    {G : Graph V₀ E₀} {H₁ : Graph V₁ E₁} {H₂ : Graph V₂ E₂}
    (i : Iso G H₁) (j : Iso H₁ H₂) (x : V(G)) :
    IsoTransport.map (F := fun G ↦ V(G)) (i.comp j) x =
      IsoAction.map (F := fun G ↦ V(G)) j (IsoTransport.map (F := fun G ↦ V(G)) i x) :=
  IsoTransport.map_post (F := fun G ↦ V(G)) i j x

/-! ### `Equivariant`: closure under pairing -/

#synth Equivariant
  (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ Set V(G) × Set E(G))
  (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦
    (emptyVertexSet G, emptyEdgeSet G))

/-! ### Same-universe logical `Invariant` composition -/

/-- info: instAnd @IsBig @IsDense -/
#guard_msgs (whitespace := lax) in
#synth Invariant (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ IsBig G ∧ IsDense G)

#synth Invariant (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ IsBig G → IsDense G)
#synth Invariant (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ ¬ IsBig G)
#synth Invariant (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ IsBig G ∨ IsDense G)
#synth Invariant (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦
  IsBig G ↔ ¬ (IsDense G ∨ ¬ IsBig G))
#synth Invariant (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ HasOrder 5 G)

/-! ### Cross-universe logical `IsoTransport` composition -/

#synth IsoTransport ⧉ fun G ↦ IsBig G ∧ IsDense G
#synth IsoTransport ⧉ fun G ↦ IsBig G → IsDense G
#synth IsoTransport ⧉ fun G ↦ ¬ IsBig G
#synth IsoTransport ⧉ fun G ↦ IsBig G ∨ IsDense G
#synth IsoTransport ⧉ fun G ↦ IsBig G ↔ ¬ (IsDense G ∨ ¬ IsBig G)
#synth IsoTransport ⧉ fun G ↦ HasOrder 5 G

/-! ### Quantifiers over graph-dependent data -/

#synth Invariant (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦
  ∃ x : V(G), bigAtVertex G x)

#synth Invariant (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦
  ∀ x : V(G), bigAtVertex G x)

/-! ### Ambient-membership bridges -/

#synth Invariant (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦
  ∀ x ∈ V(G), bigAtLabel G x)

#synth Invariant (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦
  ∃ x ∈ V(G), bigAtLabel G x)

#synth Invariant (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦
  ∀ e ∈ E(G), denseAtLabel G e)

#synth Invariant (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦
  ∃ e ∈ E(G), denseAtLabel G e)

/-! ### Existence properties cross universes -/

#synth Invariant (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ Nonempty (Set V(G)))
#synth IsoTransport ⧉ fun G ↦ Nonempty (Set V(G))
#synth IsoTransport ⧉ fun G ↦ IsEmpty (Set V(G))
#synth IsoTransport ⧉ fun G ↦ Subsingleton (Set V(G))

/-! ### Negative resolution -/

opaque Unregistered {V : Type uV} {E : Type uE} (G : Graph V E) : Prop

set_option maxHeartbeats 20000 in
example : True := by
  fail_if_success
    have : Invariant (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ Unregistered G) :=
      inferInstance
  trivial

set_option maxHeartbeats 20000 in
example : True := by
  fail_if_success
    have : IsoTransport
      (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ Unregistered G)
      (fun {V : Type uV'} {E : Type uE'} (G : Graph V E) ↦ Unregistered G) := inferInstance
  trivial

set_option maxHeartbeats 20000 in
example : True := by
  fail_if_success
    have : Invariant (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦
      IsBig G ∧ Unregistered G) := inferInstance
  trivial

-- Nested structural search must also fail rather than loop through the low-priority bridges.
set_option maxHeartbeats 20000 in
example : True := by
  fail_if_success
    have : Invariant (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦
      Nonempty (Unregistered G → Unit)) := inferInstance
  trivial

set_option maxHeartbeats 20000 in
example : True := by
  fail_if_success
    have : IsoTransport
      (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ Nonempty (Unregistered G → Unit))
      (fun {V : Type uV'} {E : Type uE'} (G : Graph V E) ↦ Nonempty (Unregistered G → Unit)) :=
      inferInstance
  trivial

end GFCheck
end Graph
