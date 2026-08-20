/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Matroid.Graph.Iso.IsoAction

/-!
# Equivariant functions and invariant graph properties

There are two deliberately different naturality layers.

* `Equivariant F f` is homogeneous: it uses the source action of the diagonal
  `IsoTransport F F`.  This remains necessary for data-valued sections because a diagonal
  heterogeneous map is not definitionally forced to be the endpoint action.
* `InvariantTransport P P'` is the sole class for proposition-valued invariance, including the
  same-universe case `InvariantTransport P P`.  Logical closure is registered only here.

`Invariant f` remains the fixed-codomain homogeneous notion for arbitrary values.  For
`Prop`-valued `P`, an `InvariantTransport P P` supplies `Invariant P` through a low-priority
bridge.

Bounded quantifiers are handled directly, without a public `Supported` wrapper.  The generic
adapter recognizes

```lean
∀ x, B G x → P G x
∃ x, B G x ∧ P G x
```

as quantification over the transportable subtype `{x // B G x}`.  The same mechanism covers
vertices, edges, and ambient vertex/edge subsets.
-/

@[expose] public section

open Set Function

namespace Graph

universe uV uE uO uO' uV' uE' uA uA'

set_option linter.checkUnivs false in
/-- A proposition-valued graph family. -/
abbrev Property := {V : Type uV} → {E : Type uE} → Graph V E → Prop

/-! ## Homogeneous equivariance -/

/-- A section respects the homogeneous action carried by the diagonal transport. -/
class Equivariant (F : {V : Type uV} → {E : Type uE} → Graph V E → Sort uO) [IsoAction F]
    (f : {V : Type uV} → {E : Type uE} → (G : Graph V E) → F G) : Prop where
  map_eq : ∀ {V V' : Type uV} {E E' : Type uE} {G : Graph V E} {H : Graph V' E'} (i : Iso G H),
    IsoAction.map i (f G) = f H

/-- Fixed-codomain homogeneous invariance. -/
abbrev Invariant {R : Sort uO} (f : {V : Type uV} → {E : Type uE} → Graph V E → R) : Prop :=
  Equivariant (fun _ ↦ R) f

namespace Equivariant

variable {F : {V : Type uV} → {E : Type uE} → Graph V E → Sort uO} [IsoAction F]
  {f : {V : Type uV} → {E : Type uE} → (G : Graph V E) → F G}
  {V V' : Type uV} {E E' : Type uE} {G : Graph V E} {H : Graph V' E'}

 theorem isoRelated [Equivariant F f] (i : Iso G H) : IsoRelated (f G) (f H) :=
  ⟨i, Equivariant.map_eq i⟩

 theorem map_apply {A : {V : Type uV} → {E : Type uE} → Graph V E → Type uO} [IsoAction A]
    {B : {V : Type uV} → {E : Type uE} → Graph V E → Type uO'} [IsoAction B]
    (η : {V : Type uV} → {E : Type uE} → (G : Graph V E) → A G → B G)
    [Equivariant (fun G ↦ A G → B G) η] (i : Iso G H) (x : A G) :
    IsoAction.map i (η G x) = η H (IsoAction.map i x) := by
  refine Eq.trans ?_ <| congrArg (fun g : A H → B H ↦ g (IsoAction.map (F := A) i x))
    (map_eq (F := fun G ↦ A G → B G) (f := η) i)
  change IsoAction.map (F := B) i (η G x) = IsoAction.map (F := B) i
    (η G ((IsoAction.map (F := A) i).symm (IsoAction.map (F := A) i x)))
  rw [Equiv.symm_apply_apply]

 theorem iff_map {A : {V : Type uV} → {E : Type uE} → Graph V E → Type uO} [IsoAction A]
    (P : {V : Type uV} → {E : Type uE} → (G : Graph V E) → A G → Prop)
    [Equivariant (fun G ↦ A G → Prop) P] (i : Iso G H) (x : A G) :
    P G x ↔ P H (IsoAction.map i x) := by
  refine eq_iff_iff.mp <| Eq.trans ?_ <|
    congrArg (fun g : A H → Prop ↦ g (IsoAction.map (F := A) i x))
      (map_eq (F := fun G ↦ A G → Prop) (f := P) i)
  change IsoAction.map (F := fun _ ↦ Prop) i (P G x) = IsoAction.map (F := fun _ ↦ Prop) i
    (P G ((IsoAction.map (F := A) i).symm (IsoAction.map (F := A) i x)))
  rw [Equiv.symm_apply_apply]

end Equivariant

/-! ## Heterogeneous equivariance -/

/-- Cross-universe naturality of two sections of transported families.

This class intentionally records only the cross-universe square.  It is not used as the
homogeneous definition of `Equivariant`, because the heterogeneous map of a diagonal transport is
not forced to equal its endpoint action. -/
class EquivariantTransport
    (F : {V : Type uV} → {E : Type uE} → Graph V E → Sort uO)
    (F' : {V : Type uV'} → {E : Type uE'} → Graph V E → Sort uO')
    [IsoTransport F F']
    (f : {V : Type uV} → {E : Type uE} → (G : Graph V E) → F G)
    (f' : {V : Type uV'} → {E : Type uE'} → (G : Graph V E) → F' G) : Prop where
  map_eq : ∀ {V : Type uV} {E : Type uE}
    {V' : Type uV'} {E' : Type uE'}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H),
    IsoTransport.map i (f G) = f' H

namespace EquivariantTransport

 theorem map_apply
    {A : {V : Type uV} → {E : Type uE} → Graph V E → Type uA}
    {A' : {V : Type uV'} → {E : Type uE'} → Graph V E → Type uA'}
    {B : {V : Type uV} → {E : Type uE} → Graph V E → Type uO}
    {B' : {V : Type uV'} → {E : Type uE'} → Graph V E → Type uO'}
    [IsoTransport A A'] [IsoTransport B B']
    (η : {V : Type uV} → {E : Type uE} → (G : Graph V E) → A G → B G)
    (η' : {V : Type uV'} → {E : Type uE'} → (G : Graph V E) → A' G → B' G)
    [EquivariantTransport (fun G ↦ A G → B G) (fun G ↦ A' G → B' G) η η']
    {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) (x : A G) :
    IsoTransport.map i (η G x) = η' H (IsoTransport.map i x) := by
  refine Eq.trans ?_ <| congrArg (fun g : A' H → B' H ↦ g (IsoTransport.map (F := A) i x))
    (map_eq (F := fun G ↦ A G → B G) (F' := fun G ↦ A' G → B' G) (f := η) (f' := η') i)
  change IsoTransport.map (F := B) i (η G x) = IsoTransport.map (F := B) i
    (η G ((IsoTransport.map (F := A) i).symm (IsoTransport.map (F := A) i x)))
  rw [Equiv.symm_apply_apply]

 theorem iff_map
    {A : {V : Type uV} → {E : Type uE} → Graph V E → Type uA}
    {A' : {V : Type uV'} → {E : Type uE'} → Graph V E → Type uA'}
    [IsoTransport A A']
    (P : {V : Type uV} → {E : Type uE} → (G : Graph V E) → A G → Prop)
    (P' : {V : Type uV'} → {E : Type uE'} → (G : Graph V E) → A' G → Prop)
    [EquivariantTransport (fun G ↦ A G → Prop) (fun G ↦ A' G → Prop) P P']
    {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) (x : A G) :
    P G x ↔ P' H (IsoTransport.map i x) := by
  refine eq_iff_iff.mp <| Eq.trans ?_ <|
    congrArg (fun g : A' H → Prop ↦ g (IsoTransport.map (F := A) i x))
      (map_eq (F := fun G ↦ A G → Prop) (F' := fun G ↦ A' G → Prop) (f := P) (f' := P') i)
  change IsoTransport.map (F := fun _ ↦ Prop) i (P G x) = IsoTransport.map (F := fun _ ↦ Prop) i
    (P G ((IsoTransport.map (F := A) i).symm (IsoTransport.map (F := A) i x)))
  rw [Equiv.symm_apply_apply]

end EquivariantTransport

/-! ## Heterogeneous proposition invariance -/

/-- A graph property and a target-universe incarnation have the same truth value on isomorphic
graphs.  This is the sole proposition-valued invariance class. -/
class InvariantTransport
    (P : {V : Type uV} → {E : Type uE} → Graph V E → Prop)
    (P' : {V : Type uV'} → {E : Type uE'} → Graph V E → Prop) : Prop where
  iff_of_iso : ∀ {V : Type uV} {E : Type uE}
    {V' : Type uV'} {E' : Type uE'}
    {G : Graph V E} {H : Graph V' E'}, Iso G H → (P G ↔ P' H)

namespace InvariantTransport

 theorem of_iff
    {P : {V : Type uV} → {E : Type uE} → Graph V E → Prop}
    {P' : {V : Type uV'} → {E : Type uE'} → Graph V E → Prop}
    (h : ∀ {V : Type uV} {E : Type uE}
      {V' : Type uV'} {E' : Type uE'}
      {G : Graph V E} {H : Graph V' E'}, Iso G H → (P G ↔ P' H)) :
    InvariantTransport P P' where
  iff_of_iso := h

 theorem of_imp
    {P : {V : Type uV} → {E : Type uE} → Graph V E → Prop}
    {P' : {V : Type uV'} → {E : Type uE'} → Graph V E → Prop}
    (h : ∀ {V : Type uV} {E : Type uE}
      {V' : Type uV'} {E' : Type uE'}
      {G : Graph V E} {H : Graph V' E'}, Iso G H → P G → P' H)
    (h' : ∀ {V : Type uV'} {E : Type uE'}
      {V' : Type uV} {E' : Type uE}
      {G : Graph V E} {H : Graph V' E'}, Iso G H → P' G → P H) :
    InvariantTransport P P' where
  iff_of_iso i := ⟨h i, h' i.symm⟩

 theorem iff_of_isIsoTo
    {P : {V : Type uV} → {E : Type uE} → Graph V E → Prop}
    {P' : {V : Type uV'} → {E : Type uE'} → Graph V E → Prop}
    [InvariantTransport P P']
    {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
    {G : Graph V E} {H : Graph V' E'} (h : G.IsIsoTo H) : P G ↔ P' H :=
  InvariantTransport.iff_of_iso h.some

 theorem map
    {P : {V : Type uV} → {E : Type uE} → Graph V E → Prop}
    {P' : {V : Type uV'} → {E : Type uE'} → Graph V E → Prop}
    [InvariantTransport P P']
    {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) : P G → P' H :=
  (InvariantTransport.iff_of_iso i).mp

 theorem comap
    {P : {V : Type uV} → {E : Type uE} → Graph V E → Prop}
    {P' : {V : Type uV'} → {E : Type uE'} → Graph V E → Prop}
    [InvariantTransport P P']
    {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) : P' H → P G :=
  (InvariantTransport.iff_of_iso i).mpr

end InvariantTransport

/-! ### Bridges to the old homogeneous/fiber interfaces -/

/-- Same-universe proposition invariance is recovered from the heterogeneous property class.
Low priority leaves direct `Invariant` instances available for legacy/non-property code. -/
instance (priority := 100) instInvariantOfTransport
    (P : {V : Type uV} → {E : Type uE} → Graph V E → Prop)
    [InvariantTransport P P] : Invariant P where
  map_eq i := propext (InvariantTransport.iff_of_iso i)

/-- Legacy proof-type transport implies property invariance.  New atomic graph properties should
register `InvariantTransport` directly rather than transport their proof objects. -/
instance (priority := 50) instInvariantTransportOfIsoTransport
    (P : {V : Type uV} → {E : Type uE} → Graph V E → Prop)
    (P' : {V : Type uV'} → {E : Type uE'} → Graph V E → Prop)
    [IsoTransport P P'] : InvariantTransport P P' where
  iff_of_iso i := IsoTransport.iff_of_iso i

namespace Invariant

variable {R : Sort uO} {f : {V : Type uV} → {E : Type uE} → Graph V E → R}
  {V V' : Type uV} {E E' : Type uE} {G : Graph V E} {H : Graph V' E'}

 theorem eq_of_iso [Invariant f] (i : Iso G H) : f G = f H :=
  Equivariant.map_eq (F := fun _ ↦ R) (f := f) i

 theorem eq_of_isIsoTo [Invariant f] (h : G.IsIsoTo H) : f G = f H :=
  eq_of_iso h.some

 theorem of_iff
    {P : {V : Type uV} → {E : Type uE} → Graph V E → Prop}
    (h : ∀ {V V' : Type uV} {E E' : Type uE}
      {G : Graph V E} {H : Graph V' E'}, Iso G H → (P G ↔ P H)) : Invariant P where
  map_eq i := propext (h i)

 theorem of_imp
    {P : {V : Type uV} → {E : Type uE} → Graph V E → Prop}
    (h : ∀ {V V' : Type uV} {E E' : Type uE}
      {G : Graph V E} {H : Graph V' E'}, Iso G H → P G → P H) : Invariant P where
  map_eq i := propext ⟨h i, h i.symm⟩

 theorem iff_of_iso {P : {V : Type uV} → {E : Type uE} → Graph V E → Prop} [Invariant P]
    (i : Iso G H) : P G ↔ P H := by
  rw [Invariant.eq_of_iso (f := P) i]

 theorem iff_of_isIsoTo {P : {V : Type uV} → {E : Type uE} → Graph V E → Prop} [Invariant P]
     (h : G.IsIsoTo H) : P G ↔ P H := iff_of_iso h.some

theorem map {P : {V : Type uV} → {E : Type uE} → Graph V E → Prop} [Invariant P]
    (i : Iso G H) : P G → P H := (iff_of_iso i).mp

theorem comap {P : {V : Type uV} → {E : Type uE} → Graph V E → Prop} [Invariant P]
    (i : Iso G H) : P H → P G := (iff_of_iso i).mpr

end Invariant

/-! Backwards-compatible proposition namespace. -/
namespace Property

 theorem iff_of_iso
    {P : {V : Type uV} → {E : Type uE} → Graph V E → Prop}
    [Invariant P]
    {V V' : Type uV} {E E' : Type uE}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) : P G ↔ P H :=
  Invariant.iff_of_iso i

 theorem iff_of_isIsoTo
    {P : {V : Type uV} → {E : Type uE} → Graph V E → Prop}
    [Invariant P]
    {V V' : Type uV} {E E' : Type uE}
    {G : Graph V E} {H : Graph V' E'} (h : G.IsIsoTo H) : P G ↔ P H :=
  Invariant.iff_of_isIsoTo h

 theorem map
    {P : {V : Type uV} → {E : Type uE} → Graph V E → Prop}
    [Invariant P]
    {V V' : Type uV} {E E' : Type uE}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) : P G → P H :=
  Invariant.map i

 theorem comap
    {P : {V : Type uV} → {E : Type uE} → Graph V E → Prop}
    [Invariant P]
    {V V' : Type uV} {E E' : Type uE}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) : P H → P G :=
  Invariant.comap i

end Property

/-! ## Logical algebra: heterogeneous only -/

instance instInvariantTransportNot
    (P : {V : Type uV} → {E : Type uE} → Graph V E → Prop)
    (P' : {V : Type uV'} → {E : Type uE'} → Graph V E → Prop)
    [InvariantTransport P P'] :
    InvariantTransport (fun G ↦ ¬ P G) (fun G ↦ ¬ P' G) :=
  InvariantTransport.of_iff fun i ↦ not_congr (InvariantTransport.iff_of_iso i)

instance instInvariantTransportAnd
    (P Q : {V : Type uV} → {E : Type uE} → Graph V E → Prop)
    (P' Q' : {V : Type uV'} → {E : Type uE'} → Graph V E → Prop)
    [InvariantTransport P P'] [InvariantTransport Q Q'] :
    InvariantTransport (fun G ↦ P G ∧ Q G) (fun G ↦ P' G ∧ Q' G) :=
  InvariantTransport.of_iff fun i ↦
    and_congr (InvariantTransport.iff_of_iso (P := P) i)
      (InvariantTransport.iff_of_iso (P := Q) i)

instance instInvariantTransportOr
    (P Q : {V : Type uV} → {E : Type uE} → Graph V E → Prop)
    (P' Q' : {V : Type uV'} → {E : Type uE'} → Graph V E → Prop)
    [InvariantTransport P P'] [InvariantTransport Q Q'] :
    InvariantTransport (fun G ↦ P G ∨ Q G) (fun G ↦ P' G ∨ Q' G) :=
  InvariantTransport.of_iff fun i ↦
    or_congr (InvariantTransport.iff_of_iso (P := P) i)
      (InvariantTransport.iff_of_iso (P := Q) i)

instance instInvariantTransportImp
    (P Q : {V : Type uV} → {E : Type uE} → Graph V E → Prop)
    (P' Q' : {V : Type uV'} → {E : Type uE'} → Graph V E → Prop)
    [InvariantTransport P P'] [InvariantTransport Q Q'] :
    InvariantTransport (fun G ↦ P G → Q G) (fun G ↦ P' G → Q' G) :=
  InvariantTransport.of_iff fun i ↦
    imp_congr (InvariantTransport.iff_of_iso (P := P) i)
      (InvariantTransport.iff_of_iso (P := Q) i)

instance instInvariantTransportIff
    (P Q : {V : Type uV} → {E : Type uE} → Graph V E → Prop)
    (P' Q' : {V : Type uV'} → {E : Type uE'} → Graph V E → Prop)
    [InvariantTransport P P'] [InvariantTransport Q Q'] :
    InvariantTransport (fun G ↦ P G ↔ Q G) (fun G ↦ P' G ↔ Q' G) :=
  InvariantTransport.of_iff fun i ↦
    iff_congr (InvariantTransport.iff_of_iso (P := P) i)
      (InvariantTransport.iff_of_iso (P := Q) i)

instance instInvariantTransportParam
    {γ : Sort*} (c : γ)
    (P : γ → {V : Type uV} → {E : Type uE} → Graph V E → Prop)
    (P' : γ → {V : Type uV'} → {E : Type uE'} → Graph V E → Prop)
    [∀ d, InvariantTransport (P d) (P' d)] :
    InvariantTransport (fun G ↦ P c G) (fun G ↦ P' c G) :=
  inferInstanceAs (InvariantTransport (P c) (P' c))

/-! ## Quantifiers over transported graph-dependent types -/

/-- General heterogeneous existential closure. -/
instance instInvariantTransportExists
    (A : {V : Type uV} → {E : Type uE} → Graph V E → Type uA)
    (A' : {V : Type uV'} → {E : Type uE'} → Graph V E → Type uA')
    [IsoTransport A A']
    (P : {V : Type uV} → {E : Type uE} → (G : Graph V E) → A G → Prop)
    (P' : {V : Type uV'} → {E : Type uE'} → (G : Graph V E) → A' G → Prop)
    [EquivariantTransport (fun G ↦ A G → Prop) (fun G ↦ A' G → Prop) P P'] :
    InvariantTransport (fun G ↦ ∃ x, P G x) (fun G ↦ ∃ x, P' G x) :=
  InvariantTransport.of_iff fun i ↦ by
    refine ⟨fun ⟨x, hx⟩ ↦ ⟨IsoTransport.map i x, (EquivariantTransport.iff_map P P' i x).1 hx⟩,
      fun ⟨y, hy⟩ ↦ ⟨(IsoTransport.map i).symm y, (EquivariantTransport.iff_map P P' i _).2 ?_⟩⟩
    rwa [Equiv.apply_symm_apply]

/-- General heterogeneous universal closure. -/
instance instInvariantTransportForall
    (A : {V : Type uV} → {E : Type uE} → Graph V E → Type uA)
    (A' : {V : Type uV'} → {E : Type uE'} → Graph V E → Type uA')
    [IsoTransport A A']
    (P : {V : Type uV} → {E : Type uE} → (G : Graph V E) → A G → Prop)
    (P' : {V : Type uV'} → {E : Type uE'} → (G : Graph V E) → A' G → Prop)
    [EquivariantTransport (fun G ↦ A G → Prop) (fun G ↦ A' G → Prop) P P'] :
    InvariantTransport (fun G ↦ ∀ x, P G x) (fun G ↦ ∀ x, P' G x) :=
  InvariantTransport.of_iff fun i ↦ by
    refine ⟨fun h y ↦ ?_, fun h x ↦ (EquivariantTransport.iff_map P P' i x).2 (h _)⟩
    have := (EquivariantTransport.iff_map P P' i ((IsoTransport.map (F := A) i).symm y)).1 (h _)
    rwa [Equiv.apply_symm_apply] at this

/-- Same-universe fallback for existing `Equivariant` predicate registrations.  It still produces
an `InvariantTransport` instance, so proposition-valued closure remains in one class hierarchy. -/
instance (priority := 900) instInvariantTransportExistsSame
    (A : {V : Type uV} → {E : Type uE} → Graph V E → Type uA)
    [IsoAction A]
    (P : {V : Type uV} → {E : Type uE} → (G : Graph V E) → A G → Prop)
    [Equivariant (fun G ↦ A G → Prop) P] :
    InvariantTransport (fun G ↦ ∃ x, P G x) (fun G ↦ ∃ x, P G x) :=
  InvariantTransport.of_iff fun i ↦ by
    refine ⟨fun ⟨x, hx⟩ ↦ ⟨IsoAction.map (F := A) i x, (Equivariant.iff_map P i x).1 hx⟩,
      fun ⟨y, hy⟩ ↦ ⟨(IsoAction.map (F := A) i).symm y, (Equivariant.iff_map P i _).2 ?_⟩⟩
    rwa [Equiv.apply_symm_apply]

instance (priority := 900) instInvariantTransportForallSame
    (A : {V : Type uV} → {E : Type uE} → Graph V E → Type uA)
    [IsoAction A]
    (P : {V : Type uV} → {E : Type uE} → (G : Graph V E) → A G → Prop)
    [Equivariant (fun G ↦ A G → Prop) P] :
    InvariantTransport (fun G ↦ ∀ x, P G x) (fun G ↦ ∀ x, P G x) :=
  InvariantTransport.of_iff fun i ↦ by
    refine ⟨fun h y ↦ ?_, fun h x ↦ (Equivariant.iff_map P i x).2 (h _)⟩
    have := (Equivariant.iff_map P i ((IsoAction.map (F := A) i).symm y)).1 (h _)
    rwa [Equiv.apply_symm_apply] at this

/-! ## Generic bounded-quantifier adapters

The ambient type `A G` itself need not transport.  Only the subtype cut out by the guard `B G`
needs an action.  This is what lets the same declaration handle both

* `x ∈ V(G)` / `e ∈ E(G)`, and
* `X ⊆ V(G)` / `F ⊆ E(G)`.
-/

instance instInvariantTransportForallBounded
    (A : {V : Type uV} → {E : Type uE} → Graph V E → Type uA)
    (A' : {V : Type uV'} → {E : Type uE'} → Graph V E → Type uA')
    (B : {V : Type uV} → {E : Type uE} → (G : Graph V E) → A G → Prop)
    (B' : {V : Type uV'} → {E : Type uE'} → (G : Graph V E) → A' G → Prop)
    (P : {V : Type uV} → {E : Type uE} → (G : Graph V E) → A G → Prop)
    (P' : {V : Type uV'} → {E : Type uE'} → (G : Graph V E) → A' G → Prop)
    [IsoTransport
      (fun G ↦ {x : A G // B G x})
      (fun G ↦ {x : A' G // B' G x})]
    [EquivariantTransport
      (fun G ↦ {x : A G // B G x} → Prop)
      (fun G ↦ {x : A' G // B' G x} → Prop)
      (fun G x ↦ P G x.1)
      (fun G x ↦ P' G x.1)] :
    InvariantTransport
      (fun G ↦ ∀ x, B G x → P G x)
      (fun G ↦ ∀ x, B' G x → P' G x) :=
  InvariantTransport.of_iff fun i ↦ by
    simpa [Subtype.forall] using
      InvariantTransport.iff_of_iso
        (P := fun G ↦ ∀ x : {x : A G // B G x}, P G x.1)
        (P' := fun G ↦ ∀ x : {x : A' G // B' G x}, P' G x.1) i

instance instInvariantTransportExistsBounded
    (A : {V : Type uV} → {E : Type uE} → Graph V E → Type uA)
    (A' : {V : Type uV'} → {E : Type uE'} → Graph V E → Type uA')
    (B : {V : Type uV} → {E : Type uE} → (G : Graph V E) → A G → Prop)
    (B' : {V : Type uV'} → {E : Type uE'} → (G : Graph V E) → A' G → Prop)
    (P : {V : Type uV} → {E : Type uE} → (G : Graph V E) → A G → Prop)
    (P' : {V : Type uV'} → {E : Type uE'} → (G : Graph V E) → A' G → Prop)
    [IsoTransport
      (fun G ↦ {x : A G // B G x})
      (fun G ↦ {x : A' G // B' G x})]
    [EquivariantTransport
      (fun G ↦ {x : A G // B G x} → Prop)
      (fun G ↦ {x : A' G // B' G x} → Prop)
      (fun G x ↦ P G x.1)
      (fun G x ↦ P' G x.1)] :
    InvariantTransport
      (fun G ↦ ∃ x, B G x ∧ P G x)
      (fun G ↦ ∃ x, B' G x ∧ P' G x) :=
  InvariantTransport.of_iff fun i ↦ by
    simpa [Subtype.exists] using
      InvariantTransport.iff_of_iso
        (P := fun G ↦ ∃ x : {x : A G // B G x}, P G x.1)
        (P' := fun G ↦ ∃ x : {x : A' G // B' G x}, P' G x.1) i

/-- Same-universe bounded universal adapter, using the endpoint action rather than the diagonal
heterogeneous map. -/
instance (priority := 900) instInvariantTransportForallBoundedSame
    (A : {V : Type uV} → {E : Type uE} → Graph V E → Type uA)
    (B : {V : Type uV} → {E : Type uE} → (G : Graph V E) → A G → Prop)
    (P : {V : Type uV} → {E : Type uE} → (G : Graph V E) → A G → Prop)
    [IsoAction (fun G ↦ {x : A G // B G x})]
    [Equivariant
      (fun G ↦ {x : A G // B G x} → Prop)
      (fun G x ↦ P G x.1)] :
    InvariantTransport
      (fun G ↦ ∀ x, B G x → P G x)
      (fun G ↦ ∀ x, B G x → P G x) :=
  InvariantTransport.of_iff fun i ↦ by
    simpa [Subtype.forall] using
      InvariantTransport.iff_of_iso
        (P := fun G ↦ ∀ x : {x : A G // B G x}, P G x.1)
        (P' := fun G ↦ ∀ x : {x : A G // B G x}, P G x.1) i

instance (priority := 900) instInvariantTransportExistsBoundedSame
    (A : {V : Type uV} → {E : Type uE} → Graph V E → Type uA)
    (B : {V : Type uV} → {E : Type uE} → (G : Graph V E) → A G → Prop)
    (P : {V : Type uV} → {E : Type uE} → (G : Graph V E) → A G → Prop)
    [IsoAction (fun G ↦ {x : A G // B G x})]
    [Equivariant
      (fun G ↦ {x : A G // B G x} → Prop)
      (fun G x ↦ P G x.1)] :
    InvariantTransport
      (fun G ↦ ∃ x, B G x ∧ P G x)
      (fun G ↦ ∃ x, B G x ∧ P G x) :=
  InvariantTransport.of_iff fun i ↦ by
    simpa [Subtype.exists] using
      InvariantTransport.iff_of_iso
        (P := fun G ↦ ∃ x : {x : A G // B G x}, P G x.1)
        (P' := fun G ↦ ∃ x : {x : A G // B G x}, P G x.1) i

/-! ## Small structural naturality instances retained from the old API -/

instance instEquivariantPair
    (A : {V : Type uV} → {E : Type uE} → Graph V E → Type uO)
    (B : {V : Type uV} → {E : Type uE} → Graph V E → Type uO')
    [IsoAction A] [IsoAction B]
    (f : {V : Type uV} → {E : Type uE} → (G : Graph V E) → A G)
    (g : {V : Type uV} → {E : Type uE} → (G : Graph V E) → B G)
    [Equivariant A f] [Equivariant B g] :
    Equivariant (fun G ↦ A G × B G) (fun G ↦ (f G, g G)) where
  map_eq i := by
    show (IsoAction.map i (f _), IsoAction.map i (g _)) = _
    rw [Equivariant.map_eq (F := A) i, Equivariant.map_eq (F := B) i]

instance instInvariantTransportNonempty
    (A : {V : Type uV} → {E : Type uE} → Graph V E → Sort uO)
    (A' : {V : Type uV'} → {E : Type uE'} → Graph V E → Sort uO')
    [IsoTransport A A'] :
    InvariantTransport (fun G ↦ Nonempty (A G)) (fun G ↦ Nonempty (A' G)) :=
  InvariantTransport.of_iff fun i ↦ (IsoTransport.map (F := A) i).nonempty_congr

instance instInvariantTransportIsEmpty
    (A : {V : Type uV} → {E : Type uE} → Graph V E → Sort uO)
    (A' : {V : Type uV'} → {E : Type uE'} → Graph V E → Sort uO')
    [IsoTransport A A'] :
    InvariantTransport (fun G ↦ IsEmpty (A G)) (fun G ↦ IsEmpty (A' G)) :=
  InvariantTransport.of_iff fun i ↦ (IsoTransport.map (F := A) i).isEmpty_congr

instance instInvariantTransportSubsingleton
    (A : {V : Type uV} → {E : Type uE} → Graph V E → Type uO)
    (A' : {V : Type uV'} → {E : Type uE'} → Graph V E → Type uO')
    [IsoTransport A A'] :
    InvariantTransport (fun G ↦ Subsingleton (A G)) (fun G ↦ Subsingleton (A' G)) :=
  InvariantTransport.of_iff fun i ↦ (IsoTransport.map (F := A) i).subsingleton_congr

end Graph
