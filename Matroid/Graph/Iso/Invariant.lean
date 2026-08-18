/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Matroid.Graph.Iso.IsoTransport

/-!
# Isomorphism-invariant functions and properties of graphs

`IsoAction` transports graph-dependent data inside one carrier-universe pair. `IsoTransport`
transports it across carrier universes. This file says when an ordinary Lean function respects the
same-universe action, and supplies the logical closure instances used by graph properties.

There is no user-facing `Property`, `TypeFamily`, or `Family.Section` wrapper. Write the expression
itself:

```lean
Invariant (fun G ↦ 3 ≤ V(G).encard)
Equivariant (fun G ↦ V(G) → Prop) (fun G x ↦ ...)
```

An atomic proposition may instead register a universe-polymorphic `IsoTransport` instance. The
low-priority bridge `instInvariantOfPropAction` then recovers its ordinary `Invariant` instance;
logical `IsoTransport` instances below compose cross-universe properties just as the ordinary
`Invariant` instances compose same-universe properties.
-/

public section

open Set Function

namespace Graph

universe uV uE uO uO' uV' uE'

theorem iff_of_equiv {P Q : Prop} (e : P ≃ Q) : P ↔ Q := ⟨e, e.symm⟩

/-! ### Equivariance and ordinary invariance -/

/-- `f` is equivariant: the same isomorphism that carries `G` to `H` carries `f G` to `f H`. -/
class Equivariant (F : {V : Type uV} → {E : Type uE} → Graph V E → Sort uO) [IsoAction F]
    (f : {V : Type uV} → {E : Type uE} → (G : Graph V E) → F G) : Prop where
  /-- The naturality square. -/
  map_eq : ∀ {V V' : Type uV} {E E' : Type uE} {G : Graph V E} {H : Graph V' E'} (i : Iso G H),
    IsoAction.map i (f G) = f H

/-- Ordinary isomorphism invariance for a fixed codomain. -/
abbrev Invariant {R : Sort uO} (f : {V : Type uV} → {E : Type uE} → Graph V E → R) : Prop :=
  Equivariant (fun _ ↦ R) f

namespace Equivariant

variable {F : {V : Type uV} → {E : Type uE} → Graph V E → Sort uO} [IsoAction F]
  {f : {V : Type uV} → {E : Type uE} → (G : Graph V E) → F G}
  {V V' : Type uV} {E E' : Type uE} {G : Graph V E} {H : Graph V' E'}

  /-- Equivariant values are `IsoRelated` along every isomorphism. -/
theorem isoRelated [Equivariant F f] (i : Iso G H) : IsoRelated (f G) (f H) :=
  ⟨i, Equivariant.map_eq i⟩

/-- Naturality in pointwise form for a family of functions. -/
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

/-- Naturality for a predicate with one graph-dependent marked argument. -/
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

/-! ### The invariant interface -/

namespace Invariant

variable {R : Sort uO} {f : {V : Type uV} → {E : Type uE} → Graph V E → R}
  {V V' : Type uV} {E E' : Type uE} {G : Graph V E} {H : Graph V' E'}

/-- Equal values on isomorphic graphs. -/
theorem eq_of_iso [Invariant f] (i : Iso G H) : f G = f H :=
  Equivariant.map_eq (F := fun _ ↦ R) (f := f) i

theorem eq_of_isIsoTo [Invariant f] (h : G.IsIsoTo H) : f G = f H := eq_of_iso h.some

/-- Build invariance from one-directional preservation. -/
theorem of_imp {P : {V : Type uV} → {E : Type uE} → Graph V E → Prop}
    (h : ∀ {V V' : Type uV} {E E' : Type uE} {G : Graph V E} {H : Graph V' E'},
      Iso G H → P G → P H) : Invariant P where
  map_eq i := propext ⟨h i, h i.symm⟩

/-- Build invariance from an iff theorem. -/
theorem of_iff {P : {V : Type uV} → {E : Type uE} → Graph V E → Prop}
    (h : ∀ {V V' : Type uV} {E E' : Type uE} {G : Graph V E} {H : Graph V' E'},
      Iso G H → (P G ↔ P H)) : Invariant P where
  map_eq i := propext (h i)

/-- The usual proposition-valued form. -/
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

/-- A proposition-valued `IsoAction` already contains ordinary invariance. Low priority leaves the
specialized logical instances below as the normal resolution path. -/
instance (priority := 100) instInvariantOfPropAction
    (P : {V : Type uV} → {E : Type uE} → Graph V E → Prop) [IsoAction P] : Invariant P :=
  Invariant.of_iff fun i ↦ IsoAction.iff_of_iso (P := P) i

/-! ### Same-universe logical combinators -/

instance instNot (P : {V : Type uV} → {E : Type uE} → Graph V E → Prop) [Invariant P] :
    Invariant (fun G ↦ ¬ P G) :=
  Invariant.of_iff fun i ↦ not_congr (Invariant.iff_of_iso (P := P) i)

instance instAnd (P Q : {V : Type uV} → {E : Type uE} → Graph V E → Prop)
    [Invariant P] [Invariant Q] : Invariant (fun G ↦ P G ∧ Q G) :=
  Invariant.of_iff fun i ↦
    and_congr (Invariant.iff_of_iso (P := P) i) (Invariant.iff_of_iso (P := Q) i)

instance instOr (P Q : {V : Type uV} → {E : Type uE} → Graph V E → Prop)
    [Invariant P] [Invariant Q] : Invariant (fun G ↦ P G ∨ Q G) :=
  Invariant.of_iff fun i ↦
    or_congr (Invariant.iff_of_iso (P := P) i) (Invariant.iff_of_iso (P := Q) i)

instance instImp (P Q : {V : Type uV} → {E : Type uE} → Graph V E → Prop)
    [Invariant P] [Invariant Q] : Invariant (fun G ↦ P G → Q G) :=
  Invariant.of_iff fun i ↦
    imp_congr (Invariant.iff_of_iso (P := P) i) (Invariant.iff_of_iso (P := Q) i)

instance instIff (P Q : {V : Type uV} → {E : Type uE} → Graph V E → Prop)
    [Invariant P] [Invariant Q] : Invariant (fun G ↦ P G ↔ Q G) :=
  Invariant.of_iff fun i ↦
    iff_congr (Invariant.iff_of_iso (P := P) i) (Invariant.iff_of_iso (P := Q) i)

/-! ### Cross-universe logical combinators

These mirror the ordinary logical instances, but now the source and target propositions may be
separate universe instantiations. -/

instance instTransportAnd (P Q : {V : Type uV} → {E : Type uE} → Graph V E → Prop)
    (P' Q' : {V : Type uV'} → {E : Type uE'} → Graph V E → Prop) [tP : IsoTransport P P']
    [tQ : IsoTransport Q Q'] : IsoTransport (fun G ↦ P G ∧ Q G) (fun G ↦ P' G ∧ Q' G) :=
  IsoTransport.of_iff
    (fun i ↦ (iff_of_equiv (tP.sourceAction.map i)).and (iff_of_equiv (tQ.sourceAction.map i)))
    (fun i ↦ (iff_of_equiv (tP.targetAction.map i)).and (iff_of_equiv (tQ.targetAction.map i)))
    (fun i ↦ (iff_of_equiv (tP.map i)).and (iff_of_equiv (tQ.map i)))

instance instTransportOr (P Q : {V : Type uV} → {E : Type uE} → Graph V E → Prop)
    (P' Q' : {V : Type uV'} → {E : Type uE'} → Graph V E → Prop) [tP : IsoTransport P P']
    [tQ : IsoTransport Q Q'] : IsoTransport (fun G ↦ P G ∨ Q G) (fun G ↦ P' G ∨ Q' G) :=
  IsoTransport.of_iff
    (fun i ↦ (iff_of_equiv (tP.sourceAction.map i)).or (iff_of_equiv (tQ.sourceAction.map i)))
    (fun i ↦ (iff_of_equiv (tP.targetAction.map i)).or (iff_of_equiv (tQ.targetAction.map i)))
    (fun i ↦ (iff_of_equiv (tP.map i)).or (iff_of_equiv (tQ.map i)))

instance instTransportIff (P Q : {V : Type uV} → {E : Type uE} → Graph V E → Prop)
    (P' Q' : {V : Type uV'} → {E : Type uE'} → Graph V E → Prop) [tP : IsoTransport P P']
    [tQ : IsoTransport Q Q'] : IsoTransport (fun G ↦ P G ↔ Q G) (fun G ↦ P' G ↔ Q' G) :=
  IsoTransport.of_iff
    (fun i ↦ (iff_of_equiv (tP.sourceAction.map i)).iff (iff_of_equiv (tQ.sourceAction.map i)))
    (fun i ↦ (iff_of_equiv (tP.targetAction.map i)).iff (iff_of_equiv (tQ.targetAction.map i)))
    (fun i ↦ (iff_of_equiv (tP.map i)).iff (iff_of_equiv (tQ.map i)))

/-! ### Quantifiers over graph-dependent data -/

instance instExists (A : {V : Type uV} → {E : Type uE} → Graph V E → Type uO) [IsoAction A]
    (P : {V : Type uV} → {E : Type uE} → (G : Graph V E) → A G → Prop)
    [Equivariant (fun G ↦ A G → Prop) P] : Invariant (fun G ↦ ∃ x, P G x) :=
  Invariant.of_iff fun i ↦ by
    refine ⟨fun ⟨x, hx⟩ ↦ ⟨IsoAction.map (F := A) i x, (Equivariant.iff_map P i x).1 hx⟩,
      fun ⟨y, hy⟩ ↦ ⟨(IsoAction.map (F := A) i).symm y, (Equivariant.iff_map P i _).2 ?_⟩⟩
    rwa [Equiv.apply_symm_apply]

instance instForall (A : {V : Type uV} → {E : Type uE} → Graph V E → Type uO) [IsoAction A]
    (P : {V : Type uV} → {E : Type uE} → (G : Graph V E) → A G → Prop)
    [Equivariant (fun G ↦ A G → Prop) P] : Invariant (fun G ↦ ∀ x, P G x) :=
  Invariant.of_iff fun i ↦ by
    refine ⟨fun h y ↦ ?_, fun h x ↦ (Equivariant.iff_map P i x).2 (h _)⟩
    have := (Equivariant.iff_map P i ((IsoAction.map (F := A) i).symm y)).1 (h _)
    rwa [Equiv.apply_symm_apply] at this

/-! ### Ambient-membership bridges -/

instance instForallMemVertexSet (P : {V : Type uV} → {E : Type uE} → Graph V E → V → Prop)
    [Equivariant (fun {V E} (G : Graph V E) ↦ V(G) → Prop)
      (fun {V E} (G : Graph V E) ↦ fun x : V(G) ↦ P G x.1)] :
    Invariant (fun {V E} (G : Graph V E) ↦ ∀ x ∈ V(G), P G x) :=
  Invariant.of_iff fun i ↦ by
    simpa [Subtype.forall] using Invariant.iff_of_iso
      (P := fun {V E} (G : Graph V E) ↦ ∀ x : V(G), P G x.1) i

instance instExistsMemVertexSet (P : {V : Type uV} → {E : Type uE} → Graph V E → V → Prop)
    [Equivariant (fun {V E} (G : Graph V E) ↦ V(G) → Prop)
      (fun {V E} (G : Graph V E) ↦ fun x : V(G) ↦ P G x.1)] :
    Invariant (fun {V E} (G : Graph V E) ↦ ∃ x ∈ V(G), P G x) :=
  Invariant.of_iff fun i ↦ by
    simpa [Subtype.exists] using
      Invariant.iff_of_iso (P := fun {V E} (G : Graph V E) ↦ ∃ x : V(G), P G x.1) i

instance instForallMemEdgeSet (P : {V : Type uV} → {E : Type uE} → Graph V E → E → Prop)
    [Equivariant (fun {V E} (G : Graph V E) ↦ E(G) → Prop)
      (fun {V E} (G : Graph V E) ↦ fun e : E(G) ↦ P G e.1)] :
    Invariant (fun {V E} (G : Graph V E) ↦ ∀ e ∈ E(G), P G e) :=
  Invariant.of_iff fun i ↦ by
    simpa [Subtype.forall] using
      Invariant.iff_of_iso (P := fun {V E} (G : Graph V E) ↦ ∀ e : E(G), P G e.1) i

instance instExistsMemEdgeSet (P : {V : Type uV} → {E : Type uE} → Graph V E → E → Prop)
    [Equivariant (fun {V E} (G : Graph V E) ↦ E(G) → Prop)
      (fun {V E} (G : Graph V E) ↦ fun e : E(G) ↦ P G e.1)] :
    Invariant (fun {V E} (G : Graph V E) ↦ ∃ e ∈ E(G), P G e) :=
  Invariant.of_iff fun i ↦ by
    simpa [Subtype.exists] using
      Invariant.iff_of_iso (P := fun {V E} (G : Graph V E) ↦ ∃ e : E(G), P G e.1) i

/-! ### Closure of `Equivariant` -/

instance instPair (A : {V : Type uV} → {E : Type uE} → Graph V E → Type uO) [IsoAction A]
    (B : {V : Type uV} → {E : Type uE} → Graph V E → Type uO') [IsoAction B]
    (f : {V : Type uV} → {E : Type uE} → (G : Graph V E) → A G) [Equivariant A f]
    (g : {V : Type uV} → {E : Type uE} → (G : Graph V E) → B G) [Equivariant B g] :
    Equivariant (fun G ↦ A G × B G) (fun G ↦ (f G, g G)) where
  map_eq i := by
    show (IsoAction.map i (f _), IsoAction.map i (g _)) = _
    rw [Equivariant.map_eq (F := A) i, Equivariant.map_eq (F := B) i]

/-- A subtype cut out by an equivariant predicate carries a same-universe action. -/
noncomputable instance instSubtype (A : {V : Type uV} → {E : Type uE} → Graph V E → Type uO)
    [IsoAction A] (P : {V : Type uV} → {E : Type uE} → (G : Graph V E) → A G → Prop)
    [Equivariant (fun G ↦ A G → Prop) P] : IsoAction (fun G ↦ {x : A G // P G x}) where
  map i := Equiv.subtypeEquiv (IsoAction.map i) fun x ↦ Equivariant.iff_map P i x
  map_id G x := Subtype.ext <| by simpa using IsoAction.map_id (F := A) G x.1
  map_comp i j x := Subtype.ext <| by simpa using IsoAction.map_comp (F := A) i j x.1

/-! ### Existence and cardinality properties of transported data -/

instance instNonempty (A : {V : Type uV} → {E : Type uE} → Graph V E → Sort uO) [IsoAction A] :
    Invariant (fun G ↦ Nonempty (A G)) :=
  Invariant.of_iff fun i ↦ (IsoAction.map (F := A) i).nonempty_congr

instance instIsEmpty (A : {V : Type uV} → {E : Type uE} → Graph V E → Sort uO) [IsoAction A] :
    Invariant (fun G ↦ IsEmpty (A G)) :=
  Invariant.of_iff fun i ↦ (IsoAction.map (F := A) i).isEmpty_congr

instance instSubsingleton (A : {V : Type uV} → {E : Type uE} → Graph V E → Type uO) [IsoAction A] :
    Invariant (fun G ↦ Subsingleton (A G)) :=
  Invariant.of_iff fun i ↦ (IsoAction.map (F := A) i).subsingleton_congr

instance instTransportNonempty (A : {V : Type uV} → {E : Type uE} → Graph V E → Sort uO)
    (A' : {V : Type uV'} → {E : Type uE'} → Graph V E → Sort uO') [t : IsoTransport A A'] :
    IsoTransport (fun G ↦ Nonempty (A G)) (fun G ↦ Nonempty (A' G)) :=
  IsoTransport.of_iff (fun i ↦ (t.sourceAction.map i).nonempty_congr)
    (fun i ↦ (t.targetAction.map i).nonempty_congr)
    (fun i ↦ (t.map i).nonempty_congr)

instance instTransportIsEmpty (A : {V : Type uV} → {E : Type uE} → Graph V E → Sort uO)
    (A' : {V : Type uV'} → {E : Type uE'} → Graph V E → Sort uO') [t : IsoTransport A A'] :
    IsoTransport (fun G ↦ IsEmpty (A G)) (fun G ↦ IsEmpty (A' G)) :=
  IsoTransport.of_iff (fun i ↦ (t.sourceAction.map i).isEmpty_congr)
    (fun i ↦ (t.targetAction.map i).isEmpty_congr)
    (fun i ↦ (t.map i).isEmpty_congr)

instance instTransportSubsingleton (A : {V : Type uV} → {E : Type uE} → Graph V E → Type uO)
    (A' : {V : Type uV'} → {E : Type uE'} → Graph V E → Type uO') [t : IsoTransport A A'] :
    IsoTransport (fun G ↦ Subsingleton (A G)) (fun G ↦ Subsingleton (A' G)) :=
  IsoTransport.of_iff (fun i ↦ (t.sourceAction.map i).subsingleton_congr)
    (fun i ↦ (t.targetAction.map i).subsingleton_congr)
    (fun i ↦ (t.map i).subsingleton_congr)

end Graph
