/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Matroid.ForMathlib.Iso.Invariant
public import Matroid.Graph.Iso.Equiv

/-!
# Graph adapter for generic `IsoInvariant`

All structural and logical closure instances come from the generic core. This file only reindexes
unbundled graph observables through `Graph.IsoObj` and provides graph-facing convenience theorems.
-/

@[expose] public section

namespace Graph

universe uV₁ uE₁ uF₁ uV₂ uE₂ uF₂ uV₃ uE₃ uF₃ uV₄ uE₄ uF₄ uA₁ uA₂ uB₁ uB₂

abbrev Observable (F : Family.{uV₁, uE₁, uF₁}) :=
  {V : Type uV₁} → {E : Type uE₁} → (G : Graph V E) → F G

/-- Reindex an unbundled graph observable by the bundled generic-core index.

Implementation detail of the generic-core adapter; ordinary users should reach the
domain-facing wrappers instead of naming this. -/
protected abbrev Observable.bundle {F : Family.{uV₁, uE₁, uF₁}} (f : Observable F) :
    _root_.Observable F.bundle := fun X ↦ @f X.V X.E X.graph

abbrev IsoInvariant {F : Family.{uV₁, uE₁, uF₁}} {F' : Family.{uV₂, uE₂, uF₂}}
    [IsoEquiv F F'] (f : Observable F) (f' : Observable F') :=
  _root_.IsoInvariant (Observable.bundle f) (Observable.bundle f')

namespace IsoInvariant

/-- Graph-facing reindexing of an invariant observable along a bundled `IsoMap`. -/
theorem reindex {f : IsoObj.{uV₁, uE₁} → IsoObj.{uV₃, uE₃}}
    {f' : IsoObj.{uV₂, uE₂} → IsoObj.{uV₄, uE₄}} [m : _root_.IsoMap f f']
    {F : Family.{uV₃, uE₃, uF₃}} {F' : Family.{uV₄, uE₄, uF₄}} [IsoEquiv F F']
    (x : Observable F) (x' : Observable F') [IsoInvariant x x'] :
    IsoInvariant (F := Family.reindex f F) (F' := Family.reindex f' F')
      (fun {V} {E} G ↦ @x (f ⟨V, E, G⟩).V (f ⟨V, E, G⟩).E (f ⟨V, E, G⟩).graph)
      (fun {V} {E} G ↦ @x' (f' ⟨V, E, G⟩).V (f' ⟨V, E, G⟩).E (f' ⟨V, E, G⟩).graph) := by
  change _root_.IsoInvariant
    (F := _root_.Reindex f F.bundle) (F' := _root_.Reindex f' F'.bundle)
    (fun X ↦ Observable.bundle x (f X)) (fun Y ↦ Observable.bundle x' (f' Y))
  exact _root_.IsoInvariant.reindex (f := f) (f' := f') (F := F.bundle) (F' := F'.bundle)
    (x := Observable.bundle x) (x' := Observable.bundle x')

/-- Proposition-valued graph invariance as an iff. -/
theorem iff_of_iso {P : {V : Type uV₁} → {E : Type uE₁} → Graph V E → Prop}
    {P' : {V : Type uV₂} → {E : Type uE₂} → Graph V E → Prop} [IsoInvariant P P']
    {V : Type uV₁} {E : Type uE₁} {V' : Type uV₂} {E' : Type uE₂}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) : P G ↔ P' H :=
  _root_.IsoInvariant.iff_of_iso (P := Observable.bundle P) (P' := Observable.bundle P')
    (X := ⟨V, E, G⟩) (Y := ⟨V', E', H⟩) i

/-- Forward transport of a proposition-valued graph invariant. -/
theorem map {P : {V : Type uV₁} → {E : Type uE₁} → Graph V E → Prop}
    {P' : {V : Type uV₂} → {E : Type uE₂} → Graph V E → Prop} [IsoInvariant P P']
    {V : Type uV₁} {E : Type uE₁} {V' : Type uV₂} {E' : Type uE₂}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) : P G → P' H := (iff_of_iso i).mp

/-- Backward transport of a proposition-valued graph invariant. -/
theorem comap {P : {V : Type uV₁} → {E : Type uE₁} → Graph V E → Prop}
    {P' : {V : Type uV₂} → {E : Type uE₂} → Graph V E → Prop} [IsoInvariant P P']
    {V : Type uV₁} {E : Type uE₁} {V' : Type uV₂} {E' : Type uE₂}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) : P' H → P G := (iff_of_iso i).mpr

/-! ### Graph-facing combinators

These mirror the generic `_root_.IsoInvariant` combinators with the bundling supplied, so that
ordinary users never mention `Observable.bundle`. -/

/-- Pointwise iff for an invariant binary predicate. -/
theorem iff_map₂ {A : TypeFamily.{uV₁, uE₁, uA₁}} {A' : TypeFamily.{uV₂, uE₂, uA₂}}
    [IsoEquiv A A'] {B : TypeFamily.{uV₁, uE₁, uB₁}} {B' : TypeFamily.{uV₂, uE₂, uB₂}}
    [IsoEquiv B B']
    {P : Observable (fun G ↦ A G → B G → Prop)} {P' : Observable (fun G ↦ A' G → B' G → Prop)}
    [IsoInvariant P P'] {V : Type uV₁} {E : Type uE₁} {V' : Type uV₂} {E' : Type uE₂}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) (x : A G) (y : B G) :
    P G x y ↔ P' H (IsoEquiv.map (F := A) (F' := A') i x) (IsoEquiv.map (F := B) (F' := B') i y) :=
  _root_.IsoInvariant.iff_map₂ (P := Observable.bundle P) (P' := Observable.bundle P')
    (X := ⟨V, E, G⟩) (Y := ⟨V', E', H⟩) i x y

/-- Applying an invariant function-valued observable to an invariant argument. -/
theorem app {A : Family.{uV₁, uE₁, uA₁}} {A' : Family.{uV₂, uE₂, uA₂}} [IsoEquiv A A']
    {B : Family.{uV₁, uE₁, uB₁}} {B' : Family.{uV₂, uE₂, uB₂}} [IsoEquiv B B']
    (f : Observable (fun G ↦ A G → B G)) (f' : Observable (fun G ↦ A' G → B' G))
    (x : Observable A) (x' : Observable A') [IsoInvariant f f'] [IsoInvariant x x'] :
    IsoInvariant (fun G ↦ f G (x G)) (fun G ↦ f' G (x' G)) :=
  _root_.IsoInvariant.app (Observable.bundle f) (Observable.bundle f')
    (Observable.bundle x) (Observable.bundle x')

/-- Pair two invariant observables. -/
theorem pair {A : TypeFamily.{uV₁, uE₁, uA₁}} {A' : TypeFamily.{uV₂, uE₂, uA₂}} [IsoEquiv A A']
    {B : TypeFamily.{uV₁, uE₁, uB₁}} {B' : TypeFamily.{uV₂, uE₂, uB₂}} [IsoEquiv B B']
    (x : Observable A) (x' : Observable A') (y : Observable B) (y' : Observable B')
    [IsoInvariant x x'] [IsoInvariant y y'] :
    IsoInvariant (fun G ↦ (x G, y G)) (fun G ↦ (x' G, y' G)) :=
  _root_.IsoInvariant.pair (Observable.bundle x) (Observable.bundle x')
    (Observable.bundle y) (Observable.bundle y')

/-- Turn an invariant predicate into the invariant set it defines. -/
theorem setOf {A : TypeFamily.{uV₁, uE₁, uA₁}} {A' : TypeFamily.{uV₂, uE₂, uA₂}} [IsoEquiv A A']
    (P : Observable (fun G ↦ A G → Prop)) (P' : Observable (fun G ↦ A' G → Prop))
    [IsoInvariant P P'] : IsoInvariant (fun G ↦ {x : A G | P G x}) (fun G ↦ {y : A' G | P' G y}) :=
  _root_.IsoInvariant.setOf (Observable.bundle P) (Observable.bundle P')

/-- Postcompose a fixed-output invariant observable by an arbitrary fixed function. -/
theorem comp_right {A : Family.{uV₁, uE₁, uA₁}} {A' : Family.{uV₂, uE₂, uA₂}} [IsoEquiv A A']
    {B : Sort*} {D : Sort*} (f : Observable (fun G ↦ A G → B)) (f' : Observable (fun G ↦ A' G → B))
    [IsoInvariant f f'] (s : B → D) : IsoInvariant (fun G x ↦ s (f G x)) (fun G y ↦ s (f' G y)) :=
  _root_.IsoInvariant.comp_right (Observable.bundle f) (Observable.bundle f') s

/-- Precompose an invariant function-valued observable by an invariant endomorphism. -/
theorem comp {A : Family.{uV₁, uE₁, uA₁}} {A' : Family.{uV₂, uE₂, uA₂}} [IsoEquiv A A']
    {B : Family.{uV₁, uE₁, uB₁}} {B' : Family.{uV₂, uE₂, uB₂}} [IsoEquiv B B']
    (f : Observable (fun G ↦ A G → B G)) (f' : Observable (fun G ↦ A' G → B' G))
    [IsoInvariant f f'] (a : Observable (fun G ↦ A G → A G))
    (a' : Observable (fun G ↦ A' G → A' G)) [IsoInvariant a a'] :
    IsoInvariant (fun G x ↦ f G (a G x)) (fun G y ↦ f' G (a' G y)) :=
  _root_.IsoInvariant.comp (Observable.bundle f) (Observable.bundle f')
    (Observable.bundle a) (Observable.bundle a')

/-- Combine two invariant observables sharing a transported argument by a fixed operation. -/
theorem combine {Ctx : Family.{uV₁, uE₁, uA₁}} {Ctx' : Family.{uV₂, uE₂, uA₂}}
    [IsoEquiv Ctx Ctx'] {A : Sort*} {B : Sort*} {D : Sort*}
    (f : Observable (fun G ↦ Ctx G → A)) (f' : Observable (fun G ↦ Ctx' G → A))
    (g : Observable (fun G ↦ Ctx G → B)) (g' : Observable (fun G ↦ Ctx' G → B))
    [IsoInvariant f f'] [IsoInvariant g g'] (op : A → B → D) :
    IsoInvariant (fun G x ↦ op (f G x) (g G x)) (fun G y ↦ op (f' G y) (g' G y)) :=
  _root_.IsoInvariant.combine (Observable.bundle f) (Observable.bundle f')
    (Observable.bundle g) (Observable.bundle g') op

end IsoInvariant

end Graph
