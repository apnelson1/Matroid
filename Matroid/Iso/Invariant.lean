/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Matroid.ForMathlib.Iso.Invariant
public import Matroid.Iso.Equiv
public import Matroid.ForMathlib.Matroid.Closure

/-!
# Matroid adapter for generic `IsoInvariant`

The invariant API is phrased intrinsically on the ground subtype `M.E`. This removes the special
empty-target branch needed by the old ambient `TransferClass`: `Matroid.isoMap` is an actual
isomorphism on ground subtypes even when the target ambient type is empty.
-/

@[expose] public section

open Set Function

namespace Matroid

universe uα₁ uα₂ uα₃ uα₄ uF₁ uF₂ uF₃ uF₄ uA₁ uA₂ uB₁ uB₂

abbrev Observable (F : Family.{uα₁, uF₁}) := {α : Type uα₁} → (M : Matroid α) → F M

/-- Reindex an unbundled matroid observable by the bundled generic-core index.

Implementation detail of the generic-core adapter; ordinary users should reach the
domain-facing wrappers instead of naming this. -/
protected abbrev Observable.bundle {F : Family.{uα₁, uF₁}} (f : Observable F) :
    _root_.Observable F.bundle := fun X ↦ @f X.α X.matroid

@[simp] theorem Observable.bundle_apply {F : Family.{uα₁, uF₁}} (f : Observable F)
    (X : IsoObj.{uα₁}) : Observable.bundle f X = f X.matroid := rfl

abbrev IsoInvariant {F : Family.{uα₁, uF₁}} {F' : Family.{uα₂, uF₂}}
    [IsoEquiv F F'] (f : Observable F) (f' : Observable F') :=
  _root_.IsoInvariant (Observable.bundle f) (Observable.bundle f')

namespace IsoInvariant

/-- Matroid-facing reindexing of an invariant observable along a bundled `IsoMap`. -/
theorem reindex {f : IsoObj.{uα₁} → IsoObj.{uα₃}} {f' : IsoObj.{uα₂} → IsoObj.{uα₄}}
    [m : _root_.IsoMap f f'] {F : Family.{uα₃, uF₃}} {F' : Family.{uα₄, uF₄}} [IsoEquiv F F']
    (x : Observable F) (x' : Observable F') [IsoInvariant x x'] :
    IsoInvariant (F := Family.reindex f F) (F' := Family.reindex f' F')
      (fun {α} M ↦ @x (f ⟨α, M⟩).α (f ⟨α, M⟩).matroid)
      (fun {α} M ↦ @x' (f' ⟨α, M⟩).α (f' ⟨α, M⟩).matroid) := by
  change _root_.IsoInvariant
    (F := _root_.Reindex f F.bundle) (F' := _root_.Reindex f' F'.bundle)
    (fun X ↦ x.bundle (f X)) (fun Y ↦ x'.bundle (f' Y))
  exact _root_.IsoInvariant.reindex (f := f) (f' := f') (F := F.bundle) (F' := F'.bundle)
    (x := x.bundle) (x' := x'.bundle)

/-- Iff form of a proposition-valued matroid invariant. -/
theorem iff_of_iso {P : {α : Type uα₁} → Matroid α → Prop} {P' : {α : Type uα₂} → Matroid α → Prop}
    [IsoInvariant P P'] {α : Type uα₁} {β : Type uα₂}
    {M : Matroid α} {N : Matroid β} (i : Matroid.Iso M N) : P M ↔ P' N :=
  _root_.IsoInvariant.iff_of_iso (P := Observable.bundle P) (P' := Observable.bundle P')
    (X := ⟨α, M⟩) (Y := ⟨β, N⟩) i

/-- Arbitrary-output map form of an invariant function-valued observable.  When the output
family is constant this is the direct replacement for `InvariantFun.map_eq`; unlike the old API,
the output family may itself vary with the matroid. -/
theorem map_apply_map {A : Family.{uα₁, uA₁}} {A' : Family.{uα₂, uA₂}} [a : IsoEquiv A A']
    {B : Family.{uα₁, uB₁}} {B' : Family.{uα₂, uB₂}} [b : IsoEquiv B B']
    {F : Observable (fun M ↦ A M → B M)} {F' : Observable (fun M ↦ A' M → B' M)}
    [IsoInvariant F F'] {α : Type uα₁} {β : Type uα₂} {M : Matroid α} {f : α → β} (hf : InjOn f M.E)
    (x : A M) : IsoEquiv.map (F := B) (F' := B') (Matroid.isoMap M f hf) (F M x) =
    F' (M.map f hf) (IsoEquiv.map (F := A) (F' := A') (Matroid.isoMap M f hf) x) :=
  _root_.IsoInvariant.map_apply (f := Observable.bundle F) (f' := Observable.bundle F')
    (X := ⟨α, M⟩) (Y := ⟨β, M.map f hf⟩) (Matroid.isoMap M f hf) x

/-- Any intrinsic invariant immediately gives its `Matroid.map` consequence via `isoMap`. -/
theorem iff_map {A : TypeFamily.{uα₁, uF₁}} {A' : TypeFamily.{uα₂, uF₂}} [a : IsoEquiv A A']
    {P : Observable (fun M ↦ A M → Prop)} {P' : Observable (fun M ↦ A' M → Prop)}
    [IsoInvariant P P'] {α : Type uα₁} {β : Type uα₂} {M : Matroid α} {f : α → β}
    (hf : InjOn f M.E) (x : A M) :
    P M x ↔ P' (M.map f hf) (IsoEquiv.map (F := A) (F' := A') (Matroid.isoMap M f hf) x) :=
  _root_.IsoInvariant.iff_map (P := Observable.bundle P) (P' := Observable.bundle P')
    (X := ⟨α, M⟩) (Y := ⟨β, M.map f hf⟩) (Matroid.isoMap M f hf) x

/-- Pointwise iff for an invariant unary predicate along a matroid isomorphism. -/
theorem iff_map_iso {A : TypeFamily.{uα₁, uA₁}} {A' : TypeFamily.{uα₂, uA₂}} [a : IsoEquiv A A']
    {P : Observable (fun M ↦ A M → Prop)} {P' : Observable (fun M ↦ A' M → Prop)}
    [IsoInvariant P P'] {α : Type uα₁} {β : Type uα₂} {M : Matroid α} {N : Matroid β}
    (i : Matroid.Iso M N) (x : A M) : P M x ↔ P' N (IsoEquiv.map (F := A) (F' := A') i x) :=
  _root_.IsoInvariant.iff_map (P := P.bundle) (P' := P'.bundle) (X := (⟨α, M⟩ : IsoObj.{uα₁}))
    (Y := (⟨β, N⟩ : IsoObj.{uα₂})) i x

/-- Target-argument form of `iff_map`: every intrinsic datum of `M.map f hf` has a unique source
preimage because `isoMap` acts by an equivalence on the active ground data. -/
theorem iff_map_target {A : TypeFamily.{uα₁, uF₁}} {A' : TypeFamily.{uα₂, uF₂}} [a : IsoEquiv A A']
    {P : Observable (fun M ↦ A M → Prop)} {P' : Observable (fun M ↦ A' M → Prop)}
    [IsoInvariant P P'] {α : Type uα₁} {β : Type uα₂} {M : Matroid α} {f : α → β}
    (hf : InjOn f M.E) (y : A' (M.map f hf)) :
    P M ((IsoEquiv.map (F := A) (F' := A') (Matroid.isoMap M f hf)).symm y) ↔ P' (M.map f hf) y :=
  _root_.IsoInvariant.iff_comap (P := Observable.bundle P) (P' := Observable.bundle P')
    (X := ⟨α, M⟩) (Y := ⟨β, M.map f hf⟩) (Matroid.isoMap M f hf) y

/-! ### Matroid-facing combinators

These mirror the generic `_root_.IsoInvariant` combinators with the bundling supplied, so that
ordinary users never mention `Observable.bundle`. -/

/-- Pointwise iff for an invariant binary predicate. -/
theorem iff_map₂ {A : TypeFamily.{uα₁, uA₁}} {A' : TypeFamily.{uα₂, uA₂}} [a : IsoEquiv A A']
    {B : TypeFamily.{uα₁, uB₁}} {B' : TypeFamily.{uα₂, uB₂}} [b : IsoEquiv B B']
    {P : Observable (fun M ↦ A M → B M → Prop)} {P' : Observable (fun M ↦ A' M → B' M → Prop)}
    [IsoInvariant P P'] {α : Type uα₁} {β : Type uα₂} {M : Matroid α} {N : Matroid β}
    (i : Matroid.Iso M N) (x : A M) (y : B M) :
    P M x y ↔ P' N (IsoEquiv.map (F := A) (F' := A') i x) (IsoEquiv.map (F := B) (F' := B') i y) :=
  _root_.IsoInvariant.iff_map₂ (P := Observable.bundle P) (P' := Observable.bundle P')
    (X := (⟨α, M⟩ : IsoObj.{uα₁})) (Y := (⟨β, N⟩ : IsoObj.{uα₂})) i x y

/-- Applying an invariant function-valued observable to an invariant argument. -/
theorem app {A : Family.{uα₁, uA₁}} {A' : Family.{uα₂, uA₂}} [IsoEquiv A A']
    {B : Family.{uα₁, uB₁}} {B' : Family.{uα₂, uB₂}} [IsoEquiv B B']
    (f : Observable (fun M ↦ A M → B M)) (f' : Observable (fun N ↦ A' N → B' N))
    (x : Observable A) (x' : Observable A') [IsoInvariant f f'] [IsoInvariant x x'] :
    IsoInvariant (fun M ↦ f M (x M)) (fun N ↦ f' N (x' N)) :=
  _root_.IsoInvariant.app f.bundle f'.bundle x.bundle x'.bundle

/-- Pair two invariant observables. -/
theorem pair {A : TypeFamily.{uα₁, uA₁}} {A' : TypeFamily.{uα₂, uA₂}} [IsoEquiv A A']
    {B : TypeFamily.{uα₁, uB₁}} {B' : TypeFamily.{uα₂, uB₂}} [IsoEquiv B B']
    (x : Observable A) (x' : Observable A') (y : Observable B) (y' : Observable B')
    [IsoInvariant x x'] [IsoInvariant y y'] :
    IsoInvariant (fun M ↦ (x M, y M)) (fun N ↦ (x' N, y' N)) :=
  _root_.IsoInvariant.pair x.bundle x'.bundle y.bundle y'.bundle

/-- Turn an invariant predicate into the invariant set it defines. -/
theorem setOf {A : TypeFamily.{uα₁, uA₁}} {A' : TypeFamily.{uα₂, uA₂}} [IsoEquiv A A']
    (P : Observable (fun M ↦ A M → Prop)) (P' : Observable (fun N ↦ A' N → Prop))
    [IsoInvariant P P'] : IsoInvariant (fun M ↦ {x : A M | P M x}) (fun N ↦ {y : A' N | P' N y}) :=
  _root_.IsoInvariant.setOf P.bundle P'.bundle

/-- Postcompose a fixed-output invariant observable by an arbitrary fixed function. -/
theorem comp_right {A : Family.{uα₁, uA₁}} {A' : Family.{uα₂, uA₂}} [IsoEquiv A A']
    {B : Sort*} {D : Sort*} (f : Observable (fun M ↦ A M → B)) (f' : Observable (fun N ↦ A' N → B))
    [IsoInvariant f f'] (s : B → D) : IsoInvariant (fun M x ↦ s (f M x)) (fun N y ↦ s (f' N y)) :=
  _root_.IsoInvariant.comp_right f.bundle f'.bundle s

/-- Precompose an invariant function-valued observable by an invariant endomorphism. -/
theorem comp {A : Family.{uα₁, uA₁}} {A' : Family.{uα₂, uA₂}} [IsoEquiv A A']
    {B : Family.{uα₁, uB₁}} {B' : Family.{uα₂, uB₂}} [IsoEquiv B B']
    (f : Observable (fun M ↦ A M → B M)) (f' : Observable (fun N ↦ A' N → B' N))
    [IsoInvariant f f'] (a : Observable (fun M ↦ A M → A M))
    (a' : Observable (fun N ↦ A' N → A' N)) [IsoInvariant a a'] :
    IsoInvariant (fun M x ↦ f M (a M x)) (fun N y ↦ f' N (a' N y)) :=
  _root_.IsoInvariant.comp f.bundle f'.bundle a.bundle a'.bundle

/-- Combine two invariant observables sharing a transported argument by a fixed operation. -/
theorem combine {Ctx : Family.{uα₁, uA₁}} {Ctx' : Family.{uα₂, uA₂}} [IsoEquiv Ctx Ctx']
    {A : Sort*} {B : Sort*} {D : Sort*}
    (f : Observable (fun M ↦ Ctx M → A)) (f' : Observable (fun N ↦ Ctx' N → A))
    (g : Observable (fun M ↦ Ctx M → B)) (g' : Observable (fun N ↦ Ctx' N → B))
    [IsoInvariant f f'] [IsoInvariant g g'] (op : A → B → D) :
    IsoInvariant (fun M x ↦ op (f M x) (g M x)) (fun N y ↦ op (f' N y) (g' N y)) :=
  _root_.IsoInvariant.combine f.bundle f'.bundle g.bundle g'.bundle op

end IsoInvariant

/-! ## Intrinsic versions of the predicates covered by the current matroid invariant system -/

abbrev IndepObs : Observable (fun {α} (M : Matroid α) ↦ Set M.E → Prop) :=
  fun M X ↦ M.Indep (↑X : Set _)

abbrev DepObs : Observable (fun {α} (M : Matroid α) ↦ Set M.E → Prop) :=
  fun M X ↦ M.Dep (↑X : Set _)

abbrev IsBaseObs : Observable (fun {α} (M : Matroid α) ↦ Set M.E → Prop) :=
  fun M X ↦ M.IsBase (↑X : Set _)

abbrev CoindepObs : Observable (fun {α} (M : Matroid α) ↦ Set M.E → Prop) :=
  fun M X ↦ M.Coindep (↑X : Set _)

abbrev CodepObs : Observable (fun {α} (M : Matroid α) ↦ Set M.E → Prop) :=
  fun M X ↦ M.Codep (↑X : Set _)

abbrev SpanningObs : Observable (fun {α} (M : Matroid α) ↦ Set M.E → Prop) :=
  fun M X ↦ M.Spanning (↑X : Set _)

abbrev NonspanningObs : Observable (fun {α} (M : Matroid α) ↦ Set M.E → Prop) :=
  fun M X ↦ M.Nonspanning (↑X : Set _)

abbrev IsBasisObs : Observable (fun {α} (M : Matroid α) ↦ Set M.E → Set M.E → Prop) :=
  fun M I X ↦ M.IsBasis (↑I : Set _) (↑X : Set _)

noncomputable abbrev EncardObs : Observable (fun {α} (M : Matroid α) ↦ Set M.E → ℕ∞) :=
  fun _ X ↦ X.encard

instance instIsoInvariantIndep : IsoInvariant IndepObs.{uα₁} IndepObs.{uα₂} :=
  _root_.IsoInvariant.of_iff_map _ _ fun i _ ↦ i.indep_image_iff

instance instIsoInvariantDep : IsoInvariant DepObs.{uα₁} DepObs.{uα₂} :=
  _root_.IsoInvariant.of_iff_map _ _ fun i _ ↦ i.dep_image_iff

instance instIsoInvariantIsBase : IsoInvariant IsBaseObs.{uα₁} IsBaseObs.{uα₂} :=
  _root_.IsoInvariant.of_iff_map _ _ fun i _ ↦ i.isBase_image_iff

instance instIsoInvariantIsBasis : IsoInvariant IsBasisObs.{uα₁} IsBasisObs.{uα₂} :=
  _root_.IsoInvariant.of_iff_map₂ _ _ fun i _ _ ↦ i.isBasis_image_iff

instance instIsoInvariantCoindep : IsoInvariant CoindepObs.{uα₁} CoindepObs.{uα₂} :=
  _root_.IsoInvariant.of_iff_map _ _ fun i X ↦ by
    simp only [Observable.bundle_apply, CoindepObs, coindep_def]
    have h := i.dual.indep_image_iff (I := X)
    rw [Iso.dual_image'] at h
    exact h

instance instIsoInvariantCodep : IsoInvariant CodepObs.{uα₁} CodepObs.{uα₂} :=
  _root_.IsoInvariant.of_iff_map _ _ fun i X ↦ by
    simp only [Observable.bundle_apply, CodepObs]
    rw [codep_def, codep_def]
    have h := i.dual.dep_image_iff (D := X)
    rw [Iso.dual_image'] at h
    exact h

instance instIsoInvariantSpanning : IsoInvariant SpanningObs.{uα₁} SpanningObs.{uα₂} :=
  _root_.IsoInvariant.of_iff_map _ _ fun i X ↦ i.spanning_iff X

instance instIsoInvariantNonspanning : IsoInvariant NonspanningObs.{uα₁} NonspanningObs.{uα₂} :=
  _root_.IsoInvariant.of_iff_map _ _ fun i X ↦ by
    simp only [Observable.bundle_apply, NonspanningObs]
    rw [nonspanning_iff, nonspanning_iff, and_iff_left (Subtype.coe_image_subset _ _),
      and_iff_left (Subtype.coe_image_subset _ _)]
    exact not_congr (i.spanning_iff X)

/-- Cardinal upper bounds on supported sets, corresponding to `InvariantSetPred.cardLE`. -/
instance instIsoInvariantEncardLE (k : ℕ∞) : IsoInvariant
    (fun {α : Type uα₁} (M : Matroid α) (X : Set M.E) ↦ X.encard ≤ k)
    (fun {α : Type uα₂} (M : Matroid α) (X : Set M.E) ↦ X.encard ≤ k) :=
  _root_.IsoInvariant.of_iff_map _ _ fun i X ↦ by
    simp only [Observable.bundle_apply]
    dsimp only [_root_.IsoEquiv.map]
    rw [show Equiv.Set.congr i.toEquiv X = i.toEquiv '' X from rfl,
      i.toEquiv.injective.encard_image]

/-! ## Domain-specific reindexing by duality -/

/-- Precomposing an invariant matroid observable with duality preserves invariance.

The family is explicitly represented as `Family.dual F`, which is the Matroid-facing wrapper
around `Reindex dualObj F.bundle`; this avoids both higher-order inference and an independent
coherence axiom. -/
theorem IsoInvariant.dual {F : Family.{uα₁, uF₁}} {F' : Family.{uα₂, uF₂}} [IsoEquiv F F']
    (f : Observable F) (f' : Observable F') [IsoInvariant f f'] :
    IsoInvariant (F := F.dual) (F' := F'.dual) (fun M ↦ f M✶) (fun N ↦ f' N✶) :=
  IsoInvariant.reindex (f := dualObj.{uα₁}) (f' := dualObj.{uα₂}) (F := F) (F' := F') f f'

/-! ## Variable-output construction -/

/-- The set of all independent subsets of the ground. -/
abbrev IndepSetsObs : Observable (fun {α} (M : Matroid α) ↦ Set (Set M.E)) :=
  fun M ↦ {I | IndepObs M I}

instance instIsoInvariantIndepSets : IsoInvariant IndepSetsObs.{uα₁} IndepSetsObs.{uα₂} :=
  _root_.IsoInvariant.setOf (Observable.bundle IndepObs.{uα₁}) (Observable.bundle IndepObs.{uα₂})

end Matroid
