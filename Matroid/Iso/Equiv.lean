/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Matroid.ForMathlib.Iso.Equiv
public import Matroid.Equiv

/-!
# Matroid adapter for the generic isomorphism-equivalence framework

Matroid isomorphisms act intrinsically on the ground subtype `M.E`. Ambient supported elements,
sets, and tuples of sets are exposed through fiber equivalences to data built from `M.E`.
-/

@[expose] public section

open Set Function

namespace Matroid

universe uα₁ uα₂ uα₃ uα₄ uF₁ uF₂ uF₃ uF₄ uι

/-- Internal bundled matroid object used only as the generic-core index. -/
structure IsoObj where
  α : Type uα₁
  matroid : Matroid α

set_option linter.checkUnivs false in
abbrev Family := {α : Type uα₁} → Matroid α → Sort uF₁

set_option linter.checkUnivs false in
abbrev TypeFamily := {α : Type uα₁} → Matroid α → Type uF₁

/-- Reindex an unbundled matroid family by the bundled generic-core index.

Implementation detail of the generic-core adapter; ordinary users should reach the
domain-facing wrappers instead of naming this. -/
protected abbrev Family.bundle (F : Family.{uα₁, uF₁}) : IsoObj.{uα₁} → Sort uF₁ :=
  fun X ↦ @F X.α X.matroid

instance instIsoRelIsoObj : _root_.IsoRel IsoObj.{uα₁} IsoObj.{uα₂} where
  Iso X Y := Matroid.Iso X.matroid Y.matroid

abbrev IsoEquiv (F : Family.{uα₁, uF₁}) (F' : Family.{uα₂, uF₂}) :=
  _root_.IsoEquiv F.bundle F'.bundle

/-- Matroid-facing transport along an isomorphism.

This is the generic `_root_.IsoEquiv.map` with the bundling index supplied. Stating matroid
results through it keeps them in unbundled vocabulary, and it is the only place `⟨α, M⟩` has to be
written: the generic `map` cannot infer that index, because unifying `IsoRel.Iso X Y` against
`Iso M N` would have to solve `?X.matroid ≡ M`. -/
abbrev IsoEquiv.map {F : Family.{uα₁, uF₁}} {F' : Family.{uα₂, uF₂}} [IsoEquiv F F']
    {α : Type uα₁} {β : Type uα₂} {M : Matroid α} {N : Matroid β} (i : Iso M N) : F M ≃ F' N :=
  _root_.IsoEquiv.map (F := F.bundle) (F' := F'.bundle) (X := ⟨α, M⟩) (Y := ⟨β, N⟩) i

/-- Matroid-facing alias for isomorphism-preserving maps between bundled matroid objects. -/
abbrev IsoMap (f : IsoObj.{uα₁} → IsoObj.{uα₃}) (f' : IsoObj.{uα₂} → IsoObj.{uα₄}) :=
  _root_.IsoMap f f'

namespace Family

/-- Reindex an unbundled matroid family along a bundled object construction. -/
def reindex (f : IsoObj.{uα₁} → IsoObj.{uα₃}) (F : Family.{uα₃, uF₃}) : Family.{uα₁, uF₃} :=
  fun {α} M ↦ @F (f ⟨α, M⟩).α (f ⟨α, M⟩).matroid

end Family

/-- Matroid-facing reindex closure. -/
instance instIsoEquivReindex (f : IsoObj.{uα₁} → IsoObj.{uα₃}) (f' : IsoObj.{uα₂} → IsoObj.{uα₄})
    (F : Family.{uα₃, uF₃}) (F' : Family.{uα₄, uF₄}) [m : _root_.IsoMap f f'] [e : IsoEquiv F F'] :
    IsoEquiv (Family.reindex f F) (Family.reindex f' F') where
  map i := IsoEquiv.map (F := F) (F' := F') (m.map i)

/-! ## Canonical object maps -/

/-- Matroid duality as a bundled object map. -/
def dualObj (X : IsoObj.{uα₁}) : IsoObj.{uα₁} := ⟨X.α, X.matroid✶⟩

instance instIsoMapDual : IsoMap dualObj.{uα₁} dualObj.{uα₂} where
  map i := i.dual

namespace Family

/-- Pull a family back along matroid duality.

This is the domain-facing named wrapper around generic `Reindex`; users normally reach it through
`IsoInvariant.dual` rather than mentioning it explicitly. -/
def dual (F : Family.{uα₁, uF₁}) : Family.{uα₁, uF₁} := reindex dualObj F

end Family

instance instIsoEquivDual (F : Family.{uα₁, uF₁}) (F' : Family.{uα₂, uF₂}) [IsoEquiv F F'] :
    IsoEquiv F.dual F'.dual := instIsoEquivReindex dualObj.{uα₁} dualObj.{uα₂} F F'

/-! ## Primitive matroid family -/

/-- The intrinsic ground-element family. -/
abbrev GroundFamily : TypeFamily.{uα₁, uα₁} := fun {α} (M : Matroid α) ↦ M.E

instance instIsoEquivGround : IsoEquiv (fun {α : Type uα₁} (M : Matroid α) ↦ M.E)
    (fun {α : Type uα₂} (M : Matroid α) ↦ M.E) where
  map i := i.toEquiv

@[simp] theorem IsoEquiv.map_ground
    {α : Type uα₁} {β : Type uα₂} {M : Matroid α} {N : Matroid β} (i : Matroid.Iso M N) :
    IsoEquiv.map (F := fun {α} (M : Matroid α) ↦ M.E)
      (F' := fun {α} (M : Matroid α) ↦ M.E) i = i.toEquiv := rfl

/-! ## Ambient supported data -/

/-- Ambient subsets supported on the ground are equivalent to intrinsic subsets of `M.E`. -/
def supportedSetEquiv {α : Type*} (M : Matroid α) : {X : Set α // X ⊆ M.E} ≃ Set M.E where
  toFun X := Subtype.val ⁻¹' X.1
  invFun t := ⟨Subtype.val '' t, Subtype.coe_image_subset M.E t⟩
  left_inv := by
    rintro ⟨X, hX⟩
    ext x
    constructor
    · rintro ⟨⟨y, hy⟩, hyX, rfl⟩
      exact hyX
    · exact fun hx ↦ ⟨⟨x, hX hx⟩, hx, rfl⟩
  right_inv := by
    intro t
    ext ⟨x, hx⟩
    simp

instance instIsoEquivSupportedSets : IsoEquiv
    (fun {α : Type uα₁} (M : Matroid α) ↦ {X : Set α // X ⊆ M.E})
    (fun {α : Type uα₂} (M : Matroid α) ↦ {X : Set α // X ⊆ M.E}) := _root_.IsoEquiv.ofFiberEquiv
    (F := fun X : IsoObj.{uα₁} ↦ Set X.matroid.E) (F' := fun X : IsoObj.{uα₂} ↦ Set X.matroid.E)
    (fun X ↦ supportedSetEquiv X.matroid) (fun X ↦ supportedSetEquiv X.matroid)

/-- A supported tuple of ambient sets is equivalent to an intrinsic tuple of sets of ground
elements. This matches the `ι → Set α` support class in the current matroid invariant API. -/
def supportedSetFunEquiv {α : Type*} (M : Matroid α) (ι : Type uι) :
    {X : ι → Set α // ∀ i, X i ⊆ M.E} ≃ (ι → Set M.E) where
  toFun X i := Subtype.val ⁻¹' X.1 i
  invFun X := ⟨fun i ↦ Subtype.val '' X i, fun i ↦ Subtype.coe_image_subset M.E (X i)⟩
  left_inv := by
    rintro ⟨X, hX⟩
    ext i x
    constructor
    · rintro ⟨⟨y, hy⟩, hyX, rfl⟩
      exact hyX
    · exact fun hx ↦ ⟨⟨x, hX i hx⟩, hx, rfl⟩
  right_inv := by
    intro X
    funext i
    ext ⟨x, hx⟩
    simp

instance instIsoEquivSupportedSetFuns (ι : Type uι) : IsoEquiv
    (fun {α : Type uα₁} (M : Matroid α) ↦ {X : ι → Set α // ∀ i, X i ⊆ M.E})
    (fun {α : Type uα₂} (M : Matroid α) ↦ {X : ι → Set α // ∀ i, X i ⊆ M.E}) :=
  _root_.IsoEquiv.ofFiberEquiv (F := fun X : IsoObj.{uα₁} ↦ ι → Set X.matroid.E)
    (F' := fun X : IsoObj.{uα₂} ↦ ι → Set X.matroid.E)
    (fun X ↦ supportedSetFunEquiv X.matroid ι) (fun X ↦ supportedSetFunEquiv X.matroid ι)

end Matroid
