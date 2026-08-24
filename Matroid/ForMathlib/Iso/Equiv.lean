/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Logic.Equiv.Set
public import Mathlib.Data.Set.Card

/-!
# Generic equivalence transport along a chosen isomorphism relation

This file is intentionally independent of graphs, matroids, and category theory.

An `IsoRel C₁ C₂` only specifies what it means for an object of `C₁` to be isomorphic to an
object of `C₂`. A `Family C` is a dependent family of sorts over objects of `C`.
`IsoEquiv F F'` says that every chosen isomorphism induces a chosen equivalence between the
corresponding fibers.

`IsoEquiv` is deliberately weak: there are no identity or composition laws here. Optional
coherence is isolated in `ForMathlib.Iso.Lawful`.

The second half of the file adds the object-map layer. `IsoMap f f'` is the object-level analogue
of weak `IsoEquiv`: every chosen source isomorphism is sent to a chosen target isomorphism, again
with no identity/composition law. `Reindex f F` pulls a family back along such a map, and is
deliberately a `def` rather than an `abbrev` so that the factorization `X ↦ F (f X)` stays
syntactically visible; typeclass inference then never has to reconstruct an unknown composition
from an expanded lambda. The central feedback rule is

* `IsoMap f f'`
* `IsoEquiv F F'`
* therefore `IsoEquiv (Reindex f F) (Reindex f' F')`,

after which the ordinary fiber constructors above continue to synthesize structurally over the
`Reindex` node.
-/

@[expose] public section

open Set Function

/-- A chosen heterogeneous notion of isomorphism between two object types. -/
class IsoRel (C₁ : Type*) (C₂ : Type*) where
  Iso : C₁ → C₂ → Sort*

/-- A family of sorts indexed by objects. -/
abbrev Family (C : Type*) := C → Sort*

/-- A `Family` whose fibers are types. -/
abbrev TypeFamily (C : Type*) := C → Type*

/-- Duplicate a universe-polymorphic expression before elaboration. -/
syntax:max term:max "⧉" term : term
macro_rules | `($f:term ⧉ $x:term) => `($f $x $x)

section Transport

variable {C₁ : Type*} {C₂ : Type*} [R : IsoRel C₁ C₂]

/-- A chosen equivalence between fibers along every chosen object isomorphism.

No coherence is required. -/
class IsoEquiv (F : Family C₁) (F' : Family C₂) where
  map : ∀ {X : C₁} {Y : C₂}, R.Iso X Y → F X ≃ F' Y

namespace IsoEquiv

variable {X : C₁} {Y : C₂}

/-- Conjugate a weak `IsoEquiv` by arbitrary pointwise equivalences of fibers. -/
@[instance_reducible]
def ofFiberEquiv {F : Family C₁} {F' : Family C₂} [e : IsoEquiv F F']
    {K : Family C₁} {K' : Family C₂} (s : ∀ X, K X ≃ F X) (t : ∀ Y, K' Y ≃ F' Y) :
    IsoEquiv K K' where
  map i := (s _).trans ((e.map i).trans (t _).symm)

/-! ## Canonical structural instances

The instances are grouped by the kind of fiber they need — `instConst` and `instArrow` accept
arbitrary `Sort`-valued families, the remaining ones need a `TypeFamily` — and each group carries
the lemmas computing its transport. -/

instance instConst (S : Sort*) : IsoEquiv (fun _ : C₁ ↦ S) (fun _ : C₂ ↦ S) where
  map _ := Equiv.refl S

@[simp] theorem map_const (S : Sort*) (i : R.Iso X Y) (x : S) :
    IsoEquiv.map (F := fun _ : C₁ ↦ S) (F' := fun _ : C₂ ↦ S) i x = x := rfl

section SortValued

variable {A : Family C₁} {A' : Family C₂} [a : IsoEquiv A A']
  {B : Family C₁} {B' : Family C₂} [b : IsoEquiv B B']

instance instArrow : IsoEquiv (fun X ↦ A X → B X) (fun Y ↦ A' Y → B' Y) where
  map i :=
    { toFun := fun f y ↦ b.map i (f ((a.map i).symm y))
      invFun := fun g x ↦ (b.map i).symm (g (a.map i x))
      left_inv := by intro f; funext x; simp
      right_inv := by intro g; funext y; simp }

@[simp] theorem map_arrow_apply (i : R.Iso X Y) (f : A X → B X) (x : A X) :
    IsoEquiv.map (F := fun X ↦ A X → B X) (F' := fun Y ↦ A' Y → B' Y) i f
        (a.map i x) = b.map i (f x) := by
  change b.map i (f ((a.map i).symm (a.map i x))) = b.map i (f x)
  rw [Equiv.symm_apply_apply]

end SortValued

section TypeValued

variable {A : TypeFamily C₁} {A' : TypeFamily C₂} [a : IsoEquiv A A']
  {B : TypeFamily C₁} {B' : TypeFamily C₂} [b : IsoEquiv B B']

instance instProd : IsoEquiv (fun X ↦ A X × B X) (fun Y ↦ A' Y × B' Y) where
  map i := Equiv.prodCongr (a.map i) (b.map i)

instance instSum : IsoEquiv (fun X ↦ A X ⊕ B X) (fun Y ↦ A' Y ⊕ B' Y) where
  map i := Equiv.sumCongr (a.map i) (b.map i)

instance instOption : IsoEquiv (fun X ↦ Option (A X)) (fun Y ↦ Option (A' Y)) where
  map i := Equiv.optionCongr (a.map i)

instance instSet : IsoEquiv (fun X ↦ Set (A X)) (fun Y ↦ Set (A' Y)) where
  map i := Equiv.Set.congr (a.map i)

@[simp] theorem map_set (i : R.Iso X Y) (S : Set (A X)) :
    IsoEquiv.map (F := fun X ↦ Set (A X)) (F' := fun Y ↦ Set (A' Y)) i S =
      Equiv.Set.congr (a.map i) S := rfl

end TypeValued

end IsoEquiv

end Transport

/-! ## Isomorphism-preserving object maps and family reindexing -/

section Reindexing

variable {C₁ C₂ D₁ D₂ E₁ E₂ : Type*}

/-- An object construction that maps chosen source isomorphisms to chosen target isomorphisms.

This is deliberately weak: no identity or composition laws are required. -/
class IsoMap [rC : IsoRel C₁ C₂] [rD : IsoRel D₁ D₂] (f : C₁ → D₁) (f' : C₂ → D₂) where
  map : ∀ {X : C₁} {Y : C₂}, rC.Iso X Y → rD.Iso (f X) (f' Y)

namespace IsoMap

/-- Identity object maps preserve every chosen isomorphism relation. -/
instance instId [r : IsoRel C₁ C₂] : IsoMap (id : C₁ → C₁) (id : C₂ → C₂) where
  map i := i

/-- Weak `IsoMap`s are closed under composition when the composition is kept syntactically
visible. -/
instance instComp [rC : IsoRel C₁ C₂] [rD : IsoRel D₁ D₂] [rE : IsoRel E₁ E₂]
    (f : C₁ → D₁) (f' : C₂ → D₂) (g : D₁ → E₁) (g' : D₂ → E₂)
    [hf : IsoMap f f'] [hg : IsoMap g g'] : IsoMap (g ∘ f) (g' ∘ f') where
  map i := hg.map (hf.map i)

end IsoMap

/-- Pull a family back along an object map.

This definition is intentionally not an `abbrev`: the visible `Reindex` head is the breadcrumb
typeclass inference needs.

Implementation detail of the generic-core adapter layer. Ordinary Graph/Matroid users should
reach this through named domain operations such as `Matroid.Family.dual`, never by writing
`Reindex` directly. -/
def Reindex {C : Type*} {D : Type*} (f : C → D) (F : Family D) : Family C := fun X ↦ F (f X)

namespace IsoEquiv

variable [rC : IsoRel C₁ C₂] [rD : IsoRel D₁ D₂]

/-- Canonical transport of a family reindexed along an `IsoMap`. -/
instance instReindex (f : C₁ → D₁) (f' : C₂ → D₂) (F : Family D₁) (F' : Family D₂)
    [m : IsoMap f f'] [e : IsoEquiv F F'] : IsoEquiv (Reindex f F) (Reindex f' F') where
  map i := e.map (m.map i)

@[simp] theorem map_reindex {f : C₁ → D₁} {f' : C₂ → D₂} {F : Family D₁} {F' : Family D₂}
    [m : IsoMap f f'] [e : IsoEquiv F F'] {X : C₁} {Y : C₂} (i : rC.Iso X Y) :
    IsoEquiv.map (F := Reindex f F) (F' := Reindex f' F') i = e.map (m.map i) := rfl

end IsoEquiv

end Reindexing
