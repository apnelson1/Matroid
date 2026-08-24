/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Matroid.ForMathlib.Iso.Equiv

/-!
# Optional coherence for generic `IsoEquiv`

The heterogeneous relation operations are kept separate from `IsoRel`: weak one-step transport only
needs the relation itself. `IsoEquiv.Lawful` needs composition; the derived diagonal identity and
inverse theorems additionally ask the relation for the corresponding identity/inverse laws.
-/

@[expose] public section

open Set Function

namespace IsoRel

variable (C₁ : Type*) (C₂ : Type*) (C₃ : Type*)

class Refl (C : Type*) [R : IsoRel C C] where
  refl : ∀ X : C, R.Iso X X

class Symm [R₁₂ : IsoRel C₁ C₂] [R₂₁ : IsoRel C₂ C₁] where
  symm : ∀ {X : C₁} {Y : C₂}, R₁₂.Iso X Y → R₂₁.Iso Y X

class Comp [R₁₂ : IsoRel C₁ C₂] [R₂₃ : IsoRel C₂ C₃] [R₁₃ : IsoRel C₁ C₃] where
  comp : ∀ {X : C₁} {Y : C₂} {Z : C₃}, R₁₂.Iso X Y → R₂₃.Iso Y Z → R₁₃.Iso X Z

/-- The one relation law needed to derive that a diagonal lawful `IsoEquiv` maps identities to
identities. -/
class ReflCompSelf (C : Type*) [R : IsoRel C C] [Refl C] [Comp C C C] : Prop where
  refl_comp_self : ∀ X : C, Comp.comp (Refl.refl X) (Refl.refl X) = Refl.refl X

/-- The relation law needed to identify transport along an inverse with the inverse equivalence. -/
class CompSymm [R₁₂ : IsoRel C₁ C₂] [R₂₁ : IsoRel C₂ C₁] [R₁₁ : IsoRel C₁ C₁]
    [Refl C₁] [Symm C₁ C₂] [Comp C₁ C₂ C₁] : Prop where
  comp_symm : ∀ {X : C₁} {Y : C₂} (i : R₁₂.Iso X Y), Comp.comp i (Symm.symm i) = Refl.refl X

end IsoRel

namespace IsoMap

/-- Three weak object maps are lawful when mapping a composite source isomorphism agrees with
composing the two mapped target isomorphisms. -/
class Lawful {C₁ : Type*} {C₂ : Type*} {C₃ : Type*} {D₁ : Type*} {D₂ : Type*} {D₃ : Type*}
    [rC₁₂ : IsoRel C₁ C₂] [rC₂₃ : IsoRel C₂ C₃] [rC₁₃ : IsoRel C₁ C₃]
    [rD₁₂ : IsoRel D₁ D₂] [rD₂₃ : IsoRel D₂ D₃] [rD₁₃ : IsoRel D₁ D₃]
    [cC : IsoRel.Comp C₁ C₂ C₃] [cD : IsoRel.Comp D₁ D₂ D₃]
    (f₁ : C₁ → D₁) (f₂ : C₂ → D₂) (f₃ : C₃ → D₃)
    [m₁₂ : IsoMap f₁ f₂] [m₂₃ : IsoMap f₂ f₃] [m₁₃ : IsoMap f₁ f₃] : Prop where
  map_comp : ∀ {X : C₁} {Y : C₂} {Z : C₃} (i : rC₁₂.Iso X Y) (j : rC₂₃.Iso Y Z),
    m₁₃.map (cC.comp i j) = cD.comp (m₁₂.map i) (m₂₃.map j)

/-- Identity object maps are lawful. -/
instance instLawfulId {C₁ : Type*} {C₂ : Type*} {C₃ : Type*}
    [r₁₂ : IsoRel C₁ C₂] [r₂₃ : IsoRel C₂ C₃] [r₁₃ : IsoRel C₁ C₃] [IsoRel.Comp C₁ C₂ C₃] :
    Lawful (id : C₁ → C₁) (id : C₂ → C₂) (id : C₃ → C₃) where
  map_comp _ _ := rfl

end IsoMap

namespace IsoEquiv

section Composable

variable {C₁ : Type*} {C₂ : Type*} {C₃ : Type*}
  [R₁₂ : IsoRel C₁ C₂] [R₂₃ : IsoRel C₂ C₃] [R₁₃ : IsoRel C₁ C₃] [c : IsoRel.Comp C₁ C₂ C₃]

/-- Three chosen weak equivalence assignments are lawful when direct transport along a composite
agrees with successive transport. -/
class Lawful (F₁ : Family C₁) (F₂ : Family C₂) (F₃ : Family C₃)
    [e₁₂ : IsoEquiv F₁ F₂] [e₂₃ : IsoEquiv F₂ F₃] [e₁₃ : IsoEquiv F₁ F₃] : Prop where
  map_comp : ∀ {X : C₁} {Y : C₂} {Z : C₃} (i : R₁₂.Iso X Y) (j : R₂₃.Iso Y Z) (x : F₁ X),
    e₁₃.map (c.comp i j) x = e₂₃.map j (e₁₂.map i x)

namespace Lawful

variable {F₁ : Family C₁} {F₂ : Family C₂} {F₃ : Family C₃}
  [e₁₂ : IsoEquiv F₁ F₂] [e₂₃ : IsoEquiv F₂ F₃] [e₁₃ : IsoEquiv F₁ F₃] [Lawful F₁ F₂ F₃]

/-- Extensional form of the composition law. -/
theorem map_comp_eq_trans {X : C₁} {Y : C₂} {Z : C₃} (i : R₁₂.Iso X Y) (j : R₂₃.Iso Y Z) :
    e₁₃.map (c.comp i j) = (e₁₂.map i).trans (e₂₃.map j) :=
  Equiv.ext (Lawful.map_comp (F₁ := F₁) (F₂ := F₂) (F₃ := F₃) i j)

end Lawful

end Composable

namespace Lawful

section Diagonal

variable {C : Type*} [R : IsoRel C C] [IsoRel.Refl C] [IsoRel.Comp C C C]
  [IsoRel.ReflCompSelf C] {F : Family C} [e : IsoEquiv F F] [Lawful F F F]

/-- On the diagonal, composition lawfulness forces transport along the registered identity to be
the identity equivalence. -/
@[simp] theorem map_id (X : C) (x : F X) : e.map (IsoRel.Refl.refl X) x = x := by
  have h := Lawful.map_comp (F₁ := F) (F₂ := F) (F₃ := F)
    (IsoRel.Refl.refl X) (IsoRel.Refl.refl X) x
  rw [IsoRel.ReflCompSelf.refl_comp_self] at h
  exact ((e.map (IsoRel.Refl.refl X)).injective h).symm

@[simp] theorem map_id_eq_refl (X : C) : e.map (IsoRel.Refl.refl X) = Equiv.refl (F X) :=
  Equiv.ext (map_id (F := F) X)

end Diagonal

/-- If forward and reverse transports form a lawful triangle, transport along the registered
inverse is the inverse equivalence. -/
theorem map_symm {C₁ C₂ : Type*} [R₁₂ : IsoRel C₁ C₂] [R₂₁ : IsoRel C₂ C₁] [R₁₁ : IsoRel C₁ C₁]
    [IsoRel.Refl C₁] [IsoRel.Symm C₁ C₂] [IsoRel.Comp C₁ C₁ C₁] [IsoRel.Comp C₁ C₂ C₁]
    [IsoRel.ReflCompSelf C₁] [IsoRel.CompSymm C₁ C₂] {F : Family C₁} {F' : Family C₂}
    [e₁₁ : IsoEquiv F F] [e₁₂ : IsoEquiv F F'] [e₂₁ : IsoEquiv F' F] [Lawful F F F] [Lawful F F' F]
    {X : C₁} {Y : C₂} (i : R₁₂.Iso X Y) : e₂₁.map (IsoRel.Symm.symm i) = (e₁₂.map i).symm := by
  apply Equiv.ext
  intro y
  obtain ⟨x, rfl⟩ := (e₁₂.map i).surjective y
  have h := Lawful.map_comp (F₁ := F) (F₂ := F') (F₃ := F) i (IsoRel.Symm.symm i) x
  rw [IsoRel.CompSymm.comp_symm, map_id] at h
  simpa using h.symm

end Lawful

/-- Reindexing a lawful fiber transport along a lawful object map is lawful. -/
instance instLawfulReindex {C₁ : Type*} {C₂ : Type*} {C₃ : Type*}
    {D₁ : Type*} {D₂ : Type*} {D₃ : Type*}
    [rC₁₂ : IsoRel C₁ C₂] [rC₂₃ : IsoRel C₂ C₃] [rC₁₃ : IsoRel C₁ C₃]
    [rD₁₂ : IsoRel D₁ D₂] [rD₂₃ : IsoRel D₂ D₃] [rD₁₃ : IsoRel D₁ D₃]
    [cC : IsoRel.Comp C₁ C₂ C₃] [cD : IsoRel.Comp D₁ D₂ D₃]
    (f₁ : C₁ → D₁) (f₂ : C₂ → D₂) (f₃ : C₃ → D₃) (F₁ : Family D₁) (F₂ : Family D₂) (F₃ : Family D₃)
    [m₁₂ : IsoMap f₁ f₂] [m₂₃ : IsoMap f₂ f₃] [m₁₃ : IsoMap f₁ f₃] [IsoMap.Lawful f₁ f₂ f₃]
    [e₁₂ : IsoEquiv F₁ F₂] [e₂₃ : IsoEquiv F₂ F₃] [e₁₃ : IsoEquiv F₁ F₃] [Lawful F₁ F₂ F₃] :
    Lawful (Reindex f₁ F₁) (Reindex f₂ F₂) (Reindex f₃ F₃) where
  map_comp i j x := by
    change e₁₃.map (m₁₃.map (cC.comp i j)) x =
      e₂₃.map (m₂₃.map j) (e₁₂.map (m₁₂.map i) x)
    rw [IsoMap.Lawful.map_comp (f₁ := f₁) (f₂ := f₂) (f₃ := f₃)]
    exact Lawful.map_comp (F₁ := F₁) (F₂ := F₂) (F₃ := F₃) (m₁₂.map i) (m₂₃.map j) x

/-! ## Structural lawfulness -/

section Composable

variable {C₁ C₂ C₃ : Type*} [R₁₂ : IsoRel C₁ C₂] [R₂₃ : IsoRel C₂ C₃] [R₁₃ : IsoRel C₁ C₃]
  [c : IsoRel.Comp C₁ C₂ C₃]

instance instLawfulConst (S : Sort*) :
    Lawful (fun _ : C₁ ↦ S) (fun _ : C₂ ↦ S) (fun _ : C₃ ↦ S) where
  map_comp _ _ _ := rfl

section SortValued

variable (A₁ : Family C₁) (A₂ : Family C₂) (A₃ : Family C₃)
  (B₁ : Family C₁) (B₂ : Family C₂) (B₃ : Family C₃)
  [a₁₂ : IsoEquiv A₁ A₂] [a₂₃ : IsoEquiv A₂ A₃] [a₁₃ : IsoEquiv A₁ A₃]
  [b₁₂ : IsoEquiv B₁ B₂] [b₂₃ : IsoEquiv B₂ B₃] [b₁₃ : IsoEquiv B₁ B₃]
  [Lawful A₁ A₂ A₃] [Lawful B₁ B₂ B₃]

instance instLawfulArrow :
    Lawful (fun X ↦ A₁ X → B₁ X) (fun X ↦ A₂ X → B₂ X) (fun X ↦ A₃ X → B₃ X) where
  map_comp i j f := by
    change (fun z ↦ b₁₃.map (c.comp i j) (f ((a₁₃.map (c.comp i j)).symm z))) =
      (fun z ↦ b₂₃.map j (b₁₂.map i (f ((a₁₂.map i).symm ((a₂₃.map j).symm z)))))
    rw [Lawful.map_comp_eq_trans (F₁ := A₁) (F₂ := A₂) (F₃ := A₃),
      Lawful.map_comp_eq_trans (F₁ := B₁) (F₂ := B₂) (F₃ := B₃)]
    rfl

end SortValued

section TypeValued

variable (A₁ : TypeFamily C₁) (A₂ : TypeFamily C₂) (A₃ : TypeFamily C₃)
  (B₁ : TypeFamily C₁) (B₂ : TypeFamily C₂) (B₃ : TypeFamily C₃)
  [a₁₂ : IsoEquiv A₁ A₂] [a₂₃ : IsoEquiv A₂ A₃] [a₁₃ : IsoEquiv A₁ A₃]
  [b₁₂ : IsoEquiv B₁ B₂] [b₂₃ : IsoEquiv B₂ B₃] [b₁₃ : IsoEquiv B₁ B₃]
  [Lawful A₁ A₂ A₃] [Lawful B₁ B₂ B₃]

instance instLawfulProd :
    Lawful (fun X ↦ A₁ X × B₁ X) (fun X ↦ A₂ X × B₂ X) (fun X ↦ A₃ X × B₃ X) where
  map_comp i j x := by
    dsimp only [IsoEquiv.map]
    rw [Lawful.map_comp_eq_trans (F₁ := A₁) (F₂ := A₂) (F₃ := A₃),
      Lawful.map_comp_eq_trans (F₁ := B₁) (F₂ := B₂) (F₃ := B₃)]
    rfl

instance instLawfulSum :
    Lawful (fun X ↦ A₁ X ⊕ B₁ X) (fun X ↦ A₂ X ⊕ B₂ X) (fun X ↦ A₃ X ⊕ B₃ X) where
  map_comp i j x := by
    dsimp only [IsoEquiv.map]
    rw [Lawful.map_comp_eq_trans (F₁ := A₁) (F₂ := A₂) (F₃ := A₃),
      Lawful.map_comp_eq_trans (F₁ := B₁) (F₂ := B₂) (F₃ := B₃)]
    cases x <;> rfl

instance instLawfulOption :
    Lawful (fun X ↦ Option (A₁ X)) (fun X ↦ Option (A₂ X)) (fun X ↦ Option (A₃ X)) where
  map_comp i j x := by
    dsimp only [IsoEquiv.map]
    rw [Lawful.map_comp_eq_trans (F₁ := A₁) (F₂ := A₂) (F₃ := A₃)]
    cases x <;> rfl

instance instLawfulSet : Lawful (fun X ↦ Set (A₁ X)) (fun X ↦ Set (A₂ X)) (fun X ↦ Set (A₃ X)) where
  map_comp i j X := by
    dsimp only [IsoEquiv.map]
    rw [Lawful.map_comp_eq_trans (F₁ := A₁) (F₂ := A₂) (F₃ := A₃)]
    exact (Set.image_image (a₂₃.map j) (a₁₂.map i) X).symm

end TypeValued

end Composable

end IsoEquiv
