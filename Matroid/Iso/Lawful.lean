/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Matroid.ForMathlib.Iso.Lawful
public import Matroid.Iso.Equiv

/-!
# Matroid adapter for generic `IsoEquiv.Lawful`
-/

@[expose] public section

namespace Matroid

universe uα₁ uα₂ uα₃ uβ₁ uβ₂ uβ₃ uF₁ uF₂ uF₃

instance instIsoRelReflIsoObj : _root_.IsoRel.Refl IsoObj.{uα₁} where
  refl _ := Matroid.Iso.refl

instance instIsoRelSymmIsoObj : _root_.IsoRel.Symm IsoObj.{uα₁} IsoObj.{uα₂} where
  symm i := i.symm

instance instIsoRelCompIsoObj : _root_.IsoRel.Comp IsoObj.{uα₁} IsoObj.{uα₂} IsoObj.{uα₃} where
  comp i j := i.trans j

instance instIsoRelReflCompSelfIsoObj : _root_.IsoRel.ReflCompSelf IsoObj.{uα₁} where
  refl_comp_self X := by
    change (Iso.refl.trans Iso.refl : X.matroid ≂ X.matroid) = Iso.refl
    apply DFunLike.ext _ _
    intro x
    rfl

instance instIsoRelCompSymmIsoObj : _root_.IsoRel.CompSymm IsoObj.{uα₁} IsoObj.{uα₂} where
  comp_symm i := by
    change (i.trans i.symm : _ ≂ _) = Iso.refl
    exact DFunLike.ext _ _ (fun x ↦ i.symm_apply_apply x)

abbrev IsoEquiv.Lawful (F₁ : Family.{uα₁, uF₁}) (F₂ : Family.{uα₂, uF₂}) (F₃ : Family.{uα₃, uF₃})
    [IsoEquiv F₁ F₂] [IsoEquiv F₂ F₃] [IsoEquiv F₁ F₃] :=
  _root_.IsoEquiv.Lawful F₁.bundle F₂.bundle F₃.bundle

/-- Duality respects composition of matroid isomorphisms. -/
instance instIsoMapLawfulDual : _root_.IsoMap.Lawful dualObj.{uα₁} dualObj.{uα₂} dualObj.{uα₃} where
  map_comp i j := by
    change ((i.trans j).dual : _ ≂ _) = (i.dual).trans (j.dual)
    apply DFunLike.ext _ _
    intro x
    rfl

namespace IsoEquiv

/-- Matroid-facing lawful reindex closure. -/
instance instLawfulReindex (f₁ : IsoObj.{uα₁} → IsoObj.{uβ₁}) (f₂ : IsoObj.{uα₂} → IsoObj.{uβ₂})
    (f₃ : IsoObj.{uα₃} → IsoObj.{uβ₃})
    (F₁ : Family.{uβ₁, uF₁}) (F₂ : Family.{uβ₂, uF₂}) (F₃ : Family.{uβ₃, uF₃})
    [_root_.IsoMap f₁ f₂] [_root_.IsoMap f₂ f₃] [_root_.IsoMap f₁ f₃]
    [_root_.IsoMap.Lawful f₁ f₂ f₃]
    [IsoEquiv F₁ F₂] [IsoEquiv F₂ F₃] [IsoEquiv F₁ F₃] [Lawful F₁ F₂ F₃] :
    Lawful (Family.reindex f₁ F₁) (Family.reindex f₂ F₂) (Family.reindex f₃ F₃) := by
  change _root_.IsoEquiv.Lawful
    (_root_.Reindex f₁ F₁.bundle) (_root_.Reindex f₂ F₂.bundle) (_root_.Reindex f₃ F₃.bundle)
  infer_instance

/-- Lawfulness propagates through dual precomposition. -/
instance instLawfulDual (F₁ : Family.{uα₁, uF₁}) (F₂ : Family.{uα₂, uF₂}) (F₃ : Family.{uα₃, uF₃})
    [IsoEquiv F₁ F₂] [IsoEquiv F₂ F₃] [IsoEquiv F₁ F₃] [Lawful F₁ F₂ F₃] :
    Lawful F₁.dual F₂.dual F₃.dual := by
  change _root_.IsoEquiv.Lawful
    (_root_.Reindex dualObj.{uα₁} F₁.bundle) (_root_.Reindex dualObj.{uα₂} F₂.bundle)
    (_root_.Reindex dualObj.{uα₃} F₃.bundle)
  infer_instance

instance instLawfulGround : Lawful (fun {α : Type uα₁} (M : Matroid α) ↦ M.E)
    (fun {α : Type uα₂} (M : Matroid α) ↦ M.E) (fun {α : Type uα₃} (M : Matroid α) ↦ M.E) where
  map_comp _ _ _ := rfl

namespace Lawful

@[simp] theorem map_id {F : Family.{uα₁, uF₁}} [e : IsoEquiv F F] [Lawful F F F]
    {α : Type uα₁} (M : Matroid α) (x : F M) :
    IsoEquiv.map (F := F) (F' := F) (Matroid.Iso.refl : Matroid.Iso M M) x = x :=
  _root_.IsoEquiv.Lawful.map_id (F := F.bundle) (X := (⟨α, M⟩ : IsoObj.{uα₁})) x

@[simp] theorem map_id_eq_refl {F : Family.{uα₁, uF₁}} [e : IsoEquiv F F] [Lawful F F F]
    {α : Type uα₁} (M : Matroid α) :
    IsoEquiv.map (F := F) (F' := F) (Matroid.Iso.refl : Matroid.Iso M M) = Equiv.refl (F M) :=
  Equiv.ext (map_id (F := F) M)

/-- Matroid-facing inverse-transport theorem. -/
theorem map_symm {F : Family.{uα₁, uF₁}} {F' : Family.{uα₂, uF₂}}
    [e₁₁ : IsoEquiv F F] [e₁₂ : IsoEquiv F F'] [e₂₁ : IsoEquiv F' F] [Lawful F F F] [Lawful F F' F]
    {α : Type uα₁} {β : Type uα₂} {M : Matroid α} {N : Matroid β} (i : Matroid.Iso M N) :
    IsoEquiv.map (F := F') (F' := F) i.symm = (IsoEquiv.map (F := F) (F' := F') i).symm :=
  _root_.IsoEquiv.Lawful.map_symm (F := F.bundle) (F' := F'.bundle) (X := ⟨α, M⟩) (Y := ⟨β, N⟩) i

end Lawful
end IsoEquiv
end Matroid
