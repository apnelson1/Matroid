/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Matroid.ForMathlib.Iso.Lawful
public import Matroid.Graph.Iso.Equiv

/-!
# Graph adapter for generic `IsoEquiv.Lawful`
-/

@[expose] public section

namespace Graph

universe uV₁ uE₁ uF₁ uV₂ uE₂ uF₂ uV₃ uE₃ uF₃ wV₁ wE₁ wV₂ wE₂ wV₃ wE₃

noncomputable instance instIsoRelReflIsoObj : _root_.IsoRel.Refl IsoObj.{uV₁, uE₁} where
  refl X := Graph.Iso.id X.graph

instance instIsoRelSymmIsoObj : _root_.IsoRel.Symm IsoObj.{uV₁, uE₁} IsoObj.{uV₂, uE₂} where
  symm i := i.symm

instance instIsoRelCompIsoObj :
    _root_.IsoRel.Comp IsoObj.{uV₁, uE₁} IsoObj.{uV₂, uE₂} IsoObj.{uV₃, uE₃} where
  comp i j := i.comp j

private theorem iso_id_symm {V : Type uV₁} {E : Type uE₁} (G : Graph V E) :
    (Iso.id G).symm = Iso.id G := by
  refine Iso.ext ?_ ?_ <;> simp [Iso.id, Iso.symm]

private theorem iso_id_comp_self {V : Type uV₁} {E : Type uE₁} (G : Graph V E) :
    (Iso.id G).comp (Iso.id G) = Iso.id G := by
  simpa [iso_id_symm] using Iso.comp_symm (Iso.id G)

instance instIsoRelReflCompSelfIsoObj : _root_.IsoRel.ReflCompSelf IsoObj.{uV₁, uE₁} where
  refl_comp_self X := iso_id_comp_self X.graph

instance instIsoRelCompSymmIsoObj : _root_.IsoRel.CompSymm IsoObj.{uV₁, uE₁} IsoObj.{uV₂, uE₂} where
  comp_symm i := Iso.comp_symm i

abbrev IsoEquiv.Lawful (F₁ : Family.{uV₁, uE₁, uF₁}) (F₂ : Family.{uV₂, uE₂, uF₂})
    (F₃ : Family.{uV₃, uE₃, uF₃}) [IsoEquiv F₁ F₂] [IsoEquiv F₂ F₃] [IsoEquiv F₁ F₃] :=
  _root_.IsoEquiv.Lawful F₁.bundle F₂.bundle F₃.bundle

namespace IsoEquiv

/-- Graph-facing lawful reindex closure. -/
instance instLawfulReindex (f₁ : IsoObj.{uV₁, uE₁} → IsoObj.{wV₁, wE₁})
    (f₂ : IsoObj.{uV₂, uE₂} → IsoObj.{wV₂, wE₂}) (f₃ : IsoObj.{uV₃, uE₃} → IsoObj.{wV₃, wE₃})
    (F₁ : Family.{wV₁, wE₁, uF₁}) (F₂ : Family.{wV₂, wE₂, uF₂}) (F₃ : Family.{wV₃, wE₃, uF₃})
    [_root_.IsoMap f₁ f₂] [_root_.IsoMap f₂ f₃] [_root_.IsoMap f₁ f₃]
    [_root_.IsoMap.Lawful f₁ f₂ f₃]
    [IsoEquiv F₁ F₂] [IsoEquiv F₂ F₃] [IsoEquiv F₁ F₃] [Lawful F₁ F₂ F₃] :
    Lawful (Family.reindex f₁ F₁) (Family.reindex f₂ F₂) (Family.reindex f₃ F₃) := by
  change _root_.IsoEquiv.Lawful
    (_root_.Reindex f₁ F₁.bundle) (_root_.Reindex f₂ F₂.bundle) (_root_.Reindex f₃ F₃.bundle)
  infer_instance

instance instLawfulVertices : Lawful (fun {V : Type uV₁} {E : Type uE₁} (G : Graph V E) ↦ V(G))
    (fun {V : Type uV₂} {E : Type uE₂} (G : Graph V E) ↦ V(G))
    (fun {V : Type uV₃} {E : Type uE₃} (G : Graph V E) ↦ V(G)) where
  map_comp := Graph.Iso.vertexEquiv_comp

instance instLawfulEdges : Lawful (fun {V : Type uV₁} {E : Type uE₁} (G : Graph V E) ↦ E(G))
    (fun {V : Type uV₂} {E : Type uE₂} (G : Graph V E) ↦ E(G))
    (fun {V : Type uV₃} {E : Type uE₃} (G : Graph V E) ↦ E(G)) where
  map_comp := Graph.Iso.edgeEquiv_comp

namespace Lawful

@[simp] theorem map_id {F : Family.{uV₁, uE₁, uF₁}} [e : IsoEquiv F F] [Lawful F F F]
    {V : Type uV₁} {E : Type uE₁} (G : Graph V E) (x : F G) :
    IsoEquiv.map (F := F) (F' := F) (Iso.id G) x = x :=
  _root_.IsoEquiv.Lawful.map_id (F := F.bundle) (X := (⟨V, E, G⟩ : IsoObj.{uV₁, uE₁})) x

@[simp] theorem map_id_eq_refl {F : Family.{uV₁, uE₁, uF₁}} [e : IsoEquiv F F] [Lawful F F F]
    {V : Type uV₁} {E : Type uE₁} (G : Graph V E) :
    IsoEquiv.map (F := F) (F' := F) (Iso.id G) = Equiv.refl (F G) := Equiv.ext (map_id (F := F) G)

/-- Graph-facing inverse-transport theorem. -/
theorem map_symm {F : Family.{uV₁, uE₁, uF₁}} {F' : Family.{uV₂, uE₂, uF₂}}
    [e₁₁ : IsoEquiv F F] [e₁₂ : IsoEquiv F F'] [e₂₁ : IsoEquiv F' F] [Lawful F F F] [Lawful F F' F]
    {V : Type uV₁} {E : Type uE₁} {V' : Type uV₂} {E' : Type uE₂}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) :
    IsoEquiv.map (F := F') (F' := F) i.symm = (IsoEquiv.map (F := F) (F' := F') i).symm :=
  _root_.IsoEquiv.Lawful.map_symm (F := F.bundle) (F' := F'.bundle)
    (X := ⟨V, E, G⟩) (Y := ⟨V', E', H⟩) i

end Lawful
end IsoEquiv
end Graph
