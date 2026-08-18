/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Matroid.Graph.Iso.IsoAction

/-!
# Transport across carrier universes

`IsoAction F` is deliberately local to one vertex-universe / edge-universe pair.  `IsoTransport
F F'` is the heterogeneous companion: it transports `F G` to `F' H` along an isomorphism whose
source and target carrier universes may be unrelated.

The class is stronger than a bare assignment of equivalences.  It contains the ordinary
`IsoAction`s on both universe slices and requires the heterogeneous map to commute with
precomposition by source isomorphisms and postcomposition by target isomorphisms.  Thus a
same-universe instance `IsoTransport F F` contains an `IsoAction F`; a low-priority bridge exposes
that action automatically when no more direct `IsoAction` instance exists.

The user-facing notation

```lean
IsoTransport ⧉ fun G ↦ Set V(G)
```

is syntax, not a function.  `f ⧉ e` expands *before elaboration* to `f e e`, so

```lean
IsoTransport (fun G ↦ Set V(G)) (fun G ↦ Set V(G))
```

and the two copies may acquire different universe levels.  This is the mechanism by which ordinary
universe-polymorphic Lean expressions remain polymorphic at the API boundary; no first-class
`Family` object is needed.

`ULift` is intentionally not baked into the class. If `α : Type u`, then `ULift.{v} α` lives in
`Type (max u v)`, not in `Type v` in general. Thus a canonical lift between arbitrary source and
target universe slices needs a *third* incarnation at the common `max` universe. The two naturality
laws below are the intrinsic coherence condition and do not privilege such a factorization; a
future common-`ULift` constructor can build an `IsoTransport` satisfying them.
-/

@[expose] public section

open Set Function

namespace Graph

universe uV₁ uE₁ uO₁ uV₂ uE₂ uO₂ uO₃ uO₄

/-- Coherent transport between two universe incarnations of graph-dependent data. -/
class IsoTransport (F : {V : Type uV₁} → {E : Type uE₁} → Graph V E → Sort uO₁)
    (F' : outParam ({V : Type uV₂} → {E : Type uE₂} → Graph V E → Sort uO₂)) where
  /-- The ordinary action on the source universe slice. -/
  sourceAction : IsoAction F
  /-- The ordinary action on the target universe slice. -/
  targetAction : IsoAction F'
  /-- Heterogeneous transport along an isomorphism. -/
  map : {V : Type uV₁} → {E : Type uE₁} → {V' : Type uV₂} → {E' : Type uE₂} →
    {G : Graph V E} → {H : Graph V' E'} → Iso G H → F G ≃ F' H
  /-- Precomposing the graph isomorphism acts first by the source `IsoAction`. -/
  map_pre : ∀ {V₀ V₁ : Type uV₁} {E₀ E₁ : Type uE₁} {V₂ : Type uV₂} {E₂ : Type uE₂}
    {G₀ : Graph V₀ E₀} {G₁ : Graph V₁ E₁} {H : Graph V₂ E₂}
    (i : Iso G₀ G₁) (j : Iso G₁ H) (x : F G₀), map (i.comp j) x = map j (sourceAction.map i x)
  /-- Postcomposing the graph isomorphism acts afterwards by the target `IsoAction`. -/
  map_post : ∀ {V₀ : Type uV₁} {E₀ : Type uE₁} {V₁ V₂ : Type uV₂} {E₁ E₂ : Type uE₂}
    {G : Graph V₀ E₀} {H₁ : Graph V₁ E₁} {H₂ : Graph V₂ E₂}
    (i : Iso G H₁) (j : Iso H₁ H₂) (x : F G), map (i.comp j) x = targetAction.map j (map i x)

/-- Duplicate an argument before elaboration, so the two copies may be instantiated at independent
universe levels. `f ⧉ e` expands to `f e e`. -/
syntax:max term:max "⧉" term : term
macro_rules | `($f:term ⧉ $x:term) => `($f $x $x)

namespace IsoTransport

variable {F : {V : Type uV₁} → {E : Type uE₁} → Graph V E → Sort uO₁}
  {F' : {V : Type uV₂} → {E : Type uE₂} → Graph V E → Sort uO₂} [t : IsoTransport F F']

/-- The pointwise source-coherence law as an equality of equivalences. -/
theorem map_pre_eq_trans {V₀ V₁ : Type uV₁} {E₀ E₁ : Type uE₁} {V₂ : Type uV₂} {E₂ : Type uE₂}
    {G₀ : Graph V₀ E₀} {G₁ : Graph V₁ E₁} {H : Graph V₂ E₂} (i : Iso G₀ G₁) (j : Iso G₁ H) :
    t.map (i.comp j) = (t.sourceAction.map i).trans (t.map j) :=
  Equiv.ext (t.map_pre i j)

/-- The pointwise target-coherence law as an equality of equivalences. -/
theorem map_post_eq_trans {V₀ : Type uV₁} {E₀ : Type uE₁} {V₁ V₂ : Type uV₂} {E₁ E₂ : Type uE₂}
    {G : Graph V₀ E₀} {H₁ : Graph V₁ E₁} {H₂ : Graph V₂ E₂} (i : Iso G H₁) (j : Iso H₁ H₂) :
    t.map (i.comp j) = (t.map i).trans (t.targetAction.map j) :=
  Equiv.ext (t.map_post i j)

/-- Proposition-valued transport, in the form callers normally want. -/
theorem iff_of_iso {P : {V : Type uV₁} → {E : Type uE₁} → Graph V E → Prop}
    {P' : {V : Type uV₂} → {E : Type uE₂} → Graph V E → Prop} [IsoTransport P P']
    {V : Type uV₁} {E : Type uE₁} {V' : Type uV₂} {E' : Type uE₂} {G : Graph V E} {H : Graph V' E'}
    (i : Iso G H) : P G ↔ P' H :=
  ⟨IsoTransport.map i, (IsoTransport.map i).symm⟩

/-- Build proposition-valued transport from source, target, and heterogeneous iff theorems.
The coherence fields are automatic by proof irrelevance. -/
@[instance_reducible]
def of_iff {P : {V : Type uV₁} → {E : Type uE₁} → Graph V E → Prop}
    {P' : {V : Type uV₂} → {E : Type uE₂} → Graph V E → Prop}
    (hsource : ∀ {V V' : Type uV₁} {E E' : Type uE₁} {G : Graph V E} {H : Graph V' E'},
      Iso G H → (P G ↔ P H))
    (htarget : ∀ {V V' : Type uV₂} {E E' : Type uE₂} {G : Graph V E} {H : Graph V' E'},
      Iso G H → (P' G ↔ P' H))
    (hcross : ∀ {V : Type uV₁} {E : Type uE₁} {V' : Type uV₂} {E' : Type uE₂}
      {G : Graph V E} {H : Graph V' E'}, Iso G H → (P G ↔ P' H)) : IsoTransport P P' where
  sourceAction := IsoAction.of_iff P hsource
  targetAction := IsoAction.of_iff P' htarget
  map i := IsoAction.equivOfIff (hcross i)
  map_pre _ _ _ := Subsingleton.elim _ _
  map_post _ _ _ := Subsingleton.elim _ _

end IsoTransport

/-- A coherent same-universe transport contains an ordinary action.  This is deliberately low
priority: direct `IsoAction` instances remain the canonical same-universe resolution path. -/
instance (priority := 100) instIsoActionOfTransport
    (F : {V : Type uV₁} → {E : Type uE₁} → Graph V E → Sort uO₁) [t : IsoTransport F F] :
    IsoAction F :=
  t.sourceAction

/-! ### Structural transport instances -/

instance instTransportConst (R : Sort uO₁) : IsoTransport (fun {_ : Type uV₁} {_ : Type uE₁} _ ↦ R)
    (fun {_ : Type uV₂} {_ : Type uE₂} _ ↦ R) where
  sourceAction := inferInstance
  targetAction := inferInstance
  map _ := Equiv.refl R
  map_pre _ _ _ := rfl
  map_post _ _ _ := rfl

instance instTransportVertices : IsoTransport
    (fun {V : Type uV₁} {E : Type uE₁} (G : Graph V E) ↦ V(G))
    (fun {V : Type uV₂} {E : Type uE₂} (G : Graph V E) ↦ V(G)) where
  sourceAction := inferInstance
  targetAction := inferInstance
  map := Iso.vertexEquiv
  map_pre := Iso.vertexEquiv_comp
  map_post := Iso.vertexEquiv_comp

instance instTransportEdges : IsoTransport
    (fun {V : Type uV₁} {E : Type uE₁} (G : Graph V E) ↦ E(G))
    (fun {V : Type uV₂} {E : Type uE₂} (G : Graph V E) ↦ E(G)) where
  sourceAction := inferInstance
  targetAction := inferInstance
  map := Iso.edgeEquiv
  map_pre := Iso.edgeEquiv_comp
  map_post := Iso.edgeEquiv_comp

instance instTransportArrow (F : {V : Type uV₁} → {E : Type uE₁} → Graph V E → Sort uO₁)
    (F' : {V : Type uV₂} → {E : Type uE₂} → Graph V E → Sort uO₂)
    (K : {V : Type uV₁} → {E : Type uE₁} → Graph V E → Sort uO₃)
    (K' : {V : Type uV₂} → {E : Type uE₂} → Graph V E → Sort uO₄) [tF : IsoTransport F F']
    [tK : IsoTransport K K'] : IsoTransport (fun G ↦ F G → K G) (fun G ↦ F' G → K' G) where
  sourceAction := by
    letI := tF.sourceAction
    letI := tK.sourceAction
    infer_instance
  targetAction := by
    letI := tF.targetAction
    letI := tK.targetAction
    infer_instance
  map i :=
    { toFun := fun f y ↦ tK.map i (f ((tF.map i).symm y))
      invFun := fun g x ↦ (tK.map i).symm (g (tF.map i x))
      left_inv := by intro f; funext x; simp
      right_inv := by intro g; funext y; simp }
  map_pre i j f := by
    funext y
    change tK.map (i.comp j) (f ((tF.map (i.comp j)).symm y)) = _
    rw [tF.map_pre_eq_trans i j, tK.map_pre_eq_trans i j]
    rfl
  map_post i j f := by
    funext y
    change tK.map (i.comp j) (f ((tF.map (i.comp j)).symm y)) = _
    rw [tF.map_post_eq_trans i j, tK.map_post_eq_trans i j]
    rfl

instance instTransportProd (F : {V : Type uV₁} → {E : Type uE₁} → Graph V E → Type uO₁)
    (F' : {V : Type uV₂} → {E : Type uE₂} → Graph V E → Type uO₂)
    (K : {V : Type uV₁} → {E : Type uE₁} → Graph V E → Type uO₃)
    (K' : {V : Type uV₂} → {E : Type uE₂} → Graph V E → Type uO₄) [tF : IsoTransport F F']
    [tK : IsoTransport K K'] : IsoTransport (fun G ↦ F G × K G) (fun G ↦ F' G × K' G) where
  sourceAction := by
    letI := tF.sourceAction
    letI := tK.sourceAction
    infer_instance
  targetAction := by
    letI := tF.targetAction
    letI := tK.targetAction
    infer_instance
  map i := Equiv.prodCongr (tF.map i) (tK.map i)
  map_pre i j x := by
    rw [tF.map_pre_eq_trans i j, tK.map_pre_eq_trans i j]
    rfl
  map_post i j x := by
    rw [tF.map_post_eq_trans i j, tK.map_post_eq_trans i j]
    rfl

instance instTransportSum (F : {V : Type uV₁} → {E : Type uE₁} → Graph V E → Type uO₁)
    (F' : {V : Type uV₂} → {E : Type uE₂} → Graph V E → Type uO₂)
    (K : {V : Type uV₁} → {E : Type uE₁} → Graph V E → Type uO₃)
    (K' : {V : Type uV₂} → {E : Type uE₂} → Graph V E → Type uO₄) [tF : IsoTransport F F']
    [tK : IsoTransport K K'] : IsoTransport (fun G ↦ F G ⊕ K G) (fun G ↦ F' G ⊕ K' G) where
  sourceAction := by
    letI := tF.sourceAction
    letI := tK.sourceAction
    infer_instance
  targetAction := by
    letI := tF.targetAction
    letI := tK.targetAction
    infer_instance
  map i := Equiv.sumCongr (tF.map i) (tK.map i)
  map_pre i j x := by
    rw [tF.map_pre_eq_trans i j, tK.map_pre_eq_trans i j]
    cases x <;> rfl
  map_post i j x := by
    rw [tF.map_post_eq_trans i j, tK.map_post_eq_trans i j]
    cases x <;> rfl

instance instTransportOption (F : {V : Type uV₁} → {E : Type uE₁} → Graph V E → Type uO₁)
    (F' : {V : Type uV₂} → {E : Type uE₂} → Graph V E → Type uO₂)
    [tF : IsoTransport F F'] : IsoTransport (fun G ↦ Option (F G)) (fun G ↦ Option (F' G)) where
  sourceAction := by
    letI := tF.sourceAction
    infer_instance
  targetAction := by
    letI := tF.targetAction
    infer_instance
  map i := Equiv.optionCongr (tF.map i)
  map_pre i j x := by
    rw [tF.map_pre_eq_trans i j]
    cases x <;> rfl
  map_post i j x := by
    rw [tF.map_post_eq_trans i j]
    cases x <;> rfl

instance instTransportSet (F : {V : Type uV₁} → {E : Type uE₁} → Graph V E → Type uO₁)
    (F' : {V : Type uV₂} → {E : Type uE₂} → Graph V E → Type uO₂) [tF : IsoTransport F F'] :
    IsoTransport (fun G ↦ Set (F G)) (fun G ↦ Set (F' G)) where
  sourceAction := by
    letI := tF.sourceAction
    infer_instance
  targetAction := by
    letI := tF.targetAction
    infer_instance
  map i := Equiv.Set.congr (tF.map i)
  map_pre i j s := by
    rw [tF.map_pre_eq_trans i j]
    exact (Set.image_image (tF.map j) (tF.sourceAction.map i) s).symm
  map_post i j s := by
    rw [tF.map_post_eq_trans i j]
    exact (Set.image_image (tF.targetAction.map j) (tF.map i) s).symm

end Graph
