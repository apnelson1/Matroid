/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Matroid.Graph.Iso.IsoTransport

/-!
# Compatibility view for homogeneous isomorphism actions

The structural hierarchy now lives entirely in `IsoTransport`.  `IsoAction F` is retained only as
the diagonal view `IsoTransport F F`, so existing imports and theorem statements can migrate
incrementally.  There are deliberately no structural `IsoAction` instances in this file.

The homogeneous map is the *source action* stored in the diagonal `IsoTransport`; it is not the
heterogeneous `IsoTransport.map`.  Keeping this distinction is necessary because the heterogeneous
map is not, in general, forced to coincide with either endpoint action even when the universe
levels happen to unify.
-/

@[expose] public section

open Set Function

namespace Graph

universe uV uE uO

/-- Compatibility name for the diagonal of `IsoTransport`.

This is an abbreviation, not a second typeclass hierarchy. -/
abbrev IsoAction
    (F : {V : Type uV} → {E : Type uE} → Graph V E → Sort uO) :=
  IsoTransport F F

namespace IsoAction

variable {F : {V : Type uV} → {E : Type uE} → Graph V E → Sort uO} [t : IsoAction F]

/-- The homogeneous action extracted from the source endpoint of the diagonal transport. -/
def map {V V' : Type uV} {E E' : Type uE} {G : Graph V E} {H : Graph V' E'} (i : Iso G H) :
    F G ≃ F H := t.sourceAction.map i

@[simp] theorem map_id {V : Type uV} {E : Type uE} (G : Graph V E) (x : F G) :
    map (F := F) (Iso.id G) x = x :=
  t.sourceAction.map_id G x

 theorem map_comp {V V' V'' : Type uV} {E E' E'' : Type uE}
    {G : Graph V E} {H : Graph V' E'} {K : Graph V'' E''}
    (i : Iso G H) (j : Iso H K) (x : F G) :
    map (F := F) (i.comp j) x = map (F := F) j (map (F := F) i x) :=
  t.sourceAction.map_comp i j x

 theorem map_symm
    {V V' : Type uV} {E E' : Type uE}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) :
    map (F := F) i.symm = (map (F := F) i).symm :=
  t.sourceAction.map_symm i

@[simp] theorem map_symm_apply
    {V V' : Type uV} {E E' : Type uE}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) (y : F H) :
    map (F := F) i.symm y = (map (F := F) i).symm y := by
  rw [map_symm]

@[simp] theorem map_id_eq_refl
    {V : Type uV} {E : Type uE} (G : Graph V E) :
    map (F := F) (Iso.id G) = Equiv.refl (F G) :=
  Equiv.ext (map_id G)

 theorem map_comp_eq_trans
    {V V' V'' : Type uV} {E E' E'' : Type uE}
    {G : Graph V E} {H : Graph V' E'} {K : Graph V'' E''}
    (i : Iso G H) (j : Iso H K) :
    map (F := F) (i.comp j) = (map (F := F) i).trans (map (F := F) j) :=
  Equiv.ext (map_comp i j)

/-- Equivalence of proof types corresponding to an iff. -/
def equivOfIff {P Q : Prop} (h : P ↔ Q) : P ≃ Q where
  toFun := h.mp
  invFun := h.mpr
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- Backwards-compatible constructor for proposition-valued diagonal actions.

New graph properties should normally register `InvariantTransport ⧉ P` in `Invariant.lean`
instead. -/
@[instance_reducible]
noncomputable def of_iff
    (P : {V : Type uV} → {E : Type uE} → Graph V E → Prop)
    (h : ∀ {V V' : Type uV} {E E' : Type uE}
      {G : Graph V E} {H : Graph V' E'}, Iso G H → (P G ↔ P H)) :
    IsoAction P :=
  IsoTransport.of_iff h h h

/-- A proposition-valued homogeneous action supplies an iff. -/
theorem iff_of_iso
    {P : {V : Type uV} → {E : Type uE} → Graph V E → Prop} [IsoAction P]
    {V V' : Type uV} {E E' : Type uE}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) : P G ↔ P H :=
  ⟨map (F := P) i, (map (F := P) i).symm⟩

@[simp]
theorem map_set {A : {V : Type uV} → {E : Type uE} → Graph V E → Type _} [IsoAction A]
    {V V' : Type uV} {E E' : Type uE} {G : Graph V E} {H : Graph V' E'} (i : Iso G H)
    (X : Set (A G)) :
    IsoAction.map (F := fun G ↦ Set (A G)) i X = Equiv.Set.congr (IsoAction.map (F := A) i) X := by
  rfl

end IsoAction

/-! ### Objects equal up to relabelling -/

/-- `x : F G` and `y : F H` name the same object up to the homogeneous action of an isomorphism. -/
def IsoRelated {F : {V : Type uV} → {E : Type uE} → Graph V E → Sort uO} [IsoAction F]
    {V V' : Type uV} {E E' : Type uE} {G : Graph V E} {H : Graph V' E'} (x : F G) (y : F H) :
    Prop :=
  ∃ i : Iso G H, IsoAction.map i x = y

namespace IsoRelated

variable {F : {V : Type uV} → {E : Type uE} → Graph V E → Sort uO} [IsoAction F]
  {V V' V'' : Type uV} {E E' E'' : Type uE} {G : Graph V E} {H : Graph V' E'} {K : Graph V'' E''}

@[refl] theorem refl (x : F G) : IsoRelated x x :=
  ⟨Iso.id G, IsoAction.map_id G x⟩

@[symm] theorem symm {x : F G} {y : F H} (h : IsoRelated x y) : IsoRelated y x := by
  obtain ⟨i, rfl⟩ := h
  exact ⟨i.symm, by rw [IsoAction.map_symm, Equiv.symm_apply_apply]⟩

 theorem trans {x : F G} {y : F H} {z : F K} (h : IsoRelated x y) (h' : IsoRelated y z) :
    IsoRelated x z := by
  obtain ⟨i, rfl⟩ := h
  obtain ⟨j, rfl⟩ := h'
  exact ⟨i.comp j, IsoAction.map_comp i j x⟩

end IsoRelated

end Graph
