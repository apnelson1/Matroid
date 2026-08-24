/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Matroid.Equiv

/-!
# Canonical transport under matroid isomorphism

Project-owned transport domains and equivalences are registered beside their definitions.
-/

@[expose] public section

open Set

namespace Matroid

universe uα uβ

variable {α : Type uα} {β : Type uβ} {M : Matroid α} {N : Matroid β}

/-! ## Binder equivalences -/

/-- Ambient subsets supported on the ground are equivalent to intrinsic subsets of `M.E`. -/
def supportedSetEquiv (M : Matroid α) : {X : Set α // X ⊆ M.E} ≃ Set M.E where
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

/-- Primitive supported action on ambient matroid elements. -/
@[irw_domain]
def Iso.elementDomain (i : M ≂ N) : IRw.SupportedDomain α β where
  sourceSupport x := x ∈ M.E
  targetSupport y := y ∈ N.E
  equiv := i.toEquiv

/-- Sets of ground elements.  Registering this explicitly (rather than letting the tactic build
`Equiv.Set.congr` from `toEquiv`) is what lets the rules below name the equivalence that
`irw` will actually substitute. -/
@[irw_equiv]
def Iso.groundSetEquiv (i : M ≂ N) : Set M.E ≃ Set N.E := Equiv.Set.congr i.toEquiv

@[irw_equiv]
def Iso.listGroundSetEquiv (i : M ≂ N) : List M.E ≃ List N.E := i.toEquiv.listEquivOfEquiv

@[simp]
theorem Iso.groundSetEquiv_apply (i : M ≂ N) (I : Set M.E) :
    i.groundSetEquiv I = i '' I := rfl

/-- Transport an ambient set together with the information that it is supported on the ground. -/
@[irw_equiv]
def Iso.supportedGroundSetEquiv (i : M ≂ N) :
    {X : Set α // X ⊆ M.E} ≃ {Y : Set β // Y ⊆ N.E} :=
  i.elementDomain.set.equiv

@[simp]
theorem Iso.supportedGroundSetEquiv_apply_val (i : M ≂ N) (X : {X : Set α // X ⊆ M.E}) :
    (i.supportedGroundSetEquiv X).1 =
      Subtype.val '' (i '' (Subtype.val ⁻¹' X.1)) := rfl

@[simp]
theorem Iso.elementDomain_set_equiv_apply_val (i : M ≂ N)
    (X : {X : Set α // X ⊆ M.E}) :
    (i.elementDomain.set.equiv X).1 =
      Subtype.val '' (i '' (Subtype.val ⁻¹' X.1)) := rfl

/-- The structural equivalence on supported ambient sets preserves inclusion. -/
theorem Iso.supportedGroundSetEquiv_subset (i : M ≂ N)
    (X Y : {X : Set α // X ⊆ M.E}) :
    X.1 ⊆ Y.1 ↔
      (i.supportedGroundSetEquiv X).1 ⊆ (i.supportedGroundSetEquiv Y).1 := by
  constructor
  · intro h _ hz
    rw [i.supportedGroundSetEquiv_apply_val] at hz ⊢
    obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hz
    exact ⟨i x, ⟨x, h hx, rfl⟩, rfl⟩
  · intro h x hx
    let x' : M.E := ⟨x, X.2 hx⟩
    have hx' : (i x' : N.E).1 ∈ (i.supportedGroundSetEquiv X).1 := by
      rw [i.supportedGroundSetEquiv_apply_val]
      exact ⟨i x', ⟨x', hx, rfl⟩, rfl⟩
    have hy' := h hx'
    rw [i.supportedGroundSetEquiv_apply_val] at hy'
    obtain ⟨_, ⟨y, hy, rfl⟩, heq⟩ := hy'
    have hxy : y = x' := (EquivLike.injective i) (Subtype.ext heq)
    simpa [hxy] using hy


end Matroid
