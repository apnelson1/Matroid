/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Matroid.Transport

/-!
# `irw` registrations for matroids

This file contains no tactic logic.  It registers the primitive equivalences and atomic iff facts
that the generic `IRw.Core.transportProp` engine consumes.

Two conventions matter for the rules to compose, and both are load-bearing.

* **State every rule's right-hand side using the registered `@[irw_equiv]` equivalence**, not using
  `⇑i` directly.  When `irw` walks under a binder it substitutes `e.symm y` for the bound variable,
  so a rule stated with `e` produces `e (e.symm y)`, which the tactic's cleanup pass collapses with
  `Equiv.apply_symm_apply`.  A rule stated with `⇑i '' _` leaves an `⇑i '' (⇑e.symm '' y)` residue
  that no generic lemma can remove.  The two spellings are definitionally equal, so `exact` still
  accepts a hypothesis written the ordinary way.
* **The ambient (`_supported`) rules have higher priority than the intrinsic ones.** Unification
  can match the intrinsic `M.Indep ↑I` against an ambient `M.Indep X.1` by unfolding the
  supported-set equivalence. The explicit priority records that the theorem retaining the bundled
  support proof is the more specific rule; declaration/import order is irrelevant.
-/

@[expose] public section

open Set

namespace Matroid

universe uα uβ

variable {α : Type uα} {β : Type uβ} {M : Matroid α} {N : Matroid β}

/-! ## Intrinsic atomic propositions -/

theorem Iso.irw_indep (i : M ≂ N) (I : Set M.E) :
    M.Indep (↑I : Set α) ↔ N.Indep (↑(i.groundSetEquiv I) : Set β) :=
  i.indep_image_iff

theorem Iso.irw_dep (i : M ≂ N) (D : Set M.E) :
    M.Dep (↑D : Set α) ↔ N.Dep (↑(i.groundSetEquiv D) : Set β) :=
  i.dep_image_iff

theorem Iso.irw_isBase (i : M ≂ N) (B : Set M.E) :
    M.IsBase (↑B : Set α) ↔ N.IsBase (↑(i.groundSetEquiv B) : Set β) :=
  i.isBase_image_iff

theorem Iso.irw_isBasis (i : M ≂ N) (I X : Set M.E) :
    M.IsBasis (↑I : Set α) (↑X : Set α) ↔
      N.IsBasis (↑(i.groundSetEquiv I) : Set β) (↑(i.groundSetEquiv X) : Set β) :=
  i.isBasis_image_iff

theorem Iso.irw_spanning (i : M ≂ N) (X : Set M.E) :
    M.Spanning (↑X : Set α) ↔ N.Spanning (↑(i.groundSetEquiv X) : Set β) :=
  i.spanning_iff X

theorem Iso.irw_coindep (i : M ≂ N) (X : Set M.E) :
    M.Coindep (↑X : Set α) ↔ N.Coindep (↑(i.groundSetEquiv X) : Set β) := by
  simp only [coindep_def, Iso.groundSetEquiv_apply]
  have h := i.dual.indep_image_iff (I := X)
  rw [Iso.dual_image'] at h
  exact h

theorem Iso.irw_codep (i : M ≂ N) (X : Set M.E) :
    M.Codep (↑X : Set α) ↔ N.Codep (↑(i.groundSetEquiv X) : Set β) := by
  rw [codep_def, codep_def, Iso.groundSetEquiv_apply]
  have h := i.dual.dep_image_iff (D := X)
  rw [Iso.dual_image'] at h
  exact h

theorem Iso.irw_nonspanning (i : M ≂ N) (X : Set M.E) :
    M.Nonspanning (↑X : Set α) ↔ N.Nonspanning (↑(i.groundSetEquiv X) : Set β) := by
  rw [nonspanning_iff, nonspanning_iff, Iso.groundSetEquiv_apply,
    and_iff_left (Subtype.coe_image_subset _ _),
    and_iff_left (Subtype.coe_image_subset _ _)]
  exact not_congr (i.spanning_iff X)

theorem Iso.irw_encard_le (i : M ≂ N) (X : Set M.E) (k : ℕ∞) :
    X.encard ≤ k ↔ (i.groundSetEquiv X).encard ≤ k := by
  rw [Iso.groundSetEquiv_apply, (EquivLike.injective i).encard_image]

/-! ## Ambient supported atomic propositions

These are the rules that make guarded quantifiers over ambient sets useful.  The generic tactic
bundles a guard `X ⊆ M.E` into `{X : Set α // X ⊆ M.E}`; these rules then consume that bundled
variable without asking unification to reconstruct it from its `.val` projection.
-/

theorem Iso.irw_indep_supported (i : M ≂ N) (X : {X : Set α // X ⊆ M.E}) :
    M.Indep X.1 ↔ N.Indep (i.supportedGroundSetEquiv X).1 := by
  simpa [supportedSetEquiv, Set.inter_eq_right.2 X.2] using
    (i.irw_indep (supportedSetEquiv M X))

theorem Iso.irw_dep_supported (i : M ≂ N) (X : {X : Set α // X ⊆ M.E}) :
    M.Dep X.1 ↔ N.Dep (i.supportedGroundSetEquiv X).1 := by
  simpa [supportedSetEquiv, Set.inter_eq_right.2 X.2] using
    (i.irw_dep (supportedSetEquiv M X))

theorem Iso.irw_isBase_supported (i : M ≂ N) (X : {X : Set α // X ⊆ M.E}) :
    M.IsBase X.1 ↔ N.IsBase (i.supportedGroundSetEquiv X).1 := by
  simpa [supportedSetEquiv, Set.inter_eq_right.2 X.2] using
    (i.irw_isBase (supportedSetEquiv M X))

theorem Iso.irw_spanning_supported (i : M ≂ N) (X : {X : Set α // X ⊆ M.E}) :
    M.Spanning X.1 ↔ N.Spanning (i.supportedGroundSetEquiv X).1 := by
  simpa [supportedSetEquiv, Set.inter_eq_right.2 X.2] using
    (i.irw_spanning (supportedSetEquiv M X))

theorem Iso.irw_coindep_supported (i : M ≂ N) (X : {X : Set α // X ⊆ M.E}) :
    M.Coindep X.1 ↔ N.Coindep (i.supportedGroundSetEquiv X).1 := by
  simpa [supportedSetEquiv, Set.inter_eq_right.2 X.2] using
    (i.irw_coindep (supportedSetEquiv M X))

theorem Iso.irw_codep_supported (i : M ≂ N) (X : {X : Set α // X ⊆ M.E}) :
    M.Codep X.1 ↔ N.Codep (i.supportedGroundSetEquiv X).1 := by
  simpa [supportedSetEquiv, Set.inter_eq_right.2 X.2] using
    (i.irw_codep (supportedSetEquiv M X))

theorem Iso.irw_nonspanning_supported (i : M ≂ N) (X : {X : Set α // X ⊆ M.E}) :
    M.Nonspanning X.1 ↔ N.Nonspanning (i.supportedGroundSetEquiv X).1 := by
  simpa [supportedSetEquiv, Set.inter_eq_right.2 X.2] using
    (i.irw_nonspanning (supportedSetEquiv M X))

theorem Iso.irw_isBasis_supported (i : M ≂ N)
    (I X : {X : Set α // X ⊆ M.E}) :
    M.IsBasis I.1 X.1 ↔
      N.IsBasis (i.supportedGroundSetEquiv I).1
        (i.supportedGroundSetEquiv X).1 := by
  simpa [supportedSetEquiv, Set.inter_eq_right.2 I.2, Set.inter_eq_right.2 X.2] using
    (i.irw_isBasis (supportedSetEquiv M I) (supportedSetEquiv M X))

/-! ## Registration for Mathlib-owned predicates

These registrations remain in an adapter because the predicates are declared in Mathlib. The
supported forms are deliberately more specific and therefore receive higher priority. -/

attribute [irw_naturality] Iso.supportedGroundSetEquiv_subset

attribute [irw_naturality high]
  Iso.irw_indep_supported
  Iso.irw_dep_supported
  Iso.irw_isBase_supported
  Iso.irw_isBasis_supported
  Iso.irw_spanning_supported
  Iso.irw_coindep_supported
  Iso.irw_codep_supported
  Iso.irw_nonspanning_supported

attribute [irw_naturality]
  Iso.irw_indep
  Iso.irw_dep
  Iso.irw_isBase
  Iso.irw_isBasis
  Iso.irw_spanning
  Iso.irw_coindep
  Iso.irw_codep
  Iso.irw_nonspanning
  Iso.irw_encard_le

end Matroid
