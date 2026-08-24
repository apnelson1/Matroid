/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Matroid.ForMathlib.Tactic.IRw
public import Mathlib.SetTheory.Cardinal.Defs

/-!
# Ordinary equivalences as an `irw` transport system

This is the first domain-independent adapter for `irw`: a chosen `e : α ≃ β` transports the
carrier `α` directly to `β`. Structural closure in the generic engine then transports sets,
products, sums, options, and nondependent function spaces.
-/

@[expose] public section

namespace IRw

universe u v

open scoped Cardinal

attribute [irw_system] Equiv

/-- The primitive domain action of an ordinary type equivalence is the equivalence itself. -/
@[irw_equiv]
def Equiv.irw_domain {α : Sort u} {β : Sort v} (e : α ≃ β) : α ≃ β := e

/-- Proposition-valued naturality for cardinality. -/
@[irw_naturality]
theorem Equiv.irw_cardinal_mk_eq {α β : Type u}
    (e : α ≃ β) (c : Cardinal) : (#α = c) ↔ (#β = c) := by
  rw [Cardinal.mk_congr e]

end IRw
