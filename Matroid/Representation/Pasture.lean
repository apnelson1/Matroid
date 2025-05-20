import Mathlib.Algebra.GroupWithZero.Defs

structure Pasture (M : Type*) [CommGroupWithZero M] where
  IsNull : M → M → M → Prop
  ε : M
  isNull_swap₁₂ {a b c : M} : IsNull a b c → IsNull b a c
  isNull_swap₂₃ {a b c : M} : IsNull a b c → IsNull a c b
  isNull_mul {a b c : M} (s : M) : IsNull a b c → IsNull (s * a) (s * b) (s * c)
  isNull_zero_zero_iff {a : M} : IsNull a 0 0 ↔ a = 0
  isNull_one_iff : ∀ x, IsNull 1 x 0 ↔ x = ε

namespace Pasture

variable {M : Type*} [CommGroupWithZero M] {P : Pasture M} {a b c : M}

lemma isNull_swap₁₃ (h : P.IsNull a b c) : P.IsNull c b a := by
  have h1 := P.isNull_swap₂₃ h
  have h2 := P.isNull_swap₁₂ h1
  have h3 := P.isNull_swap₂₃ h2
  exact h3
