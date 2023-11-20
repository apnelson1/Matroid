import Matroid.Representation.Basic
import Mathlib

open Set Matrix

variable {α β η 𝔽 : Type*} [Field 𝔽]

namespace Matroid

theorem foo [Fintype α] {B : Set α} (P : Matrix η B 𝔽) :
  Matroid.
