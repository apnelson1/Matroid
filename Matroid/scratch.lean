import Mathlib

variable {R ι : Type*} [CommSemiring R] {φ : ι → Type*} {ψ : ι → Type*}

#check LinearEquiv.piCongrRight

example (c : ι → Rˣ) : (ι → R) ≃ₗ[R] (ι → R) :=
  LinearEquiv.piCongrRight (fun i ↦ LinearEquiv.smulOfUnit (c i))
