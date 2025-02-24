import Mathlib

universe u u₁ u₂ v w

open Cardinal

example (a₁ : Cardinal.{max u u₁}) (a₂ : Cardinal.{max u u₂})
    (h : lift.{max u u₁, max u u₂} a₂ = lift.{max u u₂, max u u₁} a₁) :
    lift.{u₁, max u u₂} a₂ = lift.{u₂, max u u₁} a₁ := by
  simp_rw [← Cardinal.lift_umax] at h ⊢
  exact h

@[simp]
theorem Cardinal.lift_umax_le {a : Cardinal.{u}} {b : Cardinal.{v}} :
    lift.{max v w, u} a ≤ lift.{max u w, v} b ↔ lift.{v, u} a ≤ lift.{u, v} b := by
  simp_rw [le_lift_iff]
  refine ⟨fun ⟨a', ha'b, ha'⟩ ↦ ?_, fun ⟨a', ha'b, h⟩↦ ?_⟩
  · rw [lift_umax_eq] at ha'
    exact ⟨a', ha'b, ha'⟩
  refine ⟨a', ha'b, by rwa [lift_umax_eq]⟩

noncomputable def rank {m n R : Type*} [Semiring R] (A : Matrix m n R) : ℕ :=
  Module.finrank R <| Submodule.span R <| Set.range A.transpose
