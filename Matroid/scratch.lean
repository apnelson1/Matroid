import Mathlib.Data.ENat.Lattice

variable {α : Type*}

structure foo (α : Type*) where
  carrier : α
  h_eq : carrier = carrier


instance : Coe (foo α) α where
  coe a := a.carrier

attribute [coe] (coe : )

example (b : foo α) : (b : α) = b := by
  sorry
