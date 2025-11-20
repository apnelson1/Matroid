import Mathlib.Data.ENat.Lattice
import Mathlib.Tactic.ENatToNat

variable {α : Type} {a b c d e f g : α} {f : α → ℕ∞}


lemma ENat.ne_top_iff_lt_top {x : ℕ∞} : x ≠ ⊤ ↔ x < ⊤ := by
  rw [lt_top_iff_ne_top]

attribute [enat_to_nat_top] not_true

example {x y z : ℕ∞} (h1 : x + 1 ≤ y) (h2 : y ≤ z) (hx : x ≠ ⊤) : x < z := by
  enat_to_nat
  omega

example (h1 : f a + 1 ≤ f b) (h2 : f b ≤ f c) (h3 : f a < ⊤) : f a < f c := by
  generalize f a = x at *
  generalize f b = y at *
  generalize f c = z at *
  enat_to_nat
  omega
