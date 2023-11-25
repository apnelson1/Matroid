import Mathlib.Tactic

class P1 (n : ℕ) : Prop where
  (p : 37 < n)

class P2 (m n : ℕ) extends P1 n : Prop where
  (q : n < m)
  (p' : 2 < n)

instance foo (m n : ℕ) [h : P2 m n] : P1 n :=
  ⟨h.p⟩

/-
cannot find synthesization order for instance foo with type
  ∀ (m n : ℕ) [h : P2 m n], P1 n
all remaining arguments have metavariables:
  P2 ?m n
  -/
