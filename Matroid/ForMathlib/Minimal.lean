import Mathlib.Order.Minimal

variable {α : Type*} [LE α] {x : α} {P Q : α → Prop}

theorem minimal_congr (h : ∀ x, P x ↔ Q x) : Minimal P x ↔ Minimal Q x := by
  rw [show P = Q from funext fun x ↦ propext (h _)]

theorem maximal_congr (h : ∀ x, P x ↔ Q x) : Maximal P x ↔ Maximal Q x := by
  rw [show P = Q from funext fun x ↦ propext (h _)]

theorem minimal_and_iff_left_of_imp' (h : ∀ ⦃x⦄, P x → ∃ y, y ≤ x ∧ P y ∧ Q y) :
    Minimal P x ↔ Minimal (fun x ↦ P x ∧ Q x) x := by
