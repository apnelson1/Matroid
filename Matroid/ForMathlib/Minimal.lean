import Mathlib.Order.Minimal

variable {α : Type*} [LE α] {x : α} {P Q : α → Prop}

theorem minimal_congr (h : ∀ x, P x ↔ Q x) : Minimal P x ↔ Minimal Q x := by
  rw [show P = Q from funext fun x ↦ propext (h _)]

theorem maximal_congr (h : ∀ x, P x ↔ Q x) : Maximal P x ↔ Maximal Q x := by
  rw [show P = Q from funext fun x ↦ propext (h _)]

theorem minimal_and_iff_left_of_imp' (h : ∀ ⦃x⦄, P x → ∃ y, y ≤ x ∧ P y ∧ Q y) :
    Minimal (fun x ↦ P x ∧ Q x) x ↔ Minimal P x := by
  refine ⟨fun h' ↦ ⟨h'.prop.1, fun y hy hyx ↦ ?_⟩, fun h' ↦ ?_⟩
  · obtain ⟨z, hzy, hPz, hQz⟩ := h hy



    refine h'.le_of_le ⟨hy, h _ ⟨hy, fun z hz hzy ↦ ?_⟩⟩ hyx
    have := h'.le_of_le (y := z)
  -- rw [Minimal, Minimal, and_assoc, and_congr_right_iff]
  -- refine fun hx ↦ ⟨fun h y hy hyx ↦ ?_, fun h ↦ ?_⟩
  -- ·
