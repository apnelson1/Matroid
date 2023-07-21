import Mathlib.Order.Minimal 
import Mathlib.Order.Bounds.Basic 
import Mathlib.Data.Set.Finite
import Mathlib.Data.Nat.Interval



-- variable {α : Type _} {r : α → α → Prop} {P : α → Prop}
/-- This seems a strict improvement over the nonprimed version in mathlib - only the image needs to 
be finite, not the set itself.  -/
lemma Set.Finite.exists_maximal_wrt' {α β : Type _} [PartialOrder β] (f : α → β) (s : Set α) 
    (h : (f '' s).Finite) (h₀ : s.Nonempty) : 
  (∃ a ∈ s, ∀ (a' : α), a' ∈ s → f a ≤ f a' → f a = f a') := by
  obtain  ⟨_ ,⟨a,ha,rfl⟩, hmax⟩ := Finite.exists_maximal_wrt id (f '' s) h (h₀.image f)
  exact ⟨a, ha, fun a' ha' hf ↦ hmax _ (mem_image_of_mem f ha') hf⟩
