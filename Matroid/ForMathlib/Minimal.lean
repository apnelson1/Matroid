import Mathlib.Order.Minimal

open Set

variable {α : Type*} [LE α] {x : α} {P Q : α → Prop}

theorem minimal_congr (h : ∀ x, P x ↔ Q x) : Minimal P x ↔ Minimal Q x := by
  rw [show P = Q from funext fun x ↦ propext (h _)]

theorem maximal_congr (h : ∀ x, P x ↔ Q x) : Maximal P x ↔ Maximal Q x := by
  rw [show P = Q from funext fun x ↦ propext (h _)]

lemma minimal_apply_monotone_mem_iff {β : Type*} [Preorder β] {f : α → β} {s : Set β}
    (hmono : ∀ ⦃x y⦄, f x ∈ s → f y ∈ s → (f x ≤ f y ↔ x ≤ y)) (hf : s ⊆ range f) :
    Minimal (f · ∈ s) x ↔ Minimal (· ∈ s) (f x) := by
  simp only [Minimal, and_congr_right_iff]
  refine fun hxs ↦ ⟨fun h y hys hyx ↦ ?_, fun h y hys hyx ↦ ?_⟩
  · obtain ⟨y, rfl⟩ := hf hys
    exact (hmono hxs hys).2 <| h hys <| (hmono hys hxs).1 hyx
  rw [← hmono hxs hys]
  exact h hys ((hmono hys hxs).2 hyx)

lemma minimal_apply_antitone_mem_iff {β : Type*} [Preorder β] {f : α → β} {s : Set β}
    (hanti : ∀ ⦃x y⦄, f x ∈ s → f y ∈ s → (f x ≤ f y ↔ y ≤ x)) (hf : s ⊆ range f) :
    Minimal (f · ∈ s) x ↔ Maximal (· ∈ s) (f x) :=
  minimal_apply_monotone_mem_iff (α := α) (β := βᵒᵈ) (fun _ _ hx hy ↦ hanti hy hx) hf

lemma maximal_apply_monotone_mem_iff {β : Type*} [Preorder β] {f : α → β} {s : Set β}
    (hmono : ∀ ⦃x y⦄, f x ∈ s → f y ∈ s → (f x ≤ f y ↔ x ≤ y)) (hf : s ⊆ range f) :
    Maximal (f · ∈ s) x ↔ Maximal (· ∈ s) (f x) :=
  minimal_apply_monotone_mem_iff (α := αᵒᵈ) (β := βᵒᵈ) (fun _ _ hx hy ↦ hmono hy hx) hf

lemma maximal_apply_antitone_mem_iff {β : Type*} [Preorder β] {f : α → β} {s : Set β}
    (hanti : ∀ ⦃x y⦄, f x ∈ s → f y ∈ s → (f x ≤ f y ↔ y ≤ x)) (hf : s ⊆ range f) :
    Maximal (f · ∈ s) x ↔ Minimal (· ∈ s) (f x) :=
  minimal_apply_monotone_mem_iff (α := αᵒᵈ) (β := β) hanti hf
