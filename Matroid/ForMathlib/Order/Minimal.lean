import Mathlib.Order.Minimal

open Set

lemma mem_maximals_iff_forall_insert {α : Type*} {P : Set α → Prop}
    (hP : ∀ ⦃s t⦄, P t → s ⊆ t → P s) {s : Set α} :
    s ∈ maximals (· ⊆ ·) {t | P t} ↔ P s ∧ ∀ x ∉ s, ¬ P (insert x s) := by
  simp only [mem_maximals_iff, mem_setOf_eq, and_congr_right_iff]
  refine fun _ ↦ ⟨fun h x hx hxs ↦ hx ?_, fun h t ht hst ↦ hst.antisymm fun x hxt ↦ ?_⟩
  · rw [h hxs (subset_insert _ _)]; apply mem_insert
  exact by_contra fun hxs ↦ h x hxs (hP ht (insert_subset hxt hst))

lemma mem_minimals_iff_forall_diff_singleton {α : Type*} {P : Set α → Prop}
    (hP : ∀ ⦃s t⦄, P s → s ⊆ t → P t) {s : Set α} :
    s ∈ minimals (· ⊆ ·) {t | P t} ↔ P s ∧ ∀ x ∈ s, ¬ P (s \ {x}) := by
  simp only [mem_minimals_iff, mem_setOf_eq, and_congr_right_iff]
  refine fun _ ↦ ⟨fun h x hx hxs ↦ ?_, fun h t ht hst ↦ Eq.symm <| hst.antisymm (fun x hxs ↦ ?_)⟩
  · rw [(h hxs (diff_subset _ _))] at hx; simp at hx
  exact by_contra fun hxt ↦ h x hxs (hP ht (subset_diff_singleton hst hxt))
  -- have := mem_maximals_iff_forall_insert (P := fun (s : (Set α)ᵒᵈ) ↦ P (OrderDual.ofDual s))
  --    (s := OrderDual.toDual s)



  -- rw [← maximals_eq_minimals]
