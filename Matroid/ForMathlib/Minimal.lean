import Mathlib.Order.Minimal 

variable {α : Type _} {r : α → α → Prop} {s : Set α} {x y : α} {P : α → Prop}

instance [IsAntisymm α r] : IsAntisymm α (Function.swap r) := IsAntisymm.swap r
  
lemma mem_maximals_iff' [IsAntisymm α r] :
    x ∈ maximals r s ↔ x ∈ s ∧ ∀ ⦃y⦄, y ∈ s → r x y → x = y := by
  simp only [maximals, Set.mem_sep_iff, and_congr_right_iff]
  refine' fun _ ↦ ⟨fun h y hys hxy ↦ antisymm hxy (h hys hxy), fun h y hys hxy ↦ _⟩ 
  convert hxy <;> rw [h hys hxy]

lemma mem_minimals_iff' [IsAntisymm α r] :
    x ∈ minimals r s ↔ x ∈ s ∧ ∀ ⦃y⦄, y ∈ s → r y x → x = y := by 
  rw [←maximals_swap, mem_maximals_iff'] 

lemma maximals_dual [PartialOrder α] :
    maximals (· ≤ ·) s = @minimals αᵒᵈ (· ≤ ·) s := by
  ext x
  rw [mem_maximals_iff', @mem_minimals_iff' αᵒᵈ (· ≤ ·) s x _, and_congr_right_iff]
  exact fun _ ↦ ⟨id, id⟩

lemma minimals_dual [PartialOrder α] :
    minimals (· ≤ ·) s = @maximals αᵒᵈ (· ≤ ·) s := by
  simp [maximals_dual]; rfl 

lemma mem_maximals_Prop_iff [IsAntisymm α r] : 
    x ∈ maximals r P ↔ P x ∧ ∀ ⦃y⦄, P y → r x y → x = y :=
  mem_maximals_iff'

lemma mem_maximals_setOf_iff [IsAntisymm α r] : 
    x ∈ maximals r (setOf P) ↔ P x ∧ ∀ ⦃y⦄, P y → r x y → x = y :=
  mem_maximals_iff'

lemma mem_minimals_Prop_iff [IsAntisymm α r] : 
    x ∈ minimals r P ↔ P x ∧ ∀ ⦃y⦄, P y → r y x → x = y :=
  mem_minimals_iff'

lemma mem_minimals_setOf_iff [IsAntisymm α r] : 
    x ∈ minimals r (setOf P) ↔ P x ∧ ∀ ⦃y⦄, P y → r y x → x = y :=
  mem_minimals_iff'

lemma mem_minimals_setOf_iff' {P : Set α → Prop} {x : Set α} : 
    x ∈ minimals (· ⊆ ·) (setOf P) ↔ P x ∧ ∀ ⦃y⦄, y ⊂ x → ¬ P y := by
  simp only [mem_minimals_setOf_iff, and_congr_right_iff, ssubset_iff_subset_ne, Ne.def, 
    and_imp, not_imp_not]
  exact fun _ ↦ ⟨fun h' y hyx hy ↦ (h' hy hyx).symm, fun h' y hy hyx ↦ (h' hyx hy).symm⟩
  
lemma mem_maximals_set_of_iff' {P : Set α → Prop} {x : Set α} : 
    x ∈ maximals (· ⊆ ·) (setOf P) ↔ P x ∧ ∀ ⦃y⦄, x ⊂ y → ¬ P y := by
  simp only [mem_maximals_setOf_iff, and_congr_right_iff, ssubset_iff_subset_ne, Ne.def, 
    and_imp, not_imp_not]
  exact fun _ ↦ ⟨fun h' y hyx hy ↦ h' hy hyx, fun h' y hy hyx ↦ h' hyx hy⟩
  
  
-- def maximal {α : Type*} (r : α → α → Prop) (P : α → Prop) (x : α) := 
--   x ∈ maximals r (set_of P)

-- def minimal {α : Type*} (r : α → α → Prop) (P : α → Prop) (x : α) := 
--   x ∈ minimals r (set_of P)

-- lemma maximal.eq_of_le [IsAntisymm α r] (h : maximal r P x) (hr : r x y) (hy : P y) :
--   x = y := antisymm hr (h.2 hy hr)

-- lemma minimal.eq_of_le [IsAntisymm α r] (h : minimal r P x) (hr : r y x) (hy : P y) :
--   x = y := antisymm (h.2 hy hr) hr
