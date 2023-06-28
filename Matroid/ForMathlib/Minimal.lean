import Mathlib.Order.Minimal 
import Mathlib.Order.Bounds.Basic 
import Mathlib.Data.Set.Finite
import Mathlib.Data.Nat.Interval

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
  

open Set
/-- This seems a strict improvement over the nonprimed version in mathlib - only the image needs to 
be finite, not the set itself.  -/
lemma Finite.exists_maximal_wrt' {α β : Type _} [PartialOrder β] (f : α → β) (s : Set α) 
    (h : (f '' s).Finite) (h₀ : s.Nonempty) : 
  (∃ a ∈ s, ∀ (a' : α), a' ∈ s → f a ≤ f a' → f a = f a') := by
  obtain  ⟨_ ,⟨a,ha,rfl⟩, hmax⟩ := Finite.exists_maximal_wrt id (f '' s) h (h₀.image f)
  exact ⟨a, ha, fun a' ha' hf ↦ hmax _ (mem_image_of_mem f ha') hf⟩

lemma Finite_iff_BddAbove {α : Type _} [SemilatticeSup α] [LocallyFiniteOrder α] [OrderBot α] 
    {s : Set α} : s.Finite ↔ BddAbove s :=
⟨fun h ↦ ⟨h.toFinset.sup id, fun x hx ↦ Finset.le_sup (f := id) (by simpa : x ∈ h.toFinset)⟩,
  fun ⟨m, hm⟩ ↦ (finite_Icc ⊥ m).subset (fun x hx ↦ ⟨bot_le, hm hx⟩)⟩
  
lemma Finite_iff_BddBelow {α : Type _} [SemilatticeInf α] [LocallyFiniteOrder α] [OrderTop α]
    {s : Set α} : s.Finite ↔ ∃ a, ∀ x ∈ s, a ≤ x :=
  Finite_iff_BddAbove (α := αᵒᵈ)

lemma Finite_iff_BddBelow_BddAbove {α : Type _} [Nonempty α] [Lattice α] [LocallyFiniteOrder α] 
    {s : Set α} : s.Finite ↔ BddBelow s ∧ BddAbove s := by
  obtain (rfl | hs) := s.eq_empty_or_nonempty; simp
  refine' ⟨fun h ↦ _, fun ⟨⟨a,ha⟩,⟨b,hb⟩⟩ ↦ (finite_Icc a b).subset (fun x hx ↦ ⟨ha hx,hb hx⟩ )⟩
  obtain ⟨s,rfl⟩ := h.exists_finset_coe
  exact ⟨⟨s.inf' (by simpa using hs) id, fun x hx ↦ Finset.inf'_le id (by simpa using hx)⟩, 
    ⟨s.sup' (by simpa using hs) id, fun x hx ↦ Finset.le_sup' id (by simpa using hx)⟩⟩
