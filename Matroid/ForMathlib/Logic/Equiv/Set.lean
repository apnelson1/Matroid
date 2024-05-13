import Mathlib.Logic.Equiv.Set

open Set

variable {α β : Type*} {a b : α} {s : Set α}

theorem Equiv.swap_bijOn_self [DecidableEq α] (hs : a ∈ s ↔ b ∈ s) :
    BijOn (Equiv.swap a b) s s := by
  refine ⟨fun x hx ↦ ?_, (Equiv.injective _).injOn _, fun x hx ↦ ?_⟩
  · obtain (rfl | hxa) := eq_or_ne x a; rwa [swap_apply_left, ← hs]
    obtain (rfl | hxb) := eq_or_ne x b; rwa [swap_apply_right, hs]
    rwa [swap_apply_of_ne_of_ne hxa hxb]
  obtain (rfl | hxa) := eq_or_ne x a; simp [hs.1 hx]
  obtain (rfl | hxb) := eq_or_ne x b; simp [hs.2 hx]
  exact ⟨x, hx, swap_apply_of_ne_of_ne hxa hxb⟩

theorem Equiv.swap_bijOn_exchange [DecidableEq α] (ha : a ∈ s) (hb : b ∉ s) :
    BijOn (Equiv.swap a b) s (insert b (s \ {a})) := by
  refine ⟨fun x hx ↦ ?_, (Equiv.injective _).injOn _, fun x hx ↦ ?_⟩
  · obtain (rfl | hxa) := eq_or_ne x a; simp [swap_apply_left]
    rw [swap_apply_of_ne_of_ne hxa (by rintro rfl; contradiction)]
    exact .inr ⟨hx, hxa⟩
  obtain (rfl | hxb) := eq_or_ne x b; exact ⟨a, ha, by simp⟩
  simp only [mem_insert_iff, mem_diff, mem_singleton_iff, or_iff_right hxb] at hx
  exact ⟨x, hx.1, swap_apply_of_ne_of_ne hx.2 hxb⟩
