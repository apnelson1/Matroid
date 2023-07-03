import Mathlib.Tactic

open Set

lemma Set.InjOn.image_eq_image_iff_of_subset {f : α → β} (h : InjOn f s) (h₁ : s₁ ⊆ s) 
    (h₂ : s₂ ⊆ s) : f '' s₁ = f '' s₂ ↔ s₁ = s₂ := 
  ⟨fun h' ↦ by rw [←h.preimage_image_inter h₁, h', h.preimage_image_inter h₂], fun h' ↦ by rw [h']⟩
  
lemma Set.InjOn.image_subset_image_iff_of_subset {f : α → β} (h : InjOn f s) (h₁ : s₁ ⊆ s) 
    (h₂ : s₂ ⊆ s) : f '' s₁ ⊆ f '' s₂ ↔ s₁ ⊆ s₂ := by
  refine' ⟨fun h' ↦ _, image_subset _⟩   
  rw [←h.preimage_image_inter h₁, ←h.preimage_image_inter h₂]
  exact inter_subset_inter_left _ (preimage_mono h')
