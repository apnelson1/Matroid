import Mathlib.Tactic

open Set

theorem pair_diff_left {x y : α} (hne : x ≠ y) : ({x, y} : Set α) \ {x} = {y} := by 
  rw [insert_diff_of_mem _ (by exact rfl : x ∈ {x}), diff_singleton_eq_self (by simpa)]

theorem pair_diff_right {x y : α} (hne : x ≠ y) : ({x, y} : Set α) \ {y} = {x} := by 
  rw [pair_comm, pair_diff_left hne.symm]

lemma Set.InjOn.image_eq_image_iff_of_subset {f : α → β} (h : InjOn f s) (h₁ : s₁ ⊆ s) 
    (h₂ : s₂ ⊆ s) : f '' s₁ = f '' s₂ ↔ s₁ = s₂ := 
  ⟨fun h' ↦ by rw [←h.preimage_image_inter h₁, h', h.preimage_image_inter h₂], fun h' ↦ by rw [h']⟩
  
lemma Set.InjOn.image_subset_image_iff_of_subset {f : α → β} (h : InjOn f s) (h₁ : s₁ ⊆ s) 
    (h₂ : s₂ ⊆ s) : f '' s₁ ⊆ f '' s₂ ↔ s₁ ⊆ s₂ := by
  refine' ⟨fun h' ↦ _, image_subset _⟩   
  rw [←h.preimage_image_inter h₁, ←h.preimage_image_inter h₂]
  exact inter_subset_inter_left _ (preimage_mono h')

lemma Set.InjOn.image_diff' {f : α → β} (h : InjOn f s) : 
    f '' (s \ t) = f '' s \ f '' (s ∩ t) := by
  refine' Set.ext (fun y ↦ ⟨_,_⟩)
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx.1, rfl⟩, fun h' ↦ hx.2 (h.mem_of_mem_image (inter_subset_left _ _) hx.1 h').2⟩ 
  rintro ⟨⟨x, hx, rfl⟩,h'⟩
  exact ⟨x, ⟨hx,fun hxt ↦ h' ⟨x, ⟨hx,hxt⟩, rfl⟩⟩, rfl⟩ 
    
lemma Set.InjOn.image_diff {f : α → β} (h : InjOn f s) (hst : t ⊆ s) : 
    f '' (s \ t) = f '' s \ f '' t := by
  rw [h.image_diff', inter_eq_self_of_subset_right hst]

  



-- def LocalEquiv.LocalEquivSet (i : LocalEquiv α β) : LocalEquiv (Set α) (Set β) where
--   toFun := image i.toFun
--   invFun := image i.invFun
--   source := Iic i.source
--   target := Iic i.target
--   map_source' := by 
--   { simp only [mem_Iic, le_eq_subset, image_subset_iff]
--     exact fun s hs a has ↦ i.map_source' (hs has) }
--   map_target' := by
--   { simp only [mem_Iic, le_eq_subset, image_subset_iff]
--     exact fun s hs a has ↦ i.map_target' (hs has) }
--   left_inv' := by
--   { simp only [mem_Iic, le_eq_subset, invFun_as_coe]
--     exact fun _ h ↦ symm_image_image_of_subset_source i h }
--   right_inv' := by
--   { simp only [mem_Iic, le_eq_subset, invFun_as_coe]
--     exact fun _ h ↦ image_symm_image_of_subset_target i h }


  
