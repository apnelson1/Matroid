import Mathlib.Logic.Equiv.LocalEquiv
import Mathlib.Data.Set.NCard

open Set

theorem diff_eq_diff_iff_inter_eq_inter {s t r : Set α} : s \ t = s \ r ↔ (t ∩ s = r ∩ s) := by
  rw [←diff_inter_self_eq_diff, ←diff_inter_self_eq_diff (t := r)] 
  refine' ⟨fun h ↦ _, fun h ↦ by rw [h]⟩
  rw [←diff_diff_cancel_left (inter_subset_right t s), h, 
    diff_diff_cancel_left (inter_subset_right r s)]

@[simp] theorem Set.diff_inter_diff_right {s t r : Set α} : (t \ s) ∩ (r \ s) = (t ∩ r) \ s := by
  simp only [diff_eq, inter_assoc, inter_comm sᶜ, inter_self]

theorem inter_diff_right_comm {s t r : Set α} : (s ∩ t) \ r = (s \ r) ∩ t := by  
  simp_rw [diff_eq, inter_right_comm]

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

section Lattice

lemma biUnion_insert_eq (hX : X.Nonempty) (Y : Set α) : ⋃ (x ∈ X), (insert x Y) = X ∪ Y := by
  have := hX.to_subtype
  simp_rw [←singleton_union, biUnion_eq_iUnion, ←iUnion_union, iUnion_singleton_eq_range, 
    Subtype.range_coe_subtype, setOf_mem_eq]
  
theorem Finite.exists_localEquiv_of_encard_eq [Nonempty α] [Nonempty β] {s : Set α} {t : Set β} 
    (hfin : s.Finite) (h : s.encard = t.encard) : 
    ∃ (e : LocalEquiv α β), e.source = s ∧ e.target = t := by 
  
  obtain ⟨f, hf⟩ := hfin.exists_bijOn_of_encard_eq h
  exact ⟨hf.toLocalEquiv, rfl, hf.toLocalEquiv_target⟩
  



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


  
