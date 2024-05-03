
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Subset

open Set Function Set.Notation

variable {α β : Type*} {s s₁ s₂ t t' : Set α} {f : α → β }

lemma Set.InjOn.image_eq_image_iff_of_subset {f : α → β} (h : InjOn f s) (h₁ : s₁ ⊆ s)
    (h₂ : s₂ ⊆ s) : f '' s₁ = f '' s₂ ↔ s₁ = s₂ :=
  ⟨fun h' ↦ by rw [← h.preimage_image_inter h₁, h', h.preimage_image_inter h₂], fun h' ↦ by rw [h']⟩

lemma Set.InjOn.image_subset_image_iff_of_subset {f : α → β} (h : InjOn f s) (h₁ : s₁ ⊆ s)
    (h₂ : s₂ ⊆ s) : f '' s₁ ⊆ f '' s₂ ↔ s₁ ⊆ s₂ := by
  refine' ⟨fun h' ↦ _, image_subset _⟩
  rw [← h.preimage_image_inter h₁, ← h.preimage_image_inter h₂]
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

theorem Set.InjOn.imageFactorization_injective (h : InjOn f s) :
    Injective (s.imageFactorization f) := by
  rintro ⟨x,hx⟩ ⟨y,hy⟩ h'
  simp_rw [imageFactorization, Subtype.mk.injEq, h.eq_iff hx hy] at h'
  simp only [h']

section inverse

lemma Function.invFunOn_injOn_image_preimage [Nonempty α] (f : α → β) (S : Set α) :
    InjOn f ((invFunOn f S) '' (f '' S)) := by
  rintro _ ⟨_,⟨x,hx, rfl⟩,rfl⟩ _ ⟨_,⟨y,hy,rfl⟩,rfl⟩ h
  rw [invFunOn_eq (f := f) ⟨x, hx, rfl⟩, invFunOn_eq (f := f) ⟨y,hy,rfl⟩] at h
  rw [h]

theorem Set.BijOn.subset_right {f : α → β} {s : Set α} {r t : Set β} (hf : BijOn f s t)
    (hxt : r ⊆ t) : BijOn f (s ∩ f ⁻¹' r) r := by
  refine ⟨inter_subset_right _ _, hf.injOn.mono <| inter_subset_left _ _, fun x hx ↦ ?_⟩
  obtain ⟨y, hy, rfl⟩ := hf.surjOn (hxt hx)
  exact ⟨y, ⟨hy, hx⟩, rfl⟩

theorem Set.SurjOn.image_invFun_image_subset_eq [Nonempty α] {f : α → β} {s : Set α} {r t : Set β}
    (hf : SurjOn f s t) (hrt : r ⊆ t) : f '' ((Function.invFunOn f s) '' r) = r := by
  ext x
  simp only [mem_image, exists_exists_and_eq_and]
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨y, hy, rfl⟩ := hf (hrt hx)
    rwa [Function.invFunOn_apply_eq (f := f) hy]
  obtain ⟨y, hy, rfl⟩ := hf (hrt h)
  refine ⟨_,h, by rwa [Function.invFunOn_apply_eq (f := f)]⟩

theorem Set.SurjOn.image_invFun_image_eq [Nonempty α] {f : α → β} {s : Set α} {t : Set β}
    (hf : SurjOn f s t) : f '' ((Function.invFunOn f s) '' t) = t :=
  hf.image_invFun_image_subset_eq rfl.subset

end inverse

/-- If `f` maps `s` bijectively to `t` and, then for any `s ⊆ s₁` and `t ⊆ t' ⊆ f '' s₁`,
  there is some `s ⊆ s' ⊆ s₁` so that `f` maps `s'` bijectively to `t'`. -/
theorem Set.BijOn.extend_of_subset {f : α → β} {s s₁ : Set α} {t t' : Set β}
    (h : BijOn f s t) (hss₁ : s ⊆ s₁) (htt' : t ⊆ t') (ht' : t' ⊆ f '' s₁) :
    ∃ s', s ⊆ s' ∧ s' ⊆ s₁ ∧ Set.BijOn f s' t' := by
  have hex : ∀ (b : ↑(t' \ t)),  ∃ a, a ∈ s₁ \ s ∧ f a = b := by
    rintro ⟨b, hb⟩
    obtain ⟨a, ha, rfl⟩  := ht' hb.1
    exact ⟨_, ⟨ha, fun has ↦ hb.2 <| h.mapsTo has⟩, rfl⟩
  choose g hg using hex
  have hinj : InjOn f (s ∪ range g) := by
    rw [injOn_union, and_iff_right h.injOn, and_iff_left]
    · rintro _ ⟨⟨x,hx⟩, rfl⟩ _ ⟨⟨x', hx'⟩,rfl⟩ hf
      simp only [(hg _).2, (hg _).2] at hf; subst hf; rfl
    · rintro x hx _ ⟨⟨y,hy⟩, hy', rfl⟩ h_eq
      rw [(hg _).2] at h_eq
      obtain (rfl : _ = y) := h_eq
      exact hy.2 <| h.mapsTo hx
    rw [disjoint_iff_forall_ne]
    rintro x hx _ ⟨y, hy, rfl⟩ rfl
    have h' := h.mapsTo hx
    rw [(hg _).2] at h'
    exact y.prop.2 h'
  have hp : BijOn f (range g) (t' \ t) := by
    apply BijOn.mk
    · rintro _ ⟨x, hx, rfl⟩; rw [(hg _).2]; exact x.2
    · exact hinj.mono (subset_union_right _ _)
    exact fun x hx ↦ ⟨g ⟨x,hx⟩, by simp [(hg _).2] ⟩
  refine ⟨s ∪ range g, subset_union_left _ _, union_subset hss₁ <| ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩; exact (hg _).1.1
  convert h.union hp ?_
  · exact (union_diff_cancel htt').symm
  exact hinj

theorem Set.BijOn.extend {f : α → β} {s : Set α} {t t' : Set β} (h : BijOn f s t) (htt' : t ⊆ t')
    (ht' : t' ⊆ range f) : ∃ s', s ⊆ s' ∧ BijOn f s' t' := by
  simpa using h.extend_of_subset (subset_univ s) htt' (by simpa)



section Update

variable {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β} {a : α} {b : β}

@[simp] theorem image_update  (a : α) (f : α → β) (s : Set α) [Decidable (a ∈ s)] (b : β) :
    (update f a b) '' s = if a ∈ s then insert b (f '' (s \ {a})) else (f '' s) := by
  split_ifs with h
  · rw [subset_antisymm_iff, image_subset_iff]
    refine ⟨fun x hxs ↦ (em (x = a)).elim (fun heq ↦ ?_) (fun hne ↦ Or.inr ?_), fun x ↦ ?_⟩
    · rw [mem_preimage, update_apply, if_pos heq]; exact mem_insert _ _
    · exact ⟨x, ⟨hxs, hne⟩, by rw [update_noteq hne]⟩
    rintro (rfl | ⟨x, hx, rfl⟩)
    · use a; simpa
    exact ⟨x, hx.1, update_noteq hx.2 _ _⟩
  rw [subset_antisymm_iff, image_subset_iff, image_subset_iff]
  refine ⟨fun x hxs ↦ ⟨x, hxs, ?_⟩, fun x hxs ↦ ⟨x, hxs, ?_⟩⟩
  · rw [update_noteq]; rintro rfl; exact h hxs
  rw [update_noteq]; rintro rfl; exact h hxs

lemma preimage_update  {f : α → β} (hf : f.Injective) (a : α) (b : β) (s : Set β)
    [Decidable (b ∈ s)] :
    (update f a b) ⁻¹' s = if b ∈ s then insert a (f ⁻¹' (s \ {f a})) else (f ⁻¹' (s \ {f a})) := by

  split_ifs with h
  · rw [subset_antisymm_iff, insert_subset_iff, mem_preimage, update_same,
      preimage_diff, and_iff_right h, diff_subset_iff,
      (show {f a} = f '' {a} by rw [image_singleton]),
      preimage_image_eq _ hf, singleton_union, insert_diff_singleton]
    refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
    · obtain (rfl | hxa) := eq_or_ne x a
      · rw [mem_preimage, update_same] at hx
        apply mem_insert
      rw [mem_preimage, update_noteq hxa] at hx
      exact mem_insert_of_mem _ hx
    obtain (rfl | hxa) := eq_or_ne x a
    · exact mem_insert _ _
    rw [mem_insert_iff, mem_preimage, update_noteq hxa]
    exact Or.inr hx
  refine subset_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · obtain (rfl | hxa) := eq_or_ne x a
    · exact (h (by simpa using hx)).elim
    rw [mem_preimage, update_noteq hxa] at hx
    exact ⟨hx, by rwa [mem_singleton_iff, hf.eq_iff]⟩
  rw [mem_preimage, mem_diff, mem_singleton_iff, hf.eq_iff] at hx
  rw [mem_preimage, update_noteq hx.2]
  exact hx.1

lemma image_update_id_apply (x y : α) (s : Set α) [Decidable (x ∈ s)] :
  (update id x y) '' s = if x ∉ s then s else insert y (s \ {x}) := by simp

lemma update_injective (hf : f.Injective) (a : α) (h : b ∉ range f) : (update f a b).Injective := by
  rintro x y hy
  rw [update_apply, update_apply] at hy
  split_ifs at hy with h_1 h_2
  · rw [h_1,h_2]
  · exact (h ⟨y, hy.symm⟩).elim
  · exact (h ⟨x, hy⟩).elim
  exact hf.eq_iff.1 hy

lemma update_injOn_iff {f : α → β} {s : Set α} {a : α} {b : β} :
    InjOn (update f a b) s ↔ InjOn f (s \ {a}) ∧ (a ∈ s → ∀ x ∈ s, f x = b → x = a) := by
  refine ⟨fun h ↦ ⟨fun x hx y hy hxy ↦  h hx.1 hy.1 ?_, ?_⟩, fun h x hx y hy hxy ↦ ?_⟩
  · rwa [update_noteq hx.2, update_noteq hy.2]
  · rintro has x hxs rfl
    by_contra! hne
    have h' := h hxs has
    rw [update_noteq hne, update_same] at h'
    exact hne <| h' rfl
  obtain (rfl | hxa) := eq_or_ne x a
  · by_contra! hne
    rw [update_same, update_noteq hne.symm] at hxy
    exact hne.symm <| h.2 hx y hy hxy.symm
  obtain (rfl | hya) := eq_or_ne y a
  · rw [update_noteq hxa, update_same] at hxy
    exact h.2 hy x hx hxy
  rw [update_noteq hxa, update_noteq hya] at hxy
  exact h.1 ⟨hx, hxa⟩ ⟨hy, hya⟩ hxy

@[simp] lemma update_id_injOn_iff {a b : α} {s : Set α} :
    InjOn (update id a b) s ↔ (a ∈ s → b ∈ s → a = b) := by
  rw [update_injOn_iff, and_iff_right (injective_id.injOn _)]
  refine ⟨fun h has hbs ↦ (h has b hbs rfl).symm, ?_⟩
  rintro h has _ hbs rfl
  exact (h has hbs).symm

end Update
