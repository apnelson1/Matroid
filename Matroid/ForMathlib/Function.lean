
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Subset

open Function Set.Notation

namespace Set

variable {α β : Type*} {r s s₁ s₂: Set α} {t t' t₁ t₂ : Set β} {f : α → β}



/-- If `f` maps `s` bijectively to `t` and a set `t'` is contained in the image of some `s₁ ⊇ s`,
then `s₁` has a subset containing `s` that `f` maps bijectively to `t'`.-/
theorem BijOn.exists_extend_of_subset (h : BijOn f s t) (hss₁ : s ⊆ s₁) (htt' : t ⊆ t')
    (ht' : SurjOn f s₁ t') : ∃ s', s ⊆ s' ∧ s' ⊆ s₁ ∧ Set.BijOn f s' t' := by
  obtain ⟨r, hrss, hbij⟩ := exists_subset_bijOn ((s₁ ∩ f ⁻¹' t') \ f ⁻¹' t) f
  rw [image_diff_preimage, image_inter_preimage] at hbij
  refine ⟨s ∪ r, subset_union_left, ?_, ?_, ?_, fun y hyt' ↦ ?_⟩
  · exact union_subset hss₁ <| hrss.trans <| diff_subset.trans inter_subset_left
  · rw [mapsTo', image_union, hbij.image_eq, h.image_eq, union_subset_iff]
    exact ⟨htt', diff_subset.trans inter_subset_right⟩
  · rw [injOn_union, and_iff_right h.injOn, and_iff_right hbij.injOn]
    · refine fun x hxs y hyr hxy ↦ (hrss hyr).2 ?_
      rw [← h.image_eq]
      exact ⟨x, hxs, hxy⟩
    exact (subset_diff.1 hrss).2.symm.mono_left h.mapsTo
  rw [image_union, h.image_eq, hbij.image_eq, union_diff_self]
  exact .inr ⟨ht' hyt', hyt'⟩

/-- If `f` maps `s` bijectively to `t`, and `t'` is a superset of `t` contained in the range of `f`,
then `f` maps some superset of `s` bijectively to `t'`. -/
theorem BijOn.exists_extend (h : BijOn f s t) (htt' : t ⊆ t') (ht' : t' ⊆ range f) :
    ∃ s', s ⊆ s' ∧ BijOn f s' t' := by
  simpa using h.exists_extend_of_subset (subset_univ s) htt' (by simpa [SurjOn])

theorem InjOn.exists_subset_injOn_subset_range_eq (hinj : InjOn f r) (hrs : r ⊆ s) :
    ∃ (u : Set α), r ⊆ u ∧ u ⊆ s ∧ f '' u = f '' s ∧ Set.InjOn f u := by
  obtain ⟨u, hru, hus, h⟩ := hinj.bijOn_image.exists_extend_of_subset hrs
    (image_subset f hrs) Subset.rfl
  exact ⟨u, hru, hus, h.image_eq, h.injOn⟩
section Update

variable {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β} {a : α} {b : β}

@[simp] theorem image_update (a : α) (f : α → β) (s : Set α) [Decidable (a ∈ s)] (b : β) :
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

lemma preimage_update_of_not_mem_not_mem (f : α → β) {s : Set β} (hbs : b ∉ s) (has : f a ∉ s) :
    update f a b ⁻¹' s = f ⁻¹' s := by
  ext x
  simp only [mem_preimage, update_apply]
  split_ifs with h; simp [hbs, h.symm ▸ has]; rfl

lemma preimage_update_of_not_mem_mem (f : α → β) {s : Set β} (hbs : b ∉ s) (has : f a ∈ s) :
    update f a b ⁻¹' s = f ⁻¹' s \ {a} := by
  ext x
  obtain (rfl | hxa) := eq_or_ne x a
  · simpa
  simp [hxa]

lemma preimage_update_of_mem (f : α → β) {s : Set β} (hbs : b ∈ s) :
    update f a b ⁻¹' s = insert a (f ⁻¹' s) := by
  ext x; obtain (rfl | hxa) := eq_or_ne x a; simpa; simp [hxa]

lemma preimage_update_eq_ite (f : α → β) (a : α) (b : β) (s : Set β) [Decidable (b ∈ s)]
    [Decidable (f a ∈ s)] : update f a b ⁻¹' s =
      if b ∈ s then (insert a (f ⁻¹' s)) else (if f a ∈ s then (f ⁻¹' s) \ {a} else f ⁻¹' s) := by
  split_ifs with hb ha
  · rw [preimage_update_of_mem _ hb]
  · rw [preimage_update_of_not_mem_mem _ hb ha]
  rw [preimage_update_of_not_mem_not_mem _ hb ha]

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
  rw [update_injOn_iff, and_iff_right injective_id.injOn]
  refine ⟨fun h has hbs ↦ (h has b hbs rfl).symm, ?_⟩
  rintro h has _ hbs rfl
  exact (h has hbs).symm

end Update
