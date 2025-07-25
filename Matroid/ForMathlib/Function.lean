
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Subset

open Function Set Set.Notation

namespace Set

variable {α β : Type*} {r s s₁ s₂: Set α} {t t' t₁ t₂ : Set β} {f : α → β}


@[simp] lemma injOn_const_iff {b : β} : InjOn (fun _ ↦ b : α → β) s ↔ s.Subsingleton :=
  ⟨fun h _ hx _ hy ↦ h hx hy rfl, fun h _ hx _ hy _ ↦ h hx hy⟩

-- @[simp] lemma injOn_zero_iff [Zero (α → β)] : InjOn (0 : α → β) s ↔ s.Subsingleton :=
--   ⟨fun h _ hx _ hy ↦ h hx hy rfl, fun h _ hx _ hy _ ↦ h hx hy⟩

section Update
variable {α β : Type*} [DecidableEq α] {f : α → β} {a : α} {b : β}

@[simp] theorem image_update (a : α) (f : α → β) (s : Set α) [Decidable (a ∈ s)] (b : β) :
    (update f a b) '' s = if a ∈ s then insert b (f '' (s \ {a})) else (f '' s) := by
  split_ifs with h
  · rw [subset_antisymm_iff, image_subset_iff]
    refine ⟨fun x hxs ↦ (em (x = a)).elim (fun heq ↦ ?_) (fun hne ↦ Or.inr ?_), fun x ↦ ?_⟩
    · rw [mem_preimage, update_apply, if_pos heq]; exact mem_insert _ _
    · exact ⟨x, ⟨hxs, hne⟩, by rw [update_of_ne hne]⟩
    rintro (rfl | ⟨x, hx, rfl⟩)
    · use a; simpa
    exact ⟨x, hx.1, update_of_ne hx.2 _ _⟩
  rw [subset_antisymm_iff, image_subset_iff, image_subset_iff]
  refine ⟨fun x hxs ↦ ⟨x, hxs, ?_⟩, fun x hxs ↦ ⟨x, hxs, ?_⟩⟩
  · rw [update_of_ne]; rintro rfl; exact h hxs
  rw [update_of_ne]; rintro rfl; exact h hxs

lemma preimage_update_of_notMem_notMem (f : α → β) {s : Set β} (hbs : b ∉ s) (has : f a ∉ s) :
    update f a b ⁻¹' s = f ⁻¹' s := by
  ext x
  simp only [mem_preimage, update_apply]
  split_ifs with h; simp [hbs, h.symm ▸ has]; rfl

lemma preimage_update_of_notMem_mem (f : α → β) {s : Set β} (hbs : b ∉ s) (has : f a ∈ s) :
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
  · rw [preimage_update_of_notMem_mem _ hb ha]
  rw [preimage_update_of_notMem_notMem _ hb ha]

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
  · rwa [update_of_ne hx.2, update_of_ne hy.2]
  · rintro has x hxs rfl
    by_contra! hne
    have h' := h hxs has
    rw [update_of_ne hne, update_self] at h'
    exact hne <| h' rfl
  obtain (rfl | hxa) := eq_or_ne x a
  · by_contra! hne
    rw [update_self, update_of_ne hne.symm] at hxy
    exact hne.symm <| h.2 hx y hy hxy.symm
  obtain (rfl | hya) := eq_or_ne y a
  · rw [update_of_ne hxa, update_self] at hxy
    exact h.2 hy x hx hxy
  rw [update_of_ne hxa, update_of_ne hya] at hxy
  exact h.1 ⟨hx, hxa⟩ ⟨hy, hya⟩ hxy

@[simp] lemma update_id_injOn_iff {a b : α} {s : Set α} :
    InjOn (update id a b) s ↔ (a ∈ s → b ∈ s → a = b) := by
  rw [update_injOn_iff, and_iff_right injective_id.injOn]
  refine ⟨fun h has hbs ↦ (h has b hbs rfl).symm, ?_⟩
  rintro h has _ hbs rfl
  exact (h has hbs).symm

end Update


section BijOn

variable {f : α → β} {s : Set α} {t : Set β} {x : α} {y : β}

lemma BijOn.bijOn_insert_iff (h : BijOn f s t) (hx : x ∉ s) :
    BijOn f (Insert.insert x s) (Insert.insert y t) ↔ y = f x ∧ y ∉ t := by
  simp [BijOn]
  simp only [MapsTo, mem_insert_iff, forall_eq_or_imp, injOn_insert hx, h.image_eq,
    and_iff_right h.injOn, SurjOn, image_insert_eq, insert_subset_iff, subset_insert, and_true]
  obtain (rfl | hne) := eq_or_ne y (f x)
  · simp only [true_or, true_and, and_true, and_iff_right_iff_imp]
    exact fun _ a has ↦ by simp [h.mapsTo has]
  simp only [hne.symm, hne]
  tauto

lemma BijOn.insert_notMem (h : BijOn f s t) (hx : x ∉ s) (hx' : f x ∉ t) :
    BijOn f (Insert.insert x s) (Insert.insert (f x) t) := by
  simpa [h.bijOn_insert_iff hx]

lemma BijOn.diff_singleton (h : BijOn f s t) (hx : x ∈ s) : BijOn f (s \ {x}) (t \ {f x}) := by
  convert h.subset_left diff_subset
  rw [h.injOn.image_diff, h.image_eq, inter_eq_self_of_subset_right (by simpa), image_singleton]

lemma BijOn.bijOn_update [DecidableEq α] (h : BijOn f s t) (hx : x ∈ s) (hy : y ∉ t) :
    BijOn (Function.update f x y) s (Insert.insert y (t \ {f x})) := by
  rw [show s = Insert.insert x (s \ {x}) by simp [hx]]
  have h_eq : EqOn f (Function.update f x y) (s \ {x}) := fun a h ↦ Eq.symm <| update_of_ne h.2 _ f
  rw [((h.diff_singleton hx).congr h_eq).bijOn_insert_iff (by simp)]
  simp [hy]

end BijOn

variable {f : α → β} {x : α} {y : β}

@[simp] lemma injective_const_iff : Injective (fun (_ : α) ↦ y) ↔ Subsingleton α :=
  ⟨fun h ↦ ⟨fun _ _ ↦ h rfl⟩, fun _ _ _ _ ↦ Subsingleton.elim ..⟩

@[simp] lemma restrict_const (s : Set α) (y : β) : (s.restrict (fun _ : α ↦ y)) = fun _ ↦ y := rfl

@[simps] def Equiv.sumSet {s t : Set α} [DecidablePred (· ∈ s)] (h : Disjoint s t) :
    s ⊕ t ≃ ↥(s ∪ t) where
  toFun := Sum.elim (fun x ↦ ⟨x, by simp [x.2]⟩) (fun x ↦ ⟨x, by simp [x.2]⟩)
  invFun x := if hx : x.1 ∈ s then .inl ⟨x, hx⟩ else .inr ⟨x, Or.elim x.2 (False.elim ∘ hx) id⟩
  left_inv := by
    rintro (⟨x, hx⟩ | ⟨x, hx⟩)
    · simp [hx]
    simp [show x ∉ s from fun hxs ↦ h.ne_of_mem hxs hx rfl]
  right_inv := by
    rintro ⟨x, hx | hx⟩
    · simp [hx]
    simp [show x ∉ s from fun hxs ↦ h.ne_of_mem hxs hx rfl]

@[simp] lemma Equiv.sumSet_symm_sum_elim {s t : Set α} [DecidablePred (· ∈ s)] (h : Disjoint s t)
    {f : α → β} {x : ↥(s ∪ t)} : Sum.elim (s.restrict f) (t.restrict f)
      ((Equiv.sumSet h).symm x) = f x := by
  by_cases h : x.1 ∈ s <;> simp [h]

lemma RightInvOn.injOn {f : α → β} {g : β → α} {s : Set α} (hinv : RightInvOn f g s) :
    InjOn f s := by
  rintro a ha b hb h_eq
  replace h_eq := congr_arg g h_eq
  rwa [hinv.eq ha, hinv.eq hb] at h_eq

lemma RightInvOn.injOn_image {f : α → β} {g : β → α} {s : Set α} (hinv : RightInvOn f g s) :
    InjOn g (f '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ h_eq
  rw [hinv.eq ha, hinv.eq hb] at h_eq
  rw [h_eq]

lemma LeftInvOn.injOn_image {f : α → β} {g : β → α} {t : Set β} (hinv : LeftInvOn f g t) :
    InjOn f (g '' t) :=
  RightInvOn.injOn_image hinv


lemma Function.onFun_comp {α β γ : Type*} {r : α → α → Prop} {f : β → α} {g : γ → β} :
    (r on f ∘ g) = ((r on f) on g) := rfl
