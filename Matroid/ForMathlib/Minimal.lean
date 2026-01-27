import Mathlib.Data.Set.Image -- inefficient import

open Set

variable {α : Type*} [LE α] {x : α} {P Q : α → Prop}

theorem minimal_congr (h : ∀ x, P x ↔ Q x) : Minimal P x ↔ Minimal Q x := by
  rw [show P = Q from funext fun x ↦ propext (h _)]

theorem maximal_congr (h : ∀ x, P x ↔ Q x) : Maximal P x ↔ Maximal Q x := by
  rw [show P = Q from funext fun x ↦ propext (h _)]

lemma minimalFor_congr_val {ι : Sort*} {P : ι → Prop} {f : ι → α} {x y : ι} (hxy : f x = f y)
    (h_iff : P x ↔ P y) : MinimalFor P f x ↔ MinimalFor P f y := by
  simp [MinimalFor, hxy, h_iff]

lemma maximalFor_congr_val {ι : Sort*} {P : ι → Prop} {f : ι → α} {x y : ι} (hxy : f x = f y)
    (h_iff : P x ↔ P y) : MaximalFor P f x ↔ MaximalFor P f y := by
  simp [MaximalFor, hxy, h_iff]

@[simp]
theorem maximal_top_iff {α : Type*} [LE α] [OrderTop α] {P : α → Prop} : Maximal P ⊤ ↔ P ⊤ := by
  simp [Maximal]

@[simp]
theorem minimal_bot_iff {α : Type*} [LE α] [OrderBot α] {P : α → Prop} : Minimal P ⊥ ↔ P ⊥ := by
  simp [Minimal]

@[simp]
theorem maximal_univ_iff (α : Type*) {P : Set α → Prop} : Maximal P univ ↔ P univ :=
  maximal_top_iff

@[simp]
theorem minimal_empty_iff (α : Type*) {P : Set α → Prop} : Minimal P ∅ ↔ P ∅ :=
  minimal_bot_iff

variable {β : Type*} [Preorder β] {P : α  → Prop} {Q : β → Prop} {f : α → β} {g : β → α} {s : Set β}

-- lemma minimal_apply_mono_bijOn_iff (hbij : BijOn f {x | P x} {y | Q y})
--     (hinv : InvOn g f {x | P x} {y | Q y})
-- (hmono : ∀ ⦃x x'⦄, P x → P x' → (f x ≤ f x' ↔ x ≤ x')) :
--     Minimal P x ↔ Minimal Q (f x) := by
--   refine ⟨fun h ↦ ⟨hbij.mapsTo h.prop, fun y hy hyx ↦ ?_⟩, fun h ↦ ⟨?_, ?_⟩⟩
--   · obtain ⟨x', hx', rfl⟩ := hbij.surjOn hy
--     exact (hmono h.prop hx').2 <| h.le_of_le hx' <| (hmono hx' h.prop).1 hyx
--   · have := hinv.1

-- lemma minimal_apply_mono_bijOn_iff (hf : BijOn f {x | P x} {y | Q y})
--     (hmono : ∀ ⦃x x'⦄, P x → P x' → (f x ≤ f x' ↔ x ≤ x')) :
--     Minimal P x ↔ Minimal Q (f x) := by
--   refine ⟨fun h ↦ ⟨hf.mapsTo h.prop, fun y hy hyx ↦ ?_⟩, fun h ↦ ⟨?_, ?_⟩⟩
--   · obtain ⟨x', hx', rfl⟩ := hf.surjOn hy
--     exact (hmono h.prop hx').2 <| h.le_of_le hx' <| (hmono hx' h.prop).1 hyx
--   · obtain ⟨x', hPx', hx'⟩ := hf.surjOn h.prop





-- lemma minimal_apply_anti_bijOn_iff (hf : BijOn f {x | P x} {y | Q y})
--     (hanti : ∀ ⦃x x'⦄, P x → P x' → (f x' ≤ f x ↔ x ≤ x')) :
--     Minimal P x ↔ Maximal Q (f x) := by
--   sorry

-- lemma maximal_apply_mono_bijOn_iff (hf : BijOn f {x | P x} {y | Q y})
--     (hmono : ∀ ⦃x x'⦄, P x → P x' → (f x ≤ f x' ↔ x ≤ x')) :
--     Maximal P x ↔ Maximal Q (f x) := by
--   sorry

-- lemma maximal_apply_anti_bijOn_iff (hf : BijOn f {x | P x} {y | Q y})
--     (hanti : ∀ ⦃x x'⦄, P x → P x' → (f x ≤ f x' ↔ x' ≤ x)) :
--     Maximal P x ↔ Minimal Q (f x) := by
--   sorry

lemma minimal_apply_mono_iff (hPQ : ∀ x, P x ↔ Q (f x)) (hf : ∀ ⦃y⦄, Q y → ∃ x, P x ∧ f x = y)
    (hmono : ∀ ⦃x x'⦄, P x → P x' → (f x ≤ f x' ↔ x ≤ x')) : Minimal P x ↔ Minimal Q (f x) := by
  refine ⟨fun h ↦ ⟨(hPQ _).1 h.prop, fun b hb hbx ↦ ?_⟩,
    fun h ↦ ⟨(hPQ _).2 h.prop, fun a ha hax ↦ ?_⟩⟩
  · obtain ⟨a, ha, rfl⟩ := hf hb
    exact (hmono h.prop ha).2 <| h.le_of_le ha <| (hmono ha h.prop).1 hbx
  have hx := ((hPQ _).2 h.prop)
  exact (hmono hx ha).1 <| h.le_of_le ((hPQ _).1 ha) <| (hmono ha hx).2 hax

lemma minimal_apply_anti_iff (hPQ : ∀ x, P x ↔ Q (f x)) (hf : ∀ ⦃y⦄, Q y → ∃ x, P x ∧ f x = y)
    (hanti : ∀ ⦃x x'⦄, P x → P x' → (f x' ≤ f x ↔ x ≤ x')) : Minimal P x ↔ Maximal Q (f x) :=
  minimal_apply_mono_iff (β := βᵒᵈ) hPQ hf hanti

lemma maximal_apply_anti_iff (hPQ : ∀ x, P x ↔ Q (f x)) (hf : ∀ ⦃y⦄, Q y → ∃ x, P x ∧ f x = y)
    (hanti : ∀ ⦃x x'⦄, P x → P x' → (f x' ≤ f x ↔ x ≤ x')) : Maximal P x ↔ Minimal Q (f x) :=
  minimal_apply_mono_iff (α := αᵒᵈ) hPQ hf fun _ _ h h' ↦ hanti h' h

lemma maximal_apply_mono_iff (hPQ : ∀ x, P x ↔ Q (f x)) (hf : ∀ ⦃y⦄, Q y → ∃ x, P x ∧ f x = y)
    (hmono : ∀ ⦃x x'⦄, P x → P x' → (f x ≤ f x' ↔ x ≤ x')) : Maximal P x ↔ Maximal Q (f x) :=
  minimal_apply_mono_iff (α := αᵒᵈ) (β := βᵒᵈ) hPQ hf fun _ _ h h' ↦ hmono h' h

-- have := h.le_of_le ha (hmono )

-- lemma foo_mem [Preorder α] {s : Set α} (hfs : MonotoneOn f s)
--     (hft : InjOn f s) : Minimal (· ∈ s) x ↔ Minimal (f · ∈ f '' s) x := by
--   refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  -- _
  --   -- (hf : ∀ ⦃x x'⦄, P (f x) → P (f x') → x ≤ x' → f x ≤ f x')

  --   Minimal P (f x) := by
  -- refine ⟨hx.prop, fun y hy hyx ↦ ?_⟩
  -- obtain ⟨x', rfl⟩ := hfP hy
  -- refine hf hx.prop hy <| hx.le_of_le hy ?_


-- lemma foo (hfg : InvOn g f {x | P (f x)} {y | P y})
--     (hmono : ∀ ⦃x y⦄, P (f x) → P y → (x ≤ g y ↔ f x ≤ y)) :
--     Minimal (fun x ↦ P (f x)) x ↔ Minimal P (f x) := by
--   refine ⟨fun h ↦ ⟨h.prop, fun y hy hle ↦ ?_⟩, fun h ↦ ⟨h.prop, fun y hy hyx ↦ ?_⟩⟩
--   · rw [← hmono h.prop hy]
--     apply h.le_of_le (by rwa [hfg hy])

--     have h1 := hfg hy
--     have h2 := h.le_of_le (y := g y) (by rwa [hfg hy])
--     have h3 := hfg h.prop


-- lemma minimal_apply_monotone_iff (hmono : ∀ ⦃x y⦄, Q (f x) → Q (f y) → (f x ≤ f y ↔ x ≤ y))
--     (hf : ∀ x, Q x → x ∈ range f) : Minimal (fun x ↦ Q (f x)) x ↔ Minimal Q (f x) := by
--   refine ⟨fun h ↦ ⟨h.prop, fun y hy hle ↦ ?_⟩, fun h ↦
--     ⟨h.prop, fun y hy hyx ↦ (hmono h.prop hy).1 <| h.le_of_le hy <| (hmono hy h.prop).2 hyx⟩⟩
--   obtain ⟨x₀, rfl⟩ := hf y hy
--   exact (hmono h.prop hy).2 <| h.le_of_le hy <| (hmono hy h.prop).1 hle

-- lemma minimal_apply_antitone_iff (hanti : ∀ ⦃x y⦄, P (f x) → P (f y) → (f x ≤ f y ↔ y ≤ x))
--     (hf : ∀ x, P x → x ∈ range f) : Minimal (fun x ↦ P (f x)) x ↔ Maximal P (f x) :=
--   minimal_apply_monotone_iff (β := βᵒᵈ) (fun _ _ hx hy ↦ hanti hy hx) hf

-- lemma maximal_apply_monotone_iff (hmono : ∀ ⦃x y⦄, P (f x) → P (f y) → (f x ≤ f y ↔ x ≤ y))
--     (hf : ∀ x, P x → x ∈ range f) : Maximal (fun x ↦ P (f x)) x ↔ Maximal P (f x) :=
--   minimal_apply_monotone_iff (α := αᵒᵈ) (β := βᵒᵈ) (fun _ _ hx hy ↦ hmono hy hx) hf

-- lemma maximal_apply_antitone_iff (hanti : ∀ ⦃x y⦄, P (f x) → P (f y) → (f x ≤ f y ↔ y ≤ x))
--     (hf : ∀ x, P x → x ∈ range f) : Maximal (fun x ↦ P (f x)) x ↔ Minimal P (f x) :=
--   maximal_apply_monotone_iff (β := βᵒᵈ) (fun _ _ hx hy ↦ hanti hy hx) hf

-- lemma minimal_apply_monotone_mem_iff (hmono : ∀ ⦃x y⦄, f x ∈ s → f y ∈ s → (f x ≤ f y ↔ x ≤ y))
--     (hf : s ⊆ range f) : Minimal (f · ∈ s) x ↔ Minimal (· ∈ s) (f x) :=
--   minimal_apply_monotone_iff hmono hf

-- lemma minimal_apply_antitone_mem_iff (hanti : ∀ ⦃x y⦄, f x ∈ s → f y ∈ s → (f x ≤ f y ↔ y ≤ x))
--     (hf : s ⊆ range f) : Minimal (f · ∈ s) x ↔ Maximal (· ∈ s) (f x) :=
--   minimal_apply_antitone_iff hanti hf

-- lemma maximal_apply_monotone_mem_iff (hmono : ∀ ⦃x y⦄, f x ∈ s → f y ∈ s → (f x ≤ f y ↔ x ≤ y))
--     (hf : s ⊆ range f) : Maximal (f · ∈ s) x ↔ Maximal (· ∈ s) (f x) :=
--   maximal_apply_monotone_iff hmono hf

-- lemma maximal_apply_antitone_mem_iff (hanti : ∀ ⦃x y⦄, f x ∈ s → f y ∈ s → (f x ≤ f y ↔ y ≤ x))
--     (hf : s ⊆ range f) : Maximal (f · ∈ s) x ↔ Minimal (· ∈ s) (f x) :=
--   maximal_apply_antitone_iff hanti hf

variable {α ι : Type*} {P : α → Prop} {i j : ι} {x y : α}

lemma Minimal.le [LinearOrder α] (h : Minimal P x) (hy : P y) : x ≤ y :=
  (le_total x y).elim id (h.2 hy)

lemma MinimalFor.le [LinearOrder α] {P : ι → Prop} (f : ι → α) (h : MinimalFor P f i) (hj : P j) :
    f i ≤ f j := (le_total (f i) (f j)).elim id (h.2 hj)

lemma Maximal.le [LinearOrder α] (h : Maximal P x) (hy : P y) : y ≤ x :=
  (le_total y x).elim id (h.2 hy)

lemma MaximalFor.le [LinearOrder α] {P : ι → Prop} (f : ι → α) (h : MaximalFor P f i) (hj : P j) :
    f j ≤ f i := (le_total (f j) (f i)).elim id (h.2 hj)
