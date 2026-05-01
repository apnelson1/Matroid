import Mathlib.Data.List.Cycle

variable {α : Type*} {C C' : Cycle α} {l l' : List α} {x : α}

open List

namespace List

/-- If `l` is a sublist of `m` and `m` is a rotation of `m'`, then some rotation of `l` is a
sublist of `m'`. -/
lemma exists_isRotated_sublist_of_sublist_isRotated {l m m' : List α}
    (h : l <+ m) (hr : m ~r m') : ∃ l' : List α, l' ~r l ∧ l' <+ m' := by
  obtain ⟨n, hn, rfl⟩ := isRotated_iff_mod.mp hr
  obtain ⟨lL, lR, rfl, hL, hR⟩ := sublist_append_iff.mp <| take_append_drop n m ▸ h
  refine ⟨lR ++ lL, isRotated_append.symm, ?_⟩
  simpa [rotate_eq_drop_append_take hn] using hR.append hL

instance : IsPartialOrder (List α) Sublist where
  refl := Sublist.refl
  trans _ _ _ := Sublist.trans
  antisymm _ _ := Sublist.antisymm

instance : IsPreorder (List α) IsRotated where
  refl := IsRotated.refl
  trans _ _ _ := IsRotated.trans

end List

namespace Cycle

/-- `C <+ C'` means that `C` is a non-contiguous subcycle/sublist of `C'. -/
def IsSubcycle (C C' : Cycle α) : Prop := ∃ l l' : List α, l <+ l' ∧ l = C ∧ l' = C'

@[inherit_doc] infixl:50 " <+c " => IsSubcycle

/-- not `isSubCycle` -/
recommended_spelling "subcycle" for "<+c" in [IsSubcycle, «term_<+c_»]

/-- `l <:+: C` means that `l` is a contiguous sublist of some list representative of `C`. -/
def IsInfix (l : List α) (C : Cycle α) : Prop := ∃ l' : List α, l <:+: l' ∧ l' = C

@[inherit_doc] infixl:50 " <:+:c " => IsInfix

/-- not `isInfix` -/
recommended_spelling "infix" for "<:+:c" in [IsInfix, «term_<:+:c_»]

/-! ### Representative lemmas -/

lemma isSubcycle_iff_exists_lists : C <+c C' ↔ ∃ l ∈ C.lists, ∃ l' ∈ C'.lists, l <+ l' :=
  ⟨fun ⟨l, l', hsub, e1, e2⟩ ↦
    ⟨l, mem_lists_iff_coe_eq.mpr e1, l', mem_lists_iff_coe_eq.mpr e2, hsub⟩,
    fun ⟨l, hl, l', hl', hsub⟩ ↦
    ⟨l, l', hsub, mem_lists_iff_coe_eq.mp hl, mem_lists_iff_coe_eq.mp hl'⟩⟩

lemma exists_mem_lists (C : Cycle α) : ∃ l, l ∈ C.lists :=
  Quotient.inductionOn' C fun l => ⟨l, mem_lists_iff_coe_eq.mpr rfl⟩

lemma isSubcycle_iff_forall_right : C <+c C' ↔ ∀ l' ∈ C'.lists, ∃ l ∈ C.lists, l <+ l' := by
  refine isSubcycle_iff_exists_lists.trans ⟨fun ⟨l, hl, m, hm, hlm⟩ l' hl' ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨l₀, hrot, hsub⟩ :=
      List.exists_isRotated_sublist_of_sublist_isRotated hlm
        (coe_eq_coe.mp ((mem_lists_iff_coe_eq.mp hm).trans (mem_lists_iff_coe_eq.mp hl').symm))
    refine ⟨l₀, ?_, hsub⟩
    exact mem_lists_iff_coe_eq.mpr ((coe_eq_coe.mpr hrot).trans (mem_lists_iff_coe_eq.mp hl))
  · obtain ⟨l', hl'⟩ := exists_mem_lists C'
    obtain ⟨l, hl, hsub⟩ := h l' hl'
    exact ⟨l, hl, l', hl', hsub⟩

lemma isInfix_iff_exists_list : l <:+:c C ↔ ∃ l' ∈ C.lists, l <:+: l' :=
  ⟨fun ⟨l', hinf, e⟩ ↦ ⟨l', mem_lists_iff_coe_eq.mpr e, hinf⟩,
    fun ⟨l', hl', hinf⟩ ↦ ⟨l', hinf, mem_lists_iff_coe_eq.mp hl'⟩⟩

lemma _root_.List.Sublist.isSubcycle (h : l <+ l') : l <+c (l' : Cycle α) := ⟨l, l', h, rfl, rfl⟩

lemma _root_.List.IsInfix.isCycleInfix (h : l <:+: l') : l <:+:c (l' : Cycle α) := ⟨l', h, rfl⟩

lemma isSubcycle_coe_iff : l <+c (l' : Cycle α) ↔ ∃ m m' : List α, m ~r l ∧ m' ~r l' ∧ m <+ m' :=
  ⟨fun ⟨m, m', hsub, hm, hm'⟩ ↦ ⟨m, m', (coe_eq_coe.mp hm), (coe_eq_coe.mp hm'), hsub⟩,
    fun ⟨m, m', hr, hr', hsub⟩ ↦ ⟨m, m', hsub, coe_eq_coe.mpr hr, coe_eq_coe.mpr hr'⟩⟩

lemma isInfix_coe_iff : l <:+:c (l' : Cycle α) ↔ ∃ m : List α, m ~r l' ∧ l <:+: m :=
  ⟨fun ⟨m, hinf, e⟩ ↦ ⟨m, coe_eq_coe.mp e, hinf⟩, fun ⟨m, hr, hinf⟩ ↦ ⟨m, hinf, coe_eq_coe.mpr hr⟩⟩

/-! ### `IsSubcycle` -/

@[simp]
lemma isSubcycle_refl (C : Cycle α) : C <+c C :=
  Quotient.inductionOn' C fun l => ⟨l, l, Sublist.refl _, rfl, rfl⟩

lemma IsSubcycle.length_le (h : C <+c C') : C.length ≤ C'.length := by
  obtain ⟨l, l', hsub, rfl, rfl⟩ := h
  simpa using hsub.length_le

lemma IsSubcycle.eq_of_length_ge (h : C <+c C') (hle : C'.length ≤ C.length) : C = C' := by
  obtain ⟨l, l', hsub, rfl, rfl⟩ := h
  have hl : l'.length ≤ l.length := by simpa using hle
  simp [hsub.eq_of_length_le hl]

lemma IsSubcycle.antisymm (h : C <+c C') (h' : C' <+c C) : C = C' :=
  h.eq_of_length_ge h'.length_le

lemma IsSubcycle.trans {C₁ C₂ C₃ : Cycle α} (h₁₂ : C₁ <+c C₂) (h₂₃ : C₂ <+c C₃) : C₁ <+c C₃ := by
  rw [isSubcycle_iff_forall_right] at h₁₂ h₂₃ ⊢
  rintro l₃ hl₃
  obtain ⟨l₂, hl₂, h₂₃⟩ := h₂₃ l₃ hl₃
  obtain ⟨l₁, hl₁, h₁₂⟩ := h₁₂ l₂ hl₂
  exact ⟨l₁, hl₁, h₁₂.trans h₂₃⟩

instance : IsPartialOrder (Cycle α) IsSubcycle where
  refl := isSubcycle_refl
  trans := fun _ _ _ => IsSubcycle.trans
  antisymm := fun _ _ => IsSubcycle.antisymm

lemma IsSubcycle.mem (h : C <+c C') (hx : x ∈ C) : x ∈ C' := by
  obtain ⟨l, l', hsub, rfl, rfl⟩ := h
  simpa [mem_coe_iff] using hsub.subset hx

lemma IsSubcycle.nodup (h : C <+c C') (hC' : C'.Nodup) : C.Nodup := by
  obtain ⟨l, l', hsub, rfl, rfl⟩ := h
  simpa [nodup_coe_iff] using Nodup.sublist hsub (by simpa [nodup_coe_iff] using hC')

lemma IsSubcycle.reverse (h : C <+c C') : C.reverse <+c C'.reverse := by
  obtain ⟨l, l', hsub, rfl, rfl⟩ := h
  exact ⟨l.reverse, l'.reverse, hsub.reverse, by simp, by simp⟩

lemma nil_isSubcycle (C : Cycle α) : nil <+c C := by
  obtain ⟨l, hsub⟩ := exists_mem_lists C
  exact ⟨[], l, l.nil_sublist, rfl, mem_lists_iff_coe_eq.mp hsub⟩

@[simp]
lemma IsSubcycle.of_nil : C <+c nil ↔ C = nil := by
  refine ⟨fun ⟨l, l', hsub, h, hnil⟩ ↦ h ▸ ?_, fun h ↦ h ▸ isSubcycle_refl _⟩
  rw [coe_eq_nil] at hnil ⊢
  exact eq_nil_of_sublist_nil <| hnil ▸ hsub

/-! ### `IsInfix` (path in a cycle) -/

lemma IsInfix.isSubcycle (h : l <:+:c C) : l <+c C := by
  obtain ⟨l', hinf, rfl⟩ := h
  exact ⟨l, l', hinf.sublist, rfl, rfl⟩

lemma IsInfix.trans (h₁₂ : l <:+: l') (h₂ : l' <:+:c C) : l <:+:c C := by
  obtain ⟨l', h₂infix, rfl⟩ := h₂
  exact ⟨l', h₁₂.trans h₂infix, rfl⟩

instance : Trans (α := List α) List.IsInfix IsInfix IsInfix where
  trans := IsInfix.trans

lemma IsInfix.reverse (h : l <:+:c C) : l.reverse <:+:c C.reverse := by
  obtain ⟨l', hinf, rfl⟩ := h
  exact ⟨_, hinf.reverse, by simp⟩

@[simp]
lemma nil_isInfix (C : Cycle α) : [] <:+:c C :=
  Quotient.inductionOn' C fun l => ⟨l, ⟨l, [], by simp⟩, rfl⟩

lemma IsInfix.of_nil_iff : l <:+:c (@nil α) ↔ l = [] := by
  refine ⟨fun ⟨l', hinf, hnil⟩ ↦ ?_, fun h ↦ ⟨[], h ▸ List.infix_rfl, rfl⟩⟩
  rw [coe_eq_nil] at hnil
  subst hnil
  obtain ⟨s, t, he⟩ := hinf
  match s with
  | [] => grind [append_eq_nil_iff]
  | cons _ _ => simp at he

end Cycle
