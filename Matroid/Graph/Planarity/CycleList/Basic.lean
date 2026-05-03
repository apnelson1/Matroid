import Mathlib.Data.List.Cycle
import Mathlib.Data.List.Fold
import Mathlib.Data.List.SplitBy
import Mathlib.Data.PNat.Defs
import Mathlib.Tactic.Simproc.VecPerm

variable {α β γ : Type*} {C C' : Cycle α} {l l' : List α} {x : α} {b : β} {c : γ}

open List

namespace List

theorem exists_sublist_isRotated_iff (L L' : List α) :
    (∃ L₁ : List α, L ~r L₁ ∧ L₁ <+ L') ↔ (∃ L₂ : List α, L <+ L₂ ∧ L₂ ~r L') := by
  refine ⟨fun ⟨L₁, hLr, hL⟩ => ?_, fun ⟨L₂, hL, hLr⟩ => ?_⟩
    <;> obtain ⟨n, hn, rfl⟩ := isRotated_iff_mod.mp hLr
  · obtain ⟨L₂L, L₂R, rfl, hL₂L, hL₂R⟩ := append_sublist_iff.mp (rotate_eq_drop_append_take hn ▸ hL)
    exact ⟨L₂R ++ L₂L, (by simpa using hL₂R.append hL₂L), isRotated_append⟩
  · obtain ⟨lL, lR, rfl, hL, hR⟩ := sublist_append_iff.mp <| take_append_drop n L₂ ▸ hL
    refine ⟨lR ++ lL, isRotated_append.symm, ?_⟩
    simpa [rotate_eq_drop_append_take hn] using hR.append hL

@[simp]
theorem countP_rotate (P : α → Prop) [DecidablePred P] (l : List α) (n : ℕ) :
    countP P (l.rotate n) = countP P l := by
  induction n generalizing l with | zero => simp | succ n IH => _
  match l with | [] => simp | a :: as => _
  simp [IH, countP_cons]

theorem IsRotated.countP_eq (h : l ~r l') (P : α → Prop) [DecidablePred P] :
    countP P l = countP P l' := by
  obtain ⟨n, hn, rfl⟩ := isRotated_iff_mod.mp h
  exact l.countP_rotate P n |>.symm

@[simp]
theorem count_rotate [DecidableEq α] (x : α) (l : List α) (n : ℕ) :
    (l.rotate n).count x = l.count x := l.countP_rotate _ n

theorem IsRotated.count_eq [DecidableEq α] (h : l ~r l') (x : α) : l.count x = l'.count x := by
  obtain ⟨n, hn, rfl⟩ := isRotated_iff_mod.mp h
  exact l.count_rotate x n |>.symm

-- #check List.splitBy_nil

theorem splitBy_cons (r : α → α → Bool) (a : α) (L : List α) :
    splitBy r (a :: L) = splitBy.loop r L a [] [] := by
  simp [splitBy]

@[simp]
lemma foldl_rotate {β} (f : β → α → β) [RightCommutative f] (b : β) (n : ℕ) (l : List α) :
    (l.rotate n).foldl f b = l.foldl f b := by
  induction n generalizing l with | zero => simp | succ n ih => _
  match l with | [] => simp | a :: as => _
  simp only [rotate_cons_succ, foldl_cons_eq_apply_foldl, ih, foldl_concat]

@[simp]
lemma foldr_rotate {β} (f : α → β → β) [LeftCommutative f] (b : β) (n : ℕ) (l : List α) :
    (l.rotate n).foldr f b = l.foldr f b := by
  induction n generalizing l with | zero => simp | succ n ih => _
  match l with | [] => simp | a :: as => _
  simp only [rotate_cons_succ, foldr_cons_eq_foldr_apply, ih, foldr_concat]

theorem IsRotated.foldl {β} (h : l ~r l') (f : β → α → β) [RightCommutative f] (b : β) :
    l.foldl f b = l'.foldl f b := by
  obtain ⟨n, rfl⟩ := h
  rw [foldl_rotate]

theorem IsRotated.foldr {β} (h : l ~r l') (f : α → β → β) [LeftCommutative f] (b : β) :
    l.foldr f b = l'.foldr f b := by
  obtain ⟨n, rfl⟩ := h
  rw [foldr_rotate]

def windows (n : ℕ) (l : List α) : List (Fin n → α) :=
  match n, l with
  | n + 1, a :: as => if h : as.length < n + 1 then [] else
    (fun i => as[i]'(by grind)) :: windows (n + 1) as
  | _, _ => []

end List

namespace Cycle

@[simp]
theorem mem_toMultiset_iff (x : α) (C : Cycle α) : x ∈ C.toMultiset ↔ x ∈ C := by
  induction C using Quotient.inductionOn with | _ l => simp

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
      exists_sublist_isRotated_iff _ _ |>.mpr ⟨_, hlm,
        (coe_eq_coe.mp ((mem_lists_iff_coe_eq.mp hl').symm ▸ mem_lists_iff_coe_eq.mp hm))⟩
    refine ⟨l₀, ?_, hsub⟩
    exact mem_lists_iff_coe_eq.mpr (mem_lists_iff_coe_eq.mp hl ▸ coe_eq_coe.mpr hrot.symm)
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

lemma isInfix_coe_iff : l <:+:c (l' : Cycle α) ↔ ∃ m : List α, l <:+: m ∧ m ~r l' :=
  ⟨fun ⟨m, hinf, e⟩ ↦ ⟨m, hinf, coe_eq_coe.mp e⟩, fun ⟨m, hinf, hr⟩ ↦ ⟨m, hinf, coe_eq_coe.mpr hr⟩⟩

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

/-! ### `count` / `countP` -/

section countP

def countP (P : α → Prop) [DecidablePred P] (C : Cycle α) : ℕ :=
  Quotient.liftOn C (·.countP P) fun _ _ h => h.countP_eq P

variable (P : α → Prop) [DecidablePred P]

@[simp] theorem countP_coe (l : List α) : Cycle.countP P l = l.countP P := rfl

@[simp]
theorem countP_eq_toMultiset_countP (C : Cycle α) : C.toMultiset.countP P = C.countP P := by
  induction C using Quotient.inductionOn with | _ l => simp

@[simp]
theorem countP_eq_of_mem_lists (hl : l ∈ C.lists) : C.countP P = l.countP P := by
  rw [← mem_lists_iff_coe_eq.mp hl, countP_coe]

@[simp]
theorem countP_reverse (C : Cycle α) : C.reverse.countP P = C.countP P := by
  induction C using Quotient.inductionOn with | _ l => simp

theorem countP_le_length (C : Cycle α) : C.countP P ≤ C.length := by
  rw [← countP_eq_toMultiset_countP, ← card_toMultiset]
  exact Multiset.countP_le_card P _

@[simp]
theorem countP_true (C : Cycle α) : C.countP (fun _ : α => True) = C.length := by
  rw [← countP_eq_toMultiset_countP, ← card_toMultiset, Multiset.countP_True]

@[simp]
theorem countP_false (C : Cycle α) : C.countP (fun _ : α => False) = 0 := by
  rw [← countP_eq_toMultiset_countP, Multiset.countP_False]

theorem length_eq_countP_add_countP (C : Cycle α) :
    C.length = C.countP P + C.countP (fun x => ¬ P x) := by
  rw [← card_toMultiset, ← countP_eq_toMultiset_countP (P := P),
    ← countP_eq_toMultiset_countP (P := fun x => ¬ P x)]
  exact C.toMultiset.card_eq_countP_add_countP (p := P)

@[simp]
theorem countP_pos_iff (C : Cycle α) : 0 < C.countP P ↔ ∃ x ∈ C, P x := by
  simp_rw [← countP_eq_toMultiset_countP, Multiset.countP_pos, mem_toMultiset_iff]

@[simp]
theorem one_le_countP_iff (C : Cycle α) : 1 ≤ C.countP P ↔ ∃ x ∈ C, P x := by
  rw [Nat.add_one_le_iff, countP_pos_iff]

@[simp]
theorem countP_eq_zero (C : Cycle α) : C.countP P = 0 ↔ ∀ x ∈ C, ¬ P x := by
  simp_rw [← countP_eq_toMultiset_countP, Multiset.countP_eq_zero, mem_toMultiset_iff]

@[simp]
theorem countP_eq_length (C : Cycle α) : C.countP P = C.length ↔ ∀ x ∈ C, P x := by
  simp_rw [← countP_eq_toMultiset_countP, ← card_toMultiset, Multiset.countP_eq_card,
    mem_toMultiset_iff]

theorem IsSubcycle.countP_le (h : C <+c C') : C.countP P ≤ C'.countP P := by
  obtain ⟨l, l', hsub, rfl, rfl⟩ := h
  simpa [countP_coe] using hsub.countP_le

theorem IsSubcycle.le_countP (h : C <+c C') :
    C'.countP P - (C'.length - C.length) ≤ C.countP P := by
  obtain ⟨l, l', hsub, rfl, rfl⟩ := h
  simpa [countP_coe, length_coe] using hsub.le_countP P

theorem IsInfix.countP_le (h : l <:+:c C) : l.countP P ≤ C.countP P := by
  obtain ⟨l', hinf, rfl⟩ := h
  simpa [countP_coe] using hinf.countP_le

@[simp]
theorem countP_map {β : Type*} (f : α → β) (P : β → Prop) [DecidablePred P] (C : Cycle α) :
    (C.map f).countP P = C.countP (P ∘ f) := by
  induction C using Quotient.inductionOn with | _ l => simp [Function.comp_def]

end countP

section count

variable [DecidableEq α] (x : α)

def count (C : Cycle α) : ℕ := countP (· == x) C

@[simp]
theorem count_coe (l : List α) : Cycle.count x l = l.count x := by
  simp [Bool.beq_eq_decide_eq, count, List.count]

@[simp]
theorem count_eq_toMultiset_count (C : Cycle α) : C.toMultiset.count x = C.count x := by
  simp [Bool.beq_eq_decide_eq, eq_comm, Multiset.count, count]

@[simp]
theorem count_eq_of_mem_lists (hl : l ∈ C.lists) : C.count x = l.count x := by
  rw [← mem_lists_iff_coe_eq.mp hl, count_coe]

@[simp] theorem count_reverse (C : Cycle α) : C.reverse.count x = C.count x := by simp [count]

theorem count_le_length (C : Cycle α) : C.count x ≤ C.length := C.countP_le_length _

@[simp] theorem count_pos_iff (C : Cycle α) : 0 < C.count x ↔ x ∈ C := by simp [count]

@[simp]
theorem count_eq_zero (C : Cycle α) : C.count x = 0 ↔ x ∉ C := by
  simp only [count, beq_iff_eq, countP_eq_zero]; grind

@[simp]
theorem one_le_count_iff (C : Cycle α) : 1 ≤ C.count x ↔ x ∈ C := by
  rw [Nat.add_one_le_iff, count_pos_iff]

theorem count_eq_length (C : Cycle α) : C.count x = C.length ↔ ∀ y ∈ C, x = y := by
  simp [count]; grind

theorem IsSubcycle.count_le (h : C <+c C') : C.count x ≤ C'.count x := by
  obtain ⟨l, l', hsub, rfl, rfl⟩ := h
  simpa [count_coe] using hsub.count_le x

theorem IsSubcycle.le_count (h : C <+c C') : C'.count x - (C'.length - C.length) ≤ C.count x := by
  obtain ⟨l, l', hsub, rfl, rfl⟩ := h
  simpa [count_coe, length_coe] using hsub.le_count x

theorem IsInfix.count_le (h : l <:+:c C) : l.count x ≤ C.count x := by
  obtain ⟨l', hinf, rfl⟩ := h
  simpa [count_coe] using hinf.sublist.count_le x

theorem Nodup.count (hC : C.Nodup) : C.count x = if x ∈ C then 1 else 0 := by
  obtain ⟨l, hl⟩ := C.exists_mem_lists
  simp only [← mem_lists_iff_coe_eq.mp hl, nodup_coe_iff, count_coe, mem_coe_iff] at hC ⊢
  exact hC.count

theorem nodup_iff_count_le_one : C.Nodup ↔ ∀ x : α, C.count x ≤ 1 := by
  induction C using Quotient.inductionOn with | _ l => simp [List.nodup_iff_count_le_one]

theorem count_le_count_map [DecidableEq β] (f : α → β) (C : Cycle α) :
    C.count x ≤ (C.map f).count (f x) := by
  induction C using Quotient.inductionOn with | _ l => simpa using l.count_le_count_map

end count

section foldl

def foldl (f : β → α → β) [RightCommutative f] (b : β) (C : Cycle α) : β :=
  C.liftOn (·.foldl f b) (fun _ _ h ↦ h.foldl ..)

def foldr (f : α → β → β) [LeftCommutative f] (b : β) (C : Cycle α) : β :=
  C.liftOn (·.foldr f b) (fun _ _ h ↦ h.foldr ..)

end foldl

end Cycle
