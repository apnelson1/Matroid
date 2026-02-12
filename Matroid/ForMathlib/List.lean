import Mathlib.Data.Finset.Card

namespace List

lemma Nodup.countP_eq_card {α} {l : List α} {P : α → Prop} [DecidableEq α] [DecidablePred P]
    (h : l.Nodup) : countP P l = (l.toFinset.filter P).card := by
  rw [countP_eq_length_filter, ← toFinset_card_of_nodup (h.filter ..)]
  simp

lemma eq_of_length_eq_zero {α} {l : List α} (h : l.length = 0) : l = [] := by
  match l with
  | [] => rfl
  | head :: tail => simp at h

lemma eq_of_length_eq_one {α} {l : List α} (h : l.length = 1) : l = [l[0]] := by
  match l with
  | [] => simp at h
  | head :: tail => simpa using h

lemma eq_of_length_eq_two {α} {l : List α} (h : l.length = 2) : l = [l[0], l[1]] := by
  match l with
  | [] => simp at h
  | head :: [tail] => simp
  | head :: tail :: tail' => simpa using h

lemma eq_of_length_eq_three {α} {l : List α} (h : l.length = 3) : l = [l[0], l[1], l[2]] := by
  match l with
  | [] => simp at h
  | head :: [tail] => simp at h
  | head :: tail :: [tail'] => simp
  | head :: tail :: tail' :: tail'' => simpa using h

lemma mem_dropLast_iff {ι} {x : ι} {l : List ι} (hnd : l.Nodup) (hne : l ≠ []) :
    x ∈ l.dropLast ↔ x ∈ l ∧ x ≠ l.getLast hne := by
  obtain rfl | ⟨l', y, rfl⟩ := l.eq_nil_or_concat
  · simp at hne
  simp only [concat_eq_append, nodup_append, nodup_cons, not_mem_nil, not_false_eq_true, nodup_nil,
    and_self, mem_cons, or_false, ne_eq, forall_eq, true_and] at hnd
  simp only [concat_eq_append, ne_eq, cons_ne_self, not_false_eq_true, dropLast_append_of_ne_nil,
    dropLast_singleton, append_nil, mem_append, mem_cons, not_mem_nil, or_false,
    getLast_append_of_ne_nil, getLast_singleton]
  refine ⟨fun h => ?_, fun h => h.1.elim id (h.2 · |>.elim)⟩
  simp [h, hnd.2 x h]

lemma mem_dropLast_of_mem_ne {ι} {x : ι} {l : List ι} (hne : l ≠ []) (hmem : x ∈ l)
    (hxne : x ≠ l.getLast hne) : x ∈ l.dropLast := by
  obtain rfl | ⟨l', y, rfl⟩ := l.eq_nil_or_concat
  · simp at hne
  simp_all

lemma op_foldl_eq_foldl_op_of_assoc {α} {f : α → α → α} [Std.Associative f] :
    ∀ a b l, (foldl f (f a b) l) = f a (foldl f b l)
  | _, _, nil => rfl
  | a, b, c :: l => by
    simp only [foldl_cons]
    simp_rw [Std.Associative.assoc a b c]
    rw [op_foldl_eq_foldl_op_of_assoc ..]

lemma Nodup.eq_singleton_iff_head_getLast {α} {l : List α} (hnd : l.Nodup) (hne : l ≠ []) :
    l.head hne = l.getLast hne ↔ ∃ x, l = [x] := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · match l with
  | [] => simp at hne
  | head :: tail =>
    simp only [head_cons, nodup_cons, cons.injEq] at h hnd ⊢
    by_contra! htail
    simp_all
  obtain ⟨x, rfl⟩ := h
  simp

lemma IsSuffix.eq_of_first_mem {α} {l₁ l₂ : List α} (h : l₁.IsSuffix l₂) (hnd : l₂.Nodup)
    (hne : l₂ ≠ []) (hl : l₂.head hne ∈ l₁) : l₁ = l₂ := by
  match h with | .intro w h => ?_
  subst l₂
  rw [self_eq_append_left]
  match w with
  | [] => rfl
  | a :: as => simp_all

lemma IsPrefix.eq_of_last_mem {α} {l₁ l₂ : List α} (h : l₁.IsPrefix l₂) (hnd : l₂.Nodup)
    (hne : l₂ ≠ []) (hl : l₂.getLast hne ∈ l₁) : l₁ = l₂ := by
  simpa using h.reverse.eq_of_first_mem (by simpa) (by simpa) (by simpa)

lemma isChain_iff_all_zip_tail {α} (r : α → α → Prop) (l : List α) :
    l.IsChain r ↔ ∀ x ∈ l.zip l.tail, r x.1 x.2 := by
  induction l with | nil => simp | cons a l ih => cases l with | nil => simp | cons b t => simp [ih]

@[simp]
lemma isChain_and_iff {α} (r s : α → α → Prop) (l : List α) :
    l.IsChain (fun x y ↦ r x y ∧ s x y) ↔ l.IsChain r ∧ l.IsChain s := by
  match l with
  | [] => simp
  | [a] => simp
  | a :: b :: as =>
    simp only [isChain_cons_cons]
    rw [isChain_and_iff]
    tauto
