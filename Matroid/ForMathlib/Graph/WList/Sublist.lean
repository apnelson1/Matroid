import Matroid.ForMathlib.Graph.WList.Ops
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic


open Set Function List Nat WList

variable {α β : Type*} {u v x y z : α} {e e' f g : β} {S T U: Set α}
  {F F' : Set β} {w w₁ w₂ w₃ : WList α β}

namespace WList

/-- `w₁.IsSublist w₂` means that `w₁` is a wList using some of the vertices and edges of `w₂`
in the same order that they appear in `w₂`.
Examples include prefixes, suffixes and wLists obtained from `w₂` by shortcuts.  -/
inductive IsSublist : WList α β → WList α β → Prop
  | nil x w (h : x ∈ w) : IsSublist (nil x) w
  | cons x e w₁ w₂ (h : IsSublist w₁ w₂) : IsSublist w₁ (cons x e w₂)
  | cons₂ x e w₁ w₂ (h : IsSublist w₁ w₂) (h_eq : w₁.first = w₂.first) :
      IsSublist (cons x e w₁) (cons x e w₂)

@[simp]
lemma nil_isSublist_iff : (WList.nil x (β := β)).IsSublist w ↔ x ∈ w := by
  refine ⟨fun h ↦ ?_, IsSublist.nil _ _⟩
  induction w with
  | nil => cases h with | nil _ => assumption
  | cons u e W ih => cases h with
    | nil => assumption
    | cons x e _ _ h => simp [ih h]

@[simp]
lemma isSublist_nil_iff : w.IsSublist (nil x) ↔ w = nil x :=
  ⟨fun h ↦ by cases h with simp_all, by rintro rfl; simp⟩

@[simp]
lemma isSublist_refl (w : WList α β) : w.IsSublist w := by
  induction w with
  | nil => simp
  | cons u e w ih => exact ih.cons₂ _ _ _ _ rfl

lemma IsSublist.vx_sublist (h : w₁.IsSublist w₂) : w₁.vx <+ w₂.vx := by
  induction h with
  | nil => simpa
  | cons x e w₁ w₂ h ih => exact ih.trans <| by simp
  | cons₂ x e w₁ w₂ h ih => simpa

lemma IsSublist.mem (h : w₁.IsSublist w₂) (hx : x ∈ w₁) : x ∈ w₂ :=
  h.vx_sublist.mem hx

lemma IsSublist.edge_sublist {w₁ w₂ : WList α β} (h : w₁.IsSublist w₂) : w₁.edge <+ w₂.edge := by
  induction h with
  | nil => simp
  | cons x e w₁ w₂ h ih => exact ih.trans <| by simp
  | cons₂ x e w₁ w₂ h ih => simpa

lemma IsSublist.length_le (h : w₁.IsSublist w₂) : w₁.length ≤ w₂.length := by
  rw [← length_edge, ← length_edge]
  exact h.edge_sublist.length_le

lemma IsSublist.eq_of_length_ge (h : w₁.IsSublist w₂) (hge : w₂.length ≤ w₁.length) : w₁ = w₂ :=
  ext_vx_edge (h.vx_sublist.eq_of_length_le (by simpa)) <| h.edge_sublist.eq_of_length_le (by simpa)

lemma IsSublist.trans (h : w₁.IsSublist w₂) (h' : w₂.IsSublist w₃) : w₁.IsSublist w₃ := by
  induction h' generalizing w₁ with
  | nil x w h' => simp_all
  | cons x e w₂ w₃ h' ih => exact cons x e w₁ w₃ (ih h)
  | cons₂ x e w₂ w₃ h' h_eq ih => cases h with
    | nil y w₁ h =>
      simp only [nil_isSublist_iff, mem_cons_iff] at h ⊢
      exact h.elim .inl <| .inr ∘ h'.vx_sublist.mem
    | cons x e w₁ w₂ h => apply (ih h).cons
    | cons₂ x e w₁ w₂ h h_eq' => exact (ih h).cons₂ _ _ _ _ (h_eq'.trans h_eq)

lemma IsSublist.antisymm (h : w₁.IsSublist w₂) (h' : w₂.IsSublist w₁) : w₁ = w₂ :=
  h.eq_of_length_ge h'.length_le

@[simp]
lemma isSublist_cons_self (w : WList α β) (x : α) (e : β) : w.IsSublist (cons x e w) :=
  (isSublist_refl (w := w)).cons ..

lemma IsSublist.concat (h : w₁.IsSublist w₂) (e : β) (x : α) : w₁.IsSublist (w₂.concat e x) := by
  induction h with
  | nil x w h => simp [h]
  | cons y f w₁ w₂ h ih => simpa using ih.cons ..
  | cons₂ y f w₁ w₂ h h_eq ih => exact ih.cons₂ _ _ _ _ (by simpa)

lemma IsSublist.concat₂ (h : w₁.IsSublist w₂) (hlast : w₁.last = w₂.last) (e : β) (x : α) :
    (w₁.concat e x).IsSublist (w₂.concat e x) := by
  induction h with
  | nil y w h => induction w with
    | nil u => simp [show y = u by simpa using h]
    | cons u f w ih => exact IsSublist.cons _ _ _ _ (by simpa [show y = w.last from hlast] using ih)
  | cons y f w₁ w₂ h ih => exact (ih (by simpa using hlast)).cons y f
  | cons₂ y f w₁ w₂ h h_eq ih => exact (ih (by simpa using hlast)).cons₂ y f _ _ (by simpa)

@[simp]
lemma isSublist_concat_self (w : WList α β) (e : β) (x : α) : w.IsSublist (w.concat e x) :=
  (isSublist_refl (w := w)).concat ..

lemma IsSublist.reverse (h : w₁.IsSublist w₂) : w₁.reverse.IsSublist w₂.reverse := by
  induction h with
  | nil => simpa
  | cons x e w₁ w₂ h ih => exact ih.trans <| by simp
  | cons₂ x e w₁ w₂ h h_eq ih => apply ih.concat₂ <| by simpa

lemma IsSublist.of_reverse (h : w₁.reverse.IsSublist w₂.reverse) : w₁.IsSublist w₂ := by
  simpa using h.reverse

/-- ## Prefixes -/

-- /-- `IsPrefix w₁ w₂` means that `w₁` is a prefix of `w₂`. -/
inductive IsPrefix : WList α β → WList α β → Prop
  | nil (w : WList α β) : IsPrefix (nil w.first) w
  | cons (x) (e) (w₁ w₂ : WList α β) (h : IsPrefix w₁ w₂) : IsPrefix (cons x e w₁) (cons x e w₂)

lemma IsPrefix.first_eq (h : IsPrefix w₁ w₂) : w₁.first = w₂.first := by
  induction h with simp

lemma IsPrefix.exists_eq_append (h : IsPrefix w₁ w₂) :
    ∃ w₁', w₁.last = w₁'.first ∧ w₁ ++ w₁' = w₂ := by
  induction h with | nil => simp | cons => simpa

lemma isPrefix_append_right (hw : w₁.last = w₂.first) : w₁.IsPrefix (w₁ ++ w₂) := by
  induction w₁ with
  | nil => convert IsPrefix.nil w₂
  | cons u e w₁ ih => simpa using (ih hw).cons ..

lemma IsPrefix.isSublist (h : w₁.IsPrefix w₂) : w₁.IsSublist w₂ := by
  induction h with | nil => simp | cons _ _ _ _ h ih => exact ih.cons₂ _ _ _ _ h.first_eq

lemma IsPrefix.mem (h : w₁.IsPrefix w₂) (hx : x ∈ w₁) : x ∈ w₂ :=
  h.isSublist.mem hx

@[simp]
lemma isPrefix_refl : w.IsPrefix w := by
  induction w with
  | nil u => exact IsPrefix.nil <| nil u
  | cons _ _ _ ih => apply ih.cons

@[simp]
lemma isPrefix_nil_iff : w.IsPrefix (nil x) ↔ w = nil x :=
  ⟨fun h ↦ isSublist_nil_iff.1 h.isSublist, fun h ↦ h ▸ isPrefix_refl⟩

@[simp]
lemma nil_isPrefix_iff : (nil x).IsPrefix w ↔ w.first = x :=
  ⟨fun h ↦ by cases h with rfl, by rintro rfl; exact IsPrefix.nil w⟩

lemma IsPrefix.trans (h : w₁.IsPrefix w₂) (h' : w₂.IsPrefix w₃) : w₁.IsPrefix w₃ := by
  induction h' generalizing w₁ with
  | nil w => simp_all
  | cons x e w₂ w₃ h' ih => cases h with
    | nil w => simp
    | cons x e w₁ w₂ h => apply (ih h).cons

lemma IsPrefix.vx_isPrefix (h : w₁.IsPrefix w₂) : w₁.vx <+: w₂.vx := by
  induction h with
  | nil w => induction w with | _ => simp
  | cons => simpa

lemma IsPrefix.edge_isPrefix (h : w₁.IsPrefix w₂) : w₁.edge <+: w₂.edge := by
  induction h with | nil => simp | cons => simpa

lemma IsPrefix.eq_of_length_ge (h : w₁.IsPrefix w₂) (hge : w₂.length ≤ w₁.length) : w₁ = w₂ :=
  h.isSublist.eq_of_length_ge hge

lemma IsPrefix.length_le (h : w₁.IsPrefix w₂) : w₁.length ≤ w₂.length :=
  h.isSublist.length_le

lemma IsPrefix.antisymm (h : w₁.IsPrefix w₂) (h' : w₂.IsPrefix w₁) : w₁ = w₂ :=
  h.eq_of_length_ge h'.length_le


lemma IsPrefix.concat (h : w₁.IsPrefix w₂) (e x) : w₁.IsPrefix (w₂.concat e x) := by
  induction h with | nil => simp | cons y f w₁ w₂ h ih => exact ih.cons y f

@[simp]
lemma isPrefix_concat_self (w : WList α β) (e) (x) : w.IsPrefix (w.concat e x) :=
  isPrefix_refl.concat e x

/- ## Suffixes -/

inductive IsSuffix : WList α β → WList α β → Prop
  | nil (w : WList α β) : IsSuffix (nil w.last) w
  | concat (e x w₁ w₂) (h : IsSuffix w₁ w₂) : IsSuffix (w₁.concat e x) (w₂.concat e x)

lemma IsSuffix.reverse_isPrefix_reverse (h : w₁.IsSuffix w₂) : w₁.reverse.IsPrefix w₂.reverse := by
  induction h with | nil => simp | concat e x w₁ w₂ h ih => simp [ih.cons]

lemma IsPrefix.reverse_isSuffix_reverse (h : w₁.IsPrefix w₂) : w₁.reverse.IsSuffix w₂.reverse := by
  induction h with
  | nil w => simpa [reverse_nil] using IsSuffix.nil w.reverse
  | cons x e w₁ w₂ h ih => simpa using ih.concat e x

@[simp]
lemma reverse_isPrefix_reverse_iff : w₁.reverse.IsPrefix w₂.reverse ↔ w₁.IsSuffix w₂ :=
  ⟨fun h ↦ by simpa using h.reverse_isSuffix_reverse, IsSuffix.reverse_isPrefix_reverse⟩

@[simp]
lemma reverse_isSuffix_reverse_iff : w₁.reverse.IsSuffix w₂.reverse ↔ w₁.IsPrefix w₂ := by
  nth_rewrite 2 [← w₁.reverse_reverse, ← w₂.reverse_reverse]
  rw [reverse_isPrefix_reverse_iff]

@[simp]
lemma isSuffix_refl : w.IsSuffix w := by
  simpa using (isPrefix_refl (w := w.reverse)).reverse_isSuffix_reverse

lemma IsSuffix.isSublist (h : w₁.IsSuffix w₂) : w₁.IsSublist w₂ :=
  h.reverse_isPrefix_reverse.isSublist.of_reverse

lemma IsSuffix.mem (h : w₁.IsSuffix w₂) (hx : x ∈ w₁) : x ∈ w₂ :=
  h.isSublist.mem hx

@[simp]
lemma isSuffix_nil_iff : w.IsSuffix (nil x) ↔ w = nil x :=
  ⟨fun h ↦ isSublist_nil_iff.1 h.isSublist, fun h ↦ h ▸ isSuffix_refl⟩

@[simp]
lemma nil_isSuffix_iff : (nil x).IsSuffix w ↔ w.last = x := by
  rw [← reverse_isPrefix_reverse_iff, reverse_nil, nil_isPrefix_iff, reverse_first]

lemma IsSuffix.last_eq (h : w₁.IsSuffix w₂) : w₁.last = w₂.last :=
  by simpa using h.reverse_isPrefix_reverse.first_eq

lemma IsSuffix.length_le (h : w₁.IsSuffix w₂) : w₁.length ≤ w₂.length :=
  h.isSublist.length_le

lemma IsSuffix.trans (h : w₁.IsSuffix w₂) (h' : w₂.IsSuffix w₃) : w₁.IsSuffix w₃ := by
  simpa using (h.reverse_isPrefix_reverse.trans h'.reverse_isPrefix_reverse)

lemma IsSuffix.eq_of_length_ge (h : w₁.IsSuffix w₂) (hge : w₂.length ≤ w₁.length) : w₁ = w₂ :=
  h.isSublist.eq_of_length_ge hge

lemma IsSuffix.antisymm (h : w₁.IsSuffix w₂) (h' : w₂.IsSuffix w₁) : w₁ = w₂ :=
  h.eq_of_length_ge h'.length_le

lemma IsSuffix.cons (h : w₁.IsSuffix w₂) (x e) : w₁.IsSuffix (cons x e w₂) := by
  simpa using (h.reverse_isPrefix_reverse.concat e x).reverse_isSuffix_reverse

@[simp]
lemma isSuffix_cons_self (w : WList α β) (e) (x) : w.IsSuffix (cons x e w) :=
  isSuffix_refl.cons ..

@[simp]
lemma isSuffix_append_left (w₁ w₂ : WList α β) : w₂.IsSuffix (w₁ ++ w₂) := by
  induction w₁ with | nil => simp | cons u e w ih => simpa using ih.cons ..

/-! # Cutting wLists Off -/

variable {P : α → Prop} [DecidablePred P]

/-- Take the prefix ending at the first vertex satisfying a predicate `P`
(or the entire wList if nothing satisfies `P`). -/
def prefixUntil (w : WList α β) (P : α → Prop) [DecidablePred P] : WList α β :=
  match w with
  | nil x => nil x
  | cons x e w => if P x then nil x else cons x e (prefixUntil w P)

lemma prefixUntil_eq_nil (hP : P w.first) : w.prefixUntil P = nil w.first := by
  match w with
  | .nil u => rfl
  | .cons u e w' => simpa [prefixUntil]

@[simp] lemma prefixUntil_nil : (nil u (β := β)).prefixUntil P = nil u := rfl

@[simp]
lemma prefixUntil_cons (w) :
    (cons x e w).prefixUntil P = if P x then nil x else cons x e (w.prefixUntil P) := rfl

@[simp]
lemma prefixUntil_first (w : WList α β) : (w.prefixUntil P).first = w.first := by
  cases w with simp [apply_ite]

lemma prefixUntil_prop_last {w : WList α β} (h : ∃ u ∈ w, P u) : P (w.prefixUntil P).last := by
  induction w with
  | nil u => simpa using h
  | cons u e W ih =>
    obtain h | h : P u ∨ ∃ a ∈ W, P a := by simpa using h
    all_goals simp_all [apply_ite]

lemma prefixUntil_not_prop (hx : x ∈ w.prefixUntil P) (hne : x ≠ (w.prefixUntil P).last) :
    ¬ P x := by
  induction w with
  | nil u => simp_all
  | cons u e W ih =>
    refine (em (P u)).elim (fun _ ↦ by simp_all) fun hu ↦ ?_
    rw [prefixUntil_cons, if_neg hu, mem_cons_iff] at hx
    cases hx <;> simp_all

lemma Nonempty.prefixUntil_nil_iff (hw : Nonempty w) : (w.prefixUntil P).Nil ↔ P w.first := by
  induction w with | nil => simp at hw | cons => simp [apply_ite]

lemma Nonempty.prefixUntil_nonempty_iff (hw : Nonempty w) :
    (w.prefixUntil P).Nonempty ↔ ¬ P w.first := by
  simp [← hw.prefixUntil_nil_iff (P := P)]

lemma prefixUntil_isPrefix (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.prefixUntil P).IsPrefix w := by
  induction w with
  | nil => simp
  | cons u e W ih =>
    by_cases hP : P u
    · simp [hP]
    simpa [hP] using ih.cons u e

/-- Take the suffix starting at the first vertex satisfying a predicate `P`,
(or the `Nil` wList on the last vertex if nothing satisfies `P`) -/
def suffixFrom (w : WList α β) (P : α → Prop) [DecidablePred P] : WList α β :=
  match w with
  | nil x => nil x
  | cons x e w => if P x then cons x e w else suffixFrom w P

@[simp] lemma suffixFrom_nil : (nil u (β := β)).suffixFrom P = nil u := rfl

@[simp]
lemma suffixFrom_cons (w) :
    (cons x e w).suffixFrom P = if P x then cons x e w else w.suffixFrom P := rfl

@[simp]
lemma suffixFrom_last (w : WList α β) : (w.suffixFrom P).last = w.last := by
  induction w with simp_all [apply_ite]

lemma suffixFrom_first_prop {w : WList α β} (h : ∃ u ∈ w, P u) : P (w.suffixFrom P).first := by
  induction w with
  | nil => simpa using h
  | cons u e W ih =>
    obtain h | h : P u ∨ ∃ a ∈ W, P a := by simpa using h
    · simp [h]
    simp [ih h, apply_ite]

lemma suffixFrom_isSuffix (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.suffixFrom P).IsSuffix w := by
  induction w with
  | nil u => simp
  | cons u e W ih =>
    simp only [suffixFrom_cons]
    split_ifs
    · simp
    exact ih.trans (by simp)

/-- Take the suffix of `w` starting at the last occurence of `P` in `w`.
If `P` never occurs, this is all of `w`. -/
def suffixFromLast (w : WList α β) (P : α → Prop) [DecidablePred P] : WList α β :=
  (w.reverse.prefixUntil P).reverse

@[simp]
lemma suffixFromLast_isSuffix (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.suffixFromLast P).IsSuffix w := by
  rw [← reverse_isPrefix_reverse_iff, suffixFromLast, reverse_reverse]
  apply prefixUntil_isPrefix

lemma suffixFromLast_prop_first (h : ∃ x ∈ w, P x) : P (w.suffixFromLast P).first := by
  rw [suffixFromLast, reverse_first]
  exact prefixUntil_prop_last (by simpa)

/-- Given an element `u` of a wList `w`, take the wList starting from the first occurence of `u`. -/
def firstAt [DecidableEq α] (w : WList α β) (u : α) : WList α β := w.suffixFrom (· = u)

section drop

/-- Remove the first vertex and edge from a wList -/
def tail : WList α β → WList α β
  | nil x => nil x
  | cons _ _ w => w

@[simp]
lemma tail_nil (x : α) : (nil x (β := β)).tail = nil x := rfl

@[simp]
lemma tail_cons (x e) (w : WList α β) : (cons x e w).tail = w := rfl

@[simp]
lemma tail_last (w : WList α β) : w.tail.last = w.last := by
  induction w with simp

lemma tail_vx (hw : w.Nonempty) : w.tail.vx = w.vx.tail := by
  induction w with simp_all

lemma tail_edge (w : WList α β) : w.tail.edge = w.edge.tail := by
  induction w with simp

lemma mem_tail_iff_of_nodup (hw : Nodup w.vx) (hne : w.Nonempty) :
    x ∈ w.tail ↔ x ∈ w ∧ x ≠ w.first := by
  induction w with aesop

lemma tail_vxSet_of_nodup (hw : Nodup w.vx) (hne : w.Nonempty) :
    w.tail.vxSet = w.vxSet \ {w.first} := by
  simp_rw [vxSet, mem_tail_iff_of_nodup hw hne]
  aesop

@[simp]
lemma tail_isSuffix (w : WList α β) : w.tail.IsSuffix w := by
  induction w with simp

@[simp]
lemma eq_first_or_mem_tail (h : x ∈ w) : x = w.first ∨ x ∈ w.tail := by
  induction w with simp_all

lemma mem_iff_eq_first_or_mem_tail : x ∈ w ↔ x = w.first ∨ x ∈ w.tail := by
  refine ⟨eq_first_or_mem_tail, ?_⟩
  rintro (rfl | hx)
  · simp
  exact w.tail_isSuffix.mem hx

lemma tail_concat (hw : w.Nonempty) (e : β) (x : α) : (w.concat e x).tail = w.tail.concat e x := by
  induction w with simp_all

/-- Remove the last edge and vertex from a wList. This is the reverse of the reversed tail. -/
def dropLast : WList α β → WList α β
| nil x => nil x
| cons x _ (nil _) => nil x
| cons x e (cons y e' w) => cons x e ((cons y e' w).dropLast)

@[simp]
lemma dropLast_nil : (nil x : WList α β).dropLast = nil x := rfl

@[simp]
lemma dropLast_cons_nil : (cons x e (nil y) : WList α β).dropLast = nil x := rfl

@[simp]
lemma dropLast_cons_cons :
  (cons x e (cons y e' w) : WList α β).dropLast = cons x e ((cons y e' w).dropLast) := rfl

@[simp]
lemma reverse_tail (w : WList α β) : w.reverse.tail = w.dropLast.reverse := by
  induction w with
  | nil => simp
  | cons u e w ih => cases w with
    | nil => simp
    | cons x f w =>
      rw [reverse_cons, tail_concat, ih, ← reverse_cons, dropLast_cons_cons]
      simp

@[simp] lemma reverse_dropLast (w : WList α β) : w.reverse.dropLast = w.tail.reverse := by
  simpa using (congr_arg reverse w.reverse.reverse_tail).symm

lemma reverse_dropLast_reverse (w : WList α β) : w.reverse.dropLast.reverse = w.tail := by
  simp

lemma reverse_tail_reverse (w : WList α β) : w.reverse.tail.reverse = w.dropLast := by
  simp

@[simp]
lemma dropLast_concat (w : WList α β) (e x) : (w.concat e x).dropLast = w := by
  rw [← reverse_tail_reverse, concat_reverse, tail_cons, reverse_reverse]

@[simp]
lemma dropLast_first (w : WList α β) : (w.dropLast).first = w.first := by
  rw [← reverse_last, ← reverse_tail, tail_last, reverse_last]

@[simp]
lemma dropLast_vx (h : w.Nonempty) : (w.dropLast).vx = w.vx.dropLast := by
  rw [← reverse_tail_reverse, reverse_vx, tail_vx (by simpa)]
  simp

@[simp]
lemma dropLast_edge (w : WList α β) : (w.dropLast).edge = w.edge.dropLast := by
  rw [← reverse_tail_reverse, reverse_edge, tail_edge, reverse_edge, ← dropLast_reverse,
    List.reverse_reverse]

lemma mem_iff_eq_mem_dropLast_or_eq_last : u ∈ w ↔ u ∈ w.dropLast ∨ u = w.last := by
  rw [← mem_reverse, mem_iff_eq_first_or_mem_tail, or_comm, reverse_tail, mem_reverse,
    reverse_first]

@[simp]
lemma dropLast_vxSet_of_nodup (hw : w.vx.Nodup) (hne : w.Nonempty) :
    (w.dropLast).vxSet = w.vxSet \ {w.last} := by
  rw [← reverse_vxSet, ← reverse_tail, tail_vxSet_of_nodup (by simpa) (by simpa)]
  simp

lemma dropLast_isPrefix (w : WList α β) : w.dropLast.IsPrefix w := by
  rw [← reverse_isSuffix_reverse_iff, ← reverse_tail]
  apply tail_isSuffix

end drop

section dedup

variable [DecidableEq α]

/-- Remove duplicate vertices from a wList. -/
def dedup : WList α β → WList α β
  | nil x => nil x
  | cons x e w =>
    have := (w.suffixFrom_isSuffix (· = x)).length_le
    if x ∈ w then dedup (w.suffixFrom (· = x)) else cons x e (dedup w)
  termination_by w => w.length

@[simp]
lemma dedup_nil (x : α) : (nil x (β := β)).dedup = nil x := by
  simp [dedup]

lemma dedup_cons_eq_ite (x : α) (e : β) (w : WList α β) :
    (cons x e w).dedup = if x ∈ w then dedup (w.suffixFrom (· = x)) else cons x e w.dedup := by
  simp [dedup]

lemma dedup_cons_of_mem (hxw : x ∈ w) (e) : (cons x e w).dedup = dedup (w.suffixFrom (· = x)) := by
  simp [dedup, hxw]

lemma dedup_cons_of_not_mem (hxw : x ∉ w) (e) :
    (cons x e w).dedup = cons x e (dedup w) := by
  simp [dedup, hxw]

@[simp]
lemma dedup_first (w : WList α β) : w.dedup.first = w.first := by
  cases w with
  | nil => simp
  | cons u e w =>
    have hle := (w.suffixFrom_isSuffix (· = u)).length_le
    simp only [dedup, apply_ite, cons_first, ite_eq_right_iff]
    rw [dedup_first]
    exact fun huw ↦ suffixFrom_first_prop (P := (· = u)) ⟨_, huw, rfl⟩
  termination_by w.length

@[simp]
lemma dedup_last (w : WList α β) : w.dedup.last = w.last := by
  cases w with
  | nil => simp
  | cons u e w =>
    have hle := (w.suffixFrom_isSuffix (· = u)).length_le
    simp only [cons_last]
    by_cases huw : u ∈ w
    · rw [dedup_cons_of_mem huw, dedup_last, suffixFrom_last]
    rw [dedup_cons_of_not_mem huw, cons_last, dedup_last]
  termination_by w.length

lemma dedup_isSublist (w : WList α β) : w.dedup.IsSublist w := by
  cases w with
  | nil => simp
  | cons u e w =>
    have hle := (w.suffixFrom_isSuffix (· = u)).length_le
    by_cases huw : u ∈ w
    · rw [dedup_cons_of_mem huw]
      refine (w.suffixFrom _).dedup_isSublist.trans ?_
      exact (w.suffixFrom_isSuffix _).isSublist.trans <| by simp
    rw [dedup_cons_of_not_mem huw]
    exact (dedup_isSublist w).cons₂ _ _ _ _ (by simp)
  termination_by w.length

lemma dedup_vx_nodup (w : WList α β) : w.dedup.vx.Nodup := by
  cases w with
  | nil => simp
  | cons u e w =>
    have hle := (w.suffixFrom_isSuffix (· = u)).length_le.eq_or_lt
    by_cases huw : u ∈ w
    · rw [dedup_cons_of_mem huw]
      apply dedup_vx_nodup
    simp only [dedup_cons_of_not_mem huw, cons_vx, nodup_cons, mem_vx]
    exact ⟨mt w.dedup_isSublist.vx_sublist.mem huw, w.dedup_vx_nodup⟩
  termination_by w.length

lemma dedup_eq_self (hw : w.vx.Nodup) : w.dedup = w := by
  induction w with
  | nil => simp
  | cons u e w ih =>
    simp only [cons_vx, nodup_cons, mem_vx] at hw
    rw [dedup_cons_of_not_mem hw.1, ih hw.2]

lemma dedup_eq_self_iff : w.dedup = w ↔ w.vx.Nodup :=
  ⟨fun h ↦ by rw [← h]; exact dedup_vx_nodup w, dedup_eq_self⟩

end dedup

-- end WList
-- open WList

-- lemma IsWListFrom.dedup [DecidableEq α] (h : G.IsWListFrom S T w) :
--  G.IsPathFrom S T w.dedup := by
--   obtain ⟨hVd, hfirst, hlast⟩ := h
--   refine hVd.dedup_isPath.isPathFrom ?_ ?_
--   · rwa [dedup_first]
--   · rwa [dedup_last]

-- namespace WList

-- /- Properties of `prefixUntil` -/
-- variable {P : α → Prop} [DecidablePred P]

-- @[simp]
-- lemma prefixUntil_nil : (nil x : WList α β).prefixUntil P = nil x := rfl


-- @[simp]
-- lemma endIf_length {w : WList α β} (h : ∃ u ∈ w, P u) : (w.endIf h).length ≤ w.length := by
--   match w with
--   | .nil x => simp only [endIf, nil_length, le_refl]
--   | .cons x e w =>
--   rw [endIf]
--   split_ifs <;> simp [endIf_length]

-- lemma endIf_sizeOf_le {w : WList α β} (h : ∃ u ∈ w, P u) : sizeOf (w.endIf h) ≤ sizeOf w := by
--   match w with
--   | .nil x => simp only [endIf, nil.sizeOf_spec, sizeOf_default, add_zero, le_refl]
--   | .cons x e w =>
--   rw [endIf]
--   split_ifs <;> simp [endIf_sizeOf_le]

-- lemma ValidIn.endIf {w : WList α β} (hVd : w.ValidIn G) (h : ∃ u ∈ w, P u) :
--     (w.endIf h).ValidIn G := by
--   match w with
--   | .nil x => simpa only [endIf, nil_validIn]
--   | .cons x e w =>
--     simp only [WList.endIf]
--     split_ifs with hPx
--     · rw [nil_validIn]
--       simp only [cons_validIn] at hVd
--       exact hVd.1.vx_mem_left
--     · rw [cons_validIn] at hVd ⊢
--       refine ⟨?_, hVd.2.endIf _ ⟩
--       convert hVd.1 using 1
--       simp only [mem_cons_iff, exists_eq_or_imp, hPx, false_or] at h
--       exact endIf_first h

-- lemma endIf_vx_sublist {w : WList α β} (h : ∃ u ∈ w, P u) :
--     (w.endIf h).vx ⊆ w.vx := by
--   match w with
--   | .nil x => simp only [endIf, nil_vx, List.Subset.refl]
--   | .cons x e w =>
--     simp only [endIf, cons_vx]
--     split_ifs with h
--     · simp only [nil_vx, cons_subset, mem_cons, true_or, nil_subset, subset_cons_of_subset,
--         and_self]
--     · simp only [cons_vx, cons_subset, mem_cons, true_or, true_and]
--       refine List.Subset.trans ?_ (List.subset_cons_self _ _)
--       apply endIf_vx_sublist

-- lemma endIf_mem_vx {w : WList α β} (h : ∃ u ∈ w, P u) (hv : v ∈ w.endIf h):
--     ¬ P v ∨ v = (w.endIf h).last := by
--   match w with
--   | .nil x => simp_all only [endIf_nil, mem_nil_iff, nil_last, or_true]
--   | .cons x e w =>
--     rw [endIf_cons]
--     split_ifs with hPx
--     · simp_all only [endIf_cons, dite_true, mem_nil_iff, not_true_eq_false, nil_last, or_true]
--     · simp_all only [endIf_cons, dite_false, mem_cons_iff, cons_last]
--       obtain rfl | hvmem := hv
--       · exact Or.inl hPx
--       · simp only [mem_cons_iff, exists_eq_or_imp, hPx, false_or] at h
--         exact endIf_mem_vx h hvmem

-- lemma endIf_exists_inc₂_last {w : WList α β} (h : ∃ u ∈ w, P u) (hVd : w.ValidIn G)
--     (hNonempty : (w.endIf h).Nonempty) :
--     ∃ v ∈ (w.endIf h), ¬ P v ∧ ∃ e, G.Inc₂ e v (w.endIf h).last := by
--   match w with
--   | .nil x => simp_all only [endIf_nil, Nonempty.not_nil]
--   | .cons x e (nil y) =>
--     simp_all only [cons_validIn, nil_first, nil_validIn, endIf_cons, endIf_nil, dite_eq_ite]
--     split_ifs with hPx
--     · simp_all only [cons_vx, nil_vx, mem_cons, not_mem_nil, or_false, exists_eq_or_imp,
--       exists_eq_left, true_or, ite_true, Nonempty.not_nil]
--     · simp_all only [mem_cons_iff, mem_nil_iff, exists_eq_or_imp, exists_eq_left, false_or,
--       ite_false, Nonempty.cons_true, cons_last, nil_last, not_false_eq_true, true_and,
--       not_true_eq_false, false_and, or_false]
--       use e
--       exact hVd.1
--   | .cons x e (cons y e' w) =>
--     unfold endIf
--     split_ifs with hPx
--     · simp_all only [cons_validIn, cons_first, endIf_cons, dite_true, Nonempty.not_nil]
--     · by_cases hPy : P y
--       · simp_all only [cons_validIn, cons_first, endIf_cons, dite_true, dite_eq_ite, ite_false,
--         Nonempty.cons_true, mem_cons_iff, mem_nil_iff, cons_last, nil_last,
--      exists_eq_or_imp, not_false_eq_true, true_and, exists_eq_left, not_true_eq_false, false_and,
--         or_false]
--         use e
--         exact hVd.1
--       · let w' := cons y e' w
--         rw [cons_last]
--         have h' : ∃ u ∈ w', P u := by
--           change ∃ u ∈ cons x e w', P u at h
--           simpa only [mem_cons_iff, exists_eq_or_imp, hPx, false_or] using h
--         have hNonempty' : (w'.endIf h').Nonempty := by
--           simp only [endIf_cons, hPy, ↓reduceDIte, Nonempty.cons_true, w']
--         obtain ⟨a, ha, hh⟩ := endIf_exists_inc₂_last (w := w') h' hVd.2 hNonempty'
--         refine ⟨a, ?_, hh⟩
--         rw [mem_cons_iff]
--         right
--         exact ha

end WList
