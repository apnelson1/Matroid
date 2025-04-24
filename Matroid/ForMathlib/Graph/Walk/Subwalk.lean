import Matroid.ForMathlib.Graph.Walk.Ops
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic

namespace Graph

open Set Function List Nat Walk

variable {α β : Type*} {G H : Graph α β} {u v x y z : α} {e e' f g : β} {S T U: Set α}
  {F F' : Set β} {w w₁ w₂ w₃ : Walk α β}

namespace Walk

set_option linter.style.longLine false

/-- `w₁.IsSubwalk w₂` means that `w₁` is a walk using a subset of the vertices and edges of `w₂`
in the same order that they appear in `w₂`.
Examples include prefixes, suffixes and walks obtained from `w₂` by 'shortcutting'.  -/
inductive IsSubwalk : Walk α β → Walk α β → Prop
  | nil x w (h : x ∈ w) : IsSubwalk (nil x) w
  | cons x e w₁ w₂ (h : IsSubwalk w₁ w₂) : IsSubwalk w₁ (cons x e w₂)
  | cons₂ x e w₁ w₂ (h : IsSubwalk w₁ w₂) (h_eq : w₁.first = w₂.first) :
      IsSubwalk (cons x e w₁) (cons x e w₂)

@[simp]
lemma nil_isSubwalk_iff : (Walk.nil x (β := β)).IsSubwalk w ↔ x ∈ w := by
  refine ⟨fun h ↦ ?_, IsSubwalk.nil _ _⟩
  induction w with
  | nil => cases h with | nil _ => assumption
  | cons u e W ih => cases h with
    | nil => assumption
    | cons x e _ _ h => simp [ih h]

@[simp]
lemma isSubwalk_nil_iff : w.IsSubwalk (nil x) ↔ w = nil x :=
  ⟨fun h ↦ by cases h with simp_all, by rintro rfl; simp⟩

@[simp]
lemma isSubwalk_refl (w : Walk α β) : w.IsSubwalk w := by
  induction w with
  | nil => simp
  | cons u e w ih => exact ih.cons₂ _ _ _ _ rfl

lemma IsSubwalk.vx_sublist (h : w₁.IsSubwalk w₂) : w₁.vx <+ w₂.vx := by
  induction h with
  | nil => simpa
  | cons x e w₁ w₂ h ih => exact ih.trans <| by simp
  | cons₂ x e w₁ w₂ h ih => simpa

lemma IsSubwalk.mem (h : w₁.IsSubwalk w₂) (hx : x ∈ w₁) : x ∈ w₂ :=
  h.vx_sublist.mem hx

lemma IsSubwalk.edge_sublist {w₁ w₂ : Walk α β} (h : w₁.IsSubwalk w₂) : w₁.edge <+ w₂.edge := by
  induction h with
  | nil => simp
  | cons x e w₁ w₂ h ih => exact ih.trans <| by simp
  | cons₂ x e w₁ w₂ h ih => simpa

lemma IsSubwalk.length_le (h : w₁.IsSubwalk w₂) : w₁.length ≤ w₂.length := by
  rw [← length_edge, ← length_edge]
  exact h.edge_sublist.length_le

lemma IsSubwalk.eq_of_length_ge (h : w₁.IsSubwalk w₂) (hge : w₂.length ≤ w₁.length) : w₁ = w₂ :=
  ext_vx_edge (h.vx_sublist.eq_of_length_le (by simpa)) <| h.edge_sublist.eq_of_length_le (by simpa)

lemma IsSubwalk.trans (h : w₁.IsSubwalk w₂) (h' : w₂.IsSubwalk w₃) : w₁.IsSubwalk w₃ := by
  induction h' generalizing w₁ with
  | nil x w h' => simp_all
  | cons x e w₂ w₃ h' ih => exact cons x e w₁ w₃ (ih h)
  | cons₂ x e w₂ w₃ h' h_eq ih => cases h with
    | nil y w₁ h =>
      simp only [nil_isSubwalk_iff, mem_cons_iff] at h ⊢
      exact h.elim .inl <| .inr ∘ h'.vx_sublist.mem
    | cons x e w₁ w₂ h => apply (ih h).cons
    | cons₂ x e w₁ w₂ h h_eq' => exact (ih h).cons₂ _ _ _ _ (h_eq'.trans h_eq)

lemma IsSubwalk.antisymm (h : w₁.IsSubwalk w₂) (h' : w₂.IsSubwalk w₁) : w₁ = w₂ :=
  h.eq_of_length_ge h'.length_le

@[simp]
lemma isSubwalk_cons_self (w : Walk α β) (x : α) (e : β) : w.IsSubwalk (cons x e w) :=
  (isSubwalk_refl (w := w)).cons ..

lemma IsSubwalk.concat (h : w₁.IsSubwalk w₂) (e : β) (x : α) : w₁.IsSubwalk (w₂.concat e x) := by
  induction h with
  | nil x w h => simp [h]
  | cons y f w₁ w₂ h ih => simpa using ih.cons ..
  | cons₂ y f w₁ w₂ h h_eq ih => exact ih.cons₂ _ _ _ _ (by simpa)

lemma IsSubwalk.validIn (h : w₁.IsSubwalk w₂) (hw₂ : w₂.ValidIn G) : w₁.ValidIn G := by
  induction h with
  | nil x w h => simp [hw₂.vx_mem_of_mem h]
  | cons x e w₁ w₂ h ih => exact ih (cons_validIn.1 hw₂).2
  | cons₂ x e w₁ w₂ h h_eq ih =>
    rw [cons_validIn] at hw₂ ⊢
    rw [h_eq]
    exact ⟨hw₂.1, ih hw₂.2⟩

lemma IsSubwalk.concat₂ (h : w₁.IsSubwalk w₂) (hlast : w₁.last = w₂.last) (e : β) (x : α) :
    (w₁.concat e x).IsSubwalk (w₂.concat e x) := by
  induction h with
  | nil y w h => induction w with
    | nil u => simp [show y = u by simpa using h]
    | cons u f w ih => exact IsSubwalk.cons _ _ _ _ (by simpa [show y = w.last from hlast] using ih)
  | cons y f w₁ w₂ h ih => exact (ih (by simpa using hlast)).cons y f
  | cons₂ y f w₁ w₂ h h_eq ih => exact (ih (by simpa using hlast)).cons₂ y f _ _ (by simpa)

@[simp]
lemma isSubwalk_concat_self (w : Walk α β) (e : β) (x : α) : w.IsSubwalk (w.concat e x) :=
  (isSubwalk_refl (w := w)).concat ..

lemma IsSubwalk.reverse (h : w₁.IsSubwalk w₂) : w₁.reverse.IsSubwalk w₂.reverse := by
  induction h with
  | nil => simpa
  | cons x e w₁ w₂ h ih => exact ih.trans <| by simp
  | cons₂ x e w₁ w₂ h h_eq ih => apply ih.concat₂ <| by simpa

lemma IsSubwalk.of_reverse (h : w₁.reverse.IsSubwalk w₂.reverse) : w₁.IsSubwalk w₂ := by
  simpa using h.reverse

/-- ## Prefixes -/

-- /-- `IsPrefix w w'` means that `w` is a prefix of `w'`. -/
inductive IsPrefix : Walk α β → Walk α β → Prop
  | nil (w : Walk α β) : IsPrefix (nil w.first) w
  | cons (x) (e) (w₁ w₂ : Walk α β) (h : IsPrefix w₁ w₂) : IsPrefix (cons x e w₁) (cons x e w₂)

lemma IsPrefix.first_eq (h : IsPrefix w₁ w₂) : w₁.first = w₂.first := by
  induction h with simp

lemma IsPrefix.exists_eq_append (h : IsPrefix w₁ w₂) :
    ∃ w₁', w₁.last = w₁'.first ∧ w₁ ++ w₁' = w₂ := by
  induction h with | nil => simp | cons => simpa

lemma isPrefix_append_right (hw : w₁.last = w₂.first) : w₁.IsPrefix (w₁ ++ w₂) := by
  induction w₁ with
  | nil u => convert IsPrefix.nil w₂
  | cons u e w₁ ih => simpa using (ih hw).cons ..

lemma IsPrefix.isSubwalk (h : w₁.IsPrefix w₂) : w₁.IsSubwalk w₂ := by
  induction h with
  | nil w => simp
  | cons x e w₁ w₂ h ih => exact ih.cons₂ _ _ _ _ h.first_eq

lemma IsPrefix.mem (h : w₁.IsPrefix w₂) (hx : x ∈ w₁) : x ∈ w₂ :=
  h.isSubwalk.mem hx

@[simp]
lemma isPrefix_refl : w.IsPrefix w := by
  induction w with
  | nil u => exact IsPrefix.nil <| nil u
  | cons _ _ _ ih => apply ih.cons

@[simp]
lemma isPrefix_nil_iff : w.IsPrefix (nil x) ↔ w = nil x :=
  ⟨fun h ↦ isSubwalk_nil_iff.1 h.isSubwalk, fun h ↦ h ▸ isPrefix_refl⟩

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
  h.isSubwalk.eq_of_length_ge hge

lemma IsPrefix.length_le (h : w₁.IsPrefix w₂) : w₁.length ≤ w₂.length :=
  h.isSubwalk.length_le

lemma IsPrefix.antisymm (h : w₁.IsPrefix w₂) (h' : w₂.IsPrefix w₁) : w₁ = w₂ :=
  h.eq_of_length_ge h'.length_le

lemma ValidIn.IsPrefix (hVd : w.ValidIn G) (hPf : w₁.IsPrefix w) : w₁.ValidIn G := by
  obtain ⟨w₂, heq, rfl⟩ := hPf.exists_eq_append
  exact hVd.append_left_validIn heq

lemma _root_.Graph.IsPath.IsPrefix (hPf : w₁.IsPrefix w) (hP : G.IsPath w) : G.IsPath w₁ := by
  obtain ⟨w₂, heq, rfl⟩ := hPf.exists_eq_append
  exact append_left_isPath heq hP

lemma IsPrefix.concat (h : w₁.IsPrefix w₂) (e x) : w₁.IsPrefix (w₂.concat e x) := by
  induction h with | nil => simp | cons y f w₁ w₂ h ih => exact ih.cons y f

@[simp]
lemma isPrefix_concat_self (w : Walk α β) (e) (x) : w.IsPrefix (w.concat e x) :=
  isPrefix_refl.concat e x

/- ## Suffixes -/

inductive IsSuffix : Walk α β → Walk α β → Prop
  | nil (w : Walk α β) : IsSuffix (nil w.last) w
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

lemma IsSuffix.isSubwalk (h : w₁.IsSuffix w₂) : w₁.IsSubwalk w₂ :=
  h.reverse_isPrefix_reverse.isSubwalk.of_reverse

lemma IsSuffix.mem (h : w₁.IsSuffix w₂) (hx : x ∈ w₁) : x ∈ w₂ :=
  h.isSubwalk.mem hx

@[simp]
lemma isSuffix_nil_iff : w.IsSuffix (nil x) ↔ w = nil x :=
  ⟨fun h ↦ isSubwalk_nil_iff.1 h.isSubwalk, fun h ↦ h ▸ isSuffix_refl⟩

@[simp]
lemma nil_isSuffix_iff : (nil x).IsSuffix w ↔ w.last = x := by
  rw [← reverse_isPrefix_reverse_iff, reverse_nil, nil_isPrefix_iff, reverse_first]

lemma IsSuffix.last_eq (h : w₁.IsSuffix w₂) : w₁.last = w₂.last :=
  by simpa using h.reverse_isPrefix_reverse.first_eq

lemma IsSuffix.length_le (h : w₁.IsSuffix w₂) : w₁.length ≤ w₂.length :=
  h.isSubwalk.length_le

lemma IsSuffix.trans (h : w₁.IsSuffix w₂) (h' : w₂.IsSuffix w₃) : w₁.IsSuffix w₃ := by
  simpa using (h.reverse_isPrefix_reverse.trans h'.reverse_isPrefix_reverse)

lemma IsSuffix.eq_of_length_ge (h : w₁.IsSuffix w₂) (hge : w₂.length ≤ w₁.length) : w₁ = w₂ :=
  h.isSubwalk.eq_of_length_ge hge

lemma IsSuffix.antisymm (h : w₁.IsSuffix w₂) (h' : w₂.IsSuffix w₁) : w₁ = w₂ :=
  h.eq_of_length_ge h'.length_le

lemma ValidIn.isSuffix (hVd : w.ValidIn G) (hPf : w₁.IsSuffix w) : w₁.ValidIn G := by
  simpa using hVd.reverse.IsPrefix hPf.reverse_isPrefix_reverse

lemma _root_.Graph.IsPath.IsSuffix (hPf : w₁.IsSuffix w) (hP : G.IsPath w) : G.IsPath w₁ := by
  simpa using hP.reverse.IsPrefix <| reverse_isPrefix_reverse_iff.2 hPf

lemma IsSuffix.cons (h : w₁.IsSuffix w₂) (x e) : w₁.IsSuffix (cons x e w₂) := by
  simpa using (h.reverse_isPrefix_reverse.concat e x).reverse_isSuffix_reverse

@[simp]
lemma isSuffix_cons_self (w : Walk α β) (e) (x) : w.IsSuffix (cons x e w) :=
  isSuffix_refl.cons ..

/-! # Cutting walks Off -/

variable {P : α → Prop} [DecidablePred P]

/-- Take the prefix ending at the first vertex satisfying a predicate `P`
(or the entire walk if nothing satisfies `P`) -/
def prefixUntil (w : Walk α β) (P : α → Prop) [DecidablePred P] : Walk α β :=
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
lemma prefixUntil_first (w : Walk α β) : (w.prefixUntil P).first = w.first := by
  cases w with simp [apply_ite]

lemma prefixUntil_prop_last {w : Walk α β} (h : ∃ u ∈ w, P u) : P (w.prefixUntil P).last := by
  induction w with
  | nil u => simpa using h
  | cons u e W ih =>
    obtain h | h : P u ∨ ∃ a ∈ W, P a := by simpa using h
    · simp [h]
    simp [ih h, apply_ite]

lemma prefixUntil_not_prop (hx : x ∈ w.prefixUntil P) (hne : x ≠ (w.prefixUntil P).last) :
    ¬ P x := by
  induction w with
  | nil u => simp_all
  | cons u e W ih =>
    by_cases hu : P u
    · simp only [prefixUntil_cons, hu, ↓reduceIte, nil_last, ne_eq, mem_nil_iff] at hne hx
      contradiction
    simp only [prefixUntil_cons, hu, ↓reduceIte, cons_last, ne_eq, mem_cons_iff] at hne hx ih
    obtain rfl | hx := hx
    · assumption
    exact ih hx hne

lemma Nonempty.prefixUntil_nil_iff (hw : Nonempty w) : (w.prefixUntil P).Nil ↔ P w.first := by
  induction w with | nil => simp at hw | cons => simp [apply_ite]

lemma Nonempty.prefixUntil_nonempty_iff (hw : Nonempty w) :
    (w.prefixUntil P).Nonempty ↔ ¬ P w.first := by
  simp [← hw.prefixUntil_nil_iff (P := P)]

lemma prefixUntil_isPrefix (w : Walk α β) (P : α → Prop) [DecidablePred P] :
    (w.prefixUntil P).IsPrefix w := by
  induction w with
  | nil => simp
  | cons u e W ih =>
    by_cases hP : P u
    · simp [hP]
    simpa [hP] using ih.cons u e

/-- Take the suffix starting at the first vertex satisfying a predicate `P`,
(or the `Nil` walk on the last vertex if nothing satisfies `P`) -/
def suffixFrom (w : Walk α β) (P : α → Prop) [DecidablePred P] : Walk α β :=
  match w with
  | nil x => nil x
  | cons x e w => if P x then cons x e w else suffixFrom w P

@[simp] lemma suffixFrom_nil : (nil u (β := β)).suffixFrom P = nil u := rfl

@[simp]
lemma suffixFrom_cons (w) :
    (cons x e w).suffixFrom P = if P x then cons x e w else w.suffixFrom P := rfl

@[simp]
lemma suffixFrom_last (w : Walk α β) : (w.suffixFrom P).last = w.last := by
  induction w with simp_all [apply_ite]

lemma suffixFrom_first_prop {w : Walk α β} (h : ∃ u ∈ w, P u) : P (w.suffixFrom P).first := by
  induction w with
  | nil => simpa using h
  | cons u e W ih =>
    obtain h | h : P u ∨ ∃ a ∈ W, P a := by simpa using h
    · simp [h]
    simp [ih h, apply_ite]

lemma suffixFrom_isSuffix (w : Walk α β) (P : α → Prop) [DecidablePred P] :
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
def suffixFromLast (w : Walk α β) (P : α → Prop) [DecidablePred P] : Walk α β :=
  (w.reverse.prefixUntil P).reverse

@[simp]
lemma suffixFromLast_isSuffix (w : Walk α β) (P : α → Prop) [DecidablePred P] :
    (w.suffixFromLast P).IsSuffix w := by
  rw [← reverse_isPrefix_reverse_iff, suffixFromLast, reverse_reverse]
  apply prefixUntil_isPrefix

lemma suffixFromLast_prop_first (h : ∃ x ∈ w, P x) : P (w.suffixFromLast P).first := by
  rw [suffixFromLast, reverse_first]
  exact prefixUntil_prop_last (by simpa)

/-- Given an element `u` of a walk `w`, take the walk starting from the first occurence of `u`. -/
def firstAt [DecidableEq α] (w : Walk α β) (u : α) : Walk α β := w.suffixFrom (· = u)

section dedup

variable [DecidableEq α]

/-- Remove duplicate vertices from a walk. -/
def dedup : Walk α β → Walk α β
  | nil x => nil x
  | cons x e w =>
    have := (w.suffixFrom_isSuffix (· = x)).length_le
    if x ∈ w then dedup (w.suffixFrom (· = x)) else cons x e (dedup w)
  termination_by w => w.length

@[simp]
lemma dedup_nil (x : α) : (nil x (β := β)).dedup = nil x := by
  simp [dedup]

lemma dedup_cons_eq_ite (x : α) (e : β) (w : Walk α β) :
    (cons x e w).dedup = if x ∈ w then dedup (w.suffixFrom (· = x)) else cons x e w.dedup := by
  simp [dedup]

lemma dedup_cons_of_mem (hxw : x ∈ w) (e) : (cons x e w).dedup = dedup (w.suffixFrom (· = x)) := by
  simp [dedup, hxw]

lemma dedup_cons_of_not_mem (hxw : x ∉ w) (e) :
    (cons x e w).dedup = cons x e (dedup w) := by
  simp [dedup, hxw]

@[simp]
lemma dedup_first (w : Walk α β) : w.dedup.first = w.first := by
  cases w with
  | nil => simp
  | cons u e w =>
    have hle := (w.suffixFrom_isSuffix (· = u)).length_le
    simp only [dedup, apply_ite, cons_first, ite_eq_right_iff]
    rw [dedup_first]
    exact fun huw ↦ suffixFrom_first_prop (P := (· = u)) ⟨_, huw, rfl⟩
  termination_by w.length

@[simp]
lemma dedup_last (w : Walk α β) : w.dedup.last = w.last := by
  cases w with
  | nil => simp
  | cons u e w =>
    have hle := (w.suffixFrom_isSuffix (· = u)).length_le
    simp only [cons_last]
    by_cases huw : u ∈ w
    · rw [dedup_cons_of_mem huw, dedup_last, suffixFrom_last]
    rw [dedup_cons_of_not_mem huw, cons_last, dedup_last]
  termination_by w.length

lemma dedup_isSubwalk (w : Walk α β) : w.dedup.IsSubwalk w := by
  cases w with
  | nil => simp
  | cons u e w =>
    have hle := (w.suffixFrom_isSuffix (· = u)).length_le
    by_cases huw : u ∈ w
    · rw [dedup_cons_of_mem huw]
      refine (w.suffixFrom _).dedup_isSubwalk.trans ?_
      exact (w.suffixFrom_isSuffix _).isSubwalk.trans <| by simp
    rw [dedup_cons_of_not_mem huw]
    exact (dedup_isSubwalk w).cons₂ _ _ _ _ (by simp)
  termination_by w.length

lemma dedup_vx_nodup (w : Walk α β) : w.dedup.vx.Nodup := by
  cases w with
  | nil => simp
  | cons u e w =>
    have hle := (w.suffixFrom_isSuffix (· = u)).length_le.eq_or_lt
    by_cases huw : u ∈ w
    · rw [dedup_cons_of_mem huw]
      apply dedup_vx_nodup
    simp only [dedup_cons_of_not_mem huw, cons_vx, nodup_cons, mem_vx]
    exact ⟨mt w.dedup_isSubwalk.vx_sublist.mem huw, w.dedup_vx_nodup⟩
  termination_by w.length

lemma dedup_eq_self (hw : w.vx.Nodup) : w.dedup = w := by
  induction w with
  | nil => simp
  | cons u e w ih =>
    simp only [cons_vx, nodup_cons, mem_vx] at hw
    rw [dedup_cons_of_not_mem hw.1, ih hw.2]

lemma ValidIn.dedup (h : w.ValidIn G) : w.dedup.ValidIn G :=
  w.dedup_isSubwalk.validIn h

end dedup


section drop

/-- Remove the first vertex and edge from a walk -/
def tail : Walk α β → Walk α β
  | nil x => nil x
  | cons _ _ w => w

@[simp]
lemma tail_nil (x : α) : (nil x (β := β)).tail = nil x := rfl

@[simp]
lemma tail_cons (x e) (w : Walk α β) : (cons x e w).tail = w := rfl

@[simp]
lemma tail_last (w : Walk α β) : w.tail.last = w.last := by
  induction w with simp

lemma tail_vx (hw : w.Nonempty) : w.tail.vx = w.vx.tail := by
  induction w with simp_all

lemma tail_edge (w : Walk α β) : w.tail.edge = w.edge.tail := by
  induction w with simp

lemma tail_isSuffix (w : Walk α β) : w.tail.IsSuffix w := by
  induction w with simp

@[simp]
lemma eq_first_or_mem_tail (h : x ∈ w) : x = w.first ∨ x ∈ w.tail := by
  induction w with simp_all

lemma mem_iff_eq_first_of_mem_tail : x ∈ w ↔ x = w.first ∨ x ∈ w.tail := by
  refine ⟨eq_first_or_mem_tail, ?_⟩
  rintro (rfl | hx)
  · simp
  exact w.tail_isSuffix.mem hx

lemma tail_concat (hw : w.Nonempty) (e : β) (x : α) : (w.concat e x).tail = w.tail.concat e x := by
  induction w with simp_all

/-- Remove the last edge and vertex from a walk -/
def dropLast : Walk α β → Walk α β
| nil x => nil x
| cons x _ (nil _) => nil x
| cons x e (cons y e' w) => cons x e ((cons y e' w).dropLast)

@[simp]
lemma dropLast_nil : (nil x : Walk α β).dropLast = nil x := rfl

@[simp]
lemma dropLast_cons_nil : (cons x e (nil y) : Walk α β).dropLast = nil x := rfl

@[simp]
lemma reverse_tail (w : Walk α β) : w.reverse.tail = w.dropLast.reverse := by
  induction w with
  | nil => simp
  | cons u e w ih =>
  rw [reverse_cons, tail_concat]
  simp [ih]


/-- Properties of dropLast operation -/


@[simp]
lemma dropLast_cons_cons :
  (cons x e (cons y e' w) : Walk α β).dropLast = cons x e ((cons y e' w).dropLast) := rfl

@[simp]
lemma dropLast_first {w : Walk α β} (h : w.Nonempty) : (w.dropLast).first = w.first := by
  match w with
  | .nil x => simp at h
  | .cons x e (.nil y) => simp
  | .cons x e (cons y e' w) => simp

@[simp]
lemma dropLast_vx {w : Walk α β} (h : w.Nonempty) : (w.dropLast).vx = w.vx.dropLast := by
  match w with
  | .nil x => simp only [Nonempty.not_nil] at h
  | .cons x e (.nil y) => simp only [dropLast, nil_vx, cons_vx, dropLast_cons₂, dropLast_single]
  | .cons x e (cons y e' w) =>
    simp only [dropLast, cons_vx, dropLast_cons₂, List.cons.injEq, true_and]
    rw [← cons_vx (e := e')]
    apply dropLast_vx (by simp)

@[simp]
lemma dropLast_edge {w : Walk α β} (h : w.Nonempty) : (w.dropLast).edge = w.edge.dropLast := by
  match w with
  | .nil x => simp only [Nonempty.not_nil] at h
  | .cons x e (.nil y) => simp only [dropLast, nil_edge, cons_edge, dropLast_single]
  | .cons x e (cons y e' w) =>
    simp only [dropLast, cons_edge, dropLast_cons₂, List.cons.injEq, true_and]
    exact dropLast_edge (by simp)

lemma dropLast_validIn {w : Walk α β} (hVd : w.ValidIn G) : (w.dropLast).ValidIn G := by
  match w with
  | .nil x => simp only [dropLast, hVd]
  | .cons x e (.nil y) =>
    simp only [cons_validIn, nil_first, nil_validIn] at hVd
    exact hVd.1.vx_mem_left
  | .cons x e (cons y e' w) =>
    rw [dropLast, cons_validIn, dropLast_first (by simp)]
    rw [cons_validIn] at hVd
    exact ⟨hVd.1, dropLast_validIn hVd.2⟩

lemma mem_dropLast_or_last_of_mem {w : Walk α β} (hu : u ∈ w) : u ∈ w.dropLast ∨ u = w.last := by
  match w with
  | .nil x => simpa using hu
  | .cons x e (.nil y) =>
    simp only [mem_cons_iff, mem_nil_iff] at hu
    obtain rfl | rfl := hu <;> simp
  | .cons x e (cons y e' w) =>
    simp only [mem_cons_iff] at hu
    obtain rfl | rfl | hu := hu
    · simp
    · simp only [dropLast_cons_cons, mem_cons_iff, cons_last]
      have := mem_dropLast_or_last_of_mem (by simp : u ∈ (cons u e' w))
      rw [cons_last] at this
      tauto
    · simp only [dropLast_cons_cons, mem_cons_iff, cons_last]
      have := mem_dropLast_or_last_of_mem (by simp [hu] : u ∈ (cons y e' w))
      rw [cons_last] at this
      tauto

lemma mem_of_mem_dropLast {w : Walk α β} (h : u ∈ w.dropLast) : u ∈ w := by
  match w with
  | .nil x => simpa using h
  | .cons x e (.nil y) => simp_all only [dropLast_cons_nil, mem_nil_iff, mem_cons_iff, true_or]
  | .cons x e (cons y e' w) =>
    simp only [dropLast_cons_cons, mem_cons_iff] at h ⊢
    obtain rfl | h := h
    · left
      rfl
    · have := mem_of_mem_dropLast (w := cons y e' w) (by simpa only [Nonempty.cons_true,
      dropLast_vx, cons_vx])
      right
      simpa only [mem_cons_iff] using this

lemma mem_dropLast_or_last_of_mem_iff :
    u ∈ w.dropLast ∨ u = w.last ↔ u ∈ w := by
  refine ⟨?_, mem_dropLast_or_last_of_mem⟩
  rintro (h | rfl)
  · exact mem_of_mem_dropLast h
  · exact last_mem

@[simp]
lemma dropLast_vxSet_of_isPath {w : Walk α β} (hP : G.IsPath w) (hn : w.Nonempty) :
    (w.dropLast).vxSet = w.vxSet \ {w.last} := by
  match w with
  | .nil x => simp at hn
  | .cons x e (.nil y) =>
    simp only [dropLast_cons_nil, nil_vxSet, cons_vxSet, union_singleton, cons_last, nil_last,
      mem_singleton_iff, insert_diff_of_mem]
    rw [diff_singleton_eq_self]
    simp only [mem_singleton_iff]
    rintro rfl
    simp at hP
  | .cons x e (cons y e' w) =>
    have := dropLast_vxSet_of_isPath (w := cons y e' w)
    simp only [cons_isPath, Nonempty.cons_true, cons_vxSet, singleton_union, cons_last,
      forall_const, and_imp, cons_first, mem_cons_iff, not_or, dropLast_cons_cons,
      union_insert] at this hP ⊢
    obtain ⟨⟨hP, h₂', hynin⟩, h₂, hne, hxnin⟩ := hP
    rw [this hP h₂' hynin, ← insert_diff_of_not_mem, insert_comm]
    simp only [mem_singleton_iff]
    rintro rfl
    simp only [last_mem, not_true_eq_false] at hxnin

@[simp]
lemma last_not_mem_dropLast_of_isPath {w : Walk α β} (hP : G.IsPath w) (hn : w.Nonempty) :
    w.last ∉ w.dropLast := by
  rintro h
  rw [← mem_vxSet_iff, dropLast_vxSet_of_isPath hP hn] at h
  simp at h

end dropLast


-- end Walk
-- open Walk

-- lemma IsWalkFrom.dedup [DecidableEq α] (h : G.IsWalkFrom S T w) : G.IsPathFrom S T w.dedup := by
--   obtain ⟨hVd, hfirst, hlast⟩ := h
--   refine hVd.dedup_isPath.isPathFrom ?_ ?_
--   · rwa [dedup_first]
--   · rwa [dedup_last]

-- namespace Walk

-- /- Properties of `prefixUntil` -/
-- variable {P : α → Prop} [DecidablePred P]

-- @[simp]
-- lemma prefixUntil_nil : (nil x : Walk α β).prefixUntil P = nil x := rfl


-- @[simp]
-- lemma endIf_length {w : Walk α β} (h : ∃ u ∈ w, P u) : (w.endIf h).length ≤ w.length := by
--   match w with
--   | .nil x => simp only [endIf, nil_length, le_refl]
--   | .cons x e w =>
--   rw [endIf]
--   split_ifs <;> simp [endIf_length]

-- lemma endIf_sizeOf_le {w : Walk α β} (h : ∃ u ∈ w, P u) : sizeOf (w.endIf h) ≤ sizeOf w := by
--   match w with
--   | .nil x => simp only [endIf, nil.sizeOf_spec, sizeOf_default, add_zero, le_refl]
--   | .cons x e w =>
--   rw [endIf]
--   split_ifs <;> simp [endIf_sizeOf_le]

-- lemma ValidIn.endIf {w : Walk α β} (hVd : w.ValidIn G) (h : ∃ u ∈ w, P u) :
--     (w.endIf h).ValidIn G := by
--   match w with
--   | .nil x => simpa only [endIf, nil_validIn]
--   | .cons x e w =>
--     simp only [Walk.endIf]
--     split_ifs with hPx
--     · rw [nil_validIn]
--       simp only [cons_validIn] at hVd
--       exact hVd.1.vx_mem_left
--     · rw [cons_validIn] at hVd ⊢
--       refine ⟨?_, hVd.2.endIf _ ⟩
--       convert hVd.1 using 1
--       simp only [mem_cons_iff, exists_eq_or_imp, hPx, false_or] at h
--       exact endIf_first h

-- lemma endIf_vx_sublist {w : Walk α β} (h : ∃ u ∈ w, P u) :
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

-- lemma endIf_mem_vx {w : Walk α β} (h : ∃ u ∈ w, P u) (hv : v ∈ w.endIf h):
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

-- lemma endIf_exists_inc₂_last {w : Walk α β} (h : ∃ u ∈ w, P u) (hVd : w.ValidIn G)
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
--         exists_eq_or_imp, not_false_eq_true, true_and, exists_eq_left, not_true_eq_false, false_and,
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

end Walk
