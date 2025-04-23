import Matroid.ForMathlib.Graph.Walk.Ops

import Mathlib.Algebra.Order.Monoid.Unbundled.Basic

namespace Graph

open Set Function List Nat Walk

variable {α β : Type*} {G H : Graph α β} {u v x y z : α} {e e' f g : β} {S T U: Set α}
  {F F' : Set β} {w w₁ w₂ w₃ : Walk α β}

namespace Walk

set_option linter.style.longLine false

def IsSubwalk : Walk α β → Walk α β → Prop
  | nil x, w => x ∈ w
  | cons _ _ _, nil _ => False
  | cons x e w, cons y f w' => (x = y ∧ e = f ∧ w.IsSubwalk w') ∨ (cons x e w).IsSubwalk w'

@[simp]
lemma nil_isSubwalk_iff : (nil x).IsSubwalk w ↔ x ∈ w := by
  simp [IsSubwalk]

@[simp]
lemma isSubwalk_nil_iff : w.IsSubwalk (nil x) ↔ w = nil x := by
  induction w with simp_all [IsSubwalk]

lemma IsSubwalk.vx_sublist {w₁ w₂ : Walk α β} (h : w₁.IsSubwalk w₂) : w₁.vx <+ w₂.vx := by
  match w₁ with
  | nil u => simp_all
  | cons u e w₁ =>
  match w₂ with
  | nil u => simp_all
  | cons v f w₂ =>
  obtain ⟨rfl, rfl, h⟩ | h := h
  · simp [h.vx_sublist]
  have hle : u :: w₁.vx <+ w₂.vx := by simpa using h.vx_sublist
  exact hle.trans (by simp)

lemma IsSubwalk.edge_sublist {w₁ w₂ : Walk α β} (h : w₁.IsSubwalk w₂) : w₁.edge <+ w₂.edge := by
  match w₁ with
  | nil u => simp_all
  | cons u e w₁ =>
  match w₂ with
  | nil u => simp_all
  | cons v f w₂ =>
  obtain ⟨rfl, rfl, h⟩ | h := h
  · simp [h.edge_sublist]
  have hle : e :: w₁.edge <+ w₂.edge := by simpa using h.edge_sublist
  exact hle.trans (by simp)

lemma IsSubwalk.length_le (h : w₁.IsSubwalk w₂) : w₁.length ≤ w₂.length := by
  rw [← length_edge, ← length_edge]
  exact h.edge_sublist.length_le

lemma IsSubwalk.eq_of_length_ge (h : w₁.IsSubwalk w₂) (hge : w₂.length ≤ w₁.length) : w₁ = w₂ :=
  ext_vx_edge (h.vx_sublist.eq_of_length_le (by simpa)) <| h.edge_sublist.eq_of_length_le (by simpa)

@[simp]
lemma isSubwalk_refl (w : Walk α β) : w.IsSubwalk w := by
  induction w with simp_all [IsSubwalk]

@[simp]
lemma isSubwalk_cons (w : Walk α β) (x) (e) : w.IsSubwalk (cons x e w) := by
  induction w with simp_all [IsSubwalk]

lemma IsSubwalk.trans {w₁ w₂ w₃ : Walk α β} (h : w₁.IsSubwalk w₂) (h' : w₂.IsSubwalk w₃) :
    w₁.IsSubwalk w₃ := by
  match w₁ with
  | nil u =>
    simp_all only [nil_isSubwalk_iff]
    exact h'.vx_sublist.mem h
  | cons u₁ e₁ w₁ =>
  match w₂ with
  | nil u₂ => simp at h
  | cons u₂ e₂ w₂ =>
  obtain ⟨rfl, rfl, h⟩ | h := h
  · match w₃ with
    | nil u₃ => simp at h'
    | cons u₃ e₃ w₃ =>
    simp_all only [IsSubwalk]
    obtain ⟨rfl, rfl, h'⟩ | h' := h'
    · exact .inl ⟨rfl, rfl, h.trans h'⟩
    exact .inr <| IsSubwalk.trans (by simp [IsSubwalk, h]) h'
  match w₃ with
  | nil u₃ => simp at h'
  | cons u₃ e₃ w₃ =>
  obtain ⟨rfl, rfl, h'⟩ | h' := h'
  · exact (h.trans h').trans (by simp)
  sorry
  -- simp [IsSubwalk]

  -- refine .inr (IsSubwalk.trans ?_ h')
  -- simp [IsSubwalk, h]

  -- refine .inr <| h.trans (IsSubwalk.trans ?_ h')






/-- ## Prefixes -/

-- /-- `IsPrefix w w'` means that `w` is a prefix of `w'`. -/
protected def IsPrefix : Walk α β → Walk α β → Prop :=
  fun w W => ∃ w', w ++ w' = W ∧ w.last = w'.first

lemma isPrefix_append_right (hw : w₁.last = w₂.first) : w₁.IsPrefix (w₁ ++ w₂) :=
  ⟨w₂, rfl, hw⟩

lemma IsPrefix.first_eq (h : w₁.IsPrefix w₂) : w₁.first = w₂.first := by
  obtain ⟨w₁', rfl, h_eq⟩ := h
  cases w₁ with simp_all

lemma IsPrefix.length_le (h : w₁.IsPrefix w₂) : w₁.length ≤ w₂.length := by
  obtain ⟨w₁', rfl, h_eq⟩ := h
  simp

lemma IsPrefix.refl (w : Walk α β) : w.IsPrefix w :=
  ⟨nil w.last, by simp [append_nil rfl]⟩

lemma IsPrefix.trans (h : w₁.IsPrefix w₂) (h' : w₂.IsPrefix w₃) : w₁.IsPrefix w₃ := by
    obtain ⟨w12, rfl, heq1⟩ := h
    obtain ⟨w23, rfl, heq2⟩ := h'
    rw [append_assoc]
    exact isPrefix_append_right <| by cases w12 with simp_all

-- lemma IsPrefix.isSubwalk (h : w₁.IsPrefix w₂) : w₁.IsSubwalk w₂ := by
--   _

lemma IsPrefix.eq_of_length_ge (h : w₁.IsPrefix w₂) (hge : w₂.length ≤ w₁.length) : w₁ = w₂ := by
  obtain ⟨w₁', rfl, h_eq⟩ := h
  simp only [append_length] at hge
  rwa [((length_eq_zero (w := w₁')).1 <| by omega).eq_nil_first, append_nil]

lemma IsPrefix.antisymm (h : w₁.IsPrefix w₂) (h' : w₂.IsPrefix w₁) : w₁ = w₂ :=
  h.eq_of_length_ge h'.length_le

lemma ValidIn.IsPrefix (hVd : w.ValidIn G) (hPf : w₁.IsPrefix w) : w₁.ValidIn G := by
  obtain ⟨w₂, rfl, heq⟩ := hPf
  exact hVd.append_left_validIn heq

lemma _root_.Graph.IsPath.IsPrefix (hPf : w₁.IsPrefix w) (hP : G.IsPath w) : G.IsPath w₁ := by
  obtain ⟨w₂, rfl, heq⟩ := hPf
  exact append_left_isPath heq hP

@[simp]
lemma nil_isPrefix_iff : (nil x).IsPrefix w ↔ x = w.first := by
  simp [Walk.IsPrefix]

@[simp]
lemma isPrefix_nil_iff : w.IsPrefix (nil x) ↔ w = nil x := by
  cases w with simp [Walk.IsPrefix]

@[simp]
lemma cons_isPrefix_cons_iff :
    (cons x e w₁).IsPrefix (cons y f w₂) ↔ x = y ∧ e = f ∧ w₁.IsPrefix w₂ := by
  constructor
  · rintro ⟨w₁', h, h'⟩
    simp only [cons_append, cons.injEq] at h
    rw [and_iff_right h.1, and_iff_right h.2.1, ← h.2.2]
    exact isPrefix_append_right (by simpa using h')
  rintro ⟨rfl, rfl, w₁', ⟨h, rfl⟩, h_eq⟩
  exact ⟨w₁', by simpa⟩

@[simp]
lemma isPrefix_concat (w : Walk α β) (e) (x) : w.IsPrefix (w.concat e x) := by
  induction w with | nil => simp | cons => simpa

lemma IsPrefix.vx_isPrefix {w₁ w₂ : Walk α β} (h : w₁.IsPrefix w₂) : w₁.vx <+: w₂.vx := by
  match w₁ with
  | nil u => cases w₂ with | nil => simp_all | cons => simp_all
  | cons u e w₁ =>
  match w₂ with
  | nil v => simp_all
  | cons v f W =>
  simp only [cons_isPrefix_cons_iff] at h
  simpa [h.1] using h.2.2.vx_isPrefix

lemma IsPrefix.edge_isPrefix {w₁ w₂ : Walk α β} (h : w₁.IsPrefix w₂) : w₁.edge <+: w₂.edge := by
  match w₁ with
  | nil u => cases w₂ with | nil => simp_all | cons => simp_all
  | cons u e w₁ =>
  match w₂ with
  | nil v => simp_all
  | cons v f W =>
  simp only [cons_isPrefix_cons_iff] at h
  simpa [h.2.1] using h.2.2.edge_isPrefix

-- lemma IsPrefix.vxSet_subset (h : w₁.IsPrefix w₂) : w₁.

/- ## Suffixes -/

protected def IsSuffix : Walk α β → Walk α β → Prop :=
    fun w W => ∃ w', w' ++ w = W ∧ w'.last = w.first

lemma isSuffix_append_left (hw : w₁.last = w₂.first) : w₂.IsSuffix (w₁ ++ w₂) :=
  ⟨w₁, rfl, hw⟩

@[simp]
lemma reverse_isPrefix_reverse : w₁.reverse.IsPrefix w₂.reverse ↔ w₁.IsSuffix w₂ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨w₁', h, h_eq⟩ := h
    simp only [reverse_last] at h_eq
    have hrw : w₂ = w₁'.reverse ++ w₁ := by
      rw [← reverse_inj_iff, reverse_append (by simpa using h_eq.symm), reverse_reverse, h]
    rw [hrw]
    apply isSuffix_append_left (by simpa using h_eq.symm)
  obtain ⟨w₁', rfl, h_eq⟩ := h
  exact ⟨w₁'.reverse, by rwa [reverse_append], by simpa using h_eq.symm⟩

@[simp]
lemma reverse_isSuffix_reverse : w₁.reverse.IsSuffix w₂.reverse ↔ w₁.IsPrefix w₂ := by
  nth_rewrite 2 [← w₁.reverse_reverse, ← w₂.reverse_reverse]
  rw [reverse_isPrefix_reverse]


lemma IsSuffix.last_eq (h : w₁.IsSuffix w₂) : w₁.last = w₂.last := by
  obtain ⟨w₁', rfl, h_eq⟩ := h
  cases w₁ with simp_all

lemma IsSuffix.length_le (h : w₁.IsSuffix w₂) : w₁.length ≤ w₂.length := by
  obtain ⟨w₁', rfl, h_eq⟩ := h
  simp

@[simp]
lemma IsSuffix.refl (w : Walk α β) : w.IsSuffix w :=
  ⟨nil w.first, by simp [append_nil rfl]⟩

lemma IsSuffix.trans (h : w₁.IsSuffix w₂) (h' : w₂.IsSuffix w₃) : w₁.IsSuffix w₃ := by
    rw [← reverse_isPrefix_reverse] at *
    exact h.trans h'

lemma IsSuffix.eq_of_length_ge (h : w₁.IsSuffix w₂) (hge : w₂.length ≤ w₁.length) : w₁ = w₂ := by
  rw [← reverse_isPrefix_reverse] at h
  refine reverse_inj (h.eq_of_length_ge <| by simpa)

lemma IsSuffix.antisymm (h : w₁.IsSuffix w₂) (h' : w₂.IsSuffix w₁) : w₁ = w₂ :=
  h.eq_of_length_ge h'.length_le

lemma ValidIn.isSuffix (hVd : w.ValidIn G) (hPf : w₁.IsSuffix w) : w₁.ValidIn G := by
  simpa using hVd.reverse.IsPrefix <| reverse_isPrefix_reverse.2 hPf

lemma _root_.Graph.IsPath.IsSuffix (hPf : w₁.IsSuffix w) (hP : G.IsPath w) : G.IsPath w₁ := by
  simpa using hP.reverse.IsPrefix <| reverse_isPrefix_reverse.2 hPf

@[simp]
lemma nil_isSuffix_iff : (nil x).IsSuffix w ↔ x = w.last := by
  rw [← reverse_isPrefix_reverse, reverse_nil, nil_isPrefix_iff, reverse_first]

@[simp]
lemma isSuffix_nil_iff : w.IsSuffix (nil x) ↔ w = nil x := by
  rw [← reverse_isPrefix_reverse, reverse_nil, isPrefix_nil_iff, reverse_eq_comm, reverse_nil]

@[simp]
lemma isSuffix_cons (w : Walk α β) (e) (x) : w.IsSuffix (cons x e w) := by
  rw [← reverse_isPrefix_reverse, reverse_cons]
  apply isPrefix_concat


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
  induction w with
  | nil => simp at hw
  | cons _ _ _  => simp [apply_ite]

lemma Nonempty.prefixUntil_nonempty_iff (hw : Nonempty w) :
    (w.prefixUntil P).Nonempty ↔ ¬ P w.first := by
  simp [← hw.prefixUntil_nil_iff (P := P)]

lemma prefixUntil_isPrefix (w : Walk α β) (P : α → Prop) [DecidablePred P] :
    (w.prefixUntil P).IsPrefix w := by
  induction w with
  | nil u => simp
  | cons u e W ih =>
  by_cases hP : P u
  · simp [hP]
  simpa [hP]

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
  | nil u => simpa using h
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
  rw [← reverse_isPrefix_reverse, suffixFromLast, reverse_reverse]
  apply prefixUntil_isPrefix

/-- Given an element `u` of a walk `w`, take the walk starting from the first occurence of `u`. -/
def firstAt [DecidableEq α] (w : Walk α β) (u : α) : Walk α β := w.suffixFrom (· = u)

/-- Remove duplicate vertices from a walk -/
def dedup [DecidableEq α] : Walk α β → Walk α β
  | nil x => nil x
  | cons x e w =>
    have := (w.suffixFrom_isSuffix (· = x)).length_le
    if x ∈ w then dedup (w.suffixFrom (· = x)) else cons x e (dedup w)
  termination_by w => w.length


-- lemma firstAt_length_le [DecidableEq α] {w : Walk α β} (h : u ∈ w) :
--     (firstAt w u h).length ≤ w.length := by
--   match w with
--   | nil x => simp [firstAt]
--   | cons x e w =>
--     simp only [firstAt, cons_length]
--     split_ifs with hin
--     · have := firstAt_length_le hin
--       omega
--     · simp

-- def dedup [DecidableEq α] : Walk α β → Walk α β
-- | nil x => nil x
-- | cons x e w =>
--   if h : x ∈ w
--   then by
--     have := firstAt_length_le h
--     exact (firstAt w x h).dedup
--   else cons x e (dedup w)
-- termination_by w => w.length


-- /- Properties of `firstAt` -/
-- @[simp]
-- lemma firstAt_nil (hx : x ∈ (nil u : Walk α β)) : (nil u).firstAt x hx = nil x := by
--   rw [mem_nil_iff] at hx
--   subst u
--   rfl

-- @[simp]
-- lemma firstAt_first (hx : x ∈ w) : (w.firstAt x hx).first = x := by
--   induction w with
--   | nil u =>
--     rw [mem_nil_iff] at hx
--     exact hx.symm
--   | cons u e W ih =>
--     rw [mem_cons_iff] at hx
--     unfold firstAt
--     split_ifs with h
--     · exact ih h
--     · simp only [h, or_false, cons_first] at hx ⊢
--       exact hx.symm

-- @[simp]
-- lemma firstAt_last (hx : x ∈ w) : (w.firstAt x hx).last = w.last := by
--   induction w with
--   | nil u => rfl
--   | cons u e W ih =>
--     rw [mem_cons_iff] at hx
--     unfold firstAt
--     split_ifs with h
--     · simp only [h, ↓reduceDIte, cons_last]
--       exact ih h
--     · simp [h]

-- @[simp]
-- lemma firstAt_length (hx : x ∈ w) : (w.firstAt x hx).length ≤ w.length := by
--   induction w with
--   | nil u => simp only [firstAt_nil, nil_length, le_refl]
--   | cons u e W ih =>
--     rw [mem_cons_iff] at hx
--     unfold firstAt
--     split_ifs with h
--     · simp only [h, ↓reduceDIte, cons_length]
--       have := ih h
--       omega
--     · simp [h]

-- @[simp]
-- lemma firstAt_sizeOf_le (hx : x ∈ w) : sizeOf (w.firstAt x hx) ≤ sizeOf w := by
--   induction w with
--   | nil u => simp only [firstAt_nil, nil.sizeOf_spec, sizeOf_default, add_zero, le_refl]
--   | cons u e W ih =>
--     rw [mem_cons_iff] at hx
--     unfold firstAt
--     split_ifs with h
--     · simp only [h, ↓reduceDIte, cons.sizeOf_spec, sizeOf_default, add_zero]
--       have := ih h
--       omega
--     · simp [h]

-- lemma ValidIn.firstAt (hVd : w.ValidIn G) (hx : x ∈ w) : (w.firstAt x hx).ValidIn G := by
--   induction w with
--   | nil u =>
--     rw [mem_nil_iff] at hx
--     subst u
--     exact hVd
--   | cons u e W ih =>
--     rw [mem_cons_iff] at hx
--     unfold Walk.firstAt
--     split_ifs with h
--     · exact ih hVd.2 h
--     · simpa [h]

-- lemma firstAt_vx_count (hx : x ∈ w) : (w.firstAt x hx).vx.count x = 1 := by
--   induction w with
--   | nil u =>
--     rw [mem_nil_iff] at hx
--     subst u
--     simp
--   | cons u e W ih =>
--     rw [mem_cons_iff] at hx
--     unfold Walk.firstAt
--     split_ifs with h
--     · exact ih h
--     · simp only [h, or_false, cons_vx] at hx ⊢
--       subst u
--       simp [firstAt, count_eq_zero.2 h]


-- lemma firstAt_vx_sublist (hx : x ∈ w) : (w.firstAt x hx).vx ⊆ w.vx := by
--   induction w with
--   | nil u =>
--     rw [mem_nil_iff] at hx
--     subst u
--     simp
--   | cons u e W ih =>
--     rw [mem_cons_iff] at hx
--     unfold Walk.firstAt
--     split_ifs with h
--     · refine (ih h).trans ?_
--       simp
--     · simp [h]

-- lemma firstAt_edge_sublist (hx : x ∈ w) : (w.firstAt x hx).edge ⊆ w.edge := by
--   induction w with
--   | nil u =>
--     rw [mem_nil_iff] at hx
--     subst u
--     simp
--   | cons u e W ih =>
--     rw [mem_cons_iff] at hx
--     unfold Walk.firstAt
--     split_ifs with h
--     · refine (ih h).trans ?_
--       simp
--     · simp [h]

-- @[simp]
-- lemma dedup_first (w : Walk α β) : w.dedup.first = w.first := by
--   match w with
--   | .nil u =>
--     unfold dedup
--     rfl
--   | .cons u e W =>
--     unfold dedup
--     split_ifs with h
--     · rw [cons_first, dedup_first (W.firstAt u h), firstAt_first]
--     · rfl

-- @[simp]
-- lemma dedup_last (w : Walk α β) : w.dedup.last = w.last := by
--   match w with
--   | .nil u =>
--     unfold dedup
--     rfl
--   | .cons u e W =>
--     unfold dedup
--     split_ifs with h
--     · rw [cons_last, dedup_last (W.firstAt u h), firstAt_last]
--     · simp only [cons_last]
--       exact dedup_last W

-- lemma dedup_length (w : Walk α β) : w.dedup.length ≤ w.length := by
--   match w with
--   | .nil u =>
--     simp [dedup]
--   | .cons u e W =>
--     unfold dedup
--     split_ifs with h
--     · simp only [cons_length]
--       refine (dedup_length (W.firstAt u h)).trans ?_
--       refine (firstAt_length_le h).trans ?_
--       exact Nat.le_add_right W.length 1
--     simp [dedup_length W]

-- lemma dedup_sizeOf_le (w : Walk α β) : sizeOf w.dedup ≤ sizeOf w := by
--   match w with
--   | .nil u =>
--     simp only [dedup, nil.sizeOf_spec, sizeOf_default, add_zero, le_refl]
--   | .cons u e W =>
--     unfold dedup
--     split_ifs with h
--     · simp only [cons.sizeOf_spec, sizeOf_default, add_zero]
--       refine (dedup_sizeOf_le (W.firstAt u h)).trans ?_
--       refine (firstAt_sizeOf_le h).trans ?_
--       exact Nat.le_add_left (sizeOf W) 1
--     simp [dedup_sizeOf_le W]

-- lemma ValidIn.dedup {w : Walk α β} (hVd : w.ValidIn G) : w.dedup.ValidIn G := by
--   match w with
--   | .nil u =>
--     unfold Walk.dedup
--     exact hVd
--   | .cons u e W =>
--     unfold Walk.dedup
--     split_ifs with h
--     · simp only [h, ↓reduceDIte]
--       exact (hVd.2.firstAt h).dedup
--     · simp only [hVd.2.dedup, cons_validIn, and_true]
--       convert hVd.1 using 1
--       exact dedup_first W

-- lemma dedup_vx_sublist {w : Walk α β} {x : α} (hx : x ∈ w.dedup) : x ∈ w := by
--   match w with
--   | .nil u =>
--     unfold dedup at hx
--     exact hx
--   | .cons u e W =>
--     unfold dedup at hx
--     split_ifs at hx with h
--     · simp only at hx
--       exact mem_of_mem_tail <| firstAt_vx_sublist h <| dedup_vx_sublist hx
--     · simp only [cons_vx, mem_cons, mem_notation, mem_cons_iff] at hx ⊢
--       exact hx.imp (·) dedup_vx_sublist

-- lemma dedup_edge_sublist (w : Walk α β) : w.dedup.edge ⊆ w.edge := by
--   match w with
--   | .nil u =>
--     unfold dedup
--     simp only [nil_edge, List.Subset.refl]
--   | .cons u e W =>
--     unfold dedup
--     split_ifs with h
--     · rw [cons_edge]
--       refine (dedup_edge_sublist (W.firstAt u h)).trans ?_
--       refine (firstAt_edge_sublist h).trans ?_
--       simp only [List.Subset.refl, subset_cons_of_subset]
--     · simp only [cons_edge, cons_subset, mem_cons, true_or, true_and]
--       refine (dedup_edge_sublist W).trans ?_
--       simp only [List.Subset.refl, subset_cons_of_subset]

-- lemma dedup_vx_nodup (w : Walk α β) : w.dedup.vx.Nodup := by
--   match w with
--   | .nil u =>
--     unfold dedup
--     simp only [nil_vx, nodup_cons, not_mem_nil, not_false_eq_true, nodup_nil, and_self]
--   | .cons u e W =>
--     unfold dedup
--     split_ifs with h
--     · simp only [h, ↓reduceDIte]
--       exact dedup_vx_nodup (W.firstAt u h)
--     · simp only [cons_vx, nodup_cons, dedup_vx_nodup W, and_true]
--       contrapose! h
--       exact dedup_vx_sublist h

-- lemma dedup_edge_nodup {w : Walk α β} (hVd : w.ValidIn G) : w.dedup.edge.Nodup := by
--   match w with
--   | .nil u =>
--     unfold dedup
--     simp only [nil_edge, nodup_nil]
--   | .cons u e W =>
--   unfold dedup
--   split_ifs with h
--   · simp only [h, ↓reduceDIte]
--     exact dedup_edge_nodup (hVd.2.firstAt h)
--   simp only [cons_edge, nodup_cons, dedup_edge_nodup hVd.2, and_true]
--   obtain ⟨hne, hVd⟩ := hVd
--   contrapose! h
--   exact dedup_vx_sublist <| hVd.dedup.mem_of_mem_edge_of_inc h hne.inc_left

-- lemma ValidIn.dedup_isPath (hVd : w.ValidIn G) : G.IsPath w.dedup where
--   validIn := ValidIn.dedup hVd
--   nodup := dedup_vx_nodup w

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
