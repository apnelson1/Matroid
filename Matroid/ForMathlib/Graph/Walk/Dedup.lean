import Matroid.ForMathlib.Graph.Walk.Defs

import Mathlib.Algebra.Order.Monoid.Unbundled.Basic

namespace Graph

open Set Function List Nat Walk

variable {α β : Type*} {G H : Graph α β} {u v x y z : α} {e e' f g : β} {S T U: Set α}
  {F F' : Set β} {w w₁ w₂ : Walk α β}

namespace Walk

variable [DecidableEq α]

/-- Given an element `u` of a walk `w`, take the walk starting from the first occurence of `u`. -/
def firstAt (w : Walk α β) (u : α) (h : u ∈ w) : Walk α β :=
  match w with
  | nil x => nil x
  | cons x e w =>
    if hin : u ∈ w
    then firstAt w u hin
    else cons x e w

lemma firstAt_length_le {w : Walk α β} (h : u ∈ w) : (firstAt w u h).length ≤ w.length := by
  match w with
  | nil x => simp [firstAt]
  | cons x e w =>
    simp only [firstAt, cons_length]
    split_ifs with hin
    · have := firstAt_length_le hin
      omega
    · simp

def dedup : Walk α β → Walk α β
| nil x => nil x
| cons x e w =>
  if h : x ∈ w
  then by
    have := firstAt_length_le h
    exact (firstAt w x h).dedup
  else cons x e (dedup w)
termination_by w => w.length

def endIf {P : α → Prop} [DecidablePred P] (w : Walk α β) (h : ∃ u ∈ w, P u) : Walk α β :=
  match w with
  | nil x => nil x
  | cons x e w =>
    if hP : P x
    then nil x
    else cons x e (endIf w (by simpa [← mem_notation, hP] using h))


/- Properties of `firstAt` -/
@[simp]
lemma firstAt_nil (hx : x ∈ (nil u : Walk α β)) : (nil u).firstAt x hx = nil x := by
  rw [mem_nil_iff] at hx
  subst u
  rfl

@[simp]
lemma firstAt_first (hx : x ∈ w) : (w.firstAt x hx).first = x := by
  induction w with
  | nil u =>
    rw [mem_nil_iff] at hx
    exact hx.symm
  | cons u e W ih =>
    rw [mem_cons_iff] at hx
    unfold firstAt
    split_ifs with h
    · exact ih h
    · simp only [h, or_false, cons_first] at hx ⊢
      exact hx.symm

@[simp]
lemma firstAt_last (hx : x ∈ w) : (w.firstAt x hx).last = w.last := by
  induction w with
  | nil u => rfl
  | cons u e W ih =>
    rw [mem_cons_iff] at hx
    unfold firstAt
    split_ifs with h
    · simp only [h, ↓reduceDIte, cons_last]
      exact ih h
    · simp [h]

@[simp]
lemma firstAt_length (hx : x ∈ w) : (w.firstAt x hx).length ≤ w.length := by
  induction w with
  | nil u => simp only [firstAt_nil, nil_length, le_refl]
  | cons u e W ih =>
    rw [mem_cons_iff] at hx
    unfold firstAt
    split_ifs with h
    · simp only [h, ↓reduceDIte, cons_length]
      have := ih h
      omega
    · simp [h]

@[simp]
lemma firstAt_sizeOf_le (hx : x ∈ w) : sizeOf (w.firstAt x hx) ≤ sizeOf w := by
  induction w with
  | nil u => simp only [firstAt_nil, nil.sizeOf_spec, sizeOf_default, add_zero, le_refl]
  | cons u e W ih =>
    rw [mem_cons_iff] at hx
    unfold firstAt
    split_ifs with h
    · simp only [h, ↓reduceDIte, cons.sizeOf_spec, sizeOf_default, add_zero]
      have := ih h
      omega
    · simp [h]

lemma ValidIn.firstAt (hVd : w.ValidIn G) (hx : x ∈ w) : (w.firstAt x hx).ValidIn G := by
  induction w with
  | nil u =>
    rw [mem_nil_iff] at hx
    subst u
    exact hVd
  | cons u e W ih =>
    rw [mem_cons_iff] at hx
    unfold Walk.firstAt
    split_ifs with h
    · exact ih hVd.2 h
    · simpa [h]

lemma firstAt_vx_count (hx : x ∈ w) : (w.firstAt x hx).vx.count x = 1 := by
  induction w with
  | nil u =>
    rw [mem_nil_iff] at hx
    subst u
    simp
  | cons u e W ih =>
    rw [mem_cons_iff] at hx
    unfold Walk.firstAt
    split_ifs with h
    · exact ih h
    · simp only [h, or_false, cons_vx] at hx ⊢
      subst u
      simp [firstAt, count_eq_zero.2 h]


lemma firstAt_vx_sublist (hx : x ∈ w) : (w.firstAt x hx).vx ⊆ w.vx := by
  induction w with
  | nil u =>
    rw [mem_nil_iff] at hx
    subst u
    simp
  | cons u e W ih =>
    rw [mem_cons_iff] at hx
    unfold Walk.firstAt
    split_ifs with h
    · refine (ih h).trans ?_
      simp
    · simp [h]

lemma firstAt_edge_sublist (hx : x ∈ w) : (w.firstAt x hx).edge ⊆ w.edge := by
  induction w with
  | nil u =>
    rw [mem_nil_iff] at hx
    subst u
    simp
  | cons u e W ih =>
    rw [mem_cons_iff] at hx
    unfold Walk.firstAt
    split_ifs with h
    · refine (ih h).trans ?_
      simp
    · simp [h]

@[simp]
lemma dedup_first (w : Walk α β) : w.dedup.first = w.first := by
  match w with
  | .nil u =>
    unfold dedup
    rfl
  | .cons u e W =>
    unfold dedup
    split_ifs with h
    · rw [cons_first, dedup_first (W.firstAt u h), firstAt_first]
    · rfl

@[simp]
lemma dedup_last (w : Walk α β) : w.dedup.last = w.last := by
  match w with
  | .nil u =>
    unfold dedup
    rfl
  | .cons u e W =>
    unfold dedup
    split_ifs with h
    · rw [cons_last, dedup_last (W.firstAt u h), firstAt_last]
    · simp only [cons_last]
      exact dedup_last W

lemma dedup_length (w : Walk α β) : w.dedup.length ≤ w.length := by
  match w with
  | .nil u =>
    simp [dedup]
  | .cons u e W =>
    unfold dedup
    split_ifs with h
    · simp only [cons_length]
      refine (dedup_length (W.firstAt u h)).trans ?_
      refine (firstAt_length_le h).trans ?_
      exact Nat.le_add_right W.length 1
    simp [dedup_length W]

lemma dedup_sizeOf_le (w : Walk α β) : sizeOf w.dedup ≤ sizeOf w := by
  match w with
  | .nil u =>
    simp only [dedup, nil.sizeOf_spec, sizeOf_default, add_zero, le_refl]
  | .cons u e W =>
    unfold dedup
    split_ifs with h
    · simp only [cons.sizeOf_spec, sizeOf_default, add_zero]
      refine (dedup_sizeOf_le (W.firstAt u h)).trans ?_
      refine (firstAt_sizeOf_le h).trans ?_
      exact Nat.le_add_left (sizeOf W) 1
    simp [dedup_sizeOf_le W]

lemma ValidIn.dedup {w : Walk α β} (hVd : w.ValidIn G) : w.dedup.ValidIn G := by
  match w with
  | .nil u =>
    unfold Walk.dedup
    exact hVd
  | .cons u e W =>
    unfold Walk.dedup
    split_ifs with h
    · simp only [h, ↓reduceDIte]
      exact (hVd.2.firstAt h).dedup
    · simp only [hVd.2.dedup, cons_validIn, and_true]
      convert hVd.1 using 1
      exact dedup_first W

lemma dedup_vx_sublist {w : Walk α β} {x : α} (hx : x ∈ w.dedup) : x ∈ w := by
  match w with
  | .nil u =>
    unfold dedup at hx
    exact hx
  | .cons u e W =>
    unfold dedup at hx
    split_ifs at hx with h
    · simp only at hx
      exact mem_of_mem_tail <| firstAt_vx_sublist h <| dedup_vx_sublist hx
    · simp only [cons_vx, mem_cons, mem_notation, mem_cons_iff] at hx ⊢
      exact hx.imp (·) dedup_vx_sublist

lemma dedup_edge_sublist (w : Walk α β) : w.dedup.edge ⊆ w.edge := by
  match w with
  | .nil u =>
    unfold dedup
    simp only [nil_edge, List.Subset.refl]
  | .cons u e W =>
    unfold dedup
    split_ifs with h
    · rw [cons_edge]
      refine (dedup_edge_sublist (W.firstAt u h)).trans ?_
      refine (firstAt_edge_sublist h).trans ?_
      simp only [List.Subset.refl, subset_cons_of_subset]
    · simp only [cons_edge, cons_subset, mem_cons, true_or, true_and]
      refine (dedup_edge_sublist W).trans ?_
      simp only [List.Subset.refl, subset_cons_of_subset]

lemma dedup_vx_nodup (w : Walk α β) : w.dedup.vx.Nodup := by
  match w with
  | .nil u =>
    unfold dedup
    simp only [nil_vx, nodup_cons, not_mem_nil, not_false_eq_true, nodup_nil, and_self]
  | .cons u e W =>
    unfold dedup
    split_ifs with h
    · simp only [h, ↓reduceDIte]
      exact dedup_vx_nodup (W.firstAt u h)
    · simp only [cons_vx, nodup_cons, dedup_vx_nodup W, and_true]
      contrapose! h
      exact dedup_vx_sublist h

lemma dedup_edge_nodup {w : Walk α β} (hVd : w.ValidIn G) : w.dedup.edge.Nodup := by
  match w with
  | .nil u =>
    unfold dedup
    simp only [nil_edge, nodup_nil]
  | .cons u e W =>
  unfold dedup
  split_ifs with h
  · simp only [h, ↓reduceDIte]
    exact dedup_edge_nodup (hVd.2.firstAt h)
  simp only [cons_edge, nodup_cons, dedup_edge_nodup hVd.2, and_true]
  obtain ⟨hne, hVd⟩ := hVd
  contrapose! h
  exact dedup_vx_sublist <| hVd.dedup.mem_of_mem_edge_of_inc h hne.inc_left

lemma ValidIn.dedup_isPath (hVd : w.ValidIn G) : G.IsPath w.dedup where
  validIn := ValidIn.dedup hVd
  nodup := dedup_vx_nodup w

end Walk
open Walk

lemma IsWalkFrom.dedup [DecidableEq α] (h : G.IsWalkFrom S T w) : G.IsPathFrom S T w.dedup := by
  obtain ⟨hVd, hfirst, hlast⟩ := h
  refine hVd.dedup_isPath.isPathFrom ?_ ?_
  · rwa [dedup_first]
  · rwa [dedup_last]

namespace Walk

/- Properties of `endIf` -/
variable {P : α → Prop} [DecidablePred P]

@[simp]
lemma endIf_nil (h : ∃ u ∈ nil x, P u) : (nil x : Walk α β).endIf h = nil x := rfl

lemma endIf_eq_nil (h : ∃ u ∈ w, P u) (hP : P w.first) :
    w.endIf h = nil w.first := by
  match w with
  | .nil u => rfl
  | .cons u e w' => simpa only [endIf, cons_first, dite_eq_left_iff, reduceCtorEq, imp_false,
    not_not] using hP

  @[simp]
lemma endIf_cons (h : ∃ u ∈ cons x e w, P u) :
    (cons x e w).endIf h = if hP : P x
    then nil x
    else cons x e (endIf w (by simp [hP] at h; exact h)) := by
  match w with
  | .nil u => rfl
  | .cons u e' w' => rfl

@[simp]
lemma endIf_first (h : ∃ u ∈ w, P u) : (w.endIf h).first = w.first := by
  match w with
  | .nil x => simp only [endIf, nil_first]
  | .cons x e w =>
    simp only [endIf, cons_first]
    split_ifs <;> rfl

@[simp]
lemma endIf_last {w : Walk α β} (h : ∃ u ∈ w, P u) : P (w.endIf h).last := by
  match w with
  | .nil x => simpa using h
  | .cons x e w =>
    rw [endIf]
    split_ifs with hPx
    · simpa only [nil_last]
    · simp only [mem_cons_iff, exists_eq_or_imp, hPx, false_or, cons_last] at h ⊢
      exact endIf_last h

@[simp]
lemma endIf_eq_nil_iff (h : ∃ u ∈ w, P u) : w.endIf h = nil w.first ↔ P w.first :=
  ⟨fun heq ↦ by simpa only [heq, nil_last] using endIf_last h, fun a ↦ endIf_eq_nil h a⟩

@[simp]
lemma endIf_nonempty_iff (h : ∃ u ∈ w, P u) : (w.endIf h).Nonempty ↔ ¬ P w.first := by
  rw [iff_not_comm]
  convert (endIf_eq_nil_iff h).symm
  simp only [Nonempty.not_iff, endIf_eq_nil_iff]
  constructor <;> rintro h'
  · obtain ⟨x, hx⟩ := h'
    simpa [hx, ← hx ▸ endIf_first h] using endIf_last h
  · use w.first
    simp only [endIf_eq_nil_iff, h']

@[simp]
lemma endIf_length {w : Walk α β} (h : ∃ u ∈ w, P u) : (w.endIf h).length ≤ w.length := by
  match w with
  | .nil x => simp only [endIf, nil_length, le_refl]
  | .cons x e w =>
  rw [endIf]
  split_ifs <;> simp [endIf_length]

lemma endIf_sizeOf_le {w : Walk α β} (h : ∃ u ∈ w, P u) : sizeOf (w.endIf h) ≤ sizeOf w := by
  match w with
  | .nil x => simp only [endIf, nil.sizeOf_spec, sizeOf_default, add_zero, le_refl]
  | .cons x e w =>
  rw [endIf]
  split_ifs <;> simp [endIf_sizeOf_le]

lemma ValidIn.endIf {w : Walk α β} (hVd : w.ValidIn G) (h : ∃ u ∈ w, P u) :
    (w.endIf h).ValidIn G := by
  match w with
  | .nil x => simpa only [endIf, nil_validIn]
  | .cons x e w =>
    simp only [Walk.endIf]
    split_ifs with hPx
    · rw [nil_validIn]
      simp only [cons_validIn] at hVd
      exact hVd.1.vx_mem_left
    · rw [cons_validIn] at hVd ⊢
      refine ⟨?_, hVd.2.endIf _ ⟩
      convert hVd.1 using 1
      simp only [mem_cons_iff, exists_eq_or_imp, hPx, false_or] at h
      exact endIf_first h

lemma endIf_vx_sublist {w : Walk α β} (h : ∃ u ∈ w, P u) :
    (w.endIf h).vx ⊆ w.vx := by
  match w with
  | .nil x => simp only [endIf, nil_vx, List.Subset.refl]
  | .cons x e w =>
    simp only [endIf, cons_vx]
    split_ifs with h
    · simp only [nil_vx, cons_subset, mem_cons, true_or, nil_subset, subset_cons_of_subset,
        and_self]
    · simp only [cons_vx, cons_subset, mem_cons, true_or, true_and]
      refine List.Subset.trans ?_ (List.subset_cons_self _ _)
      apply endIf_vx_sublist

lemma endIf_mem_vx {w : Walk α β} (h : ∃ u ∈ w, P u) (hv : v ∈ w.endIf h):
    ¬ P v ∨ v = (w.endIf h).last := by
  match w with
  | .nil x => simp_all only [endIf_nil, mem_nil_iff, nil_last, or_true]
  | .cons x e w =>
    rw [endIf_cons]
    split_ifs with hPx
    · simp_all only [endIf_cons, dite_true, mem_nil_iff, not_true_eq_false, nil_last, or_true]
    · simp_all only [endIf_cons, dite_false, mem_cons_iff, cons_last]
      obtain rfl | hvmem := hv
      · exact Or.inl hPx
      · simp only [mem_cons_iff, exists_eq_or_imp, hPx, false_or] at h
        exact endIf_mem_vx h hvmem

lemma endIf_exists_inc₂_last {w : Walk α β} (h : ∃ u ∈ w, P u) (hVd : w.ValidIn G)
    (hNonempty : (w.endIf h).Nonempty) :
    ∃ v ∈ (w.endIf h), ¬ P v ∧ ∃ e, G.Inc₂ e v (w.endIf h).last := by
  match w with
  | .nil x => simp_all only [endIf_nil, Nonempty.not_nil]
  | .cons x e (nil y) =>
    simp_all only [cons_validIn, nil_first, nil_validIn, endIf_cons, endIf_nil, dite_eq_ite]
    split_ifs with hPx
    · simp_all only [cons_vx, nil_vx, mem_cons, not_mem_nil, or_false, exists_eq_or_imp,
      exists_eq_left, true_or, ite_true, Nonempty.not_nil]
    · simp_all only [mem_cons_iff, mem_nil_iff, exists_eq_or_imp, exists_eq_left, false_or,
      ite_false, Nonempty.cons_true, cons_last, nil_last, not_false_eq_true, true_and,
      not_true_eq_false, false_and, or_false]
      use e
      exact hVd.1
  | .cons x e (cons y e' w) =>
    unfold endIf
    split_ifs with hPx
    · simp_all only [cons_validIn, cons_first, endIf_cons, dite_true, Nonempty.not_nil]
    · by_cases hPy : P y
      · simp_all only [cons_validIn, cons_first, endIf_cons, dite_true, dite_eq_ite, ite_false,
        Nonempty.cons_true, mem_cons_iff, mem_nil_iff, cons_last, nil_last,
        exists_eq_or_imp, not_false_eq_true, true_and, exists_eq_left, not_true_eq_false, false_and,
        or_false]
        use e
        exact hVd.1
      · let w' := cons y e' w
        rw [cons_last]
        have h' : ∃ u ∈ w', P u := by
          change ∃ u ∈ cons x e w', P u at h
          simpa only [mem_cons_iff, exists_eq_or_imp, hPx, false_or] using h
        have hNonempty' : (w'.endIf h').Nonempty := by
          simp only [endIf_cons, hPy, ↓reduceDIte, Nonempty.cons_true, w']
        obtain ⟨a, ha, hh⟩ := endIf_exists_inc₂_last (w := w') h' hVd.2 hNonempty'
        refine ⟨a, ?_, hh⟩
        rw [mem_cons_iff]
        right
        exact ha

end Walk
