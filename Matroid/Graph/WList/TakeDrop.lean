import Matroid.Graph.WList.Sublist

open Set Function List Nat WList

variable {α β : Type*} {u v x y z : α} {e e' f g : β} {S T U: Set α}
  {F F' : Set β} {w w₀ w₁ w₂ w₃ l l₁ l₂ l₃ : WList α β}

namespace WList


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
lemma prefixUntil_first (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.prefixUntil P).first = w.first := by
  cases w with simp [apply_ite]

lemma prefixUntil_prop_last {w : WList α β} (h : ∃ u ∈ w, P u) : P (w.prefixUntil P).last := by
  induction w with
  | nil u => simpa using h
  | cons u e W ih =>
    obtain h | h : P u ∨ ∃ a ∈ W, P a := by simpa using h
    all_goals simp_all [apply_ite]

lemma prefixUntil_not_prop (hx : x ∈ w.prefixUntil P) (hne : (w.prefixUntil P).last ≠ x) :
    ¬ P x := by
  induction w with
  | nil u => simp_all
  | cons u e W ih =>
    refine (em (P u)).elim (fun _ ↦ by simp_all) fun hu ↦ ?_
    rw [prefixUntil_cons, if_neg hu, mem_cons_iff] at hx
    cases hx <;> simp_all

lemma prefixUntil_last_eq_of_prop (hv : v ∈ w.prefixUntil P) (hvP : P v) :
    (w.prefixUntil P).last = v := by
  by_contra! hvne
  exact prefixUntil_not_prop hv hvne hvP

lemma Nonempty.prefixUntil_nil_iff (hw : w.Nonempty) : (w.prefixUntil P).Nil ↔ P w.first := by
  induction w with | nil => simp at hw | cons => simp [apply_ite]

lemma Nonempty.prefixUntil_nonempty_iff (hw : w.Nonempty) :
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

lemma prefixUntil_last_eq_iff_prop (h : ∃ u ∈ w, P u) :
    P v ∧ v ∈ w.prefixUntil P ↔ (w.prefixUntil P).last = v := by
  refine ⟨fun ⟨hvP, hv⟩ ↦ prefixUntil_last_eq_of_prop hv hvP, ?_⟩
  rintro rfl
  exact ⟨prefixUntil_prop_last h, last_mem⟩

lemma prefixUntil_inter_eq_last [DecidablePred (· ∈ S)] (h : ∃ u ∈ w, u ∈ S) :
    S ∩ V(w.prefixUntil (· ∈ S)) = {(w.prefixUntil (· ∈ S)).last} := by
  ext x
  simp only [Set.mem_inter_iff, mem_vertexSet_iff, mem_singleton_iff]
  rwa [eq_comm, w.prefixUntil_last_eq_iff_prop]

lemma prefixUntil_eq_self_of_forall {w : WList α β} (h : ∀ u ∈ w, ¬ P u) : w.prefixUntil P = w := by
  match w with
  | nil u => simp
  | cons u e w =>
    simp_all only [mem_cons_iff, forall_eq_or_imp, prefixUntil_cons, ↓reduceIte, cons.injEq,
      true_and]
    exact prefixUntil_eq_self_of_forall h.2

lemma prefixUntil_concat_of_exists {w : WList α β} (h : ∃ u ∈ w, P u) :
    (w.concat e x).prefixUntil P = w.prefixUntil P := by
  match w with
  | nil u => simp_all
  | cons u e w =>
    by_cases hP : P u
    · simp [hP]
    simp_all only [mem_cons_iff, exists_eq_or_imp, false_or, cons_concat, prefixUntil_cons,
      ↓reduceIte, cons.injEq, true_and]
    exact prefixUntil_concat_of_exists h

lemma prefixUntil_concat_of_forall {w : WList α β} (h : ∀ u ∈ w, ¬ P u) :
    (w.concat e x).prefixUntil P = w.concat e x := by
  match w with
  | nil u => simp_all
  | cons u e w =>
    simp_all only [mem_cons_iff, forall_eq_or_imp, cons_concat, prefixUntil_cons, ↓reduceIte,
      cons.injEq, true_and]
    exact prefixUntil_concat_of_forall h.2

lemma prefixUntil_concat (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.concat e x).prefixUntil P = if w.vertex.all (¬ P ·) then w.concat e x
    else w.prefixUntil P := by
  split_ifs with h
  · exact prefixUntil_concat_of_forall (by simpa using h)
  · exact prefixUntil_concat_of_exists (by simpa using h)

/-- The prefix of `w` ending at a vertex `x`. Equal to `w` if `x ∉ w`. -/
def prefixUntilVertex [DecidableEq α] (w : WList α β) (x : α) : WList α β := w.prefixUntil (· = x)

@[simp]
lemma prefixUntilVertex_nil [DecidableEq α] : (nil (β := β) u).prefixUntilVertex x = nil u := by
  simp [prefixUntilVertex]

@[simp]
lemma prefixUntilVertex_cons_eq_nil [DecidableEq α] (u e) (w : WList α β) :
    (cons u e w).prefixUntilVertex u = nil u := by
  simp [prefixUntilVertex, prefixUntil_cons]

lemma prefixUntilVertex_cons_of_ne [DecidableEq α] (w : WList α β) (hne : x ≠ y) (e : β) :
    (cons x e w).prefixUntilVertex y = cons x e (w.prefixUntilVertex y) := by
  simpa [prefixUntilVertex]

lemma prefixUntilVertex_cons [DecidableEq α] (u e) (w : WList α β) :
    (cons u e w).prefixUntilVertex x = if u = x then nil u else
    cons u e (w.prefixUntilVertex x) := by
  simp [prefixUntilVertex, prefixUntil]

lemma prefixUntilVertex_isPrefix [DecidableEq α] (w : WList α β) (x : α) :
    (w.prefixUntilVertex x).IsPrefix w := prefixUntil_isPrefix ..

@[simp]
lemma prefixUntilVertex_last [DecidableEq α] (hxw : x ∈ w) : (w.prefixUntilVertex x).last = x :=
  prefixUntil_prop_last (P := (· = x)) ⟨_, hxw, rfl⟩

@[simp]
lemma prefixUntilVertex_first (w : WList α β) (x) [DecidableEq α] :
    (w.prefixUntilVertex x).first = w.first :=
  prefixUntil_first ..

@[simp]
lemma prefixUntilVertex_length [DecidableEq α] (hx : x ∈ w) :
    (w.prefixUntilVertex x).length = w.idxOf x := by
  induction w with | nil => simp_all [prefixUntilVertex] | cons u e w ih =>
  obtain rfl | hu := eq_or_ne x u
  · simp [prefixUntilVertex]
  simp_all [prefixUntilVertex, hu.symm, idxOf_cons_ne hu.symm]

-- lemma prefixUntilVertex_index_iff [DecidableEq α] (hx : x ∈ w) (hy : y ∈ w) :
--     y ∈ w.prefixUntilVertex x ↔  w.idxOf y ≤ w.idxOf x := by
--   simp only [prefixUntilVertex]
--   fun_induction WList.prefixUntil with simp_all [idxOf_eq_zero_iff]
--   | case3 u e w hne IH =>
--     obtain (rfl | hne') := em (u = y)
--     · simp
--     simp_all
--     tauto

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

lemma suffixFrom_prop_first {w : WList α β} (h : ∃ u ∈ w, P u) : P (w.suffixFrom P).first := by
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

lemma suffixFrom_eq_nil_of_forall (w : WList α β) (P : α → Prop) [DecidablePred P]
    (h : ∀ u ∈ w, ¬ P u) : w.suffixFrom P = nil w.last := by
  match w with
  | nil u => simp
  | cons u e w =>
    simp only [mem_cons_iff, forall_eq_or_imp] at h
    simp only [suffixFrom_cons, h.1, ↓reduceIte, last_cons]
    exact suffixFrom_eq_nil_of_forall w P h.2

lemma suffixFrom_concat_of_forall (w : WList α β) (P : α → Prop) [DecidablePred P]
    (h : ∀ u ∈ w, ¬ P u) : (w.concat e x).suffixFrom P = nil x := by
  match w with
  | nil u => simp_all
  | cons u e w =>
    simp_all only [mem_cons_iff, forall_eq_or_imp, cons_concat, suffixFrom_cons, ↓reduceIte]
    exact suffixFrom_concat_of_forall w P h.2

lemma suffixFrom_concat_of_exists (w : WList α β) (P : α → Prop) [DecidablePred P]
    (h : ∃ u ∈ w, P u) : (w.concat e x).suffixFrom P = (w.suffixFrom P).concat e x := by
  match w with
  | nil u => simp_all
  | cons u e w =>
    by_cases hP : P u
    · simp [hP]
    simp_all only [mem_cons_iff, exists_eq_or_imp, false_or, cons_concat, suffixFrom_cons,
      ↓reduceIte]
    exact suffixFrom_concat_of_exists w P h

lemma suffixFrom_concat (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.concat e x).suffixFrom P = if w.vertex.all (¬ P ·) then nil x
    else (w.suffixFrom P).concat e x := by
  split_ifs with h
  · exact suffixFrom_concat_of_forall w P (by simpa using h)
  · exact suffixFrom_concat_of_exists w P (by simpa using h)

@[simp]
lemma prefixUntil_append_suffixFrom (w : WList α β) (P : α → Prop) [DecidablePred P] :
    w.prefixUntil P ++ w.suffixFrom P = w := by
  induction w with
  | nil => simp
  | cons u e w ih =>
    simp only [prefixUntil_cons, suffixFrom_cons]
    split_ifs with hu
    · simp
    simpa

@[simp]
lemma prefixUntil_last_eq_suffixFrom_first (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.prefixUntil P).last = (w.suffixFrom P).first := by
  induction w with
  | nil => simp
  | cons u e w ih =>
    simp only [prefixUntil_cons, suffixFrom_cons]
    split_ifs with hu
    · simp
    simpa

/-- The suffix of `w` starting at the first occurence of a vertex `x`.
Equal to `[w.last]` if `x ∉ w`. -/
def suffixFromVertex [DecidableEq α] (w : WList α β) (x : α) : WList α β := w.suffixFrom (· = x)

@[simp]
lemma suffixFromVertex_nil [DecidableEq α] : (nil (β := β) u).suffixFromVertex x = nil u := by
  simp [suffixFromVertex]

lemma suffixFromVertex_cons_of_ne [DecidableEq α] (w : WList α β) (hne : x ≠ y) (e : β) :
    (cons x e w).suffixFromVertex y = w.suffixFromVertex y := by
  simp [suffixFromVertex, hne]

lemma suffixFromVertex_cons_or [DecidableEq α] (u e) (w : WList α β) (x) :
    (u = x ∧ (cons u e w).suffixFromVertex x = cons u e w) ∨
    (u ≠ x ∧ (cons u e w).suffixFromVertex x = w.suffixFromVertex x) := by
  obtain rfl | h := eq_or_ne u x <;> simp_all [suffixFromVertex]

@[simp]
lemma suffixFromVertex_of_notMem [DecidableEq α] (w : WList α β) (x : α) (hx : x ∉ w) :
    w.suffixFromVertex x = nil w.last := by
  apply w.suffixFrom_eq_nil_of_forall (· = x)
  grind

@[simp]
lemma suffixFromVertex_first [DecidableEq α] (hxw : x ∈ w) : (w.suffixFromVertex x).first = x :=
  suffixFrom_prop_first (P := (· = x)) ⟨_, hxw, rfl⟩

lemma suffixFromVertex_isSuffix [DecidableEq α] (w : WList α β) (x : α) :
    (w.suffixFromVertex x).IsSuffix w := suffixFrom_isSuffix ..

@[simp]
lemma suffixFromVertex_last (w : WList α β) (x) [DecidableEq α] :
    (w.suffixFromVertex x).last = w.last :=
  suffixFrom_last ..

@[simp]
lemma suffixFromVertex_eq_self_iff [DecidableEq α] (w : WList α β) (x : α) :
    w.suffixFromVertex x = w ↔ w.Nil ∨ x = w.first := by
  match w with
  | .nil u => simp
  | .cons u e w =>
  obtain ⟨rfl, h⟩ | ⟨hne, h⟩ := w.suffixFromVertex_cons_or u e x
  · simpa
  simp only [h, not_nil_cons, first_cons, hne.symm, or_self, iff_false, ne_eq]
  by_cases hxw : x ∈ w
  · apply_fun first
    simp [hxw, hne.symm]
  simp [hxw]

@[simp]
lemma prefixUntilVertex_append_suffixFromVertex [DecidableEq α] (w : WList α β) (x : α) :
    w.prefixUntilVertex x ++ w.suffixFromVertex x = w :=
  prefixUntil_append_suffixFrom ..

lemma sufixFromVertex_length [DecidableEq α] (w : WList α β) (x : α) (hx : x ∈ w) :
    (w.suffixFromVertex x).length + w.idxOf x = w.length := by
  induction w with | nil => simp_all [suffixFromVertex] | cons u e w ih =>
  obtain rfl | hu := eq_or_ne x u
  · simp [suffixFromVertex]
  simp_all [idxOf_cons_ne hu.symm ]
  have he : (cons u e w).suffixFromVertex x = w.suffixFromVertex x := by
    simp_all [suffixFromVertex, suffixFrom_cons w]
    intro h
    by_contra
    exact hu h.symm
  rw [he]
  exact Eq.symm ((fun {m k n} ↦ Nat.add_left_inj.mpr) ih.symm)

@[simp]
lemma suffixFromVertex_first_eq [DecidableEq α] (w : WList α β) :
    w.suffixFromVertex w.first = w := by
  induction w with (simp_all [suffixFromVertex])

lemma suffixFromVertex_second_eq [DecidableEq α] (e) (hx : x ≠ w.first) :
    (cons x e w).suffixFromVertex w.first = w := by
  simp only [suffixFromVertex, suffixFrom_cons, hx, ↓reduceIte]
  exact suffixFromVertex_first_eq w

lemma prefixUntilVertex_suffixFromVertex_length [DecidableEq α] (w : WList α β) (x : α)
    (hx : x ∈ w) :
    (w.prefixUntilVertex x).length + (w.suffixFromVertex x).length = w.length := by
  rw [prefixUntilVertex_length hx, ←sufixFromVertex_length w x hx, add_comm]

@[simp]
lemma prefixUntilVertex_last_eq_suffixFromVertex_first [DecidableEq α] (hx : x ∈ w) :
    (w.prefixUntilVertex x).last = (w.suffixFromVertex x).first := by
  rw [prefixUntilVertex_last hx, suffixFromVertex_first hx]

@[simp]
lemma suffixFromVertex_idempotent [DecidableEq α] (p : WList α β) (x) :
    (p.suffixFromVertex x).suffixFromVertex x = p.suffixFromVertex x := by
  induction p generalizing x with | nil u => simp_all [suffixFromVertex] | cons x' e p IH =>
  obtain rfl | hne := eq_or_ne x' x <;> simp_all [suffixFromVertex]

/-- Take the prefix of `w` ending at the last occurence of `x` in `w`.
Equal to `w` if `x ∉ w`. -/
def prefixUntilLast (w : WList α β) (P : α → Prop) [DecidablePred P] : WList α β :=
  (w.reverse.suffixFrom P).reverse

@[simp]
lemma prefixUntilLast_isPrefix (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.prefixUntilLast P).IsPrefix w := by
  rw [← reverse_isSuffix_reverse_iff, prefixUntilLast, reverse_reverse]
  apply suffixFrom_isSuffix

lemma prefixUntilLast_prop_last (h : ∃ x ∈ w, P x) : P (w.prefixUntilLast P).last := by
  rw [prefixUntilLast, reverse_last]
  exact suffixFrom_prop_first (by simpa)

@[simp]
lemma prefixUntilLast_first (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.prefixUntilLast P).first = w.first := by
  rw [prefixUntilLast, reverse_first, suffixFrom_last, reverse_last]

/-- `w.prefixUntil P` is a prefix of `w.prefixUntilLast P` if `P` occurs in `w`.
  Otherwise, `w.prefixUntil P = w` and `w.prefixUntilLast P = nil w.first`. -/
@[simp]
lemma prefixUntil_isPrefix_prefixUntilLast (w : WList α β) (P : α → Prop) [DecidablePred P]
    (h : ∃ x ∈ w, P x) : (w.prefixUntil P).IsPrefix (w.prefixUntilLast P) := by
  match w with
  | nil x => simp
  | cons x e w =>
    by_cases hP : P x
    · simp [prefixUntil_cons, hP]
    have h' : ¬(∀ u ∈ w, ¬ P u) := by simpa [hP] using h
    simp only [prefixUntil_cons, hP, ↓reduceIte, prefixUntilLast, reverse_cons, suffixFrom_concat,
      reverse_vertex, decide_not, all_reverse, all_eq_true, mem_vertex, Bool.not_eq_eq_eq_not,
      Bool.not_true, decide_eq_false_iff_not, h', concat_reverse]
    exact (prefixUntil_isPrefix_prefixUntilLast w P (by simpa using h')).cons x e

-- lemma prefixUntilLast_eq_prefixUntil (w : WList α β) (P : α → Prop) [DecidablePred P]
--     (h : w.vertex.countP P = 1) : w.prefixUntilLast P = w.prefixUntil P := by sorry

lemma prefixUntilLast_eq_prefixUntil_of_nodup [DecidableEq α] (hnd : w.vertex.Nodup)
    (h : w.vertex.count x = 1) : w.prefixUntilLast (· = x) = w.prefixUntilVertex x := by
  rw [List.count_eq_length_filter, length_eq_one_iff] at h
  obtain ⟨y, hy⟩ := h
  have hwl := w.prefixUntilLast_isPrefix (· = x)
  have hin : ∀ z, z ∈ w.vertex.filter (· == x) ↔ z = y := by simp [hy]
  simp only [mem_filter, mem_vertex, beq_iff_eq] at hin
  have hex : ∃ z ∈ w, z = x := ⟨y, hin y |>.mpr rfl⟩
  refine (prefixUntil_isPrefix_prefixUntilLast w (· = x) hex).eq_of_last_mem
    (hnd.sublist hwl.prefix.sublist) ?_ |>.symm
  obtain rfl := (hin _).mp ⟨hwl.subset last_mem, (w.prefixUntilLast_prop_last hex)⟩
  exact ((hin _).mp ⟨(w.prefixUntil_isPrefix (· = x)).subset last_mem,
    (w.prefixUntil_prop_last hex)⟩) ▸ last_mem

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

@[simp]
lemma suffixFromLast_last (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.suffixFromLast P).last = w.last := by
  rw [suffixFromLast, reverse_last, prefixUntil_first, reverse_first]

lemma suffixFromLast_first_eq_of_prop (hv : v ∈ w.suffixFromLast P) (hvP : P v) :
    (w.suffixFromLast P).first = v := by
  rw [suffixFromLast, reverse_first, prefixUntil_last_eq_of_prop ?_ hvP]
  unfold suffixFromLast at hv
  rwa [mem_reverse] at hv

lemma suffixFromLast_first_eq_iff_prop (h : ∃ x ∈ w, P x) :
    P v ∧ v ∈ w.suffixFromLast P ↔ (w.suffixFromLast P).first = v := by
  refine ⟨fun ⟨hvP, hv⟩ ↦ suffixFromLast_first_eq_of_prop hv hvP, ?_⟩
  rintro rfl
  exact ⟨suffixFromLast_prop_first h, first_mem⟩

lemma suffixFromLast_inter_eq_first [DecidablePred (· ∈ S)] (h : ∃ u ∈ w, u ∈ S) :
    S ∩ V(w.suffixFromLast (· ∈ S)) = {(w.suffixFromLast (· ∈ S)).first} := by
  ext x
  simp only [mem_inter_iff, mem_vertexSet_iff, mem_singleton_iff]
  rw [eq_comm, suffixFromLast_first_eq_iff_prop h]

lemma suffixFromLast_eq_self_of_forall {w : WList α β} (h : ∀ x ∈ w, ¬ P x) :
    w.suffixFromLast P = w := by
  rw [suffixFromLast, w.reverse.prefixUntil_eq_self_of_forall (by simpa), reverse_reverse]

@[simp]
lemma suffixFrom_isSuffix_suffixFromLast {w : WList α β} (h : ∃ x ∈ w, P x) :
    (w.suffixFromLast P).IsSuffix (w.suffixFrom P) := by
  match w with
  | nil x => simp [suffixFromLast]
  | cons x e w =>
    simp only [suffixFrom_cons, suffixFromLast, reverse_cons, prefixUntil_concat, reverse_vertex,
      decide_not, all_reverse, all_eq_true, mem_vertex, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not]
    split_ifs with hPx hPw hPw
    · simp
    · absurd h
      simpa [hPw]
    · exact (w.suffixFromLast_isSuffix P).cons x e
    simp only [mem_cons_iff, exists_eq_or_imp, hPw, false_or] at h
    exact suffixFrom_isSuffix_suffixFromLast h

lemma suffixFrom_eq_suffixFromLast_of_nodup [DecidableEq α] (hnd : w.vertex.Nodup)
    (h : w.vertex.count x = 1) : w.suffixFrom (· = x) = w.suffixFromLast (· = x) := by
  rw [← w.reverse_reverse] at h ⊢
  rw [← reverse_inj_iff]
  rw [reverse_vertex, List.count_reverse] at h
  change (w.reverse.prefixUntilLast (· = x)) =
    (w.reverse.reverse.reverse.prefixUntil (· = x)).reverse.reverse
  simp only [reverse_reverse]
  rw [← List.nodup_reverse, ← reverse_vertex] at hnd
  exact prefixUntilLast_eq_prefixUntil_of_nodup hnd h

lemma IsSublist.exists_append_append (hw₀ : w₀.IsSublist w) (hw : w.vertex.Nodup) :
    ∃ w₁ w₂, w₁.last = w₀.first ∧ w₀.last = w₂.first ∧ w = w₁ ++ w₀ ++ w₂ := by
  classical
  induction hw₀ with
  | @nil x w h =>
  · refine ⟨w.prefixUntilVertex x, w.suffixFromVertex x, ?_⟩
    rw [nil_first, nil_last, prefixUntilVertex_last h, suffixFromVertex_first h,
      append_assoc, nil_append, prefixUntilVertex_append_suffixFromVertex]
    simp
  | @cons x e w₁ w₂ h ih =>
  · simp only [cons_vertex, nodup_cons, mem_vertex] at hw
    obtain ⟨w₁', w₂', h_eq, h_eq', rfl⟩ := ih hw.2
    exact ⟨WList.cons x e w₁', w₂', by simp [h_eq', h_eq]⟩
  | @cons₂ x e w₁ w₂ h h_eq ih =>
  · simp only [cons_vertex, nodup_cons, mem_vertex] at hw
    obtain ⟨w₁', w₂', h1, h2, rfl⟩ := ih hw.2
    cases w₁' with
    | nil u => exact ⟨WList.nil x, w₂', by simpa⟩
    | cons u e w₁' =>
    exfalso
    obtain rfl : w₁.first = u := by simpa using h_eq
    rw [cons_append, append_vertex' (by simpa)] at hw
    simp at hw

/-- If `w₀` is a sublist `w` and `w` has no vertex repetitions,
then `w₀` is a suffix of a prefix of `w`. -/
lemma IsSublist.exists_isPrefix_isSuffix (hw₀ : w₀.IsSublist w) (hw : w.vertex.Nodup) :
    ∃ w', w'.IsPrefix w ∧ w₀.IsSuffix w' := by
  obtain ⟨w₁, w₂, h1, h2, rfl⟩ := hw₀.exists_append_append hw
  exact ⟨w₁ ++ w₀, isPrefix_append_right (by simpa), isSuffix_append_left ..⟩

lemma isSublist_iff_isInfix (hnd : w.vertex.Nodup) : w₀ ≤ w ↔ w₀.IsInfix w := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.isSublist⟩
  obtain ⟨wL, wR, hL, hR, rfl⟩ := h.exists_append_append hnd
  exact ⟨wL, wR, hL, hR, rfl⟩

lemma exists_sublist_of_mem_mem (hx : x ∈ w) (hy : y ∈ w) : ∃ w₀ : WList α β,
    w₀.IsSublist w ∧ (x = w₀.first ∧ y = w₀.last ∨ x = w₀.last ∧ y = w₀.first) := by
  classical
  let w₁ := w.prefixUntilVertex x
  let w₂ := w.suffixFromVertex x
  have h : w₁ ++ w₂ = w := w.prefixUntilVertex_append_suffixFromVertex x
  by_cases hyw₁ : y ∈ w₁
  · use w₁.suffixFromVertex y, (w₁.suffixFromVertex_isSuffix y).isSublist.trans
      (w.prefixUntilVertex_isPrefix x).isSublist, .inr ⟨?_, ?_⟩
    · simp only [suffixFromVertex_last, w₁]
      exact (prefixUntilVertex_last hx).symm
    · simp only [w₁]
      exact (suffixFromVertex_first hyw₁).symm
  have hyw₂ : y ∈ w₂ := by
    rw [← h, ← mem_vertex, append_vertex] at hy
    have hw₁dl : y ∉ w₁.vertex.dropLast := (hyw₁ <| w₁.vertex.dropLast_sublist.mem ·)
    simpa [mem_append, hw₁dl, mem_vertex, false_or] using hy
  use w₂.prefixUntilVertex y, (w₂.prefixUntilVertex_isPrefix y).isSublist.trans
    (w.suffixFromVertex_isSuffix x).isSublist, .inl ⟨?_, ?_⟩
  · simp only [prefixUntilVertex_first, w₂]
    exact (suffixFromVertex_first hx).symm
  · exact (prefixUntilVertex_last hyw₂).symm

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

lemma tail_vertex (hw : w.Nonempty) : w.tail.vertex = w.vertex.tail := by
  induction w with simp_all

lemma tail_edge (w : WList α β) : w.tail.edge = w.edge.tail := by
  induction w with simp

lemma tail_length (w : WList α β) : w.tail.length = w.length - 1 := by
  induction w with simp

lemma mem_tail_iff_of_nodup (hw : Nodup w.vertex) (hne : w.Nonempty) :
    x ∈ w.tail ↔ x ∈ w ∧ x ≠ w.first := by
  induction w with aesop

lemma first_notMem_tail_of_nodup (hw : Nodup w.vertex) (hne : w.Nonempty) :
    w.first ∉ w.tail := by
  simp [mem_tail_iff_of_nodup hw hne]

lemma tail_vertexSet_of_nodup (hw : Nodup w.vertex) (hne : w.Nonempty) :
    V(w.tail) = V(w) \ {w.first} := by
  simp_rw [WList.vertexSet, mem_tail_iff_of_nodup hw hne]
  aesop

lemma Nonempty.cons_tail (hw : w.Nonempty) : w.tail.cons w.first (hw.firstEdge w) = w := by
  cases hw with simp

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

lemma tail_append (hw₁ : w₁.Nonempty) (w₂ : WList α β) : (w₁ ++ w₂).tail = w₁.tail ++ w₂ := by
  induction w₁ with simp_all

lemma Nonempty.tail_isLink_iff (hw : w.Nonempty) (hnd : w.edge.Nodup) :
    w.tail.IsLink f x y ↔ w.IsLink f x y ∧ ¬f = hw.firstEdge := by
  cases hw with | cons u e w =>
  simp only [tail_cons, Nonempty.firstEdge_cons]
  have ⟨hew, hnd⟩  : e ∉ w.edge ∧ w.edge.Nodup := by simpa using hnd
  exact ⟨fun h ↦ ⟨h.cons .., fun hfe ↦ hew <| by simpa [hfe.symm] using h.edge_mem⟩,
    fun ⟨h, hne⟩ ↦ by cases h with simp_all⟩

lemma IsSuffix.eq_or_isSuffix_of_cons {w₁ w₂ : WList α β} (hsf : w₁.IsSuffix w₂) :
    w₁ = w₂ ∨ w₂.Nonempty ∧ w₁.IsSuffix w₂.tail := by
  match hsf with
  | .nil w => exact w.nil_or_nonempty.imp (Nil.eq_nil_last · |>.symm) (by simp)
  | .concat e x w₁ w₂ h =>
    obtain rfl | hne := eq_or_ne w₁ w₂
    · simp
    obtain h := h.eq_or_isSuffix_of_cons.resolve_left hne
    obtain ⟨v, rfl⟩ | hnem := w₂.exists_eq_nil_or_nonempty
    · simp [hne] at h
    rw [tail_concat hnem]
    exact Or.inr <| ⟨by simp, h.2.concat ..⟩

lemma IsSuffix.recOfTail {P : WList α β → Prop} (h : ∀ w, P w → P w.tail) {w₁ w₂}
    (hw₂ : P w₂) (hsf : w₁.IsSuffix w₂) : P w₁ := by
  obtain rfl | ⟨hne, hsf⟩ := hsf.eq_or_isSuffix_of_cons
  · exact hw₂
  have := hne.length_pos
  have : w₂.tail.length < w₂.length := by
    rw [tail_length]
    omega
  exact hsf.recOfTail h (h w₂ hw₂)

lemma idxOf_tail [DecidableEq α] (hw : w.Nonempty) (hxf : w.first ≠ x) (hx : x ∈ w) :
    (w.tail).idxOf x + 1 = w.idxOf x := by
  fun_induction WList.idxOf with simp_all

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

lemma Nonempty.dropLast_cons (hw : w.Nonempty) (x : α) (e : β) :
    (WList.cons x e w).dropLast = WList.cons x e w.dropLast := by
  cases hw with simp

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

lemma Nonempty.concat_dropLast (hw : w.Nonempty) : w.dropLast.concat hw.lastEdge w.last = w := by
  simpa [hw.firstEdge_reverse] using congr_arg WList.reverse hw.reverse.cons_tail

lemma Nonempty.exists_concat (hw : w.Nonempty) :
    ∃ (w' : WList α β) (e : β) (x : α), w'.concat e x = w :=
  ⟨w.dropLast, hw.lastEdge, w.last, hw.concat_dropLast⟩

lemma Nontrivial.exists_cons_concat (hw : w.Nontrivial) :
    ∃ x e w' f y, w = cons x e (concat w' f y) := by
  obtain ⟨x, e, w1, rfl⟩ := hw.nonempty.exists_cons
  rw [cons_nontrivial_iff] at hw
  obtain ⟨w', f, y, rfl⟩ := hw.exists_concat
  use x, e, w', f, y

@[simp]
lemma dropLast_first (w : WList α β) : (w.dropLast).first = w.first := by
  rw [← reverse_last, ← reverse_tail, tail_last, reverse_last]

@[simp]
lemma dropLast_vertex (h : w.Nonempty) : (w.dropLast).vertex = w.vertex.dropLast := by
  rw [← reverse_tail_reverse, reverse_vertex, tail_vertex (by simpa)]
  simp

@[simp]
lemma dropLast_edge (w : WList α β) : (w.dropLast).edge = w.edge.dropLast := by
  rw [← reverse_tail_reverse, reverse_edge, tail_edge, reverse_edge, ← dropLast_reverse,
    List.reverse_reverse]

lemma dropLast_length (w : WList α β) : w.dropLast.length = w.length - 1 := by
  induction w with | nil => simp | cons u e w ih => cases w with simp_all

lemma append_dropLast (w₁ : WList α β) (hw₂ : w₂.Nonempty) :
    (w₁ ++ w₂).dropLast = w₁ ++ w₂.dropLast := by
  induction w₁ with
  | nil u => simp
  | cons u e w ih => rw [cons_append, cons_append, Nonempty.dropLast_cons (by simp [hw₂]), ih]

lemma mem_iff_eq_mem_dropLast_or_eq_last : u ∈ w ↔ u ∈ w.dropLast ∨ u = w.last := by
  rw [← mem_reverse, mem_iff_eq_first_or_mem_tail, or_comm, reverse_tail, mem_reverse,
    reverse_first]

lemma dropLast_vertexSet_of_nodup (hw : w.vertex.Nodup) (hne : w.Nonempty) :
    V(w.dropLast) = V(w) \ {w.last} := by
  rw [← reverse_vertexSet, ← reverse_tail, tail_vertexSet_of_nodup (by simpa) (by simpa)]
  simp

lemma mem_dropLast_iff_of_nodup (hw : w.vertex.Nodup) (hne : w.Nonempty) :
    x ∈ w.dropLast ↔ x ∈ w ∧ x ≠ w.last := by
  rw [← reverse_tail_reverse, mem_reverse, mem_tail_iff_of_nodup (by simpa) (by simpa),
    mem_reverse, reverse_first]

lemma dropLast_isPrefix (w : WList α β) : w.dropLast.IsPrefix w := by
  rw [← reverse_isSuffix_reverse_iff, ← reverse_tail]
  apply tail_isSuffix

lemma dropLast_isPrefix_append_right (hw₁ : w₁.Nonempty) : w₁.dropLast.IsPrefix (w₁ ++ w₂) := by
  obtain ⟨w', e, x, rfl⟩ := hw₁.exists_concat
  simp only [dropLast_concat, WList.concat_append]
  exact w'.isPrefix_append_right (by simp)

protected lemma tail_dropLast (hw : w.length ≠ 1) : w.tail.dropLast = w.dropLast.tail := by
  induction w with | nil => simp | cons u e w ih => cases w with simp_all

lemma Nontrivial.tail_dropLast (hw : w.Nontrivial) : w.tail.dropLast = w.dropLast.tail :=
  WList.tail_dropLast hw.one_lt_length.ne.symm

@[simp]
lemma tail_nil_iff : w.tail.Nil ↔ w.length ≤ 1 := by
  cases w with simp

@[simp]
lemma tail_nonempty_iff : w.tail.Nonempty ↔ w.Nontrivial := by
  cases w with simp
alias ⟨_, Nontrivial.tail_nonempty⟩ := tail_nonempty_iff

lemma idxOf_dropLast [DecidableEq α] (hw : w.Nonempty) (hx : x ∈ w) :
    (w.dropLast).idxOf x = w.idxOf x := by
  induction w using concat_induction with simp_all | concat w e u IH =>
  obtain h_mem | h_notMem := em (x ∈ w)
  · exact (idxOf_concat_of_mem h_mem).symm
  replace hx : x = u := by tauto
  fun_induction w.idxOf x with simp_all

@[simp]
lemma dropLast_nonempty_iff : w.dropLast.Nonempty ↔ w.Nontrivial := by
  rw [← reverse_tail_reverse, reverse_nonempty, tail_nonempty_iff, reverse_nontrivial_iff]

alias ⟨_, Nontrivial.dropLast_nonempty⟩ := dropLast_nonempty_iff

lemma Nontrivial.dropLast_firstEdge (hw : w.Nontrivial) :
    hw.dropLast_nonempty.firstEdge = hw.nonempty.firstEdge := by
  cases hw with simp

lemma Nonempty.firstEdge_notMem_tail (hw : w.Nonempty) (hnd : w.edge.Nodup) :
    hw.firstEdge w ∉ w.tail.edge := by
  cases hw with simp_all

lemma Nonempty.lastEdge_notMem_dropLast (hw : w.Nonempty) (hnd : w.edge.Nodup) :
    hw.lastEdge w ∉ w.dropLast.edge := by
  have := hw.reverse.firstEdge_notMem_tail <| by simpa
  rw [hw.firstEdge_reverse] at this
  simp_all

lemma Nontrivial.tail_lastEdge (hw : w.Nontrivial) :
    hw.tail_nonempty.lastEdge = hw.nonempty.lastEdge := by
  convert hw.reverse.dropLast_firstEdge using 1
  simp [hw.tail_nonempty.firstEdge_reverse]

lemma Nontrivial.firstEdge_ne_lastEdge (hw : w.Nontrivial) (hnd : w.edge.Nodup) :
    hw.nonempty.firstEdge ≠ hw.nonempty.lastEdge := by
  refine fun h_eq ↦ hw.nonempty.firstEdge_notMem_tail hnd ?_
  rw [h_eq, ← hw.tail_lastEdge]
  exact Nonempty.lastEdge_mem (tail_nonempty hw)

lemma IsPrefix.eq_or_isPrefix_of_cons {w₁ w₂ : WList α β} (hsf : w₁.IsPrefix w₂) :
    w₁ = w₂ ∨ w₂.Nonempty ∧ w₁.IsPrefix w₂.dropLast := by
  match hsf with
  | .nil w => exact w.nil_or_nonempty.imp (Nil.eq_nil_first · |>.symm) (by simp)
  | .cons x e w₁ w₂ h =>
    obtain rfl | hne := eq_or_ne w₁ w₂
    · simp
    obtain h := h.eq_or_isPrefix_of_cons.resolve_left hne
    obtain ⟨v, rfl⟩ | hnem := w₂.exists_eq_nil_or_nonempty
    · simp [hne] at h
    rw [hnem.dropLast_cons]
    exact Or.inr <| ⟨by simp, h.2.cons ..⟩

lemma IsPrefix.recOfDropLast {P : WList α β → Prop} (h : ∀ w, P w → P w.dropLast) {w₁ w₂}
    (hw₂ : P w₂) (hpf : w₁.IsPrefix w₂) : P w₁ := by
  obtain rfl | ⟨hne, hpf⟩ := hpf.eq_or_isPrefix_of_cons
  · exact hw₂
  have := hne.length_pos
  have : w₂.dropLast.length < w₂.length := by
    rw [dropLast_length]
    omega
  exact hpf.recOfDropLast h (h w₂ hw₂)
termination_by w₂.length

-- lemma Nontrivial.lastEdge_mem_tail (hw : w.Nontrivial) : hw.nonempty.lastEdge ∈ w.tail.edge := by
--   rw [tail_lastE]
  -- cases hw withhC.isWalk.edgeSet_subset
  -- | cons_cons u e v f w =>
  --   simp

    -- Nonempty.lastEdge w (show w.Nonempty by rw [WList.nonempty_iff_]) ∈ w.tail.edge := sorry

variable {n m : ℕ}

/-- Take the first `n` vertices from a `WList`. Returns the entire list if `n ≥ w.length + 1`. -/
def take : WList α β → ℕ → WList α β
  | nil x, _ => nil x
  | cons x _ _, 0 => nil x
  | cons x e w, n+1 => cons x e (w.take n)

@[simp]
lemma take_nil (x : α) (n : ℕ) : (nil x (β := β)).take n = nil x := rfl

@[simp]
lemma take_zero (w : WList α β) : w.take 0 = nil w.first := by
  cases w with simp [take]

@[simp]
lemma take_cons_succ (x e) (w : WList α β) (n : ℕ) :
  (cons x e w).take (n+1) = cons x e (w.take n) := rfl

@[simp]
lemma take_length (w : WList α β) (n : ℕ) : (w.take n).length = min n w.length := by
  induction n generalizing w with
  | zero => simp
  | succ n IH => cases w with simp [take, IH]

@[simp]
lemma take_length_le (w : WList α β) (n : ℕ) : (w.take n).length ≤ n := by simp

@[simp]
lemma take_length_le' (w : WList α β) (n : ℕ) : (w.take n).length ≤ w.length := by simp

@[simp]
lemma take_eq_self (w : WList α β) : w.take w.length = w := by
  induction w <;> simp_all

@[simp]
lemma take_first (w : WList α β) (n : ℕ) : (w.take n).first = w.first := by
  cases n with
  | zero => simp
  | succ n =>
    cases w with
    | nil => simp
    | cons => simp

@[simp]
lemma take_last (w : WList α β) (n : ℕ) : (w.take n).last = w.get n := by
  induction n generalizing w with
  | zero => simp [get_zero]
  | succ n IH =>
    cases w with
    | nil => simp
    | cons x e w =>
      simp only [take_cons_succ, last_cons, get_cons_add]
      exact IH w

@[simp]
lemma take_vertex (w : WList α β) (n : ℕ) : (w.take n).vertex = w.vertex.take (n + 1) := by
  match w, n with
  | nil x, n => simp
  | cons x e w, 0 => simp
  | cons x e w, n + 1 => simp [w.take_vertex n]

@[simp]
lemma take_edge (w : WList α β) (n : ℕ) : (w.take n).edge = w.edge.take n := by
  match w, n with
  | nil x, n => simp
  | cons x e w, 0 => simp
  | cons x e w, n + 1 => simp [w.take_edge n]

lemma take_concat (w : WList α β) (e : β) (x : α) (n : ℕ) :
    (w.concat e x).take n = if n ≤ w.length then w.take n else w.concat e x := by
  match w, n with
  | nil x, 0 => simp
  | nil x, n + 1 => simp
  | cons x e w, 0 => simp
  | cons x e w, n + 1 =>
    simp only [cons_concat, take_cons_succ, take_concat, cons_length, add_le_add_iff_right]
    split_ifs with h <;> rfl

@[simp]
lemma take_append_length {w₁ w₂ : WList α β} (heq : w₁.last = w₂.first) :
    (w₁ ++ w₂).take w₁.length = w₁ := by
  match w₁ with
  | .nil u => simp_all
  | .cons u e w =>
    simp only [cons_append, cons_length, take_cons_succ, cons.injEq, true_and]
    simp only [last_cons] at heq
    exact w.take_append_length heq

@[simp]
lemma take_take (w : WList α β) (m n : ℕ) : (w.take n).take m = w.take (min m n) := by
  match w, m, n with
  | nil x, m, n => simp
  | cons x e w, 0, n => simp
  | cons x e w, m + 1, 0 => simp
  | cons x e w, m + 1, n + 1 => simp [w.take_take m n]

lemma take_take_comm (w : WList α β) (m n : ℕ) : (w.take n).take m = (w.take m).take n := by
  rw [take_take w m n, take_take w n m, min_comm]

/-- Drop the first `n` vertices from a `WList`. Returns `nil w.last` if `n ≥ w.length + 1`. -/
def drop : WList α β → ℕ → WList α β
  | w, 0 => w
  | nil x, _ => nil x
  | cons _ _ w, n+1 => w.drop n

@[simp]
lemma drop_zero (w : WList α β) : w.drop 0 = w := by
  match w with
  | .nil u => rfl
  | .cons u e w => rfl

@[simp]
lemma drop_nil (x : α) (n : ℕ) : (nil x (β := β)).drop n = nil x := by
  match n with
  | 0 => rfl
  | n + 1 => rfl

@[simp]
lemma drop_cons_succ (x e) (w : WList α β) (n : ℕ) :
  (cons x e w).drop (n+1) = w.drop n := rfl

@[simp]
lemma drop_length (w : WList α β) (n : ℕ) : (w.drop n).length = w.length - n := by
  match w, n with
  | nil x, n => simp
  | cons x e w, 0 => simp
  | cons x e w, n + 1 => simp [w.drop_length n]

lemma drop_eq_nil_of_length_le {w : WList α β} {n} (h : w.length ≤ n) :
    w.drop n = nil w.last := by
  match w, n with
  | nil x, n => simp
  | cons x e w, 0 => simp at h
  | cons x e w, n + 1 =>
    simp_all only [cons_length, add_le_add_iff_right, drop_cons_succ, last_cons]
    exact drop_eq_nil_of_length_le h

@[simp]
lemma drop_length_eq (w : WList α β) : w.drop w.length = nil w.last :=
  drop_eq_nil_of_length_le <| refl _

@[simp]
lemma drop_first (w : WList α β) (n : ℕ) : (w.drop n).first = w.get n := by
  match w, n with
  | nil x, n => simp
  | cons x e w, 0 => simp
  | cons x e w, n + 1 => simp [w.drop_first (by simpa)]

lemma drop_first_of_length_lt (h : w.length < n) : (w.drop n).first = w.last := by
  rw [drop_eq_nil_of_length_le (by omega)]
  simp

@[simp]
lemma drop_last (w : WList α β) (n : ℕ) : (w.drop n).last = w.last := by
  match w, n with
  | nil x, n => simp
  | cons x e w, 0 => simp
  | cons x e w, n + 1 => simp [w.drop_last n]

@[simp]
lemma drop_vertex (w : WList α β) (hn : n ≤ w.length) : (w.drop n).vertex = w.vertex.drop n := by
  induction n generalizing w
  case zero => simp
  case succ n IH =>
    cases w with
    | nil => simp at hn
    | cons x e w =>
      simp only [cons_length, add_le_add_iff_right, drop_cons_succ, cons_vertex,
        drop_succ_cons] at hn ⊢
      exact IH _ hn

@[simp]
lemma drop_edge (w : WList α β) (n : ℕ) : (w.drop n).edge = w.edge.drop n := by
  match w, n with
  | nil x, n => simp
  | cons x e w, 0 => simp
  | cons x e w, n + 1 => simp [w.drop_edge n]

lemma drop_concat_comm {w : WList α β} {n} (hn : n ≤ w.length) :
    (w.concat e x).drop n = (w.drop n).concat e x := by
  match w, n with
  | _, 0 => simp
  | .nil u_1, n_2 + 1 => simp at hn
  | .cons v f w, n + 1 =>
    simp only [cons_concat, drop_cons_succ]
    simp only [cons_length, add_le_add_iff_right] at hn
    exact w.drop_concat_comm hn

-- @[simp]
-- lemma drop_concat (w : WList α β) (e : β) (x : α) (n : ℕ) :
--     (w.concat e x).drop n = if n ≤ w.length then w.drop n else nil x := by
--   split_ifs with h
--   · induction n generalizing w
--     case zero => simp
--     case succ n IH =>
--       cases w with
--       | nil => simp at h
--       | cons u f w =>
--         simp only [drop_cons_succ, cons_concat, cons_length, Nat.add_le_add_iff_right] at h ⊢
--         rw [IH _ h]
--   · rw [drop_eq_nil_of_length_le]
--     simp only [concat_length, not_le] at h
--     omega

@[simp]
lemma drop_append_length (w₁ w₂ : WList α β) : (w₁ ++ w₂).drop w₁.length = w₂ := by
  match w₁ with
  | .nil u => simp
  | .cons u e w =>
    simp only [cons_append, cons_length, drop_cons_succ]
    exact w.drop_append_length w₂

-- @[simp]
-- lemma drop_append (w₁ w₂ : WList α β) (n : ℕ) :
--     (w₁ ++ w₂).drop n = if n ≤ w₁.length then w₁.drop n ++ w₂ else w₂.drop (n - w₁.length) := by
--   split_ifs with h
--   · induction n generalizing w₁
--     case zero => simp
--     case succ n IH =>
--       cases w₁ with
--       | nil => simp
--       | cons x e w₁ =>
--         simp only [drop_cons_succ, cons_append, cons_length, Nat.add_le_add_iff_right] at h ⊢
--         rw [IH _ h]
--   · induction w₁ generalizing n
--     case nil => simp
--     case cons x e w₁ ih =>
--       simp only [cons_append, cons_length, drop_cons_succ]
--       have : n > w₁.length + 1 := by omega
--       rw [ih (by omega)]
--       simp [Nat.sub_add_eq]

@[simp]
lemma drop_drop (w : WList α β) (m n : ℕ) : (w.drop n).drop m = w.drop (m + n) := by
  match w, n, m with
  | nil x, n, m => simp
  | cons x e w, 0, m => simp
  | cons x e w, n + 1, m =>
    rw [← add_assoc]
    simp [w.drop_drop m n]

-- lemma take_reverse (w : WList α β) (n : ℕ) :
--     (w.reverse).take n = (w.drop ((w.length + 1) - n)).reverse := by
--   match w, n with
--   | nil x, n => simp
--   | cons x e w, 0 => simp
--   | cons x e w, n + 1 => simp [w.take_reverse n]

@[simp]
lemma take_drop (w : WList α β) (n : ℕ) : w.take n ++ w.drop n = w := by
  match w, n with
  | nil x, n => simp
  | cons x e w, 0 => simp
  | cons x e w, n + 1 => simp [w.take_drop n]

@[simp]
lemma dropLast_take {w : WList α β} {n} (hn : n ≤ w.length) :
    (w.take n).dropLast = w.take (n - 1) := by
  match w, n with
  | nil x, _ => simp
  | cons x e w, 0 => simp
  | cons x e (nil y), n + 1 => simp_all
  | cons x e (cons y f w), 1 => simp
  | cons x e (cons y f w), n + 1 + 1 =>
    simp only [take_cons_succ, dropLast_cons_cons, add_tsub_cancel_right, cons.injEq, true_and]
    rw [← take_cons_succ, dropLast_take (by simpa using hn)]
    simp

@[simp]
lemma drop_one (w : WList α β) : w.drop 1 = w.tail := by
  cases w <;> simp [drop, tail]

@[simp]
lemma drop_length_eq_zero_iff (w : WList α β) (n : ℕ) : (w.drop n).length = 0 ↔ w.length ≤ n := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [drop_length, Nat.sub_eq_zero_iff_le] at h
    omega
  rw [drop_eq_nil_of_length_le h, nil_length]

-- lemma take_drop_comm (w : WList α β) (m n : ℕ) :
--     (w.take m).drop n = (w.drop n).take (m - n) := by
--   by_cases h : n ≤ m
--   · induction n generalizing m w
--     case zero => simp
--     case succ n IH =>
--       cases m with
--       | zero => simp at h
--       | succ m =>
--         cases w with
--         | nil => simp [take, drop]
--         | cons x e w =>
--           simp only [take_cons_succ, drop_cons_succ, cons_length]
--           have : n ≤ m := by omega
--           rw [IH _ this, drop_cons_succ, take_cons_succ]
--           simp [Nat.sub_succ]
--   · have hlt : m < n := by omega
--     rw [Nat.sub_eq_zero_of_le (by omega), take_zero]
--     by_cases hw : m ≤ w.length
--     · have : n > (w.take m).length := by
--         rw [take_length]
--         omega
--       rw [drop_eq_nil_of_length_le (by omega), take_last _ _ hw]
--       simp
--     · have : w.length < m := by omega
--       rw [take_eq_self_of_length_le (by omega), drop_eq_nil_of_length_le]
--       · simp
--       · omega

/-! ### Relationships with prefixUntil and suffixFrom -/

lemma IsPrefix.take_eq (h : w₁.IsPrefix w₂) : w₂.take w₁.length = w₁ := by
  induction h
  case nil => simp
  case cons x e w₁ w₂ h ih => simp [take_cons_succ, ih]

lemma take_isPrefix (w : WList α β) (n : ℕ) : (w.take n).IsPrefix w := by
  match w, n with
  | nil x, _ => simp
  | cons x e w, 0 => simp
  | cons x e w, n + 1 => apply (take_isPrefix w n).cons

@[simp]
lemma take_prefixUntilVertex [DecidableEq α] (hx : x ∈ w) :
    w.take (w.idxOf x) = w.prefixUntilVertex x := by
  induction w with
  | nil u =>
    simp only [mem_nil_iff] at hx
    subst hx
    simp [take, prefixUntilVertex, prefixUntil]
  | cons u e w ih =>
    obtain rfl | hne := eq_or_ne x u
    · simp [prefixUntilVertex, prefixUntil, idxOf_cons_self]
    · simp only [mem_cons_iff, hne, false_or] at hx
      simp only [idxOf_cons_ne hne.symm, take_cons_succ, prefixUntilVertex_cons_of_ne _ hne.symm,
        cons.injEq, true_and]
      exact ih hx

lemma IsPrefix.eq_take_length {w₁ w₂ : WList α β} (h : w₁.IsPrefix w₂) :
    w₁ = w₂.take w₁.length := match h with
  | .nil w => by simp
  | .cons x e w₁ w₂ h => by
    simp only [cons_length, take_cons_succ, cons.injEq, true_and]
    exact h.eq_take_length

lemma drop_isSuffix (w : WList α β) (n : ℕ) : (w.drop n).IsSuffix w := by
  match w, n with
  | nil x, _ => simp
  | cons x e w, 0 => simp
  | cons x e w, n + 1 => apply (drop_isSuffix w n).cons

@[simp]
lemma drop_suffixFromVertex [DecidableEq α] (hx : x ∈ w) :
    w.drop (w.idxOf x) = w.suffixFromVertex x := by
  induction w with
  | nil u =>
    simp only [mem_nil_iff] at hx
    subst hx
    simp [suffixFromVertex]
  | cons u e w ih =>
    obtain rfl | hne := eq_or_ne x u
    · simp [suffixFromVertex, idxOf_cons_self]
    · simp only [mem_cons_iff, hne, false_or] at hx
      simp only [drop_cons_succ, idxOf_cons_ne hne.symm, suffixFromVertex_cons_of_ne _ hne.symm]
      exact ih hx

lemma IsSuffix.eq_drop_length {w₁ w₂ : WList α β} (h : w₁.IsSuffix w₂) :
    w₁ = w₂.drop (w₂.length - w₁.length) := match h with
  | .nil w => by simp
  | .concat e x w₁ w₂ h => by
    simp only [concat_length, reduceSubDiff]
    rw [drop_concat_comm (by omega)]
    congr 1
    exact h.eq_drop_length

lemma drop_eq_suffixFromVertex_of_idxOf [DecidableEq α] (hx : x ∈ w) (hn : n = w.idxOf x) :
    w.drop n = w.suffixFromVertex x := by
  rw [hn, drop_suffixFromVertex hx]

@[simp]
lemma prefixUntilVertex_take [DecidableEq α] {w : WList α β} (hx : x ∈ w) {n} (hn : w.idxOf x ≤ n)
    (hn' : n ≤ w.length) : (w.take n).prefixUntilVertex x = w.prefixUntilVertex x := by
  match w, n with
  | nil x, n => simp
  | cons y e w, 0 =>
    simp only [nonpos_iff_eq_zero, idxOf_eq_zero_iff, first_cons] at hn
    simp [prefixUntilVertex, hn.symm]
  | cons y e w, n + 1 =>
    simp_all only [mem_cons_iff, cons_length, add_le_add_iff_right, take_cons_succ,
      prefixUntilVertex_cons]
    split_ifs with hyx
    · subst y
      simp
    simp only [cons.injEq, true_and]
    apply prefixUntilVertex_take (hx.resolve_left (hyx ·.symm)) ?_ (by omega)
    simpa [idxOf_cons_ne hyx] using hn

-- @[simp]
-- lemma suffixFromVertex_drop [DecidableEq α] {w : WList α β} (hx : x ∈ w) (hn : n ≤ w.idxOf x) :
--     (w.drop n).suffixFromVertex x = w.suffixFromVertex x := by
--   match w, n with
--   | nil x, n => simp
--   | cons y e w, 0 => simp
--   | cons y e w, n + 1 =>
--     simp_all only [mem_cons_iff, suffixFromVertex, drop_cons_succ, suffixFrom_cons]
--     split_ifs with hyx
--     · subst y
--       simp

-- lemma drop_suffixFrom [DecidablePred P] (w : WList α β) (h : ∃ u ∈ w, P u) :
--     w.drop ((w.length + 1) - (w.suffixFrom P).length) = w.suffixFrom P := by
--   -- This requires more careful calculation of the index
--   sorry

-- lemma prefixUntil_take [DecidablePred P] (w : WList α β) (n : ℕ) (hn : n ≤ w.length)
--     (h : ∃ u ∈ w.take n, P u) :
--     (w.take n).prefixUntil P = w.prefixUntil P := by
--   have hpfx := prefixUntil_isPrefix w P
--   have hpfx' := prefixUntil_isPrefix (w.take n) P
--   refine hpfx'.eq_of_length_ge ?_
--   rw [hpfx.length_le, take_length]
--   omega

-- lemma suffixFrom_drop [DecidablePred P] (w : WList α β) (n : ℕ) (hn : n ≤ w.length)
--     (h : ∃ u ∈ w.drop n, P u) :
--     (w.drop n).suffixFrom P = w.suffixFrom P := by
--   -- This requires showing that the first occurrence of P in w.drop n is the same as in w
--   sorry

-- @[simp]
-- lemma dropLast_prefixUntil [DecidablePred P] (w : WList α β) (hne : w.Nonempty)
--     (h : ∃ u ∈ w.dropLast, P u) :
--     (w.dropLast).prefixUntil P = w.prefixUntil P := by
--   have hpfx := prefixUntil_isPrefix w P
--   have hpfx' := prefixUntil_isPrefix w.dropLast P
--   refine hpfx'.eq_of_length_ge ?_
--   rw [hpfx.length_le, dropLast_length]
--   omega

-- @[simp]
-- lemma dropLast_suffixFrom [DecidablePred P] (w : WList α β) (hne : w.Nonempty)
--     (h : ∃ u ∈ w.dropLast, P u) :
--     (w.dropLast).suffixFrom P = w.suffixFrom P := by
--   -- This requires more careful handling
--   sorry

-- @[simp]
-- lemma prefixUntilVertex_dropLast [DecidableEq α] (w : WList α β) (x : α) (hx : x ∈ w.dropLast)
--     (hne : w.Nonempty) :
--     (w.dropLast).prefixUntilVertex x = w.prefixUntilVertex x := by
--   have hxw : x ∈ w := by
--     rw [mem_iff_eq_mem_dropLast_or_eq_last] at hx
--     exact hx.elim id (fun heq => heq ▸ last_mem)
--   rw [← take_prefixUntilVertex w x hxw, ← take_prefixUntilVertex w.dropLast x hx]
--   rw [take_dropLast]
--   exact hne.length_pos.le

-- @[simp]
-- lemma suffixFromVertex_dropLast [DecidableEq α] (w : WList α β) (x : α) (hx : x ∈ w.dropLast)
--     (hne : w.Nonempty) :
--     (w.dropLast).suffixFromVertex x = w.suffixFromVertex x := by
--   -- This requires showing the index is the same
--   sorry

lemma take_length_prefixUntilVertex [DecidableEq α] (hx : x ∈ w) :
    w.take (w.prefixUntilVertex x).length = w.prefixUntilVertex x := by
  rw [prefixUntilVertex_length hx, take_prefixUntilVertex hx]

lemma idxOf_eq_length_prefixUntilVertex [DecidableEq α] (hx : x ∈ w) :
    w.idxOf x = (w.prefixUntilVertex x).length := by
  induction w with | nil => simp_all [prefixUntilVertex] | cons u e w ih =>
  obtain rfl | hu := eq_or_ne x u
  · simp [prefixUntilVertex]
  simp only [mem_cons_iff, hu, false_or] at hx
  simp only [hx, prefixUntilVertex, forall_const, ne_eq, hu.symm, not_false_eq_true, idxOf_cons_ne,
    prefixUntil_cons, ↓reduceIte, cons_length, Nat.add_right_cancel_iff] at ih ⊢
  assumption

end drop

section dedup

variable [DecidableEq α]

/-- Remove duplicate vertices from a `WList` to give a duplicate-free sublist. -/
def dedup : WList α β → WList α β
  | nil x => nil x
  | cons x e w =>
    have := (w.suffixFromVertex_isSuffix x).length_le
    if x ∈ w then dedup (w.suffixFromVertex x) else cons x e (dedup w)
  termination_by w => w.length

@[simp]
lemma dedup_nil (x : α) : (nil x (β := β)).dedup = nil x := by
  simp [dedup]

lemma dedup_cons_eq_ite (x : α) (e : β) (w : WList α β) :
    (cons x e w).dedup = if x ∈ w then dedup (w.suffixFromVertex x) else cons x e w.dedup := by
  simp [dedup]

lemma dedup_cons_of_mem (hxw : x ∈ w) (e) : (cons x e w).dedup = dedup (w.suffixFromVertex x) := by
  simp [dedup, hxw]

lemma dedup_cons_of_notMem (hxw : x ∉ w) (e) :
    (cons x e w).dedup = cons x e (dedup w) := by
  simp [dedup, hxw]

@[simp]
lemma dedup_first (w : WList α β) : w.dedup.first = w.first := by
  cases w with
  | nil => simp
  | cons u e w =>
    have hle := (w.suffixFromVertex_isSuffix u).length_le
    simp only [dedup, apply_ite, first_cons, ite_eq_right_iff]
    rw [dedup_first]
    exact fun huw ↦ suffixFrom_prop_first (P := (· = u)) ⟨_, huw, rfl⟩
termination_by w.length

@[simp]
lemma dedup_last (w : WList α β) : w.dedup.last = w.last := by
  cases w with
  | nil => simp
  | cons u e w =>
    have hle := (w.suffixFromVertex_isSuffix u).length_le
    simp only [last_cons]
    by_cases huw : u ∈ w
    · rw [dedup_cons_of_mem huw, dedup_last, suffixFromVertex_last]
    rw [dedup_cons_of_notMem huw, last_cons, dedup_last]
termination_by w.length

lemma dedup_isSublist (w : WList α β) : w.dedup.IsSublist w := by
  cases w with
  | nil => simp
  | cons u e w =>
    have hle := (w.suffixFromVertex_isSuffix u).length_le
    by_cases huw : u ∈ w
    · rw [dedup_cons_of_mem huw]
      refine (w.suffixFromVertex _).dedup_isSublist.trans ?_
      exact (w.suffixFromVertex_isSuffix _).isSublist.trans <| by simp
    rw [dedup_cons_of_notMem huw]
    exact (dedup_isSublist w).cons₂ _ _ (by simp)
termination_by w.length

lemma dedup_vertex_nodup (w : WList α β) : w.dedup.vertex.Nodup := by
  cases w with
  | nil => simp
  | cons u e w =>
    have hle := (w.suffixFromVertex_isSuffix u).length_le.eq_or_lt
    by_cases huw : u ∈ w
    · rw [dedup_cons_of_mem huw]
      apply dedup_vertex_nodup
    simp only [dedup_cons_of_notMem huw, cons_vertex, nodup_cons, mem_vertex]
    exact ⟨mt w.dedup_isSublist.sublist.mem huw, w.dedup_vertex_nodup⟩
termination_by w.length

lemma dedup_eq_self (hw : w.vertex.Nodup) : w.dedup = w := by
  induction w with
  | nil => simp
  | cons u e w ih =>
    simp only [cons_vertex, nodup_cons, mem_vertex] at hw
    rw [dedup_cons_of_notMem hw.1, ih hw.2]

lemma dedup_eq_self_iff : w.dedup = w ↔ w.vertex.Nodup :=
  ⟨fun h ↦ by rw [← h]; exact dedup_vertex_nodup w, dedup_eq_self⟩

end dedup

/-- If a proposition `P` holds at the first vertex of `w` but not the last,
then `w` has a directed edge `e` from `x` to `y` such that `x` satisfies `P` but `y` doesn't. -/
lemma exists_dInc_prop_not_prop {P : α → Prop} (hfirst : P w.first) (hlast : ¬ P w.last) :
    ∃ e x y, w.DInc e x y ∧ P x ∧ ¬ P y := by
  induction w with
  | nil => simp_all
  | cons u e w ih =>
    by_cases hP : P w.first
    · obtain ⟨f, x, y, h, hx, hy⟩ := ih hP (by simpa using hlast)
      exact ⟨f, x, y, h.cons .., hx, hy⟩
    exact ⟨e, u, w.first, DInc.cons_left .., hfirst, hP⟩

lemma exists_dInc_not_prop_prop {P : α → Prop} (hfirst : ¬ P w.first) (hlast : P w.last) :
    ∃ e x y, w.DInc e x y ∧ ¬ P x ∧ P y := by
  obtain ⟨e, x, y, h, hx, hy⟩ := exists_dInc_prop_not_prop (P := fun x ↦ ¬ P x) hfirst (by simpa)
  exact ⟨e, x, y, h, hx, by simpa using hy⟩

lemma exists_isLink_prop_not_prop {P : α → Prop} (hxw : x ∈ V(w)) (hT : P x) (hyw : y ∈ V(w))
    (hF : ¬ P y) : ∃ e x y, w.IsLink e x y ∧ P x ∧ ¬ P y := by
  obtain ⟨w₀, hsub, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := exists_sublist_of_mem_mem hxw hyw
  · obtain ⟨e, x, y, h, hx, hy⟩ := exists_dInc_prop_not_prop hT hF
    exact ⟨e, x, y, (h.of_isSublist hsub).isLink, hx, hy⟩
  · rw [← w₀.reverse_reverse] at hF hT
    rw [reverse_first] at hF
    rw [reverse_last] at hT
    obtain ⟨e, x, y, h, hx, hy⟩ := exists_dInc_prop_not_prop hT hF
    refine ⟨e, x, y, ?_, hx, hy⟩
    rw [dInc_reverse_iff] at h
    exact (h.of_isSublist hsub).isLink.symm

section deloop

variable [DecidableEq α]

/-- Remove loops from a `WList` by removing edges where the source equals the target. -/
def deloop : WList α β → WList α β
| nil x => nil x
| cons x e w =>
  if x = w.first then deloop w else cons x e (deloop w)

@[simp]
lemma deloop_nil (x : α) : (nil x (β := β)).deloop = nil x := by
  simp [deloop]

@[grind =]
lemma deloop_cons_eq_ite (x : α) (e : β) (w : WList α β) :
    (cons x e w).deloop = if x = w.first then deloop w else cons x e w.deloop := by
  simp [deloop]

@[simp]
lemma deloop_cons_of_eq_first (hxw : x = w.first) (e) :
    (cons x e w).deloop = deloop w := by
  simp [deloop, hxw]

@[simp]
lemma deloop_cons_of_ne_first (hxw : x ≠ w.first) (e) :
    (cons x e w).deloop = cons x e (deloop w) := by
  simp [deloop, hxw]

@[simp]
lemma deloop_first (w : WList α β) : w.deloop.first = w.first := by
  cases w with
  | nil => simp
  | cons u e w =>
    simp only [deloop, apply_ite, first_cons, ite_eq_right_iff]
    intro heq
    rw [deloop_first, heq]

@[simp]
lemma deloop_last (w : WList α β) : w.deloop.last = w.last := by
  cases w with
  | nil => simp
  | cons u e w =>
    simp only [last_cons]
    by_cases heq : u = w.first
    · rw [deloop_cons_of_eq_first heq, deloop_last]
    rw [deloop_cons_of_ne_first heq, last_cons, deloop_last]

lemma deloop_isSublist (w : WList α β) : w.deloop.IsSublist w := by
  cases w with
  | nil => simp
  | cons u e w =>
    by_cases heq : u = w.first
    · rw [deloop_cons_of_eq_first heq]
      exact w.deloop_isSublist.trans (by simp)
    rw [deloop_cons_of_ne_first heq]
    exact (deloop_isSublist w).cons₂ _ _ (by simp)

@[simp]
lemma deloop_vertexSet (w : WList α β) : V(w.deloop) = V(w) := by
  induction w with
  | nil => simp
  | cons u e w ih =>
    simp only [deloop_cons_eq_ite, apply_ite, cons_vertexSet]
    split_ifs with hu
    · subst u
      simpa
    simp [ih]

@[simp]
lemma mem_deloop_iff : x ∈ w.deloop ↔ x ∈ w := by
  rw [← mem_vertexSet_iff, deloop_vertexSet, mem_vertexSet_iff]

@[gcongr]
lemma deloop_isSublist_mono (h : w₁.IsSublist w₂) : w₁.deloop.IsSublist w₂.deloop := by
  induction h with
  | nil h => simpa
  | cons x e h ih =>
    rw [deloop_cons_eq_ite]
    split_ifs with hx
    · subst x
      exact ih
    exact ih.cons x e
  | cons₂ x e h h_eq ih =>
    rename_i w₁ w₂
    simp_rw [deloop_cons_eq_ite]
    obtain rfl | hx := eq_or_ne x w₁.first
    · simpa [h_eq]
    simp only [hx, ↓reduceIte, h_eq ▸ hx]
    apply ih.cons₂ ..
    simpa

lemma dedup_isSublist_deloop (w : WList α β) : w.dedup.IsSublist w.deloop := by
  match w with
  | nil x => simp
  | cons u e w' =>
    by_cases huw : u ∈ w'
    · have hle := (w'.suffixFromVertex_isSuffix u).length_le
      rw [dedup_cons_of_mem huw, deloop_cons_eq_ite]
      split_ifs with heq
      · subst heq
        exact (w'.suffixFromVertex w'.first).dedup_isSublist_deloop.trans
          (deloop_isSublist_mono (w'.suffixFromVertex_isSuffix _).isSublist)
      exact (w'.suffixFromVertex u).dedup_isSublist_deloop.trans
      <| (deloop_isSublist_mono (w'.suffixFromVertex_isSuffix _).isSublist).cons ..
    rw [dedup_cons_of_notMem huw, deloop_cons_eq_ite]
    split_ifs with heq
    · subst heq
      exact absurd (w'.deloop_first ▸ first_mem : w'.first ∈ w'.deloop) (mt mem_deloop_iff.mp huw)
    exact w'.dedup_isSublist_deloop.cons₂ _ _ (by simp)
termination_by w.length

end deloop

section noLoop

/-- A `WList` has no loops if no edge connects a vertex to the next vertex being itself. -/
def NoLoop : WList α β → Prop
  | nil _ => True
  | cons x _ w => x ≠ w.first ∧ w.NoLoop

@[simp]
lemma noLoop_nil (x : α) : (nil x (β := β)).NoLoop := by
  simp [NoLoop]

@[simp]
lemma noLoop_cons (x : α) (e : β) (w : WList α β) :
    (cons x e w).NoLoop ↔ x ≠ w.first ∧ w.NoLoop := by
  simp [NoLoop]

lemma deloop_noLoop [DecidableEq α] (w : WList α β) : w.deloop.NoLoop := by
  cases w with
  | nil => simp
  | cons u e w =>
    by_cases heq : u = w.first
    · rw [deloop_cons_of_eq_first heq]
      apply deloop_noLoop
    simp only [deloop_cons_of_ne_first heq, noLoop_cons, deloop_first, ne_eq]
    exact ⟨heq, w.deloop_noLoop⟩

@[simp]
lemma deloop_eq_self [DecidableEq α] (hw : w.NoLoop) : w.deloop = w := by
  induction w with
  | nil => simp
  | cons u e w ih =>
    simp only [noLoop_cons] at hw
    rw [deloop_cons_of_ne_first hw.1, ih hw.2]

@[simp]
lemma deloop_eq_self_iff [DecidableEq α] : w.deloop = w ↔ w.NoLoop :=
  ⟨fun h ↦ by rw [← h]; exact deloop_noLoop w, deloop_eq_self⟩

@[simp]
lemma noLoop_of_vertex_nodup (hw : w.vertex.Nodup) : w.NoLoop := by
  induction w with
  | nil => simp
  | cons x e w ih =>
    simp only [cons_vertex, nodup_cons] at hw
    refine ⟨?_, ih hw.2⟩
    rintro rfl
    exact hw.1 w.first_mem

lemma noLoop_iff_ne_of_dInc : w.NoLoop ↔ ∀ e x y, w.DInc e x y → x ≠ y := by
  refine ⟨fun h e x y hex ↦ ?_, fun h ↦ ?_⟩
  · induction hex with simp_all
  induction w with
  | nil u => simp
  | cons u e w ih =>
    simp only [noLoop_cons, ne_eq, h e u w.first (by simp), not_false_eq_true, true_and]
    exact ih fun e x y hex ↦ h e x y (by simp [hex])

lemma noLoop_iff_not_dInc : w.NoLoop ↔ ∀ e x, ¬ w.DInc e x x := by
  rw [noLoop_iff_ne_of_dInc]
  grind

@[simp]
lemma NoLoop.not_dInc (h : w.NoLoop) (e : β) (x : α) : ¬ w.DInc e x x := by
  rw [noLoop_iff_not_dInc] at h
  exact h e x

lemma noLoop_iff_ne_of_isLink : w.NoLoop ↔ ∀ e x y, w.IsLink e x y → x ≠ y := by
  refine ⟨fun h e x y hxy ↦ ?_, fun h ↦ ?_⟩
  · induction hxy with simp_all [eq_comm]
  induction w with
  | nil u => simp
  | cons u e w ih =>
    simp only [noLoop_cons, ne_eq, h e u w.first (DInc.isLink <| by simp), not_false_eq_true,
      true_and]
    exact ih fun e x y hxy ↦ h e x y <| hxy.cons ..

lemma noLoop_iff_not_isLink : w.NoLoop ↔ ∀ e x, ¬ w.IsLink e x x := by
  rw [noLoop_iff_ne_of_isLink]
  grind

@[simp]
lemma NoLoop.not_isLink (h : w.NoLoop) (e : β) (x : α) : ¬ w.IsLink e x x := by
  rw [noLoop_iff_not_isLink] at h
  exact h e x

end noLoop

section edgeRemove

variable [DecidablePred (· ∈ F)]

/-- Remove edges from a `WList` that belong to a given edge set `F`. -/
def edgeRemove (F : Set β) [DecidablePred (· ∈ F)] : WList α β → WList α β
  | nil x => nil x
  | cons x e w => if e ∈ F then edgeRemove F w else cons x e (edgeRemove F w)

@[simp]
lemma edgeRemove_nil : (nil x (β := β)).edgeRemove F = nil x := rfl

@[grind =]
lemma edgeRemove_cons (x : α) (e : β) (w : WList α β) :
    (cons x e w).edgeRemove F = if e ∈ F then edgeRemove F w else cons x e (w.edgeRemove F) :=
  rfl

@[simp]
lemma edgeRemove_cons_of_mem (heF : e ∈ F) (x : α) (w : WList α β) :
    (cons x e w).edgeRemove F = w.edgeRemove F := by
  simp [edgeRemove_cons, heF]

@[simp]
lemma edgeRemove_cons_of_notMem (heF : e ∉ F) (x : α) (w : WList α β) :
    (cons x e w).edgeRemove F = cons x e (w.edgeRemove F) := by
  simp [edgeRemove_cons, heF]

@[simp]
lemma edgeRemove_empty (w : WList α β) : w.edgeRemove (∅ : Set β) = w := by
  induction w with
  | nil => simp
  | cons u e w ih => simp [ih]

lemma edgeRemove_notMem_edge (w : WList α β) (e : β) (he : e ∈ F) : e ∉ (w.edgeRemove F).edge := by
  induction w with
  | nil => simp
  | cons u f w ih =>
    by_cases hf : f ∈ F
    · rwa [edgeRemove_cons_of_mem hf]
    simp only [cons_edge, List.mem_cons, edgeRemove_cons_of_notMem hf]
    rintro (rfl | hmem)
    · exact hf he
    · exact ih hmem

@[simp]
lemma edgeRemove_edgeRemove (F F' : Set β) [DecidablePred (· ∈ F)]
    [DecidablePred (· ∈ F')] [DecidablePred (· ∈ F ∪ F')] (w : WList α β) :
    (w.edgeRemove F).edgeRemove F' = w.edgeRemove (F ∪ F') := by
  induction w with
  | nil => simp
  | cons u e w ih =>
    simp only [edgeRemove_cons, Set.mem_union]
    by_cases he : e ∈ F
    · simp [he, ih]
    by_cases he' : e ∈ F'
    · simp [he, he', ih]
    simp [he, he', ih]

@[simp]
lemma edgeRemove_last (w : WList α β) : (w.edgeRemove F).last = w.last := by
  induction w with
  | nil => simp
  | cons u e w ih =>
    rw [edgeRemove_cons]
    split_ifs with he <;> simp [ih]

@[simp]
lemma edgeRemove_edge (w : WList α β) : (w.edgeRemove F).edge = w.edge.filter (· ∉ F) := by
  induction w with
  | nil => simp
  | cons u e w ih =>
    rw [edgeRemove_cons]
    split_ifs with he <;> simp [ih, he]

@[simp]
lemma mem_edgeRemove_edge_iff : e ∈ (w.edgeRemove F).edge ↔ e ∈ w.edge ∧ e ∉ F := by
  rw [edgeRemove_edge]
  simp

@[simp]
lemma edgeRemove_edgeSet (w : WList α β) : E(w.edgeRemove F) = E(w) \ F := by
  ext e
  simp

lemma edgeRemove_append_eq_right (w₁ w₂ : WList α β) (hw₁ : E(w₁) ⊆ F) :
    (w₁ ++ w₂).edgeRemove F = w₂.edgeRemove F := by
  induction w₁ with
  | nil => simp
  | cons u e w ih => grind [cons_append, cons_edgeSet]

end edgeRemove

end WList
