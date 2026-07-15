import Matroid.Graph.WList.TakeDrop.Defs

open Set Function List Nat WList

variable {α β : Type*} {u v x y z : α} {e e' f g : β} {S T U: Set α}
  {F F' : Set β} {w w' w₀ w₁ w₂ w₃ l l₁ l₂ l₃ : WList α β}

namespace WList

variable {P : α → Prop} [DecidablePred P]
variable {n m : ℕ}
@[simp]
lemma tail_last (w : WList α β) : w.tail.last = w.last := by
  induction w with simp

lemma tail_edge (w : WList α β) : w.tail.edge = w.edge.tail := by
  induction w with simp

@[simp, grind =]
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
lemma Nonempty.vertex_tail (hw : w.Nonempty) : w.tail.vertex = w.vertex.tail := by
  induction w with simp_all

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

lemma mem_iff_eq_vertex_first_or_mem_tail : x ∈ w ↔ x = w.first ∨ x ∈ w.vertex.tail := by
  refine ⟨by induction w with simp_all, ?_⟩
  rintro (rfl | hx)
  · simp
  exact mem_of_mem_tail hx

lemma IsSublist.le_tail_of_ne_first {w₀} (h : w₀ ≤ w) (hne : w₀.first ≠ w.first) : w₀ ≤ w.tail := by
  induction h with
  | nil h =>
    obtain rfl | hx := mem_iff_eq_first_or_mem_tail.mp h
    · exact (hne rfl).elim
    · exact IsSublist.nil hx
  | cons x e h ih => exact h
  | cons₂ x e h h_eq ih => simp at hne

lemma Nonempty.tail_concat (hw : w.Nonempty) (e : β) (x : α) :
    (w.concat e x).tail = w.tail.concat e x := by
  induction w with simp_all

lemma tail_append (hw₁ : w₁.Nonempty) (w₂ : WList α β) : (w₁ ++ w₂).tail = w₁.tail ++ w₂ := by
  induction w₁ with simp_all

lemma Nonempty.tail_isLink_iff (hw : w.Nonempty) (hnd : w.edge.Nodup) :
    w.tail.IsLink f x y ↔ w.IsLink f x y ∧ ¬f = hw.firstEdge := by
  cases hw with | cons u e w =>
  simp only [tail_cons, Nonempty.firstEdge_cons]
  have ⟨hew, hnd⟩ : e ∉ w.edge ∧ w.edge.Nodup := by simpa using hnd
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
    rw [hnem.tail_concat]
    exact Or.inr <| ⟨by simp, h.2.concat ..⟩

@[simp]
lemma tail_eq_self_iff (w : WList α β) : w.tail = w ↔ w.Nil := by
  match w with
  | .nil u => simp
  | .cons u e (nil v) => simp
  | .cons u e (cons v f w) =>
    simp only [tail_cons, cons.injEq, not_nil_cons, iff_false, not_and]
    rintro rfl rfl h
    simpa using congr_arg WList.length h

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
      rw [reverse_cons, Nonempty.tail_concat, ih, ← reverse_cons, dropLast_cons_cons]
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
lemma Nonempty.vertex_dropLast (h : w.Nonempty) : w.dropLast.vertex = w.vertex.dropLast := by
  rw [← reverse_tail_reverse, reverse_vertex, Nonempty.vertex_tail (by simpa)]
  simp

@[simp]
lemma dropLast_edge (w : WList α β) : (w.dropLast).edge = w.edge.dropLast := by
  rw [← reverse_tail_reverse, reverse_edge, tail_edge, reverse_edge, ← dropLast_reverse,
    List.reverse_reverse]

@[simp, grind =]
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

lemma mem_iff_eq_mem_vertex_dropLast_or_eq_last : u ∈ w ↔ u ∈ w.vertex.dropLast ∨ u = w.last := by
  rw [← mem_reverse, mem_iff_eq_vertex_first_or_mem_tail, or_comm, reverse_vertex, tail_reverse,
    List.mem_reverse, reverse_first]

lemma eq_last_or_mem_dropLast (h : x ∈ w) : x = w.last ∨ x ∈ w.dropLast := by
  grind [mem_iff_eq_mem_dropLast_or_eq_last]

lemma IsSublist.le_dropLast_of_ne_last (h : w₀ ≤ w) (hne : w₀.last ≠ w.last) : w₀ ≤ w.dropLast := by
  induction h with
  | nil hx =>
    obtain hx | hx := mem_iff_eq_mem_dropLast_or_eq_last.mp hx
    · exact IsSublist.nil hx
    · exact (hne hx).elim
  | @cons x e w₁ w₂ h ih =>
    have hl : w₁.last ≠ w₂.last := by simpa [last_cons] using hne
    cases w₂ with
    | nil y =>
      obtain rfl := isSublist_nil_iff.mp h
      simp at hne
    | cons y f w₂' =>
      rw [Nonempty.dropLast_cons (by simp)]
      exact le_trans (ih hl) (isSublist_cons_self ..)
  | @cons₂ x e w₁ w₂ h h_eq ih =>
    have hl : w₁.last ≠ w₂.last := by simpa [last_cons] using hne
    cases w₂ with
    | nil y =>
      obtain rfl := isSublist_nil_iff.mp h
      simp at hne
    | cons y f w₂' =>
      rw [Nonempty.dropLast_cons (by simp)]
      exact IsSublist.cons₂ x e (ih hl) (by simpa [dropLast_first] using h_eq)

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

@[simp]
lemma dropLast_eq_self_iff (w : WList α β) : w.dropLast = w ↔ w.Nil := by
  match w with
  | .nil u => simp
  | .cons u e (nil v) => simp
  | .cons u e (cons v f w) =>
    simpa [not_nil_cons, iff_false, ne_eq] using (cons v f w).dropLast_eq_self_iff

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

@[gcongr] lemma IsPrefix.take (h : w₁.IsPrefix w₂) (n : ℕ) : (w₁.take n).IsPrefix (w₂.take n) := by
  induction h generalizing n with
  | nil w => simp_rw [take_nil, nil_isPrefix_iff, take_first]
  | cons x e w₁ w₂ h ih =>
    cases n
    · simp
    simp only [take_cons_succ]
    exact (ih _).cons x e

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

lemma drop_drop_comm (m n : ℕ) : (w.drop m).drop n = (w.drop n).drop m := by
  rw [drop_drop, drop_drop, Nat.add_comm]

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

lemma drop_isSuffix_drop {m n : ℕ} (hmn : m ≤ n) : (w.drop n).IsSuffix (w.drop m) := by
  rw [← Nat.add_sub_of_le hmn, Nat.add_comm]
  simpa [drop_drop, drop_drop_comm] using drop_isSuffix (w.drop m) (n - m)

lemma IsSuffix.eq_drop_length {w₁ w₂ : WList α β} (h : w₁.IsSuffix w₂) :
    w₁ = w₂.drop (w₂.length - w₁.length) := match h with
  | .nil w => by simp
  | .concat e x w₁ w₂ h => by
    simp only [concat_length, reduceSubDiff]
    rw [drop_concat_comm (by omega)]
    congr 1
    exact h.eq_drop_length

@[gcongr] lemma IsPrefix.drop (h : w₁.IsPrefix w₂) {n : ℕ} (hn : n ≤ w₁.length) :
    (w₁.drop n).IsPrefix (w₂.drop n) := by
  induction h generalizing n with
  | nil w =>
    match n with
    | 0 => simp
    | n + 1 => grind [nil_length]
  | cons x e w₁ w₂ h ih =>
    match n with
    | 0 => simpa [drop_zero] using h.cons x e
    | m + 1 =>
      simp only [drop_cons_succ]
      exact ih (by simpa using hn)

@[gcongr] lemma IsSuffix.drop (h : w₁.IsSuffix w₂) (n : ℕ) : (w₁.drop n).IsSuffix (w₂.drop n) := by
  rw [h.eq_drop_length, drop_drop]
  exact drop_isSuffix_drop (w := w₂) (m := n) (n := n + (w₂.length - w₁.length)) (le_add_right n _)

@[gcongr] lemma IsInfix.drop (h : w₁.IsInfix w₂) {n : ℕ} (hn : n ≤ w₁.length) :
    (w₁.drop n).IsInfix (w₂.drop n) := by
  rw [isInfix_iff_exists_isPrefix_isSuffix] at h ⊢
  obtain ⟨w, h₁, h₂⟩ := h
  use w.drop n, h₁.drop hn, h₂.drop n

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

lemma idxOf_eq_length_prefixUntilVertex [DecidableEq α] (hx : x ∈ w) :
    w.idxOf x = (w.prefixUntilVertex x).length := by
  induction w with | nil => simp_all [prefixUntilVertex] | cons u e w ih =>
  obtain rfl | hu := eq_or_ne x u
  · simp [prefixUntilVertex]
  simp only [mem_cons_iff, hu, false_or] at hx
  simp only [hx, prefixUntilVertex, forall_const, ne_eq, hu.symm, not_false_eq_true, idxOf_cons_ne,
    prefixUntil_cons, ↓reduceIte, cons_length, Nat.add_right_cancel_iff] at ih ⊢
  assumption

end WList
