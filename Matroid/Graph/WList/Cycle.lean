import Matroid.Graph.WList.Sublist

variable {α β : Type*} {x y z u v : α} {e f : β} {w w₁ w₂ : WList α β} (m n : ℕ)

open Set WList


namespace WList

/-- A `WList` is closed if its first and last entries are equal. -/
def IsClosed (w : WList α β) : Prop := w.first = w.last

lemma IsClosed.eq (h : w.IsClosed) : w.first = w.last := h

@[simp]
lemma nil_isClosed (x : α) : (nil x (β := β)).IsClosed := rfl

@[simp]
lemma cons_isClosed_iff : (cons x e w).IsClosed ↔ x = w.last := by
  simp [IsClosed]

@[simp]
lemma concat_isClosed_iff : (w.concat e x).IsClosed ↔ x = w.first := by
  simp [IsClosed, eq_comm]

lemma IsClosed.vertexSet_tail (h : w.IsClosed) : V(w.tail) = V(w) := by
  induction w with simp_all

lemma IsClosed.reverse (h : w.IsClosed) : w.reverse.IsClosed := by
  simp_all [IsClosed]

@[simp]
lemma reverse_isClosed_iff : w.reverse.IsClosed ↔ w.IsClosed := by
  simp [IsClosed, eq_comm]

lemma IsClosed.vertexSet_dropLast (h : w.IsClosed) : V(w.dropLast) = V(w) := by
  rw [← reverse_tail_reverse, reverse_vertexSet, h.reverse.vertexSet_tail, reverse_vertexSet]

lemma IsClosed.mem_tail_iff (h : w.IsClosed) : x ∈ w.tail ↔ x ∈ w := by
  rw [← mem_vertexSet_iff, h.vertexSet_tail, mem_vertexSet_iff]

lemma IsClosed.mem_dropLast (h : w.IsClosed) : x ∈ w.dropLast ↔ x ∈ w := by
   rw [← mem_vertexSet_iff, h.vertexSet_dropLast, mem_vertexSet_iff]

lemma IsClosed.tail_dropLast (hw : w.IsClosed) : w.tail.dropLast = w.dropLast.tail := by
  refine (eq_or_ne w.length 1).elim (fun h1 ↦ ?_) WList.tail_dropLast
  cases w with
  | nil => simp
  | cons u e w => cases w with | nil => simpa [eq_comm, IsClosed] using hw | cons => simp at h1

lemma IsClosed.length_eq_one_iff (hw : w.IsClosed) :
    w.length = 1 ↔ ∃ x e, w = cons x e (nil x) := by
  cases w with
  | nil => simp
  | cons u e w => cases w with simp_all

lemma IsClosed.dropLast_vertex_nodup (hw : w.IsClosed) (hw₁ : w.tail.vertex.Nodup) :
    w.dropLast.vertex.Nodup := by
  obtain ⟨x, rfl⟩ | hne := w.exists_eq_nil_or_nonempty
  · simp
  rw [tail_vertex hne] at hw₁
  rw [dropLast_vertex hne]
  apply hw₁.perm
  have htail : w.vertex.tail ≠ [] := by simpa [← List.length_pos_iff]
  have hdropLast : w.vertex.dropLast ≠ [] := by simpa [← List.length_pos_iff]
  rw [← w.vertex.tail.dropLast_append_getLast htail, ← w.vertex.dropLast.cons_head_tail hdropLast]
  simp only [List.getLast_tail, vertex_getLast, List.head_dropLast, vertex_head]
  rw [← hw, w.vertex.tail_dropLast]
  exact w.vertex.tail.dropLast.perm_append_singleton w.first

lemma IsClosed.idxOf_get [DecidableEq α] (hw : w.IsClosed) (hw₁ : w.tail.vertex.Nodup) {n}
    (hn : n < w.length) : w.idxOf (w.get n) = n := by
  have hge : n ≤ w.dropLast.length := by
    rw [w.dropLast_length]
    omega
  rw [← w.dropLast_isPrefix.get_eq_of_length_ge hge, ← w.dropLast_isPrefix.idxOf_eq_of_mem
  <| w.dropLast.get_mem n]
  exact WList.idxOf_get (hw.dropLast_vertex_nodup hw₁) hge


lemma IsClosed.idxOf_lt_length {C : WList α β} [DecidableEq α] (hC : C.IsClosed) (hx : x ∈ C)
    (hne : C.Nonempty) : C.idxOf x < C.length := by
  induction C using concat_induction with
  | nil u => simp at hne
  | concat w f y ih =>
  · obtain rfl : y = w.first := by simpa using hC
    have hxw : x ∈ w := by
      obtain hxw | rfl := mem_concat.1 hx
      · assumption
      simp
    grw [idxOf_concat_of_mem hxw, concat_length, idxOf_mem_le hxw]
    exact Nat.lt_add_one w.length



/-! ### Rotations -/

/-- Rotate a WList `n` vertices to the left.
This behaves badly (forgets the first vertex) if the list isn't closed. -/
protected def rotate : WList α β → ℕ → WList α β
  | w, 0 => w
  | nil x, _ => nil x
  | cons _ e w, n + 1 => (w.concat e w.first).rotate n

@[simp]
lemma rotate_zero (w : WList α β) : w.rotate 0 = w := by
  simp [WList.rotate]

@[simp]
lemma rotate_nil (x : α) (n : ℕ) : (nil x (β := β)).rotate n = nil x := by
  unfold WList.rotate
  aesop

@[simp]
lemma cons_rotate_one : (cons x e w).rotate 1 = w.concat e w.first := by
  simp [WList.rotate]

@[simp]
lemma rotate_cons_succ (w : WList α β) (x e) (n : ℕ) :
  (cons x e w).rotate (n+1) = (w.concat e w.first).rotate n := rfl

-- maybe we do need index-based take and drop instead of pred/vertex based take and drop...
lemma rotate_eq_append {w₁ w₂ : WList α β} (h : w₁.first = w₂.last) (h' : w₁.last = w₂.first) :
    (w₁ ++ w₂).rotate w₁.length = w₂ ++ w₁ := by
  match w₁ with
  | .nil u =>
    obtain rfl := by simpa using h
    simp
  | .cons u e w =>
    obtain rfl := by simpa using h
    simp only [cons_append, cons_length, rotate_cons_succ]
    rw [← WList.append_concat, ← WList.concat_append]
    apply rotate_eq_append <;> simp_all

@[simp]
lemma rotate_rotate : ∀ (w : WList α β) (m n : ℕ), (w.rotate m).rotate n = w.rotate (m + n)
  | nil x, _, _=> by simp
  | cons x e w, 0, n => by simp
  | cons x e w, m+1, n => by
    rw [rotate_cons_succ, rotate_rotate, Nat.add_right_comm, ← rotate_cons_succ]

lemma rotate_succ (w : WList α β) (n : ℕ) : w.rotate (n+1) = (w.rotate 1).rotate n := by
  rw [rotate_rotate, Nat.add_comm]

@[simp]
lemma length_rotate (w : WList α β) (n : ℕ) : (w.rotate n).length = w.length := by
  induction n generalizing w with
  | zero => simp
  | succ n IH =>
    rw [rotate_succ, IH]
    cases w with simp

@[simp]
lemma rotate_nonempty_iff : (w.rotate n).Nonempty ↔ w.Nonempty := by
  induction n generalizing w with
  | zero => simp
  | succ n IH =>
    rw [rotate_succ, IH]
    cases w with simp

lemma Nonempty.rotate (hw : w.Nonempty) (n : ℕ) : (w.rotate n).Nonempty := by
  simpa

@[simp]
lemma rotate_nontrivial_iff : (w.rotate n).Nontrivial ↔ w.Nontrivial := by
  rw [← one_lt_length_iff, length_rotate, one_lt_length_iff]

lemma Nontrivial.rotate (hw : w.Nontrivial) (n : ℕ) : (w.rotate n).Nontrivial := by
  exact (rotate_nontrivial_iff n).mpr hw

lemma rotate_firstEdge (n : ℕ) (hn : n < w.length) :
    have hne : w.Nonempty := length_pos_iff.1 <| (zero_le _).trans_lt hn
    have hn : n < w.edge.length := by simpa
    (hne.rotate n).firstEdge = w.edge[n] := by
  induction n generalizing w with
  | zero => cases w with | nil => simp at hn | cons => simp
  | succ n IH =>
    simp
    cases w with
    | nil => simp at hn
    | cons u e w =>
      simp_rw [add_comm (b := 1), ← rotate_rotate]
      simp only [cons_length, add_lt_add_iff_right] at hn
      rw [IH (hn.trans (by simp))]
      simp [concat_edge, add_comm (a := 1), hn]

lemma rotate_first (w : WList α β) (n : ℕ) (hn : n ≤ w.length) : (w.rotate n).first = w.get n := by
  induction n generalizing w with
  | zero => simp
  | succ n IH => cases w with
    | nil => simp
    | cons u e w =>
      simp only [cons_length, Nat.add_le_add_iff_right] at hn
      rwa [rotate_cons_succ, get_cons_add, IH _ (hn.trans (by simp)), get_concat]

lemma rotate_induction {motive : WList α β → Prop} (h0 : motive w)
    (rotate : ∀ ⦃w⦄, motive w → motive (w.rotate 1)) (n : ℕ) : motive (w.rotate n) := by
  induction n with | zero => simpa | succ n IH => rw [← rotate_rotate]; exact rotate IH

lemma IsClosed.rotate (hw : w.IsClosed) (n : ℕ) : (w.rotate n).IsClosed :=
  rotate_induction hw (by rintro (x | ⟨u, e, w⟩) hw <;> simp) n

@[simp]
lemma rotate_edge (w : WList α β) (n : ℕ) : (w.rotate n).edge = w.edge.rotate n := by
  suffices aux : ∀ (w : WList α β), (w.rotate 1).edge = w.edge.rotate 1 by induction n with
    | zero => simp | succ n IH => rw [← rotate_rotate, aux, ← List.rotate_rotate, IH]
  rintro (w | ⟨x, e, w⟩) <;> simp

@[simp]
lemma rotate_vertex_tail (w : WList α β) (n : ℕ) :
    (w.rotate n).tail.vertex = w.tail.vertex.rotate n := by
  suffices aux : ∀ (w : WList α β), (w.rotate 1).tail.vertex = w.tail.vertex.rotate 1 by
    induction n with
      | zero => simp
      | succ n IH => rw [← rotate_rotate, aux, ← List.rotate_rotate, IH]
  rintro (w | ⟨x, e, (w | ⟨y, f, w⟩)⟩) <;> simp

lemma IsClosed.rotate_vertexSet (hw : w.IsClosed) (n) : V(w.rotate n) = V(w) := by
  simp_rw [← (hw.rotate _).vertexSet_tail, WList.vertexSet, ← mem_vertex, rotate_vertex_tail,
    List.mem_rotate, mem_vertex]
  rw [← WList.vertexSet, hw.vertexSet_tail, WList.vertexSet]

lemma IsClosed.mem_rotate (hw : w.IsClosed) {n} : x ∈ w.rotate n ↔ x ∈ w := by
  rw [← mem_vertexSet_iff, hw.rotate_vertexSet, mem_vertexSet_iff]

lemma IsClosed.dInc_rotate (hw : w.IsClosed) (h : w.DInc e x y) (n) : (w.rotate n).DInc e x y := by
  induction n generalizing w with
  | zero => simpa
  | succ n IH =>
    rw [rotate_succ]
    apply IH (hw.rotate _)
    cases w with
    | nil => simp at h
    | cons u f w =>
      simp_all only [cons_isClosed_iff, dInc_cons_iff, rotate_cons_succ, rotate_zero]
      obtain rfl := hw
      obtain ⟨rfl, rfl, rfl⟩ | h := h
      · exact dInc_concat w f w.first
      exact h.concat ..

lemma IsClosed.isLink_rotate (hw : w.IsClosed) (h : w.IsLink e x y) (n) :
    (w.rotate n).IsLink e x y := by
  rw [isLink_iff_dInc] at ⊢ h
  exact h.elim (fun h' ↦ .inl (hw.dInc_rotate h' n)) (fun h' ↦ .inr (hw.dInc_rotate h' n))

@[simp]
lemma rotate_edgeSet (w : WList α β) (n) : E(w.rotate n) = E(w) := by
  simp [WList.edgeSet, rotate_edge]

@[simp]
lemma IsClosed.rotate_length (hw : w.IsClosed) : w.rotate w.length = w := by
  refine ext_vertex_edge ?_ (by rw [rotate_edge, ← length_edge, List.rotate_length])
  cases w with
  | nil => simp
  | cons u e w =>
    rw [cons_length, rotate_cons_succ, cons_vertex,
      ← ((w.concat e w.first).rotate w.length).vertex.cons_head_tail (by simp),
      ← tail_vertex (by simp), rotate_vertex_tail, vertex_head, rotate_first _ _ (by simp),
      get_concat _ _ _ rfl.le, get_length, eq_comm, show u = w.last from hw]
    convert rfl
    cases w with
    | nil => simp
    | cons y f w =>
      rw [first_cons, cons_concat, tail_cons, concat_vertex, cons_length, cons_vertex,
        ← w.length_vertex, List.rotate_append_length_eq]
      simp

lemma IsClosed.rotate_eq_mod (hw : w.IsClosed) (n) : w.rotate n = w.rotate (n % w.length) := by
  obtain ⟨x, rfl⟩ | hne := w.exists_eq_nil_or_nonempty
  · simp
  obtain hlt | hle := lt_or_ge n w.length
  · rw [Nat.mod_eq_of_lt hlt]
  obtain ⟨c, hc⟩ := exists_add_of_le hle
  have hc' : c < n := by
    have := hne.length_pos
    omega
  rw [hc, Nat.add_mod_left, ← rotate_rotate, hw.rotate_length, hw.rotate_eq_mod]

lemma IsClosed.rotate_first_mod (hw : w.IsClosed) (n) :
    (w.rotate n).first = w.get (n % w.length) := by
  obtain ⟨x, rfl⟩ | hne := w.exists_eq_nil_or_nonempty
  · simp
  rw [hw.rotate_eq_mod]
  exact w.rotate_first _ (Nat.mod_lt _ hne.length_pos).le

@[simp]
lemma rotate_idxOf_first [DecidableEq α] (hx : x ∈ w) : (w.rotate (w.idxOf x)).first = x := by
  rw [rotate_first _ _ (by simpa), get_idxOf _ hx]

lemma exists_rotate_first_eq (hx : x ∈ w) : ∃ n ≤ w.length, (w.rotate n).first = x := by
  classical
  exact ⟨w.idxOf x, by simpa, rotate_idxOf_first hx⟩

lemma IsClosed.exists_rotate_first_eq (hw : w.IsClosed) (hw' : w.Nonempty) (hx : x ∈ w) :
    ∃ n < w.length, (w.rotate n).first = x := by
  classical
  use w.idxOf x, ?_, rotate_idxOf_first hx
  refine lt_of_le_of_ne (by simpa) fun hlen ↦ ?_
  rw [idxOf_eq_length_prefixUntilVertex _ _ hx] at hlen
  have heqw := (w.prefixUntilVertex_isPrefix x).eq_of_length_ge hlen.ge
  have hlast : (w.prefixUntilVertex x).last = x := prefixUntil_prop_last (P := (· = x)) ⟨x, hx, rfl⟩
  rw [heqw, ← hw] at hlast
  have : w.prefixUntilVertex x = _ := prefixUntil_eq_nil hlast
  exact nil_not_nonempty (this ▸ heqw ▸ hw')

lemma exists_rotate_firstEdge_eq (hx : e ∈ w.edge) :
    ∃ n < w.length, ∃ (hw : w.Nonempty), (hw.rotate n).firstEdge = e := by
  classical
  have hne : w.Nonempty := by cases w with simp_all
  have hi : List.idxOf e w.edge < w.length := by rwa [← length_edge, List.idxOf_lt_length_iff]
  exact ⟨w.edge.idxOf e, hi, hne, by rw [rotate_firstEdge _ hi, List.getElem_idxOf]⟩

lemma firstEdge_rotate_one (hw : w.Nontrivial) :
    (hw.nonempty.rotate 1).firstEdge = hw.tail_nonempty.firstEdge := by
  cases hw with simp

lemma IsClosed.rotate_one_dropLast (hw : w.IsClosed) : (w.rotate 1).dropLast = w.tail := by
  cases w with simp

/-! ### Relationships with take and drop -/

lemma rotate_first_eq_drop_first (w : WList α β) (n : ℕ) (hn : n ≤ w.length) :
    (w.rotate n).first = (w.drop n).first := by
  rw [rotate_first _ _ hn, drop_first _ _ hn]

@[simp]
lemma IsClosed.rotate_eq_drop_append_take (hw : w.IsClosed) (n : ℕ) :
    w.rotate n = w.drop (n % w.length) ++ w.take (n % w.length) := by
  obtain ⟨x, rfl⟩ | hne := w.exists_eq_nil_or_nonempty
  · simp [rotate_nil]
  rw [hw.rotate_eq_mod, IsClosed.rotate_take_drop hw _ (Nat.mod_lt _ hne.length_pos).le]

lemma IsClosed.rotate_take_drop (hw : w.IsClosed) (n : ℕ) (hn : n ≤ w.length) :
    w.rotate n = w.drop n ++ w.take n := by
  rw [← take_drop w n] at hw ⊢
  rw [rotate_eq_append (by rw [take_last _ _ hn, drop_first _ _ hn])
    (by rw [take_first, drop_last, hw]), take_length, min_eq_left hn]

-- Note: The general relationship `w.rotate n = w.drop n ++ w.take n` requires `w.IsClosed`
-- because rotate is designed for closed lists. See `IsClosed.rotate_take_drop` for the
-- proven version with the closed assumption.

lemma rotate_take (hw : w.IsClosed) (n m : ℕ) (hn : n ≤ w.length) :
    (w.rotate n).take m = if m ≤ (w.drop n).length then (w.drop n).take m
    else w.drop n ++ (w.take n).take (m - (w.drop n).length) := by
  rw [IsClosed.rotate_take_drop hw hn, take_append]
  split_ifs <;> simp [Nat.sub_add_cancel (by omega)]

lemma rotate_drop (hw : w.IsClosed) (n m : ℕ) (hn : n ≤ w.length) :
    (w.rotate n).drop m = if m ≤ (w.drop n).length then (w.drop n).drop m ++ w.take n
    else (w.take n).drop (m - (w.drop n).length) := by
  rw [IsClosed.rotate_take_drop hw hn, drop_append]
  split_ifs <;> simp [Nat.sub_add_cancel (by omega)]

lemma rotate_last_eq_take_last (hw : w.IsClosed) (n : ℕ) (hn : n ≤ w.length) :
    (w.rotate n).last = (w.take n).last := by
  rw [IsClosed.rotate_take_drop hw hn, append_last, drop_last]

-- theorem WList.IsSuffix.exists_isPrefix_rotate.extracted_1_5  (w₁ w₂ : WList α β)
--     (hne : w₂.Nonempty) (n : ℕ) (hn : n ≤ w₂.length) (hpfx : w₁.IsPrefix (w₂.rotate n)) :
--     (w₁.concat e x).IsPrefix ((w₂.concat e x).rotate n) := by
--   obtain ⟨w₂', hj, h⟩ := hpfx.exists_eq_append

--   sorry

-- lemma IsSuffix.exists_isPrefix_rotate {w₁ w₂ : WList α β} (hw : w₁.IsSuffix w₂)
--     (hw₂ne : w₂.Nonempty) : ∃ n ≤ w₂.length, w₁.IsPrefix (w₂.rotate n) := by
--   match hw with
--   | .nil w =>
--     obtain ⟨x, e, w⟩ := hw₂ne
--     simp only [cons_length, last_cons, nil_isPrefix_iff]
--     use w.length +1, by omega
--     rw [rotate_first _ _ (by simp), ← cons_length, get_length, WList.last_cons]
--   | .concat e x w₁ w₂ h =>
--     obtain ⟨x, rfl⟩ | hne := w₂.exists_eq_nil_or_nonempty
--     · use 0
--       simp_all
--     obtain ⟨n, hn, hpfx⟩ := h |>.exists_isPrefix_rotate hne
--     use n, by simp [hn.trans (Nat.le_succ _)], ?_
--     extract_goal

-- lemma exists_rotate_first_dInc (hC : w.IsClosed) (hCwf : w.WellFormed) (he : w.DInc e x y) :
--     ∃ n < w.length, ∃ w', w.rotate n = cons x e w' ∧ w'.first = y := by
--   sorry

-- lemma IsClosed.exists_first_of_dInc (hC : w.IsClosed) (hCwf : w.WellFormed)
--     (he : w.DInc e x y) : ∃ w', E(w) = E(cons x e w') ∧ w'.first = y := by
--   sorry

-- lemma IsClosed.exists_first_of_isLink (hC : w.IsClosed) (hCwf : w.WellFormed)
--     (he : w.IsLink e x y) : ∃ w', E(w) = E(cons x e w') ∧ w'.first = y := by
--   obtain (h | h) := isLink_iff_dInc.mp he
--   · exact hC.exists_first_of_dInc hCwf h
--   sorry

/-- Rotate by an integer amount. -/
def intRotate (w : WList α β) (n : ℤ) : WList α β :=
  w.rotate (n.natMod w.length)

@[simp]
lemma length_intRotate (w : WList α β) (m : ℤ) : (w.intRotate m).length = w.length :=
  length_rotate ..

@[simp]
lemma intRotate_zero : w.intRotate 0 = w := by
  cases w with simp [intRotate, Int.natMod]

@[simp]
lemma nil_intRotate (x : α) (n) : (nil x : WList α β).intRotate n = nil x := by
  simp [intRotate]

lemma IsClosed.intRotate_eq_rotate (hw : w.IsClosed) (n : ℕ) : w.intRotate n = w.rotate n := by
  obtain ⟨x, rfl⟩ | hne := w.exists_eq_nil_or_nonempty
  · simp [intRotate]
  rw [intRotate, hw.rotate_eq_mod, Int.natMod, eq_comm, hw.rotate_eq_mod, Int.ofNat_mod_ofNat,
    Int.toNat_natCast, Nat.mod_mod]

/-- Nasty proof. -/
lemma IsClosed.intRotate_intRotate (hw : w.IsClosed) (m n : ℤ) :
    (w.intRotate m).intRotate n = w.intRotate (m + n) := by
  obtain ⟨x, rfl⟩ | hne := w.exists_eq_nil_or_nonempty
  · simp [intRotate]
  simp only [intRotate, length_rotate, rotate_rotate, Int.natMod]
  rw [hw.rotate_eq_mod, Int.add_emod]
  generalize hm' : m % w.length = m'
  generalize hn' : n % w.length = n'
  lift m' to ℕ using by simpa [← hm'] using Int.emod_nonneg _ (by simpa)
  lift n' to ℕ using by simpa [← hn'] using Int.emod_nonneg _ (by simpa)
  norm_cast

lemma IsClosed.rotate_intRotate_neg (hw : w.IsClosed) (n) : (w.rotate n).intRotate (-n) = w := by
  simp [← hw.intRotate_eq_rotate, hw.intRotate_intRotate]

lemma IsClosed.dInc_intRotate (hw : w.IsClosed) (n : ℤ) (h : w.DInc e x y) :
    (w.intRotate n).DInc e x y :=
  hw.dInc_rotate h ..

@[simp]
lemma IsClosed.dInc_rotate_iff (hw : w.IsClosed) : (w.rotate n).DInc e x y ↔ w.DInc e x y := by
  refine ⟨fun h ↦ ?_, fun h ↦ hw.dInc_rotate h _⟩
  rw [← hw.rotate_intRotate_neg n]
  exact (hw.rotate n).dInc_intRotate (-n) h

@[simp]
lemma IsClosed.isLink_rotate_iff (hw : w.IsClosed) :
    (w.rotate n).IsLink e x y ↔ w.IsLink e x y := by
  rw [isLink_iff_dInc, isLink_iff_dInc, hw.dInc_rotate_iff, hw.dInc_rotate_iff]

lemma WellFormed.rotate (hw : w.WellFormed) (h_closed : w.IsClosed) (n : ℕ) :
    (w.rotate n).WellFormed := by
  simpa [WellFormed, h_closed.isLink_rotate_iff] using hw

@[simp]
lemma IsClosed.wellFormed_rotate_iff (h_closed : w.IsClosed) :
    (w.rotate n).WellFormed ↔ w.WellFormed := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.rotate h_closed _⟩
  rw [← h_closed.rotate_intRotate_neg n]
  apply h.rotate (h_closed.rotate _) ..

end WList
