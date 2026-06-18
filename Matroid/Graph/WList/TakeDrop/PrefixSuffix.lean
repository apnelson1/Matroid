import Matroid.Graph.WList.TakeDrop.Defs

open Set Function List Nat WList

variable {α β : Type*} {u v x y z : α} {e e' f g : β} {S T U: Set α}
  {F F' : Set β} {w w' w₀ w₁ w₂ w₃ l l₁ l₂ l₃ : WList α β}

namespace WList

variable {P : α → Prop} [DecidablePred P]
lemma prefixUntil_eq_nil (hP : P w.first) : w.prefixUntil P = nil w.first := by
  match w with
  | .nil u => rfl
  | .cons u e w' => simpa [prefixUntil]


@[simp]
lemma prefixUntil_first (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.prefixUntil P).first = w.first := by
  cases w with simp [apply_ite]

@[simp, grind .]
lemma prefixUntil_prop_last_iff (w : WList α β) (P : α → Prop) [DecidablePred P] :
    P (w.prefixUntil P).last ↔ ∃ x ∈ w, P x := by
  induction w with | nil u => simp | cons u e w ih => grind

lemma prefixUntil_prop_last (h : ∃ u ∈ w, P u) : P (w.prefixUntil P).last :=
  prefixUntil_prop_last_iff .. |>.mpr h

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

lemma prefixUntil_isPrefix_of_prop {w' : WList α β} (hw' : w'.IsPrefix w) (h : ∃ u ∈ w', P u) :
    (w.prefixUntil P).IsPrefix w' := by
  induction hw' with
  | nil w =>
    simp only [mem_nil_iff, exists_eq_left] at h
    simp [prefixUntil_eq_nil h]
  | cons x e w₁ w₂ h ih =>
    simp only [mem_cons_iff, exists_eq_or_imp] at h
    obtain hPx | hPx := em (P x)
    · simp [hPx]
    replace h := h.resolve_left hPx
    simp only [prefixUntil_cons, hPx, ↓reduceIte]
    exact (ih h).cons ..

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

@[simp]
lemma prefixUntil_eq_self_iff (w : WList α β) (P : α → Prop) [DecidablePred P] :
    w.prefixUntil P = w ↔ ∀ u ∈ w.vertex.dropLast, ¬ P u := by
  induction w with
  | nil u => simp
  | cons u e w ih => grind [cons_vertex, dropLast_cons_of_ne_nil]

lemma prefixUntil_eq_self_of_forall (h : ∀ u ∈ w, ¬ P u) : w.prefixUntil P = w :=
  (prefixUntil_eq_self_iff ..).mpr <| fun u hu ↦ h u <| w.vertex.dropLast_subset hu

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

lemma IsPrefix.prefixUntil_eq_prefixUntil_of_exists (hw' : w'.IsPrefix w)
    (h : ∃ u ∈ w', P u) : w'.prefixUntil P = w.prefixUntil P := by
  refine IsPrefix.antisymm ?_ ?_
  · refine prefixUntil_isPrefix_of_prop (prefixUntil_isPrefix_of_prop hw' h) ?_
    obtain ⟨u, hu, hPu⟩ := h
    exact ⟨(w.prefixUntil P).last, last_mem, prefixUntil_prop_last ⟨u, hw'.mem hu, hPu⟩⟩
  exact prefixUntil_isPrefix_of_prop ((prefixUntil_isPrefix ..).trans hw')
    ⟨(w'.prefixUntil P).last, last_mem, prefixUntil_prop_last h⟩

lemma prefixUntil_eq_of_prefix {w' : WList α β} (hP : ∃ u ∈ w, P u)
    (h : w'.IsPrefix (w.prefixUntil P)) (hl : (w.prefixUntil P).last ∈ w') :
    w.prefixUntil P = w' := by
  refine IsPrefix.antisymm ?_ h
  refine prefixUntil_isPrefix_of_prop (h.trans (prefixUntil_isPrefix ..)) ?_
  use (w.prefixUntil P).last, hl, prefixUntil_prop_last hP

lemma prefixUntil_vertex_dropLast_not_prop (hx : x ∈ (w.prefixUntil P).vertex.dropLast) :
    ¬ P x := by
  induction w with
  | nil u => simp at hx
  | cons u e w ih =>
    by_cases hPu : P u
    · simp [hPu] at hx
    simp [List.dropLast_cons_of_ne_nil vertex_ne_nil, List.mem_cons, hPu] at hx
    grind

lemma vertex_prefixUntil (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.prefixUntil P).vertex = w.vertex.take (w.vertex.findIdx P + 1) := by
  induction w with
  | nil u => simp
  | cons u e w ih => by_cases hPu : P u <;> simp [hPu, ih, findIdx_cons]



lemma prefixUntilVertex_cons_of_ne [DecidableEq α] (w : WList α β) (hne : x ≠ y) (e : β) :
    (cons x e w).prefixUntilVertex y = cons x e (w.prefixUntilVertex y) := by
  simpa [prefixUntilVertex]


lemma prefixUntilVertex_isPrefix [DecidableEq α] (w : WList α β) (x : α) :
    (w.prefixUntilVertex x).IsPrefix w := prefixUntil_isPrefix ..

lemma prefixUntil_eq_prefixUntilVertex_last [DecidableEq α] (h : ∃ u ∈ w, P u) :
    w.prefixUntilVertex (w.prefixUntil P).last = w.prefixUntil P := by
  let P' := (· = (w.prefixUntil P).last)
  refine prefixUntil_eq_of_prefix ⟨(w.prefixUntil P).last, (prefixUntil_isPrefix ..).mem
    last_mem, rfl⟩ ?_ ?_
  · refine prefixUntil_isPrefix_of_prop (prefixUntil_isPrefix ..)
      ⟨(w.prefixUntil P').last, last_mem, ?_⟩
    rw [prefixUntil_prop_last (P := P')
      ⟨(w.prefixUntil P).last, (prefixUntil_isPrefix ..).mem last_mem, rfl⟩]
    exact prefixUntil_prop_last h
  convert last_mem using 1
  exact prefixUntil_prop_last (P := P')
    ⟨(w.prefixUntil P).last, (prefixUntil_isPrefix ..).mem last_mem, rfl⟩

lemma prefixUntil_eq_prefixUntilVertex_last_of_nodup [DecidableEq α] (hnd : w.vertex.Nodup) :
    w.prefixUntilVertex (w.prefixUntil P).last = w.prefixUntil P := by
  obtain h | h := em (∃ u ∈ w, P u)
  · exact prefixUntil_eq_prefixUntilVertex_last h
  rw [prefixUntil_eq_self_of_forall (by simpa using h)]
  refine (prefixUntilVertex_isPrefix w w.last).eq_of_last_mem hnd ?_
  convert (last_mem : (w.prefixUntil (· = w.last)).last ∈ w.prefixUntil (· = w.last)) using 1
  exact (prefixUntil_prop_last (P := (· = w.last)) ⟨w.last, last_mem, rfl⟩).symm

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



@[simp]
lemma suffixFrom_last (w : WList α β) : (w.suffixFrom P).last = w.last := by
  induction w with simp_all [apply_ite]

@[simp, grind .]
lemma suffixFrom_prop_first_iff (w : WList α β) (P : α → Prop) [DecidablePred P] :
    P (w.suffixFrom P).first ↔ ∃ x ∈ w, P x := by
  induction w with | nil u => simp | cons u e w ih => grind

lemma suffixFrom_prop_first {w : WList α β} (h : ∃ u ∈ w, P u) : P (w.suffixFrom P).first :=
  suffixFrom_prop_first_iff .. |>.mpr h


lemma suffixFrom_eq_nil_of_forall {w : WList α β} (h : ∀ u ∈ w, ¬ P u) :
    w.suffixFrom P = nil w.last := by
  match w with
  | nil u => simp
  | cons u e w =>
    simp only [mem_cons_iff, forall_eq_or_imp] at h
    simp only [suffixFrom_cons, h.1, ↓reduceIte, last_cons]
    exact suffixFrom_eq_nil_of_forall h.2

lemma suffixFrom_eq_nil_iff : w.suffixFrom P = nil w.last ↔ ∀ u ∈ w.vertex.dropLast, ¬ P u := by
  induction w with
  | nil u => simp
  | cons u e w ih =>
    rw [suffixFrom_cons]
    split_ifs with hpu <;> simp [hpu, List.dropLast_cons_of_ne_nil vertex_ne_nil, ih]

lemma suffixFrom_eq_self_iff (w : WList α β) (P : α → Prop) [DecidablePred P] :
    w.suffixFrom P = w ↔ w.Nil ∨ P w.first := by
  induction w with
  | nil u => simp
  | cons u e w ih =>
    by_cases hPu : P u
    · simp [hPu]
    simp only [suffixFrom_cons, hPu, ↓reduceIte, first_cons, not_nil_cons, or_self, iff_false]
    grind [w.suffixFrom_isSuffix P |>.isSublist.length_le]

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

lemma IsSuffix.suffixFrom_eq_suffixFrom_of_forall (hP : ∀ u ∈ w₂, P u → u ∈ w₁)
    (hnd : w₂.vertex.Nodup) (h : w₁.IsSuffix w₂) : w₁.suffixFrom P = w₂.suffixFrom P := by
  induction h with
  | nil w =>
    symm
    simp only [mem_nil_iff, suffixFrom_nil, suffixFrom_eq_nil_iff,
      List.mem_dropLast_iff hnd w.vertex_ne_nil] at hP ⊢
    grind
  | concat e x w₁ w₂ h ih =>
    rw [concat_vertex, List.nodup_append] at hnd
    obtain hF | hT := em' (∃ u ∈ w₂, P u)
    · rw [suffixFrom_concat_of_forall w₁ P fun u hu huP ↦ hF ⟨u, h.mem hu, huP⟩,
        suffixFrom_concat_of_forall w₂ P fun u hu huP ↦ hF ⟨u, hu, huP⟩]
    have hP' : ∀ u ∈ w₂, P u → u ∈ w₁ := fun u hu huP ↦
      (mem_concat.mp (hP u (mem_concat.mpr (Or.inl hu)) huP)).elim id
      (hnd.2.2 u hu x (by simp) · |>.elim)
    rw [suffixFrom_concat_of_exists w₁ P (by tauto), suffixFrom_concat_of_exists w₂ P hT]
    exact congr_arg (fun w ↦ w.concat e x) <| ih hP' hnd.1

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

lemma suffixFrom_vertex_filter_eq_vertex_filter (w : WList α β) (P Q : α → Prop) [DecidablePred P]
    [DecidablePred Q] : (w.suffixFrom P).vertex.filter Q = w.vertex.filter Q ∨
    (w.suffixFrom Q).vertex.filter P = w.vertex.filter P := by
  induction w with | nil u => simp | cons u e w ih => grind

lemma vertex_suffixFrom (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.suffixFrom P).vertex = w.vertex.drop (min (w.vertex.findIdx P) w.length) := by
  induction w with
  | nil u => simp
  | cons u e w ih => by_cases hPu : P u <;> simp [hPu, ih, findIdx_cons]



lemma suffixFromVertex_cons_of_ne [DecidableEq α] (w : WList α β) (hne : x ≠ y) (e : β) :
    (cons x e w).suffixFromVertex y = w.suffixFromVertex y := by
  simp [suffixFromVertex, hne]

lemma suffixFromVertex_append_right_of_notMem [DecidableEq α] {P Q : WList α β} {uf : α}
    (huf : uf ∉ P) : (P ++ Q).suffixFromVertex uf = Q.suffixFromVertex uf := by
  induction P with
  | nil y => simp [suffixFromVertex, nil_append]
  | cons y e P ih =>
    rw [mem_cons_iff, not_or, ← ne_eq] at huf
    simp only [cons_append, suffixFromVertex, suffixFrom_cons, huf.1.symm, ↓reduceIte]
    exact ih huf.2

lemma suffixFromVertex_cons_or [DecidableEq α] (u e) (w : WList α β) (x) :
    (u = x ∧ (cons u e w).suffixFromVertex x = cons u e w) ∨
    (u ≠ x ∧ (cons u e w).suffixFromVertex x = w.suffixFromVertex x) := by
  obtain rfl | h := eq_or_ne u x <;> simp_all [suffixFromVertex]

@[simp]
lemma suffixFromVertex_of_notMem [DecidableEq α] (w : WList α β) (x : α) (hx : x ∉ w) :
    w.suffixFromVertex x = nil w.last := by
  apply w.suffixFrom_eq_nil_of_forall
  grind

@[simp]
lemma suffixFromVertex_first [DecidableEq α] (hxw : x ∈ w) : (w.suffixFromVertex x).first = x :=
  suffixFrom_prop_first (P := (· = x)) ⟨_, hxw, rfl⟩


lemma suffixFrom_eq_suffixFromVertex_first [DecidableEq α] (h : ∃ u ∈ w, P u) :
    w.suffixFromVertex (w.suffixFrom P).first = w.suffixFrom P := by
  induction w with
  | nil u => simp
  | cons u e w ih =>
    obtain hT | hF := em (P u)
    · simp [suffixFromVertex, hT]
    simp only [mem_cons_iff, exists_eq_or_imp, hF, false_or, suffixFrom_cons, ↓reduceIte] at h ⊢
    have hne : u ≠ (w.suffixFrom P).first := fun heq ↦ hF <| heq ▸ (suffixFrom_prop_first h)
    rw [suffixFromVertex_cons_of_ne _ hne]
    exact ih h

lemma suffixFrom_eq_suffixFromVertex_first_of_nodup [DecidableEq α] (hnd : w.vertex.Nodup) :
    w.suffixFromVertex (w.suffixFrom P).first = w.suffixFrom P := by
  induction w with
  | nil u => simp
  | cons u e w ih =>
    obtain hT | hF := em (P u)
    · simp [suffixFromVertex, hT]
    have hne : (w.suffixFrom P).first ≠ u := by
      rintro rfl
      exact (List.nodup_cons.mp hnd).1 ((suffixFrom_isSuffix ..).mem first_mem)
    simp only [suffixFrom_cons, hF, ↓reduceIte]
    rw [suffixFromVertex_cons_of_ne _ hne.symm]
    exact ih (by simpa using (List.nodup_cons.mp hnd).2)

@[simp]
lemma suffixFromVertex_last (w : WList α β) (x) [DecidableEq α] :
    (w.suffixFromVertex x).last = w.last :=
  suffixFrom_last ..

@[simp]
lemma suffixFromVertex_eq_self_iff [DecidableEq α] (w : WList α β) (x : α) :
    w.suffixFromVertex x = w ↔ w.Nil ∨ w.first = x := w.suffixFrom_eq_self_iff (· = x)

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

@[simp]
lemma prefixUntilLast_isPrefix (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.prefixUntilLast P).IsPrefix w := by
  rw [← reverse_isSuffix_reverse_iff, prefixUntilLast, reverse_reverse]
  apply suffixFrom_isSuffix

@[simp, grind .]
lemma prefixUntilLast_prop_last_iff (w : WList α β) (P : α → Prop) [DecidablePred P] :
    P (w.prefixUntilLast P).last ↔ ∃ x ∈ w, P x := by
  rw [prefixUntilLast, reverse_last]
  exact (w.reverse.suffixFrom_prop_first_iff ..).trans <| by simp

lemma prefixUntilLast_prop_last (h : ∃ x ∈ w, P x) : P (w.prefixUntilLast P).last :=
  prefixUntilLast_prop_last_iff .. |>.mpr h

@[simp]
lemma prefixUntilLast_first (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.prefixUntilLast P).first = w.first := by
  rw [prefixUntilLast, reverse_first, suffixFrom_last, reverse_last]

lemma prefixUntilLast_vertex_filter_eq_vertex_filter (w : WList α β) (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q] : (w.prefixUntilLast P).vertex.filter Q = w.vertex.filter Q
    ∨ (w.prefixUntilLast Q).vertex.filter P = w.vertex.filter P := by
  simp only [prefixUntilLast, reverse_vertex, List.filter_reverse]
  rcases suffixFrom_vertex_filter_eq_vertex_filter w.reverse P Q with h | h
  · exact Or.inl (by rw [h, reverse_vertex, filter_reverse, List.reverse_reverse])
  · exact Or.inr (by rw [h, reverse_vertex, filter_reverse, List.reverse_reverse])

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

@[simp]
lemma suffixFromLast_isSuffix (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.suffixFromLast P).IsSuffix w := by
  rw [← reverse_isPrefix_reverse_iff, suffixFromLast, reverse_reverse]
  apply prefixUntil_isPrefix

lemma suffixFromLast_prop_first_iff (w : WList α β) (P : α → Prop) [DecidablePred P] :
    P (w.suffixFromLast P).first ↔ ∃ x ∈ w, P x := by
  rw [suffixFromLast, reverse_first]
  exact (w.reverse.prefixUntil_prop_last_iff ..).trans <| by simp

lemma suffixFromLast_prop_first (h : ∃ x ∈ w, P x) : P (w.suffixFromLast P).first :=
  suffixFromLast_prop_first_iff .. |>.mpr h

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

lemma suffixFromLast_not_prop (hx : x ∈ w.suffixFromLast P)
    (hne : (w.suffixFromLast P).first ≠ x) : ¬ P x := by
  rw [suffixFromLast, mem_reverse] at hx
  rw [suffixFromLast, reverse_first] at hne
  exact prefixUntil_not_prop hx hne

lemma suffixFromLast_inter_eq_first [DecidablePred (· ∈ S)] (h : ∃ u ∈ w, u ∈ S) :
    S ∩ V(w.suffixFromLast (· ∈ S)) = {(w.suffixFromLast (· ∈ S)).first} := by
  ext x
  simp only [mem_inter_iff, mem_vertexSet_iff, mem_singleton_iff]
  rw [eq_comm, suffixFromLast_first_eq_iff_prop h]

@[simp]
lemma suffixFromLast_eq_self_iff (w : WList α β) (P : α → Prop) [DecidablePred P] :
    w.suffixFromLast P = w ↔ ∀ x ∈ w.vertex.tail, ¬ P x := by
  rw [suffixFromLast, WList.reverse_eq_comm, w.reverse.prefixUntil_eq_self_iff P]
  simp

lemma suffixFromLast_eq_self_of_forall (h : ∀ x ∈ w, ¬ P x) : w.suffixFromLast P = w := by
  rw [suffixFromLast, w.reverse.prefixUntil_eq_self_of_forall (by simpa), reverse_reverse]

lemma IsSuffix.suffixFromLast_eq_suffixFromLast_of_exists (hw' : w'.IsSuffix w)
    (h : ∃ u ∈ w', P u) : w'.suffixFromLast P = w.suffixFromLast P := by
  rw [suffixFromLast, suffixFromLast,
    hw'.reverse_isPrefix_reverse.prefixUntil_eq_prefixUntil_of_exists]
  simpa using h

lemma IsPrefix.prefixUntilLast_eq_prefixUntilLast_of_forall (hP : ∀ u ∈ w₂, P u → u ∈ w₁)
    (hnd : w₂.vertex.Nodup) (h : w₁.IsPrefix w₂) : w₁.prefixUntilLast P = w₂.prefixUntilLast P := by
  rw [prefixUntilLast, prefixUntilLast, ← reverse_inj_iff, reverse_reverse, reverse_reverse]
  refine h.reverse_isSuffix_reverse.suffixFrom_eq_suffixFrom_of_forall ?_ ?_
  · exact fun u hu ↦ by simpa using hP u (by simpa using hu)
  simpa [reverse_vertex] using (List.nodup_reverse.mpr hnd)

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

lemma suffixFromLast_vertex_tail_not_prop (hx : x ∈ (w.suffixFromLast P).vertex.tail) : ¬ P x := by
  simp only [suffixFromLast, reverse_vertex, tail_reverse, List.mem_reverse] at hx
  exact prefixUntil_vertex_dropLast_not_prop hx

lemma IsSublist.exists_append_append (hw₀ : w₀.IsSublist w) (hw : w.vertex.Nodup) :
    ∃ w₁ w₂, w₁.last = w₀.first ∧ w₀.last = w₂.first ∧ w = w₁ ++ w₀ ++ w₂ := by
  classical
  induction hw₀ with
  | @nil x w h =>
    refine ⟨w.prefixUntilVertex x, w.suffixFromVertex x, ?_⟩
    rw [nil_first, nil_last, prefixUntilVertex_last h, suffixFromVertex_first h,
      append_assoc, nil_append, prefixUntilVertex_append_suffixFromVertex]
    simp
  | @cons x e w₁ w₂ h ih =>
    simp only [cons_vertex, nodup_cons, mem_vertex] at hw
    obtain ⟨w₁', w₂', h_eq, h_eq', rfl⟩ := ih hw.2
    exact ⟨WList.cons x e w₁', w₂', by simp [h_eq', h_eq]⟩
  | @cons₂ x e w₁ w₂ h h_eq ih =>
    simp only [cons_vertex, nodup_cons, mem_vertex] at hw
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

end WList
