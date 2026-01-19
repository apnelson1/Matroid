import Matroid.Graph.WList.Ops
import Matroid.ForMathlib.List

open Set Function List Nat WList

variable {α β : Type*} {u v x y z : α} {e e' f g : β} {S T U: Set α}
  {F F' : Set β} {w w₁ w₂ w₃ l l₁ l₂ l₃ : WList α β}

@[simp]
lemma List.singleton_isPrefix_iff {w : List α} (hw : w ≠ []) : [x].IsPrefix w ↔ w.head hw = x := by
  constructor
  · rintro ⟨w', rfl⟩
    simp
  rintro rfl
  use w.tail
  simp

@[simp]
lemma List.singleton_isSuffix_iff {w : List α} (hw : w ≠ []) :
    [x].IsSuffix w ↔ w.getLast hw = x := by
  constructor
  · rintro ⟨w', rfl⟩
    simp
  rintro rfl
  use w.dropLast, dropLast_concat_getLast hw

@[simp]
lemma List.concat_suffix_concat {l₁ l₂ : List α} :
    l₁.concat x <:+ l₂.concat y ↔ x = y ∧ l₁ <:+ l₂ := by
  simp [concat_eq_append, suffix_concat_iff]

@[simp]
lemma List.tail_eq_self_iff {l : List α} : l.tail = l ↔ l = [] := by
  cases l <;> simp

@[simp]
lemma List.dropLast_eq_self_iff {l : List α} : l.dropLast = l ↔ l = [] := by
  generalize h : l.reverse = l'
  convert l'.tail_eq_self_iff using 1 <;> simp [← h]

namespace WList

/-- `w₁.IsSublist w₂` means that `w₁` is a wList using some of the vertices and edges of `w₂`
in the same order that they appear in `w₂`.
Examples include prefixes, suffixes and wLists obtained from `w₂` by shortcuts.  -/
inductive IsSublist : WList α β → WList α β → Prop
  | nil {x w} (h : x ∈ w) : IsSublist (nil x) w
  | cons x e {w₁ w₂} (h : IsSublist w₁ w₂) : IsSublist w₁ (cons x e w₂)
  | cons₂ x e {w₁ w₂} (h : IsSublist w₁ w₂) (h_eq : w₁.first = w₂.first) :
      IsSublist (cons x e w₁) (cons x e w₂)

@[simp]
lemma nil_isSublist_iff : (WList.nil x (β := β)).IsSublist w ↔ x ∈ w := by
  refine ⟨fun h ↦ ?_, IsSublist.nil⟩
  induction w with
  | nil => cases h with | nil _ => assumption
  | cons u e W ih => cases h with
    | nil => assumption
    | cons x e h => simp [ih h]

@[simp]
lemma isSublist_nil_iff : w.IsSublist (nil x) ↔ w = nil x :=
  ⟨fun h ↦ by cases h with simp_all, by rintro rfl; simp⟩

@[simp]
lemma isSublist_refl (w : WList α β) : w.IsSublist w := by
  induction w with
  | nil => simp
  | cons u e w ih => exact ih.cons₂ _ _ rfl

lemma IsSublist.sublist (h : w₁.IsSublist w₂) : w₁.vertex <+ w₂.vertex := by
  induction h with
  | nil => simpa
  | cons x e h ih => exact ih.trans <| by simp
  | cons₂ x e h ih => simpa

lemma IsSublist.subset (h : w₁.IsSublist w₂) : V(w₁) ⊆ V(w₂) :=
  fun _ hx ↦ (h.sublist.subset hx)

lemma IsSublist.mem (h : w₁.IsSublist w₂) (hx : x ∈ w₁) : x ∈ w₂ :=
  h.sublist.mem hx

lemma IsSublist.edge_sublist {w₁ w₂ : WList α β} (h : w₁.IsSublist w₂) : w₁.edge <+ w₂.edge := by
  induction h with
  | nil => simp
  | cons x e h ih => exact ih.trans <| by simp
  | cons₂ x e h ih => simpa

lemma IsSublist.edge_subset (h : w₁.IsSublist w₂) : E(w₁) ⊆ E(w₂) :=
  fun _ hx ↦ (h.edge_sublist.subset hx)

lemma IsSublist.mem_edge (h : w₁.IsSublist w₂) (he : e ∈ w₁.edge) : e ∈ w₂.edge :=
  h.edge_subset he

lemma IsSublist.length_le (h : w₁.IsSublist w₂) : w₁.length ≤ w₂.length := by
  rw [← length_edge, ← length_edge]
  exact h.edge_sublist.length_le

lemma IsSublist.eq_of_length_ge (h : w₁.IsSublist w₂) (hge : w₂.length ≤ w₁.length) : w₁ = w₂ :=
  ext_vertex_edge (h.sublist.eq_of_length_le (by simpa)) <|
    h.edge_sublist.eq_of_length_le (by simpa)

lemma IsSublist.length_lt (h : w₁.IsSublist w₂) (hne : w₁ ≠ w₂) : w₁.length < w₂.length :=
  h.length_le.lt_of_ne fun h_eq ↦ hne <| h.eq_of_length_ge h_eq.symm.le

lemma IsSublist.trans (h : w₁.IsSublist w₂) (h' : w₂.IsSublist w₃) : w₁.IsSublist w₃ := by
  induction h' generalizing w₁ with
  | nil => simp_all
  | @cons x e w₂ w₃ h' ih => exact cons x e (ih h)
  | @cons₂ x e w₂ w₃ h' h_eq ih => cases h with
    | @nil y w₁ h =>
      simp only [nil_isSublist_iff, mem_cons_iff] at h ⊢
      exact h.elim .inl <| .inr ∘ h'.sublist.mem
    | @cons x e w₁ w₂ h => apply (ih h).cons
    | @cons₂ x e w₁ w₂ h h_eq' => exact (ih h).cons₂ _ _ (h_eq'.trans h_eq)

lemma IsSublist.antisymm (h : w₁.IsSublist w₂) (h' : w₂.IsSublist w₁) : w₁ = w₂ :=
  h.eq_of_length_ge h'.length_le

/-- The sublist order as a partial order on `WList α β`, for access to order API.  -/
instance : PartialOrder (WList α β) where
  le := IsSublist
  le_refl := isSublist_refl
  le_trans _ _ _ := IsSublist.trans
  le_antisymm _ _ := IsSublist.antisymm

@[simp] lemma le_iff_isSublist : w₁ ≤ w₂ ↔ w₁.IsSublist w₂ := Iff.rfl

lemma length_monotone : Monotone (WList.length (α := α) (β := β)) :=
  fun _ _ h ↦ h.length_le

lemma Nil.eq_of_le (h : w₁ ≤ w₂) (hnil : w₂.Nil) : w₁ = w₂ := by
  obtain ⟨x, rfl⟩ := nil_iff_eq_nil.mp hnil
  simpa using h

@[simp]
lemma isSublist_cons_self (w : WList α β) (x : α) (e : β) : w.IsSublist (cons x e w) :=
  (isSublist_refl (w := w)).cons ..

lemma IsSublist.concat (h : w₁.IsSublist w₂) (e : β) (x : α) : w₁.IsSublist (w₂.concat e x) := by
  induction h with
  | nil h => simp [h]
  | cons y f h ih => simpa using ih.cons ..
  | cons₂ y f h h_eq ih => exact ih.cons₂ _ _ (by simpa)

@[gcongr]
lemma IsSublist.concat₂ (h : w₁.IsSublist w₂) (hlast : w₁.last = w₂.last) (e : β) (x : α) :
    (w₁.concat e x).IsSublist (w₂.concat e x) := by
  induction h with
  | @nil y w h => induction w with
    | nil u => simp [show y = u by simpa using h]
    | cons u f w ih => exact IsSublist.cons _ _ (by simpa [show y = w.last from hlast] using ih)
  | cons y f h ih => exact (ih (by simpa using hlast)).cons y f
  | cons₂ y f h h_eq ih => exact (ih (by simpa using hlast)).cons₂ y f (by simpa)

@[simp]
lemma isSublist_concat_self (w : WList α β) (e : β) (x : α) : w.IsSublist (w.concat e x) :=
  (isSublist_refl (w := w)).concat ..

@[gcongr]
lemma IsSublist.reverse (h : w₁.IsSublist w₂) : w₁.reverse.IsSublist w₂.reverse := by
  induction h with
  | nil => simpa
  | cons x e h ih => exact ih.trans <| by simp
  | cons₂ x e h h_eq ih => apply ih.concat₂ <| by simpa

lemma IsSublist.of_reverse (h : w₁.reverse.IsSublist w₂.reverse) : w₁.IsSublist w₂ := by
  simpa using h.reverse

lemma DInc.of_isSublist (h : w₁.DInc e x y) (hle : w₁.IsSublist w₂) : w₂.DInc e x y := by
  induction hle with
  | nil => simp at h
  | cons _ _ h ih => simp [ih h]
  | cons₂ u f h h_eq ih => cases h with
    | cons_left x e w => exact h_eq ▸ (DInc.cons_left ..)
    | cons u f hw => exact DInc.cons _ _ (ih hw)

lemma IsLink.of_isSublist (h : w₁.IsLink e x y) (hle : w₁.IsSublist w₂) : w₂.IsLink e x y :=
  (isLink_iff_dInc.1 h).elim (fun h ↦ (h.of_isSublist hle).isLink)
    fun h ↦ (h.of_isSublist hle).isLink.symm

lemma WellFormed.sublist (h : w₂.WellFormed) (hle : w₁.IsSublist w₂) : w₁.WellFormed :=
  fun _ _ _ _ _ h₁ h₂ ↦ h (h₁.of_isSublist hle) (h₂.of_isSublist hle)

lemma cons_wellFormed_iff : (cons x e w).WellFormed ↔
    w.WellFormed ∧ ∀ y₁ y₂, w.IsLink e y₁ y₂ → s(y₁, y₂) = s(x, w.first) := by
  refine ⟨fun h' ↦ ⟨h'.sublist (by simp), fun y₁ y₂ h ↦ ?_⟩, fun h ↦ ?_⟩
  · exact h' (h.cons ..) (IsLink.cons_left ..)
  intro f x₁ x₂ y₁ y₂ h₁ h₂
  cases h₁ with
  | cons_left u f w =>
    rw [isLink_cons_iff, and_iff_right rfl] at h₂
    exact h₂.elim Eq.symm fun h' ↦ (h.2 _ _ h').symm
  | cons_right u f w =>
    rw [Sym2.eq_swap]
    rw [isLink_cons_iff, and_iff_right rfl] at h₂
    refine h₂.elim Eq.symm fun h' ↦ (h.2 _ _ h').symm
  | cons u f hw =>
    obtain ⟨rfl, h₂'⟩ | h₂ := isLink_cons_iff.1 h₂
    · rw [h₂', h.2 _ _ hw]
    exact h.1 hw h₂

/-! ## Prefixes -/

/-- `IsPrefix w₁ w₂` means that `w₁` is a prefix of `w₂`. -/
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
  induction h with | nil => simp | cons _ _ _ _ h ih => exact ih.cons₂ _ _ h.first_eq

lemma IsPrefix.prefix (h : w₁.IsPrefix w₂) : w₁.vertex <+: w₂.vertex := by
  induction h with | nil => simp | cons => simpa

lemma IsPrefix.mem (h : w₁.IsPrefix w₂) (hx : x ∈ w₁) : x ∈ w₂ :=
  h.isSublist.mem hx

lemma IsPrefix.subset (h : w₁.IsPrefix w₂) : V(w₁) ⊆ V(w₂) := fun _ ↦ h.mem

lemma IsPrefix.edge_prefix (h : w₁.IsPrefix w₂) : w₁.edge <+: w₂.edge := by
  induction h with | nil => simp | cons => simpa

lemma IsPrefix.edge_subset (h : w₁.IsPrefix w₂) : E(w₁) ⊆ E(w₂) := h.isSublist.edge_subset

lemma IsPrefix.mem_edge (h : w₁.IsPrefix w₂) (he : e ∈ w₁.edge) : e ∈ w₂.edge :=
  h.isSublist.mem_edge he

@[simp]
lemma isPrefix_refl (w : WList α β) : w.IsPrefix w := by
  induction w with
  | nil u => exact IsPrefix.nil <| nil u
  | cons _ _ _ ih => apply ih.cons

@[simp]
lemma isPrefix_nil_iff : w.IsPrefix (nil x) ↔ w = nil x :=
  ⟨fun h ↦ isSublist_nil_iff.1 h.isSublist, fun h ↦ h ▸ isPrefix_refl _⟩

@[simp]
lemma nil_isPrefix_iff : (nil x).IsPrefix w ↔ w.first = x :=
  ⟨fun h ↦ by cases h with rfl, by rintro rfl; exact IsPrefix.nil w⟩

lemma IsPrefix.trans (h : w₁.IsPrefix w₂) (h' : w₂.IsPrefix w₃) : w₁.IsPrefix w₃ := by
  induction h' generalizing w₁ with
  | nil w => simp_all
  | cons x e w₂ w₃ h' ih => cases h with
    | nil w => simp
    | cons x e w₁ w₂ h => apply (ih h).cons

lemma IsPrefix.eq_of_length_ge (h : w₁.IsPrefix w₂) (hge : w₂.length ≤ w₁.length) : w₁ = w₂ :=
  h.isSublist.eq_of_length_ge hge

lemma IsPrefix.length_le (h : w₁.IsPrefix w₂) : w₁.length ≤ w₂.length :=
  h.isSublist.length_le

lemma IsPrefix.antisymm (h : w₁.IsPrefix w₂) (h' : w₂.IsPrefix w₁) : w₁ = w₂ :=
  h.eq_of_length_ge h'.length_le

instance : IsPartialOrder (WList α β) IsPrefix where
  refl := isPrefix_refl
  trans _ _ _ := IsPrefix.trans
  antisymm _ _ := IsPrefix.antisymm

lemma IsPrefix.concat (h : w₁.IsPrefix w₂) (e x) : w₁.IsPrefix (w₂.concat e x) := by
  induction h with | nil => simp | cons y f w₁ w₂ h ih => exact ih.cons y f

@[simp]
lemma isPrefix_concat_self (w : WList α β) (e) (x) : w.IsPrefix (w.concat e x) :=
  (isPrefix_refl _).concat e x

lemma IsPrefix.get_eq_of_length_ge (h : w₁.IsPrefix w₂) {n} (hn : n ≤ w₁.length) :
    w₁.get n = w₂.get n := by
  induction h generalizing n with | nil => simp_all | cons => induction n with simp_all

lemma IsPrefix.idxOf_eq_of_mem [DecidableEq α] (h : w₁.IsPrefix w₂) (hx : x ∈ w₁) :
    w₁.idxOf x = w₂.idxOf x := by
  induction h generalizing x with
  | nil => simp_all
  | cons y e w w' hw ih =>
    obtain rfl | hne := eq_or_ne y x
    · simp
    simp only [mem_cons_iff, hne.symm, false_or] at hx
    simp [hne, ih hx]

lemma IsPrefix.eq_of_last_mem (h : w₁.IsPrefix w₂) (hnd : w₂.vertex.Nodup) (hl : w₂.last ∈ w₁) :
    w₁ = w₂ := by
  induction h with
  | nil w =>
    rw [mem_nil_iff, eq_comm, first_eq_last_iff hnd] at hl
    exact (Nil.eq_nil_first hl).symm
  | cons x e w₁ w₂ h ih =>
    simp_all only [cons_vertex, nodup_cons, mem_vertex, last_cons, mem_cons_iff, cons.injEq,
      true_and, forall_const]
    exact hl.elim (fun h => (hnd.1 <| h ▸ last_mem).elim) ih

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
lemma isSuffix_refl (w : WList α β) : w.IsSuffix w := by
  simpa using (isPrefix_refl (w := w.reverse)).reverse_isSuffix_reverse

lemma IsSuffix.isSublist (h : w₁.IsSuffix w₂) : w₁.IsSublist w₂ :=
  h.reverse_isPrefix_reverse.isSublist.of_reverse

lemma IsSuffix.suffix (h : w₁.IsSuffix w₂) : w₁.vertex <:+ w₂.vertex := by
  induction h with | nil => simp | concat => simpa [← concat_eq_append]

lemma IsSuffix.mem (h : w₁.IsSuffix w₂) (hx : x ∈ w₁) : x ∈ w₂ :=
  h.isSublist.mem hx

lemma IsSuffix.subset (h : w₁.IsSuffix w₂) : V(w₁) ⊆ V(w₂) := fun _ ↦ h.mem

lemma IsSuffix.edge_suffix (h : w₁.IsSuffix w₂) : w₁.edge <:+ w₂.edge := by
  induction h with | nil => simp | concat => simpa [← concat_eq_append]

lemma IsSuffix.edge_subset (h : w₁.IsSuffix w₂) : E(w₁) ⊆ E(w₂) := h.isSublist.edge_subset

lemma IsSuffix.mem_edge (h : w₁.IsSuffix w₂) (he : e ∈ w₁.edge) : e ∈ w₂.edge :=
  h.isSublist.mem_edge he

@[simp]
lemma isSuffix_nil_iff : w.IsSuffix (nil x) ↔ w = nil x :=
  ⟨fun h ↦ isSublist_nil_iff.1 h.isSublist, fun h ↦ h ▸ isSuffix_refl _⟩

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

instance : IsPartialOrder (WList α β) IsSuffix where
  refl := isSuffix_refl
  trans _ _ _ := IsSuffix.trans
  antisymm _ _ := IsSuffix.antisymm

lemma IsSuffix.cons (h : w₁.IsSuffix w₂) (x e) : w₁.IsSuffix (cons x e w₂) := by
  simpa using (h.reverse_isPrefix_reverse.concat e x).reverse_isSuffix_reverse

@[simp]
lemma isSuffix_cons_self (w : WList α β) (e) (x) : w.IsSuffix (cons x e w) :=
  (isSuffix_refl _).cons ..

@[simp]
lemma isSuffix_append_left (w₁ w₂ : WList α β) : w₂.IsSuffix (w₁ ++ w₂) := by
  induction w₁ with | nil => simp | cons u e w ih => simpa using ih.cons ..

lemma IsSuffix.eq_of_first_mem (h : w₁.IsSuffix w₂) (hnd : w₂.vertex.Nodup) (hl : w₂.first ∈ w₁) :
    w₁ = w₂ := by
  induction h with
  | nil w =>
    rw [mem_nil_iff, first_eq_last_iff hnd] at hl
    exact (Nil.eq_nil_last hl).symm
  | concat e x w₁ w₂ h ih =>
    simp_all [List.nodup_append]

lemma DInc.exists_isSuffix {w} (h : w.DInc e x y) :
    ∃ w', IsSuffix (WList.cons x e w') w ∧ w'.first = y := by
  match w with
  | .nil u => simp at h
  | .cons u e w =>
    obtain ⟨rfl, rfl, rfl⟩ | h := by simpa using h
    · use w, refl _
    obtain ⟨W, hW, rfl⟩ := h.exists_isSuffix
    use W, hW.trans <| w.isSuffix_cons_self e u

lemma IsSuffix.nonmepty_of_ne (hsf : w₁.IsSuffix w₂)  (hne : w₁ ≠ w₂) : w₂.Nonempty := by
  refine w₂.exists_eq_nil_or_nonempty.resolve_left ?_
  rintro ⟨v, rfl⟩
  simp [hne] at hsf

/-! ## Infixes -/

/-- `IsInfix w₁ w₂` means that `w₁` appears as a *contiguous* sub-wList of `w₂`.
More precisely, `w₂` decomposes as `wL ++ w₁ ++ wR` with the obvious endpoint compatibilities. -/
def IsInfix (w₁ w₂ : WList α β) : Prop :=
  ∃ wL wR : WList α β, wL.last = w₁.first ∧ w₁.last = wR.first ∧ wL ++ w₁ ++ wR = w₂

variable {wL wR : WList α β}

lemma IsInfix.infix (h : w₁.IsInfix w₂) : w₁.vertex <:+: w₂.vertex := by
  rcases h with ⟨wL, wR, hL, hR, rfl⟩
  simp only [append_vertex, ne_eq, vertex_ne_nil, not_false_eq_true, dropLast_append_of_ne_nil,
    List.append_assoc]
  use wL.vertex.dropLast, wR.vertex.tail
  simp only [List.append_assoc, append_cancel_left_eq]
  cases hwR : wR.vertex with
  | nil => exact (wR.vertex_ne_nil hwR).elim
  | cons head tail =>
    obtain rfl := by simpa [← wR.vertex_head, hwR, head_cons] using hR
    rw [← w₁.vertex_getLast, append_cons, dropLast_concat_getLast]
    simp

namespace IsInfix

@[simp]
lemma refl (w : WList α β) : w.IsInfix w := by
  refine ⟨nil w.first, nil w.last, by simp, by simp, ?_⟩
  simp

@[simp]
lemma isSublist (h : w₁.IsInfix w₂) : w₁ ≤ w₂ := by
  rcases h with ⟨wL, wR, hL, hR, rfl⟩
  simpa [append_assoc] using ((isPrefix_append_right hR).isSublist).trans
  <| wL.isSuffix_append_left (w₁ ++ wR) |>.isSublist

lemma mem (h : w₁.IsInfix w₂) (hx : x ∈ w₁) : x ∈ w₂ := h.isSublist.mem hx

lemma subset (h : w₁.IsInfix w₂) : V(w₁) ⊆ V(w₂) := fun _ hx ↦ h.mem hx

lemma edgeSet_subset (h : w₁.IsInfix w₂) : E(w₁) ⊆ E(w₂) := h.isSublist.edge_subset

lemma length_le (h : w₁.IsInfix w₂) : w₁.length ≤ w₂.length := h.isSublist.length_le

lemma eq_of_length_ge (h : w₁.IsInfix w₂) (hge : w₂.length ≤ w₁.length) : w₁ = w₂ :=
  h.isSublist.eq_of_length_ge hge

lemma length_lt (h : w₁.IsInfix w₂) (hne : w₁ ≠ w₂) : w₁.length < w₂.length :=
  h.isSublist.length_lt hne

lemma trans (h₁ : w₁.IsInfix w₂) (h₂ : w₂.IsInfix w₃) : w₁.IsInfix w₃ := by
  rcases h₁ with ⟨L₁, R₁, hL₁, hR₁, rfl⟩
  rcases h₂ with ⟨L₂, R₂, hL₂, hR₂, rfl⟩
  refine ⟨L₂ ++ L₁, R₁ ++ R₂, ?_, ?_, ?_⟩
  · simpa [append_last] using hL₁
  · rcases R₁.exists_eq_nil_or_nonempty with ⟨x, rfl⟩ | hne <;> simp_all
  · simp [append_assoc]

lemma antisymm (h : w₁.IsInfix w₂) (h' : w₂.IsInfix w₁) : w₁ = w₂ :=
  h.eq_of_length_ge h'.length_le

instance : IsPartialOrder (WList α β) IsInfix where
  refl := refl
  trans _ _ _ := trans
  antisymm _ _ := antisymm

lemma reverse (h : w₁.IsInfix w₂) : w₁.reverse.IsInfix w₂.reverse := by
  rcases h with ⟨wL, wR, hL, hR, rfl⟩
  refine ⟨wR.reverse, wL.reverse, ?_, ?_, ?_⟩
  · simpa using hR.symm
  · simpa using hL.symm
  rw [append_assoc, reverse_append, reverse_append hL]
  simpa

end IsInfix

@[simp]
lemma reverse_iff : w₁.reverse.IsInfix w₂.reverse ↔ w₁.IsInfix w₂ :=
  ⟨fun h ↦ by simpa using h.reverse, fun h ↦ h.reverse⟩

@[simp]
lemma isInfix_nil_iff : w.IsInfix (nil x) ↔ w = nil x :=
  ⟨fun h ↦ isSublist_nil_iff.1 h.isSublist, fun h ↦ h ▸ (IsInfix.refl _)⟩

@[simp]
lemma nil_isInfix_iff : (nil x).IsInfix w ↔ x ∈ w := by
  refine ⟨fun h ↦ nil_isSublist_iff.mp h.isSublist, fun hx ↦ ?_⟩
  obtain ⟨wL, wR, rfl, heq, rfl⟩ := eq_append_of_vertex_mem hx
  refine ⟨wL, wR, heq, ?_, ?_⟩
  · simp
  rw [append_assoc, nil_append]

/-! ## Decomposed wLists -/

def appendList [Inhabited α] (L : List (WList α β)) : WList α β :=
  L.foldl (· ++ ·) (nil default)

notation L "⁺" => appendList L

@[simp]
lemma foldl_append_nil [Inhabited α] {L : List (WList α β)} (hne : L ≠ []) :
    L.foldl (· ++ ·) (nil x) = L⁺ := by
  induction L <;> simp_all [appendList]

@[simp]
lemma foldl_append_replicate_nil (n : ℕ) :
    (List.replicate n (nil x)).foldl (· ++ ·) (nil x : WList α β) = nil x := by
  induction n with
  | zero => simp
  | succ n ih => simp [replicate_succ, ih]

@[simp]
lemma appendList_replicate_nil [Inhabited α] {n : ℕ} (hn : n ≠ 0) :
    (List.replicate n (nil x : WList α β))⁺ = nil x := by
  induction n with
  | zero => simp at hn
  | succ n ih =>
    rw [appendList, foldl_append_nil replicate_succ_ne_nil]
    exact foldl_append_replicate_nil _

@[simp]
lemma appendList_nil [Inhabited α] : []⁺ = (nil default : WList α β) := by
  simp [appendList]

@[simp]
lemma appendList_ret [Inhabited α] {l : WList α β} : [l]⁺ = l := by
  simp [appendList]

@[simp]
lemma appendList_cons [Inhabited α] {l : WList α β} {L : List (WList α β)}
    (h : l.last = (L⁺).first) : (l :: L)⁺ = l ++ L⁺ := by
  match L with
  | [] =>
    simp only [appendList, foldl_nil, nil_first, foldl_cons, nil_append] at h ⊢
    exact (append_nil h).symm
  | head :: tail =>
    simp only [appendList, foldl_cons, nil_append]
    rw [List.op_foldl_eq_foldl_op_of_assoc]

@[simp↓]
lemma appendList_nil_cons [Inhabited α] (x : α) {L : List (WList α β)} (hne : L ≠ []) :
    (nil x :: L)⁺ = L⁺ := by
  unfold appendList
  simp [hne]

@[simp↓]
lemma appendList_concat [Inhabited α] (l : WList α β) (L : List (WList α β)) :
    (L.concat l)⁺ = L⁺ ++ l := by
  simp [appendList]

@[simp]
lemma appendList_first [Inhabited α] {L : List (WList α β)} (hne : L ≠ [])
    (h : L.IsChain (·.last = ·.first)) : L⁺.first = (L.head hne).first := by
  match L with
  | [] => simp at hne
  | [l] => simp
  | l₁ :: l₂ :: L =>
    have : l₁.last = ((l₂ :: L)⁺).first := by
      rw [appendList_first (by simp) (isChain_of_isChain_cons h), head_cons]
      exact h.rel_head
    rw [appendList_cons this, append_first_of_eq this, head_cons]

@[simp]
lemma appendList_reverse [Inhabited α] {L : List (WList α β)} (h : L.IsChain (·.last = ·.first)) :
    L⁺.reverse = (L.map reverse).reverse⁺ := by
  match L with
  | [] => simp [appendList]
  | [l] => simp [appendList]
  | l₁ :: l₂ :: L =>
    have hrel : l₁.last = (l₂ :: L)⁺.first := by
      rw [appendList_first (by simp) (isChain_of_isChain_cons h)]
      exact h.rel_head
    apply_fun reverse using reverse_injective
    rw [reverse_reverse, appendList_cons hrel, List.map_cons, List.reverse_cons', appendList_concat,
      reverse_append ?_, reverse_reverse, ← appendList_reverse (isChain_of_isChain_cons h),
      reverse_reverse]
    rw [← appendList_reverse (isChain_of_isChain_cons h)]
    simp only [reverse_last, reverse_first, hrel]

@[simp]
lemma appendList_cons_cons [Inhabited α] {l₁ l₂ : WList α β} {L : List (WList α β)}
    (h : (l₁ :: l₂ :: L).IsChain (·.last = ·.first)) : (l₁ :: l₂ :: L)⁺ = l₁ ++ (l₂ :: L)⁺ := by
  rw [appendList_cons (by simp [isChain_of_isChain_cons h, h.rel_head])]

@[simp]
lemma appendList_edge [Inhabited α] (L : List (WList α β)) :
    L⁺.edge = (L.map edge).foldl (· ++ ·) [] := by
  match L with
  | [] => simp
  | [l] => simp
  | l₁ :: l₂ :: L =>
    have := appendList_edge (l₂ :: L)
    simp only [appendList, foldl_cons, nil_append, List.map_cons, List.nil_append] at this ⊢
    rw [op_foldl_eq_foldl_op_of_assoc, op_foldl_eq_foldl_op_of_assoc, append_edge, ← this]


/-- A decomposed wList is a list of wLists that appends to the original wList and
  the last vertex of each wList is the first vertex of the next wList.

  As there is no 'emtpy' wList, we start the fold with the default value of `α`.
  Hence, without the nonempty assumption, wList `nil default` decompose to the empty list. -/
structure DecomposeTo [Inhabited α] (w : WList α β) (L : List (WList α β)) : Prop where
  nonempty : L ≠ []
  append : w = L⁺
  chain_eq : List.IsChain (·.last = ·.first) L

namespace DecomposeTo
variable {L : List (WList α β)} {l w' : WList α β} [Inhabited α]

@[simp]
lemma nil_right : ¬ w.DecomposeTo [] :=
  fun h ↦ h.nonempty rfl

@[simp]
lemma nil_cons (h : w.DecomposeTo ((nil x) :: L)) (hne : L ≠ []) : w.DecomposeTo L :=
  ⟨hne, h.append ▸ (appendList_nil_cons x hne), isChain_of_isChain_cons h.chain_eq⟩

lemma append_cons (h : (w ++ w').DecomposeTo (w :: L)) (hL : L ≠ []) : w'.DecomposeTo L := by
  refine ⟨hL, ?_, isChain_of_isChain_cons h.chain_eq⟩
  obtain ⟨l, L', rfl⟩ := List.exists_cons_of_ne_nil hL
  simpa only [appendList_cons_cons h.chain_eq, w.append_right_inj_iff] using h.append

@[simp]
lemma head_first_eq_first {w : WList α β} {L : List (WList α β)} (h : w.DecomposeTo L) :
    (L.head h.nonempty).first = w.first := by
  obtain ⟨l, L', hl⟩ := List.exists_cons_of_ne_nil h.nonempty
  match l, L' with
  | nil u, [] => simp [hl, h.append]
  | nil u, l' :: L' =>
    obtain rfl := nil_last ▸ (hl ▸ h.chain_eq).rel_head
    simpa [hl] using (hl ▸ h).nil_cons (by simp) |>.head_first_eq_first
  | cons u e w', [] =>
    subst L
    simp [h.append]
  | cons u e w', l' :: L' =>
    subst L
    simp only [appendList, head_cons, first_cons, h.append, foldl_cons, nil_append]
    rw [List.op_foldl_eq_foldl_op_of_assoc]
    simp
termination_by L
decreasing_by simp [hl]

@[simp]
lemma append_cons_iff (heq : w.last = w'.first) (hL : L ≠ []) :
    (w ++ w').DecomposeTo (w :: L) ↔ w'.DecomposeTo L := by
  refine ⟨fun h => h.append_cons hL, fun h => ⟨by simp, ?_, ?_⟩⟩
  · obtain ⟨l, L', rfl⟩ := List.exists_cons_of_ne_nil hL
    simp [h.append, appendList, L'.op_foldl_eq_foldl_op_of_assoc]
  simp only [isChain_cons, Option.mem_def, h.chain_eq, and_true]
  rintro l hl
  rw [head?_eq_some_head hL, Option.some_inj] at hl
  rw [heq, ← h.head_first_eq_first, hl]

lemma head_isPrefix (h : w.DecomposeTo L) : (L.head h.nonempty).IsPrefix w := by
  obtain ⟨l, L', rfl⟩ := List.exists_cons_of_ne_nil h.nonempty
  simp only [head_cons, h.append, appendList, foldl_cons, nil_append]
  match L' with
  | [] => simp
  | l' :: L' =>
    simp only [foldl_cons]
    rw [List.op_foldl_eq_foldl_op_of_assoc]
    apply WList.isPrefix_append_right
    rw [h.chain_eq.rel_head]
    have := h.append ▸ h
    simp only [foldl_cons, appendList, nil_append] at this
    rw [List.op_foldl_eq_foldl_op_of_assoc] at this
    simpa using (this.append_cons (by simp)).head_first_eq_first

lemma isSublist_of_mem {L : List (WList α β)} {w l : WList α β} (h : w.DecomposeTo L) (hl : l ∈ L) :
    l.IsSublist w := by
  match L with
  | [] => simp at hl
  | l' :: L' =>
    obtain rfl | hl := (by simpa using hl) <;> have := by simpa using h.head_isPrefix
    · exact this.isSublist
    obtain ⟨w', hw', rfl⟩ := this.exists_eq_append; clear this
    exact (h.append_cons (ne_nil_of_mem hl) |>.isSublist_of_mem hl).trans
    <| (isSuffix_append_left _ _).isSublist

@[simp]
lemma nil_decomposeTo_iff : (nil x).DecomposeTo L ↔ L ≠ [] ∧ ∀ l ∈ L, l = nil x := by
  refine ⟨fun h ↦ ⟨h.nonempty, fun l hl ↦ isSublist_nil_iff.mp <| h.isSublist_of_mem hl⟩,
    fun ⟨hne, hall⟩ ↦ ⟨hne, ?_, ?_⟩⟩ <;> have := List.eq_replicate_length.mpr hall
  · rw [this, ← foldl_append_nil (x := x) (by simpa), foldl_append_replicate_nil]
  exact this ▸ isChain_replicate_of_rel L.length rfl

lemma reverse (h : w.DecomposeTo L) : w.reverse.DecomposeTo (L.map reverse).reverse := by
  refine ⟨by simp [h.nonempty], h.append ▸ appendList_reverse h.chain_eq, ?_⟩
  rw [isChain_reverse]
  refine isChain_map_of_isChain _ ?_ h.chain_eq
  simp [eq_comm]

lemma getLast_isSuffix (h : w.DecomposeTo L) : (L.getLast h.nonempty).IsSuffix w := by
  simpa using h.reverse.head_isPrefix

lemma disjoint_of_edge_nodup {w : WList α β} {L : List (WList α β)} (h : w.DecomposeTo L)
    (hw : w.edge.Nodup) : L.Pairwise (_root_.Disjoint on WList.edgeSet) := by
  match L with
  | [] => simp
  | [l] => simp
  | l₁ :: l₂ :: L =>
    rw [pairwise_cons]
    obtain hprefix := by simpa using h.head_isPrefix
    obtain ⟨w', hw', rfl⟩ := hprefix.exists_eq_append
    have h' := h.append_cons (by simp)
    have hnd := by simpa only [append_edge, nodup_append] using hw
    exact ⟨fun l' hl' ↦ (edgeSet_disjoint_of_append_nodup hw).mono_right (h'.isSublist_of_mem hl'
    |>.edge_subset), disjoint_of_edge_nodup h' hnd.2.1⟩

end DecomposeTo
end WList
