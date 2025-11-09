import Matroid.Graph.WList.Ops
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic


open Set Function List Nat WList

variable {α β : Type*} {u v x y z : α} {e e' f g : β} {S T U: Set α}
  {F F' : Set β} {w w₁ w₂ w₃ l l₁ l₂ l₃ : WList α β}

lemma List.op_foldl_eq_foldl_op_of_assoc {f : α → α → α} [Std.Associative f] :
    ∀ a b l, (foldl f (f a b) l) = f a (foldl f b l)
  | _, _, nil => rfl
  | a, b, c :: l => by
    simp only [foldl_cons]
    simp_rw [Std.Associative.assoc a b c]
    rw [op_foldl_eq_foldl_op_of_assoc ..]

lemma List.Nodup.eq_singleton_iff_head_getLast {l : List α} (hnd : l.Nodup) (hne : l ≠ []) :
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

lemma List.IsSuffix.eq_of_first_mem {l₁ l₂ : List α} (h : l₁.IsSuffix l₂) (hnd : l₂.Nodup)
    (hne : l₂ ≠ []) (hl : l₂.head hne ∈ l₁) : l₁ = l₂ := by
  match h with | .intro w h => ?_
  subst l₂
  rw [self_eq_append_left]
  match w with
  | [] => rfl
  | a :: as => simp_all

lemma List.IsPrefix.eq_of_last_mem {l₁ l₂ : List α} (h : l₁.IsPrefix l₂) (hnd : l₂.Nodup)
    (hne : l₂ ≠ []) (hl : l₂.getLast hne ∈ l₁) : l₁ = l₂ := by
  simpa using h.reverse.eq_of_first_mem (by simpa) (by simpa) (by simpa)

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

lemma IsSublist.vertex_sublist (h : w₁.IsSublist w₂) : w₁.vertex <+ w₂.vertex := by
  induction h with
  | nil => simpa
  | cons x e h ih => exact ih.trans <| by simp
  | cons₂ x e h ih => simpa

lemma IsSublist.vertex_subset (h : w₁.IsSublist w₂) : V(w₁) ⊆ V(w₂) :=
  fun _ hx ↦ (h.vertex_sublist.subset hx)

lemma IsSublist.mem (h : w₁.IsSublist w₂) (hx : x ∈ w₁) : x ∈ w₂ :=
  h.vertex_sublist.mem hx

lemma IsSublist.edge_sublist {w₁ w₂ : WList α β} (h : w₁.IsSublist w₂) : w₁.edge <+ w₂.edge := by
  induction h with
  | nil => simp
  | cons x e h ih => exact ih.trans <| by simp
  | cons₂ x e h ih => simpa

lemma IsSublist.edgeSet_subset (h : w₁.IsSublist w₂) : E(w₁) ⊆ E(w₂) :=
  fun _ hx ↦ (h.edge_sublist.subset hx)

lemma IsSublist.length_le (h : w₁.IsSublist w₂) : w₁.length ≤ w₂.length := by
  rw [← length_edge, ← length_edge]
  exact h.edge_sublist.length_le

lemma IsSublist.eq_of_length_ge (h : w₁.IsSublist w₂) (hge : w₂.length ≤ w₁.length) : w₁ = w₂ :=
  ext_vertex_edge (h.vertex_sublist.eq_of_length_le (by simpa)) <|
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
      exact h.elim .inl <| .inr ∘ h'.vertex_sublist.mem
    | @cons x e w₁ w₂ h => apply (ih h).cons
    | @cons₂ x e w₁ w₂ h h_eq' => exact (ih h).cons₂ _ _ (h_eq'.trans h_eq)

lemma IsSublist.antisymm (h : w₁.IsSublist w₂) (h' : w₂.IsSublist w₁) : w₁ = w₂ :=
  h.eq_of_length_ge h'.length_le

@[simp]
lemma isSublist_cons_self (w : WList α β) (x : α) (e : β) : w.IsSublist (cons x e w) :=
  (isSublist_refl (w := w)).cons ..

lemma IsSublist.concat (h : w₁.IsSublist w₂) (e : β) (x : α) : w₁.IsSublist (w₂.concat e x) := by
  induction h with
  | nil h => simp [h]
  | cons y f h ih => simpa using ih.cons ..
  | cons₂ y f h h_eq ih => exact ih.cons₂ _ _ (by simpa)

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

lemma IsPrefix.mem (h : w₁.IsPrefix w₂) (hx : x ∈ w₁) : x ∈ w₂ :=
  h.isSublist.mem hx

lemma IsPrefix.subset (h : w₁.IsPrefix w₂) : V(w₁) ⊆ V(w₂) := fun _ ↦ h.mem

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

lemma IsPrefix.vertex_isPrefix (h : w₁.IsPrefix w₂) : w₁.vertex <+: w₂.vertex := by
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

lemma IsSuffix.vertex_isSuffix (h : w₁.IsSuffix w₂) : w₁.vertex.IsSuffix w₂.vertex := by
  simpa using h.reverse_isPrefix_reverse.vertex_isPrefix

lemma IsSuffix.subset (h : w₁.IsSuffix w₂) : V(w₁) ⊆ V(w₂) := fun _ ↦ h.mem

lemma IsSuffix.cons (h : w₁.IsSuffix w₂) (x e) : w₁.IsSuffix (cons x e w₂) := by
  simpa using (h.reverse_isPrefix_reverse.concat e x).reverse_isSuffix_reverse

@[simp]
lemma isSuffix_cons_self (w : WList α β) (e) (x) : w.IsSuffix (cons x e w) :=
  isSuffix_refl.cons ..

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
    rw [reverse_reverse, appendList_cons hrel, map_cons, List.reverse_cons', appendList_concat,
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
    simp only [appendList, foldl_cons, nil_append, map_cons, List.nil_append] at this ⊢
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
  rw [head?_eq_head hL, Option.some_inj] at hl
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
  simp [flip, eq_comm]

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
    |>.edgeSet_subset), disjoint_of_edge_nodup h' hnd.2.1⟩

end DecomposeTo

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

lemma prefixUntil_last_eq_iff_prop (h : ∃ u ∈ w, P u) :
    P v ∧ v ∈ w.prefixUntil P ↔ (w.prefixUntil P).last = v := by
  refine ⟨fun ⟨hvP, hv⟩ ↦ prefixUntil_last_eq_of_prop hv hvP, ?_⟩
  rintro rfl
  exact ⟨prefixUntil_prop_last h, last_mem⟩

lemma prefixUntil_inter_eq_last (w : WList α β) (S : Set α) [DecidablePred (· ∈ S)]
    (h : ∃ u ∈ w, u ∈ S) :
    S ∩ V(w.prefixUntil (· ∈ S)) = {(w.prefixUntil (· ∈ S)).last} := by
  ext x
  simp only [Set.mem_inter_iff, mem_vertexSet_iff, mem_singleton_iff]
  rwa [eq_comm, w.prefixUntil_last_eq_iff_prop]

lemma prefixUntil_eq_self_of_forall (w : WList α β) (P : α → Prop) [DecidablePred P]
    (h : ∀ u ∈ w, ¬ P u) : w.prefixUntil P = w := by
  match w with
  | nil u => simp
  | cons u e w =>
    simp_all only [mem_cons_iff, forall_eq_or_imp, prefixUntil_cons, ↓reduceIte, cons.injEq,
      true_and]
    exact prefixUntil_eq_self_of_forall w P h.2

lemma prefixUntil_concat_of_exists (w : WList α β) (P : α → Prop) [DecidablePred P]
    (h : ∃ u ∈ w, P u) : (w.concat e x).prefixUntil P = w.prefixUntil P := by
  match w with
  | nil u => simp_all
  | cons u e w =>
    by_cases hP : P u
    · simp [hP]
    simp_all only [mem_cons_iff, exists_eq_or_imp, false_or, cons_concat, prefixUntil_cons,
      ↓reduceIte, cons.injEq, true_and]
    exact prefixUntil_concat_of_exists w P h

lemma prefixUntil_concat_of_forall (w : WList α β) (P : α → Prop) [DecidablePred P]
    (h : ∀ u ∈ w, ¬ P u) : (w.concat e x).prefixUntil P = w.concat e x := by
  match w with
  | nil u => simp_all
  | cons u e w =>
    simp_all only [mem_cons_iff, forall_eq_or_imp, cons_concat, prefixUntil_cons, ↓reduceIte,
      cons.injEq, true_and]
    exact prefixUntil_concat_of_forall w P h.2

lemma prefixUntil_concat (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.concat e x).prefixUntil P = if w.vertex.all (¬ P ·) then w.concat e x
    else w.prefixUntil P := by
  split_ifs with h
  · exact prefixUntil_concat_of_forall w P (by simpa using h)
  · exact prefixUntil_concat_of_exists w P (by simpa using h)

/-- The prefix of `w` ending at a vertex `x`. Equal to `w` if `x ∉ w`. -/
def prefixUntilVertex [DecidableEq α] (w : WList α β) (x : α) : WList α β := w.prefixUntil (· = x)

lemma prefixUntilVertex_isPrefix [DecidableEq α] (w : WList α β) (x : α) :
    (w.prefixUntilVertex x).IsPrefix w := prefixUntil_isPrefix ..

lemma prefixUntilVertex_last [DecidableEq α] (hxw : x ∈ w) : (w.prefixUntilVertex x).last = x :=
  prefixUntil_prop_last (P := (· = x)) ⟨_, hxw, rfl⟩

@[simp]
lemma prefixUntilVertex_first (w : WList α β) (x) [DecidableEq α] :
    (w.prefixUntilVertex x).first = w.first :=
  prefixUntil_first ..

lemma prefixUntilVertex_cons_of_ne [DecidableEq α] (w : WList α β) (hne : x ≠ y) (e : β) :
    (cons x e w).prefixUntilVertex y = cons x e (w.prefixUntilVertex y) := by
  simpa [prefixUntilVertex]

lemma prefixUntilVertex_length [DecidableEq α] (w : WList α β) (x : α) (hx : x ∈ w) :
    (w.prefixUntilVertex x).length = w.idxOf x := by
  induction w with | nil => simp_all [prefixUntilVertex] | cons u e w ih =>
  obtain rfl | hu := eq_or_ne x u
  · simp [prefixUntilVertex]
  simp_all [prefixUntilVertex, hu.symm, idxOf_cons_ne hu.symm]

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

lemma suffixFromVertex_first [DecidableEq α] (hxw : x ∈ w) : (w.suffixFromVertex x).first = x :=
  suffixFrom_prop_first (P := (· = x)) ⟨_, hxw, rfl⟩

lemma suffixFromVertex_isSuffix [DecidableEq α] (w : WList α β) (x : α) :
    (w.suffixFromVertex x).IsSuffix w := suffixFrom_isSuffix ..

@[simp]
lemma suffixFromVertex_last (w : WList α β) (x) [DecidableEq α] :
    (w.suffixFromVertex x).last = w.last :=
  suffixFrom_last ..

@[simp]
lemma prefixUntilVertex_append_suffixFromVertex [DecidableEq α] (w : WList α β) (x : α) :
    w.prefixUntilVertex x ++ w.suffixFromVertex x = w :=
  prefixUntil_append_suffixFrom ..

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

lemma suffixFromLast_inter_eq_first (w : WList α β) (S : Set α) [DecidablePred (· ∈ S)]
    (h : ∃ u ∈ w, u ∈ S) :
    S ∩ V(w.suffixFromLast (· ∈ S)) = {(w.suffixFromLast (· ∈ S)).first} := by
  ext x
  simp only [mem_inter_iff, mem_vertexSet_iff, mem_singleton_iff]
  rw [eq_comm, suffixFromLast_first_eq_iff_prop h]

lemma suffixFromLast_eq_self_of_forall (w : WList α β) (P : α → Prop) [DecidablePred P]
    (h : ∀ x ∈ w, ¬ P x) : w.suffixFromLast P = w := by
  rw [suffixFromLast, w.reverse.prefixUntil_eq_self_of_forall P (by simpa), reverse_reverse]

@[simp]
lemma suffixFrom_isSuffix_suffixFromLast (w : WList α β) (P : α → Prop) [DecidablePred P]
    (h : ∃ x ∈ w, P x) :
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
    exact suffixFrom_isSuffix_suffixFromLast w P h

/- This is a subwalk of `w` from the last vertex in `S`, `s`, to the first vertex in `T` after
  `s`, if any such vertex exists. Otherwise, it returns `w`.
  In the case where `w` is a path with some vertex in `S` before some vertex in `T`,
  its result satisfies `w.IsPathFrom S T`. -/
def extractPathFrom (w : WList α β) (S T : Set α) [DecidablePred (· ∈ S)]
    [DecidablePred (· ∈ T)] : WList α β :=
  (w.suffixFromLast (· ∈ S)).prefixUntil (· ∈ T)

@[simp]
lemma extractPathFrom_isSublist (w : WList α β) (S T : Set α) [DecidablePred (· ∈ S)]
    [DecidablePred (· ∈ T)] : (w.extractPathFrom S T).IsSublist w :=
  (prefixUntil_isPrefix _ _).isSublist.trans (w.suffixFromLast_isSuffix (· ∈ S)).isSublist

lemma extractPathFrom_first_mem [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (hw : ∃ x ∈ w, x ∈ S) : (w.extractPathFrom S T).first ∈ S := by
  rw [extractPathFrom, prefixUntil_first]
  exact suffixFromLast_prop_first hw

lemma extractPathFrom_first_eq_of_mem [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (hv : v ∈ w.extractPathFrom S T) (hvS : v ∈ S) : (w.extractPathFrom S T).first = v := by
  rw [extractPathFrom, prefixUntil_first]
  exact suffixFromLast_first_eq_of_prop ((prefixUntil_isPrefix _ _).mem hv) hvS

lemma extractPathFrom_first_eq_iff_mem [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (hw : ∃ x ∈ w, x ∈ S) :
    (w.extractPathFrom S T).first = v ↔ v ∈ V(w.extractPathFrom S T) ∧ v ∈ S :=
  ⟨fun h ↦ ⟨h ▸ first_mem, h ▸ extractPathFrom_first_mem hw⟩,
    fun ⟨hv, hvS⟩ ↦ extractPathFrom_first_eq_of_mem hv hvS⟩

/- When there are multiple `S` to `T` segments in `w`, `w.extractPathFrom S T` will return the
  last such segment. This is an arbitrary choice and it means that `extractPathFrom_first_mem`
  only requires having some vertex from `S` in `w`, whereas for this lemma, it is more strict. -/
lemma extractPathFrom_last_mem [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (hw : ∃ u ∈ w.suffixFromLast (· ∈ S), u ∈ T) : (w.extractPathFrom S T).last ∈ T := by
  rw [extractPathFrom]
  exact prefixUntil_prop_last hw

lemma extractPathFrom_last_eq_of_mem [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (hv : v ∈ w.extractPathFrom S T) (hvT : v ∈ T) : (w.extractPathFrom S T).last = v :=
  prefixUntil_last_eq_of_prop hv hvT

lemma extractPathFrom_last_eq_iff_mem [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (hw : ∃ u ∈ w.suffixFromLast (· ∈ S), u ∈ T) :
    (w.extractPathFrom S T).last = v ↔ v ∈ V(w.extractPathFrom S T) ∧ v ∈ T :=
  ⟨fun h ↦ ⟨h ▸ last_mem, h ▸ extractPathFrom_last_mem hw⟩,
    fun ⟨hv, hvT⟩ ↦ extractPathFrom_last_eq_of_mem hv hvT⟩

def breakAt_aux (w : WList α β) (P : α → Prop) [DecidablePred P] (e' : β) (w' : WList α β)
    (L : List (WList α β)) : List (WList α β) :=
  match w with
  | nil x => if P x then nil x :: (cons x e' w') :: L else (cons x e' w') :: L
  | cons x e w => if P x
    then breakAt_aux w P e (nil x) ((cons x e' w') :: L)
    else breakAt_aux w P e (cons x e' w') L

@[simp]
lemma breakAt_aux_length (w : WList α β) (P : α → Prop) [DecidablePred P] (e' : β) (w' : WList α β)
    (L : List (WList α β)) :
    (breakAt_aux w P e' w' L).length = w.vertex.countP P + L.length + 1 := by
  match w with
  | nil x => by_cases hPx : P x <;> unfold breakAt_aux <;> simp [hPx, add_comm]
  | cons x e w =>
    by_cases hPx : P x <;> unfold breakAt_aux <;> simp only [hPx, ↓reduceIte, cons_vertex,
      decide_false, Bool.false_eq_true, not_false_eq_true, decide_true, countP_cons_of_pos,
      countP_cons_of_neg] <;> rw [breakAt_aux_length]
    simp only [length_cons, Nat.add_right_cancel_iff]
    omega

lemma breakAt_aux_append (w : WList α β) (P : α → Prop) [DecidablePred P] (e' : β) (w' : WList α β)
    (L : List (WList α β)) :
    (breakAt_aux w P e' w' L) = breakAt_aux w P e' w' [] ++ L := by
  match w with
  | nil x => by_cases hPx : P x <;> unfold breakAt_aux <;> simp [hPx]
  | cons x e w =>
    by_cases hPx : P x <;> unfold breakAt_aux
    · simp only [hPx, ↓reduceIte]
      rw [breakAt_aux_append, breakAt_aux_append w P (L := [cons x e' w'])]
      simp
    simp only [hPx, ↓reduceIte]
    rw [breakAt_aux_append]

lemma breakAt_aux_eq_concat (w : WList α β) (P : α → Prop) [DecidablePred P] (e' : β)
    (w' w'' : WList α β) :
    (breakAt_aux w P e' w' [w'']) = (breakAt_aux w P e' w' []).concat w'' := by
  rw [breakAt_aux_append, concat_eq_append]

@[simp]
lemma breakAt_aux_foldl (w : WList α β) (P : α → Prop) [DecidablePred P] (e' : β) (w' : WList α β):
    (breakAt_aux w P e' w' []).foldl (· ++ ·) (nil x) = w.reverse.concat e' w'.first ++ w' := by
  match w with
  | nil x => by_cases hPx : P x <;> unfold breakAt_aux <;> simp [hPx]
  | cons x e w =>
    by_cases hPx : P x <;> unfold breakAt_aux <;> simp only [hPx, ↓reduceIte, reverse_cons] <;>
    rw [breakAt_aux_append, List.foldl_append, breakAt_aux_foldl] <;> simp

lemma breakAt_aux_ne_nil' (w : WList α β) (P : α → Prop) [DecidablePred P] (e' : β)
    (w' : WList α β) : (breakAt_aux w P e' w' []) ≠ [] := by
  match w with
  | nil x => by_cases hPx : P x <;> unfold breakAt_aux <;> simp [hPx]
  | cons x e w =>
    by_cases hPx : P x <;> unfold breakAt_aux <;> simp only [hPx, ↓reduceIte]
    · rw [breakAt_aux_append]
      simp
    exact breakAt_aux_ne_nil' w P e (cons x e' w')

@[simp]
lemma breakAt_aux_ne_nil (w : WList α β) (P : α → Prop) [DecidablePred P] (e' : β) (w' : WList α β)
    (L : List (WList α β)) : (breakAt_aux w P e' w' L) ≠ [] := by
  rw [breakAt_aux_append]
  simp [breakAt_aux_ne_nil']

lemma breakAt_aux_getLast (w : WList α β) (P : α → Prop) [DecidablePred P] (e' : β)
    (w' : WList α β) : (breakAt_aux w P e' w' []).getLast (by simp) =
    (w.prefixUntil P).reverse ++ cons w.first e' w' := by
  match w with
  | nil u => by_cases hPu : P u <;> unfold breakAt_aux <;> simp [hPu]
  | cons u e w =>
    by_cases hPu : P u <;> unfold breakAt_aux <;> simp only [hPu, ↓reduceIte, prefixUntil_cons,
      reverse_nil, first_cons, nil_append]
    · suffices (w.breakAt_aux P e (nil u) [] ++ [cons u e' w']).getLast (by simp) = cons u e' w' by
        convert this using 2
        rw [breakAt_aux_append]
      simp
    rw [breakAt_aux_getLast]
    simp

lemma breakAt_aux_head (w : WList α β) (P : α → Prop) [DecidablePred P] (e' : β) (w' : WList α β) :
    (breakAt_aux w P e' w' []).head (by simp) = if w.vertex.all (¬ P ·)
    then (w.suffixFromLast P).reverse ++ cons w.first e' w' else (w.suffixFromLast P).reverse := by
  match w with
  | nil x => by_cases hPx : P x <;> unfold breakAt_aux suffixFromLast <;> simp [hPx]
  | cons x e w =>
    unfold breakAt_aux suffixFromLast
    have h : (w.breakAt_aux P e (nil x) [cons x e' w']).head (by simp) =
      if (w.vertex.all fun x ↦ decide ¬P x)
      then (w.suffixFromLast P).reverse ++ cons w.first e (nil x)
      else (w.suffixFromLast P).reverse := by
      simp only [← breakAt_aux_head, breakAt_aux_append w P e (nil x) [cons x e' w'],
        ne_eq, breakAt_aux_ne_nil, not_false_eq_true, head_append_of_ne_nil]
    by_cases hPx : P x <;> by_cases hPw : w.vertex.all fun x ↦ !decide (P x) <;> simp [hPx, hPw, h]
    · simp only [suffixFromLast, reverse_reverse, prefixUntil_concat, reverse_vertex, decide_not,
      all_reverse, hPw, ↓reduceIte]
      rw [WList.concat_eq_append, prefixUntil_eq_self_of_forall _ _ (by simpa using hPw)]
      simp
    · simp [suffixFromLast, prefixUntil_concat, hPw]
    · rw [breakAt_aux_head]
      simp only [decide_not, hPw, ↓reduceIte, suffixFromLast, reverse_reverse, prefixUntil_concat,
        reverse_vertex, all_reverse, WList.concat_append, reverse_last]
      rw [prefixUntil_eq_self_of_forall _ _ (by simpa using hPw)]
    rw [breakAt_aux_head]
    simp [hPw, suffixFromLast, prefixUntil_concat]

lemma breakAt_aux_isChain_eq (w : WList α β) (P : α → Prop) [DecidablePred P] {e' : β}
    {w' : WList α β} : (w.breakAt_aux P e' w' []).IsChain (·.last = ·.first) := by
  unfold breakAt_aux
  match w with
  | nil u => by_cases hPu : P u <;> simp [hPu]
  | cons u e w =>
    by_cases hPu : P u <;> simp only [hPu, ↓reduceIte]
    · rw [breakAt_aux_append, List.isChain_append]
      simp only [breakAt_aux_isChain_eq, IsChain.singleton, Option.mem_def, head?_cons,
        Option.some.injEq, forall_eq', first_cons, true_and]
      rw [getLast?_eq_getLast_of_ne_nil (by simp)]
      simp [breakAt_aux_getLast]
    exact w.breakAt_aux_isChain_eq P

lemma nonempty_of_mem_breakAt_aux_tail (w : WList α β) (P : α → Prop) [DecidablePred P] {e' : β}
    {w' Q : WList α β} (hQ : Q ∈ (w.breakAt_aux P e' w' []).tail) : Q.Nonempty := by
  unfold breakAt_aux at hQ
  match w with
  | nil x => by_cases hPx : P x <;> simp_all
  | cons x e w =>
    by_cases hPx : P x <;> simp_all only [↓reduceIte]
    · rw [breakAt_aux_append] at hQ
      obtain hQ | rfl := by simpa using hQ
      · exact w.nonempty_of_mem_breakAt_aux_tail P hQ
      simp
    exact w.nonempty_of_mem_breakAt_aux_tail P hQ

lemma breakAt_aux_map_first_eq_vertex_filter (w : WList α β) (P : α → Prop) [DecidablePred P]
    {e' : β} {w' : WList α β} :
    (w.breakAt_aux P e' w' []).tail.map (·.first) = (w.vertex.filter P).reverse := by
  unfold breakAt_aux
  match w with
  | nil x => by_cases hPx : P x <;> simp [hPx]
  | cons x e w =>
    by_cases hPx : P x <;> simp [hPx, ↓reduceIte, -map_tail]
    · rw [breakAt_aux_append]
      simp only [map_append, map_cons, first_cons, map_nil, ne_eq,
        breakAt_aux_ne_nil, not_false_eq_true, tail_append_of_ne_nil]
      rw [w.breakAt_aux_map_first_eq_vertex_filter P]
    rw [breakAt_aux_map_first_eq_vertex_filter]

/-- The segmentation of `w` breaks `w` at every vertex satisfying `P` and returns
  the list of segments. With the possible exception of the first and the last segment,
  all segments have the endpoints satisfying `P`.
  If `P` never occurs, this is `[w]`.
  If `w.first` satisfies `P`, then the first segment is `nil w.first`.
  Similarly, if `w.last` satisfies `P`, then the last segment is `nil w.last`. -/
def breakAt (w : WList α β) (P : α → Prop) [DecidablePred P] : List (WList α β) :=
  match w.reverse with
  | nil x => if P x then [nil x, nil x] else [nil x]
  | cons x e w => if P x
    then breakAt_aux w P e (nil x) [nil x]
    else breakAt_aux w P e (nil x) []

@[simp]
lemma breakAt_nil : (nil x (β := β)).breakAt P = if P x then [nil x, nil x] else [nil x] := rfl

lemma breakAt_reverse_ne_nil (w : WList α β) (P : α → Prop) [DecidablePred P] :
    w.reverse.breakAt P ≠ [] := by
  match w with
  | nil u => by_cases hPu : P u <;> simp [hPu]
  | cons u e w => by_cases hPu : P u <;> simp [breakAt, hPu]

@[simp]
lemma breakAt_ne_nil : w.breakAt P ≠ [] := by
  rw [← w.reverse_reverse]
  apply breakAt_reverse_ne_nil

lemma breakAt_reverse_length (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.reverse.breakAt P).length = w.vertex.countP P + 1 := by
  match w with
  | nil x => by_cases hPx : P x <;> simp [hPx]
  | cons x e w => by_cases hPx : P x <;> simp [breakAt, hPx, breakAt_aux_length]

@[simp]
lemma breakAt_length (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.breakAt P).length = w.vertex.countP P + 1 := by
  conv_lhs => rw [← w.reverse_reverse]
  rw [breakAt_reverse_length]
  simp

lemma breakAt_reverse_foldl_append_cancel (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.reverse.breakAt P).foldl (· ++ ·) (nil x) = w.reverse := by
  unfold breakAt
  rw [reverse_reverse]
  match w with
  | nil u => by_cases hPu : P u <;> simp [hPu]
  | cons u e w =>
    by_cases hPu : P u <;> simp only [hPu, ↓reduceIte, breakAt_aux_foldl, nil_first, concat_last,
      append_nil, reverse_cons]
    rw [breakAt_aux_append, List.foldl_append, breakAt_aux_foldl]
    simp

@[simp]
lemma breakAt_foldl_append_cancel (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.breakAt P).foldl (· ++ ·) (nil x) = w := by
  rw [← w.reverse_reverse, breakAt_reverse_foldl_append_cancel]

@[simp]
lemma breakAt_appendList [Inhabited α] (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.breakAt P)⁺ = w := breakAt_foldl_append_cancel w P

lemma breakAt_reverse_getLast (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.reverse.breakAt P).getLast (by simp) = (w.prefixUntil P).reverse := by
  unfold breakAt
  match w with
  | nil u => by_cases hPu : P u <;> simp [hPu, prefixUntil]
  | cons u e w =>
    by_cases hPu : P u <;> simp only [reverse_cons, concat_reverse, reverse_reverse, hPu,
      ↓reduceIte, prefixUntil]
    · suffices (w.breakAt_aux P e (nil u) [] ++ [nil u]).getLast (by simp) = nil u by
        convert this using 2
        rw [breakAt_aux_append]
      simp
    rw [breakAt_aux_getLast, WList.concat_eq_append]
    simp

lemma breakAt_getLast (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.breakAt P).getLast (by simp) = w.suffixFromLast P := by
  rw [← w.reverse_reverse, breakAt_reverse_getLast, reverse_reverse]
  rfl

lemma breakAt_reverse_head (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.reverse.breakAt P).head (by simp) = (w.suffixFromLast P).reverse := by
  unfold breakAt
  match w with
  | nil u => by_cases hPu : P u <;> simp [hPu, suffixFromLast]
  | cons u e w =>
    by_cases hPu : P u <;> simp only [reverse_cons, concat_reverse, reverse_reverse, hPu,
      ↓reduceIte, suffixFromLast]
    · suffices (w.breakAt_aux P e (nil u) [] ++ [nil u]).head (by simp) =
        (w.reverse.concat e u).prefixUntil P by
        convert this using 2
        rw [breakAt_aux_append]
      simp only [ne_eq, breakAt_aux_ne_nil, not_false_eq_true, head_append_of_ne_nil,
        breakAt_aux_head, decide_not, suffixFromLast, reverse_reverse]
      by_cases hPw : w.vertex.all fun x ↦ !decide (P x) <;> simp [hPw, prefixUntil_concat]
      simp [w.reverse.prefixUntil_eq_self_of_forall P (by simpa [mem_reverse] using hPw),
        WList.concat_eq_append]
    simp only [breakAt_aux_head, decide_not, suffixFromLast, reverse_reverse]
    by_cases hPw : w.vertex.all fun x ↦ !decide (P x) <;> simp [hPw, prefixUntil_concat]
    simp [WList.concat_eq_append, w.reverse.prefixUntil_eq_self_of_forall P (by simpa using hPw)]

@[simp]
lemma breakAt_head (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.breakAt P).head (by simp) = w.prefixUntil P := by
  rw [← w.reverse_reverse, breakAt_reverse_head, suffixFromLast, reverse_reverse]

lemma breakAt_reverse_isChain_eq (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.reverse.breakAt P).IsChain (·.last = ·.first) := by
  simp only [breakAt, reverse_reverse]
  match w with
  | nil x => by_cases hPx : P x <;> simp [hPx]
  | cons x e w =>
    by_cases hPx : P x <;> simp only [hPx, ↓reduceIte]
    · rw [breakAt_aux_append, List.isChain_append]
      simp only [breakAt_aux_isChain_eq, IsChain.singleton, Option.mem_def, head?_cons,
        Option.some.injEq, forall_eq', nil_first, true_and]
      rw [getLast?_eq_getLast_of_ne_nil (by simp)]
      simp [breakAt_aux_getLast]
    exact breakAt_aux_isChain_eq w P

lemma breakAt_isChain_eq (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.breakAt P).IsChain (·.last = ·.first) := by
  rw [← w.reverse_reverse]
  apply w.reverse.breakAt_reverse_isChain_eq

@[simp]
lemma decomposeTo_breakAt [Inhabited α] (w : WList α β) (P : α → Prop) [DecidablePred P] :
    w.DecomposeTo (w.breakAt P) where
  nonempty := breakAt_ne_nil
  append := (w.breakAt_appendList P).symm
  chain_eq := breakAt_isChain_eq w P

lemma nonempty_of_mem_breakAt_dropLast_tail' (w : WList α β) (P : α → Prop) [DecidablePred P]
    {Q : WList α β} (hQ : Q ∈ (w.reverse.breakAt P).dropLast.tail) : Q.Nonempty := by
  unfold breakAt at hQ
  match w with
  | nil x => by_cases hPx : P x <;> simp [hPx] at hQ
  | cons x e w =>
    by_cases hPx : P x <;> simp [hPx] at hQ
    · rw [breakAt_aux_append, ← concat_eq_append] at hQ
      simp only [concat_eq_append, ne_eq, cons_ne_self, not_false_eq_true,
        dropLast_append_of_ne_nil, dropLast_singleton, List.append_nil] at hQ
      exact nonempty_of_mem_breakAt_aux_tail w P hQ
    rw [tail_dropLast] at hQ
    exact nonempty_of_mem_breakAt_aux_tail w P <| mem_of_mem_dropLast hQ

lemma nonempty_of_mem_breakAt_dropLast_tail (w : WList α β) (P : α → Prop) [DecidablePred P]
    {Q : WList α β} (hQ : Q ∈ (w.breakAt P).dropLast.tail) : Q.Nonempty := by
  rw [← w.reverse_reverse] at hQ
  exact nonempty_of_mem_breakAt_dropLast_tail' w.reverse P hQ

lemma breakAt_reverse_tail_map_first_eq_vertex_filter_reverse (w : WList α β) (P : α → Prop)
    [DecidablePred P] : (w.reverse.breakAt P).tail.map (·.first) = w.reverse.vertex.filter P := by
  unfold breakAt
  match w with
  | nil x => by_cases hPx : P x <;> simp [hPx]
  | cons x e w =>
    by_cases hPx : P x <;> conv_lhs => simp only [reverse_cons, concat_reverse, reverse_reverse,
      hPx, ↓reduceIte]
    · conv_lhs => simp [breakAt_aux_eq_concat, -map_tail]
      simp [w.breakAt_aux_map_first_eq_vertex_filter P, hPx]
    simpa [w.breakAt_aux_map_first_eq_vertex_filter P]

lemma breakAt_tail_map_first_eq_vertex_filter (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.breakAt P).tail.map first = w.vertex.filter P := by
  rw [← w.reverse_reverse, breakAt_reverse_tail_map_first_eq_vertex_filter_reverse, reverse_reverse]

lemma breakAt_tail_map_first_eq_inter (w : WList α β) (S : Set α) [DecidablePred (· ∈ S)] :
    {x | x ∈ (w.breakAt (· ∈ S)).tail.map first} = V(w) ∩ S := by
  ext x
  rw [breakAt_tail_map_first_eq_vertex_filter]
  simp

-- lemma nil_mem_breakAt_iff (w : WList α β) (P : α → Prop) [DecidablePred P] (x : α) :
--     nil x ∈ w.breakAt P ↔ (P w.first ∧ x = w.first) ∨ (P w.last ∧ x = w.last) := by
--   sorry

lemma IsSublist.exists_append_append {w₀ : WList α β} (hw₀ : w₀.IsSublist w) (hw : w.vertex.Nodup) :
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
lemma IsSublist.exists_isPrefix_isSuffix {w₀ : WList α β} (hw₀ : w₀.IsSublist w)
    (hw : w.vertex.Nodup) : ∃ w', w'.IsPrefix w ∧ w₀.IsSuffix w' := by
  obtain ⟨w₁, w₂, h1, h2, rfl⟩ := hw₀.exists_append_append hw
  exact ⟨w₁ ++ w₀, isPrefix_append_right (by simpa), isSuffix_append_left ..⟩

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

/-- The sublist order as a partial order on `WList α β`, for access to order API.  -/
instance : PartialOrder (WList α β) where
  le := IsSublist
  le_refl := isSublist_refl
  le_trans _ _ _ := IsSublist.trans
  le_antisymm _ _ := IsSublist.antisymm

@[simp]
lemma le_iff_isSublist : w₁ ≤ w₂ ↔ w₁.IsSublist w₂ := Iff.rfl

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

lemma tail_dropLast (hw : w.length ≠ 1) : w.tail.dropLast = w.dropLast.tail := by
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

-- lemma Nontrivial.lastEdge_mem_tail (hw : w.Nontrivial) : hw.nonempty.lastEdge ∈ w.tail.edge := by
--   rw [tail_lastE]
  -- cases hw withhC.isWalk.edgeSet_subset
  -- | cons_cons u e v f w =>
  --   simp

    -- Nonempty.lastEdge w (show w.Nonempty by rw [WList.nonempty_iff_]) ∈ w.tail.edge := sorry

-- def take : WList α β → ℕ → WList α β
--   | nil x, _ => nil x
--   | cons x _ _, 0 => nil x
--   | cons x e w, n+1 => cons x e (w.take n)

-- @[simp]
-- lemma take_nil (x : α) (n : ℕ) : (nil x (β := β)).take n = nil x := rfl

-- @[simp]
-- lemma take_zero (w : WList α β) : w.take 0 = nil w.first := by
--   cases w with simp [take]

-- @[simp]
-- lemma take_cons_succ (x e) (w : WList α β) (n : ℕ) :
--   (cons x e w).take (n+1) = cons x e (w.take n) := rfl

lemma idxOf_eq_length_prefixUntilVertex [DecidableEq α] (w : WList α β) (x : α) (hx : x ∈ w) :
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
    exact ⟨mt w.dedup_isSublist.vertex_sublist.mem huw, w.dedup_vertex_nodup⟩
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
--       exact hVd.1.left_mem
--     · rw [cons_validIn] at hVd ⊢
--       refine ⟨?_, hVd.2.endIf _ ⟩
--       convert hVd.1 using 1
--       simp only [mem_cons_iff, exists_eq_or_imp, hPx, false_or] at h
--       exact endIf_first h

-- lemma endIf_vertex_sublist {w : WList α β} (h : ∃ u ∈ w, P u) :
--     (w.endIf h).vertex ⊆ w.vertex := by
--   match w with
--   | .nil x => simp only [endIf, nil_vertex, List.Subset.refl]
--   | .cons x e w =>
--     simp only [endIf, cons_vertex]
--     split_ifs with h
--     · simp only [nil_vertex, cons_subset, mem_cons, true_or, nil_subset, subset_cons_of_subset,
--         and_self]
--     · simp only [cons_vertex, cons_subset, mem_cons, true_or, true_and]
--       refine List.Subset.trans ?_ (List.subset_cons_self _ _)
--       apply endIf_vertex_sublist

-- lemma endIf_mem_vertex {w : WList α β} (h : ∃ u ∈ w, P u) (hv : v ∈ w.endIf h):
--     ¬ P v ∨ v = (w.endIf h).last := by
--   match w with
--   | .nil x => simp_all only [endIf_nil, mem_nil_iff, nil_last, or_true]
--   | .cons x e w =>
--     rw [endIf_cons]
--     split_ifs with hPx
--     · simp_all only [endIf_cons, dite_true, mem_nil_iff, not_true_eq_false, nil_last, or_true]
--     · simp_all only [endIf_cons, dite_false, mem_cons_iff, last_cons]
--       obtain rfl | hvmem := hv
--       · exact Or.inl hPx
--       · simp only [mem_cons_iff, exists_eq_or_imp, hPx, false_or] at h
--         exact endIf_mem_vertex h hvmem

-- lemma endIf_exists_isLink_last {w : WList α β} (h : ∃ u ∈ w, P u) (hVd : w.ValidIn G)
--     (hNonempty : (w.endIf h).Nonempty) :
--     ∃ v ∈ (w.endIf h), ¬ P v ∧ ∃ e, G.IsLink e v (w.endIf h).last := by
--   match w with
--   | .nil x => simp_all only [endIf_nil, Nonempty.not_nil]
--   | .cons x e (nil y) =>
--     simp_all only [cons_validIn, nil_first, nil_validIn, endIf_cons, endIf_nil, dite_eq_ite]
--     split_ifs with hPx
--     · simp_all only [cons_vertex, nil_vertex, mem_cons, notMem_nil, or_false, exists_eq_or_imp,
--       exists_eq_left, true_or, ite_true, Nonempty.not_nil]
--     · simp_all only [mem_cons_iff, mem_nil_iff, exists_eq_or_imp, exists_eq_left, false_or,
--       ite_false, Nonempty.cons_true, last_cons, nil_last, not_false_eq_true, true_and,
--       not_true_eq_false, false_and, or_false]
--       use e
--       exact hVd.1
--   | .cons x e (cons y e' w) =>
--     unfold endIf
--     split_ifs with hPx
--     · simp_all only [cons_validIn, first_cons, endIf_cons, dite_true, Nonempty.not_nil]
--     · by_cases hPy : P y
--       · simp_all only [cons_validIn, first_cons, endIf_cons, dite_true, dite_eq_ite, ite_false,
--         Nonempty.cons_true, mem_cons_iff, mem_nil_iff, last_cons, nil_last,
--      exists_eq_or_imp, not_false_eq_true, true_and, exists_eq_left, not_true_eq_false, false_and,
--         or_false]
--         use e
--         exact hVd.1
--       · let w' := cons y e' w
--         rw [last_cons]
--         have h' : ∃ u ∈ w', P u := by
--           change ∃ u ∈ cons x e w', P u at h
--           simpa only [mem_cons_iff, exists_eq_or_imp, hPx, false_or] using h
--         have hNonempty' : (w'.endIf h').Nonempty := by
--           simp only [endIf_cons, hPy, ↓reduceDIte, Nonempty.cons_true, w']
--         obtain ⟨a, ha, hh⟩ := endIf_exists_isLink_last (w := w') h' hVd.2 hNonempty'
--         refine ⟨a, ?_, hh⟩
--         rw [mem_cons_iff]
--         right
--         exact ha

end WList
