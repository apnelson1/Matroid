import Matroid.ForMathlib.Graph.WList.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Data.Finset.Disjoint

open Set Function List Nat WList
variable {α β : Type*} {u v x y z : α} {e e' f g : β} {S T U: Set α}
  {F F' : Set β} {w w₁ w₂ : WList α β}

namespace WList

/-- Add an edge and a vertex to the end of a WList -/
def concat : WList α β → β → α → WList α β
| nil x, e, y => cons x e (nil y)
| cons x e w, f, y => cons x e (w.concat f y)

/-- Glue two wLists `w₁, w₂` together. The last vertex of `w₁` is ignored,
so this is most reasonable if `w₁.last = w₂.first` -/
def append : WList α β → WList α β → WList α β
| nil _x, w => w
| cons x e w, w' => cons x e (w.append w')

instance instAppend : Append (WList α β) where
  append := append

/-- Properties of concat operation -/
@[simp]
lemma nil_concat : (nil x).concat e y = cons x e (nil y) := rfl

@[simp]
lemma cons_concat : (cons x e w).concat f y = cons x e (w.concat f y) := rfl

@[simp]
lemma concat_first : (w.concat e v).first = w.first := by
  cases w with simp [concat]

@[simp]
lemma concat_last : (w.concat e v).last = v := by
  induction w with | nil => rfl | cons => simpa [concat]

@[simp]
lemma concat_vx : (w.concat e v).vx = w.vx ++ [v] := by
  induction w with | nil => rfl | cons => simpa [concat]

@[simp]
lemma concat_edge : (w.concat e v).edge = w.edge ++ [e] := by
  induction w with | nil => rfl | cons => simpa [concat]

@[simp]
lemma concat_length : (w.concat e v).length = w.length + 1 := by
  induction w with | nil => rfl | cons => simpa [concat]

@[simp]
lemma mem_concat : x ∈ w.concat e y ↔ x ∈ w ∨ x = y := by
  induction w with simp_all [or_assoc]

@[simp]
lemma concat_nonempty (w : WList α β) (e x) : (w.concat e x).Nonempty := by
  induction w with simp_all

@[simp]
lemma concat_vxSet_eq (w : WList α β) (e x) : (w.concat e x).V = insert x w.V := by
  induction w with | nil => simp [pair_comm] | cons _ _ _ ih => simp [ih, insert_comm]

lemma get_concat (w : WList α β) (e x) {n} (hn : n ≤ w.length) :
    (w.concat e x).get n = w.get n := by
  induction n generalizing w with
  | zero => simp
  | succ n IH => cases w with
    | nil => simp at hn
    | cons u f w => simp [IH w (by simpa using hn)]

lemma dInc_concat (w : WList α β) (e x) : (w.concat e x).DInc e w.last x := by
  induction w with simp_all

lemma DInc.concat (h : w.DInc e x y) (f) (v) : (w.concat f v).DInc e x y := by
  induction h with simp_all

lemma dInc_concat_iff :
    (w.concat f u).DInc e x y ↔ w.DInc e x y ∨ (f = e ∧ x = w.last ∧ y = u) := by
  induction w with
  | nil v =>
    simp only [nil_concat, dInc_cons_iff, nil_first, not_nil_dInc, or_false, nil_last, false_or]
    tauto
  | cons v g w ih =>
    simp only [cons_concat, dInc_cons_iff, concat_first, ih, last_cons]
    tauto

lemma inc₂_concat_iff : (w.concat f u).Inc₂ e x y ↔
    w.Inc₂ e x y ∨ (f = e ∧ (x = w.last ∧ y = u ∨ x = u ∧ y = w.last)) := by
  rw [inc₂_iff_dInc, dInc_concat_iff, dInc_concat_iff, inc₂_iff_dInc]
  tauto

/- Properties of append operation -/
@[simp]
lemma append_notation : append w₁ w₂ = w₁ ++ w₂ := rfl

@[simp]
lemma nil_append : nil x ++ w₂ = w₂ := rfl

@[simp]
lemma cons_append : cons x e w₁ ++ w₂ = cons x e (w₁ ++ w₂) := rfl

lemma append_assoc (w₁ w₂ w₃ : WList α β) : (w₁ ++ w₂) ++ w₃ = w₁ ++ (w₂ ++ w₃) := by
  induction w₁ with simp_all

@[simp]
lemma append_vx : (w₁ ++ w₂).vx = w₁.vx.dropLast ++ w₂.vx := by
  induction w₁ with
  | nil => simp
  | cons x e w ih =>
      rw [cons_append, cons_vx, cons_vx, List.dropLast_cons_of_ne_nil vx_ne_nil, List.cons_append]
      simpa

lemma append_vx' {w₁ w₂ : WList α β} (heq : w₁.last = w₂.first) :
    (w₁ ++ w₂).vx = w₁.vx ++ w₂.vx.tail := by
  rw [append_vx, ← w₁.vx.dropLast_concat_getLast (by simp), List.append_assoc,
    vx_getLast, dropLast_concat, heq, ← vx_head]
  simp [- vx_head]

protected lemma concat_eq_append (w : WList α β) (e) (x) :
    w.concat e x = w ++ (cons w.last e (nil x)) := by
  induction w with simp_all

@[simp]
lemma append_edge {w₁ w₂ : WList α β} : (w₁ ++ w₂).edge = w₁.edge ++ w₂.edge := by
  induction w₁ with simp_all

@[simp]
lemma append_length : (w₁ ++ w₂).length = w₁.length + w₂.length := by
  induction w₁ with simp_all [add_right_comm]

@[simp]
lemma append_nil (h : w.last = x) : w ++ (nil x) = w := by
  induction w with simp_all

@[simp]
lemma append_first_of_eq (h : w₁.last = w₂.first):
  (w₁ ++ w₂).first = w₁.first := by
  induction w₁ with simp_all

@[simp]
lemma append_first_of_nonempty (h : w₁.Nonempty) :
  (w₁ ++ w₂).first = w₁.first := by
  induction w₁ with simp_all

@[simp]
lemma append_last : (w₁ ++ w₂).last = w₂.last := by
  induction w₁ with simp_all

lemma append_right_injective : Injective (w ++ ·) :=
  fun w₁ w₂ h ↦ by induction w with simp_all

@[simp]
lemma append_right_inj_iff : w ++ w₁ = w ++ w₂ ↔ w₁ = w₂ :=
  ⟨fun h ↦ append_right_injective h, fun h ↦ by rw [h]⟩

@[simp]
lemma append_right_eq_self : w ++ w₁ = w ↔ w₁ = nil w.last := by
  induction w with simp_all

@[simp]
lemma append_left_eq_self : w₁ ++ w = w ↔ w₁.Nil :=
  ⟨fun h ↦ by simpa using congr_arg length h, fun h ↦ by rw [h.eq_nil_first, nil_append]⟩

@[simp]
lemma append_eq_nil_iff : w₁ ++ w₂ = nil x ↔ w₁.Nil ∧ w₂ = nil x := by
  induction w₁ with simp

@[simp]
lemma nil_append_iff : (w₁ ++ w₂).Nil ↔ w₁.Nil ∧ w₂.Nil := by
  simp [← length_eq_zero]

/-- See `prefixUntilVx_append_suffixFromVx`. The `u ∈ w` assumption isn't needed. -/
lemma eq_append_of_vx_mem {w : WList α β} {u : α} (hmem : u ∈ w) :
    ∃ w₁ w₂ : WList α β, w = w₁ ++ w₂ ∧ w₁.last = u ∧ w₂.first = u := by
  induction w with
  | nil x =>
    rw [mem_nil_iff] at hmem
    subst u
    exact ⟨nil x, nil x, rfl, rfl, rfl⟩
  | cons x e w ih =>
    rw [mem_cons_iff] at hmem
    obtain rfl | h := hmem
    · exact ⟨nil u, cons u e w, rfl, rfl, rfl⟩
    · obtain ⟨w₁, w₂, rfl, hfin, hfirst⟩ := ih h
      use cons x e w₁, w₂
      simp only [cons_append, last_cons, hfin, hfirst, and_self]

lemma eq_append_cons_of_edge_mem {w : WList α β} {e : β} (he : e ∈ w.edge) :
    ∃ w₁ w₂ : WList α β, w = w₁ ++ cons w₁.last e w₂ ∧ e ∉ w₁.edge := by
  induction w with
  | nil x => simp only [nil_edge, not_mem_nil] at he
  | cons x e' w ih =>
    simp only [cons_edge, mem_cons] at he
    obtain rfl | he' := he
    · use nil x, w, rfl, by simp only [nil_edge, not_mem_nil, not_false_eq_true]
    · by_cases h : e = e'
      · subst e'
        use nil x, w, rfl, by simp only [nil_edge, not_mem_nil, not_false_eq_true]
      · obtain ⟨w₁, w₂, rfl, hnin⟩ := ih he'
        use cons x e' w₁, w₂, by simp only [last_cons, cons_append]
        simp only [cons_edge, mem_cons, h, hnin, or_self, not_false_eq_true]



/-- Reverse the order of the vertices and edges of a wList. -/
def reverse : WList α β → WList α β
| nil x => nil x
| cons x e w => w.reverse.concat e x

/-- Properties of reverse operation -/
@[simp]
lemma reverse_nil : (nil x : WList α β).reverse = nil x := rfl

@[simp]
lemma reverse_cons : (cons x e w).reverse = (w.reverse).concat e x := rfl

@[simp]
lemma reverse_nonempty : w.reverse.Nonempty ↔ w.Nonempty := by
  induction w with simp_all

lemma Nonempty.reverse (hw : w.Nonempty) : w.reverse.Nonempty :=
  reverse_nonempty.2 hw

@[simp]
lemma reverse_nil_iff (w : WList α β) : w.reverse.Nil ↔ w.Nil := by
  induction w with simp_all

@[simp]
lemma reverse_first : (reverse w).first = w.last := by
  induction w with
  | nil x => simp [reverse]
  | cons x e w ih => simp [reverse, ih]

@[simp]
lemma reverse_last : (reverse w).last = w.first := by
  induction w with
  | nil x => simp [reverse]
  | cons x e w ih => simp [reverse, ih]

@[simp]
lemma reverse_vx : (reverse w).vx = w.vx.reverse := by
  induction w with
  | nil x => simp [reverse]
  | cons x e w ih => simp [reverse, ih]

@[simp]
lemma reverse_edge {w : WList α β} : (reverse w).edge = w.edge.reverse := by
  induction w with
  | nil x => simp [reverse]
  | cons x e w ih => simp [reverse, ih]

@[simp]
lemma reverse_length {w : WList α β} : (reverse w).length = w.length := by
  induction w with
  | nil x => simp [reverse]
  | cons x e w ih => simp [reverse, ih]

lemma reverse_append {w₁ w₂ : WList α β} (h_eq : w₁.last = w₂.first) :
    (w₁ ++ w₂).reverse = w₂.reverse ++ w₁.reverse := by
  induction w₁ with
  | nil u => rw [nil_append, reverse_nil, append_nil (by simpa using h_eq.symm)]
  | cons u e w₁ ih =>
  simp only [cons_append, reverse_cons, ih (by simpa using h_eq)]
  rw [WList.concat_eq_append, WList.concat_eq_append, ← append_assoc]
  simp

@[simp]
lemma concat_reverse (w : WList α β) (e) (x) : (w.concat e x).reverse = cons x e w.reverse := by
  rw [WList.concat_eq_append, reverse_append (by simp)]
  simp

lemma Nonempty.firstEdge_concat (hw : w.Nonempty) :
    (concat_nonempty w e x).firstEdge = hw.firstEdge := by
  induction w with | nil u => simp at hw | cons => simp

@[simp]
lemma reverse_reverse (w : WList α β) : w.reverse.reverse = w := by
  induction w with | nil => simp | cons => simpa

lemma reverse_inj (h : w₁.reverse = w₂.reverse) : w₁ = w₂ := by
  rw [← reverse_reverse w₁, h, reverse_reverse]

@[simp]
lemma reverse_inj_iff : w₁.reverse = w₂.reverse ↔ w₁ = w₂ :=
  ⟨reverse_inj, fun h ↦ by rw [h]⟩

lemma reverse_eq_comm : w₁.reverse = w₂ ↔ w₁ = w₂.reverse := by
  rw [← reverse_reverse w₂, reverse_inj_iff, reverse_reverse]

@[simp]
lemma reverse_nontrivial_iff : w.reverse.Nontrivial ↔ w.Nontrivial := by
  rw [← one_lt_length_iff, reverse_length, one_lt_length_iff]

alias ⟨_, Nontrivial.reverse⟩ := reverse_nontrivial_iff

@[simp]
lemma mem_reverse : x ∈ w.reverse ↔ x ∈ w := by
  induction w with
  | nil => simp
  | cons u e w ih => simp [ih, or_comm]

@[simp]
lemma reverse_vxSet (w : WList α β) : w.reverse.V = w.V := by
  simp [WList.V]

lemma DInc.reverse (h : w.DInc e x y) : w.reverse.DInc e y x := by
  induction h with
  | cons_left x e w =>
    convert dInc_concat _ _ _ using 1
    simp
  | cons _ _ _ ih => apply ih.concat

@[simp]
lemma dInc_reverse_iff : w.reverse.DInc e x y ↔ w.DInc e y x :=
  ⟨fun h ↦ by simpa using h.reverse, DInc.reverse⟩

@[simp]
lemma inc₂_reverse_iff : w.reverse.Inc₂ e x y ↔ w.Inc₂ e x y := by
  simp [inc₂_iff_dInc, or_comm]

lemma concat_induction {motive : WList α β → Prop} (nil : ∀ u, motive (nil u))
    (concat : ∀ {w} e x, motive w → motive (w.concat e x)) (w : WList α β) : motive w := by
  suffices h : ∀ (w' : WList α β), motive w'.reverse by simpa using (h w.reverse)
  intro w'
  induction w' with
  | nil u => exact nil u
  | cons u e w ih => exact concat _ _ ih


/-- The last edge of a nonempty `WList` -/
def Nonempty.lastEdge (w : WList α β) (hw : w.Nonempty) : β := hw.reverse.firstEdge

@[simp]
lemma Nonempty.firstEdge_reverse (hw : w.Nonempty) :
    hw.reverse.firstEdge w.reverse = hw.lastEdge := rfl

lemma Nonempty.lastEdge_cons (hw : w.Nonempty) : (cons_nonempty x e w).lastEdge = hw.lastEdge := by
  simp only [lastEdge, reverse_cons]
  rw [Nonempty.firstEdge_concat]

@[simp]
lemma lastEdge_concat (w : WList α β) (e : β) (x : α) : (concat_nonempty w e x).lastEdge = e := by
  simp [Nonempty.lastEdge]

@[simp]
lemma Nonempty.lastEdge_mem (hw : w.Nonempty) : hw.lastEdge w ∈ w.edge := by
  simpa [firstEdge_reverse hw] using hw.reverse.firstEdge_mem

end WList
