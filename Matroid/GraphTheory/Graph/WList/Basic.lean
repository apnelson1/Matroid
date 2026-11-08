module

public import Matroid.GraphTheory.Graph.WList.Defs
public import Matroid.ForMathlib.List.Basic

/-!
Walk lists: concatenation, reversal, maps, and sublist relations.
-/

@[expose] public section

/-! ## Concatenation, reversal, and maps -/

section

open Set Function List Nat WList
variable {α β : Type*} {u v x y z : α} {e e' f g : β} {S T U: Set α}
  {F F' : Set β} {w w₁ w₂ : WList α β}

namespace WList

/-- Add an edge and a vertex to the end of a WList -/
def concat : WList α β → β → α → WList α β
| nil x, e, y => cons x e (nil y)
| cons x e w, f, y => cons x e (w.concat f y)

@[simp, grind =]
lemma concat_length : (w.concat e v).length = w.length + 1 := by
  induction w with | nil => rfl | cons => simpa [concat]


inductive TsiLw (α β : Type*) where
| nil (u : α) : TsiLw α β
| concat (w : TsiLw α β) (e : β) (u : α) : TsiLw α β

@[simp]
def toWList : TsiLw α β → WList α β
| .nil u => nil u
| .concat w e u => concat (toWList w) e u

@[simp]
def TsiLw.cons : α → β → TsiLw α β → TsiLw α β
| x, e, .nil u => .concat (nil x) e u
| x, e, .concat w e' u => (cons x e w).concat e' u

@[simp]
def fromWList : WList α β → TsiLw α β
| nil u => .nil u
| cons x e w => TsiLw.cons x e (fromWList w)

@[simp]
lemma concat_fromWList : fromWList (concat w e u) = (fromWList w).concat e u := by
  fun_induction fromWList with
  | case1 v => simp only [concat, fromWList, TsiLw.cons]
  | case2 x e w ih => simp [ih, TsiLw.cons, fromWList, concat]

@[simp]
lemma cons_toWList {w : TsiLw α β} : toWList (TsiLw.cons x e w) = cons x e (toWList w) := by
  fun_induction toWList with
  | case1 u => simp [TsiLw.cons, toWList, concat]
  | case2 w e u ih => simp [ih, TsiLw.cons, toWList, concat]

def TsiLw_equiv : TsiLw α β ≃ WList α β where
  toFun w := toWList w
  invFun w := fromWList w
  left_inv w := by
    induction w with
    | nil u => simp
    | concat w e u ih => simp [ih]
  right_inv w := by
    induction w with
    | nil u => simp
    | cons w e u ih => simp [ih]

@[simp]
def TsiLw.length : TsiLw α β → Nat
| .nil _ => 0
| .concat w _ _ => w.length + 1

@[simp]
lemma TsiLw.length_cons {w : TsiLw α β} : (TsiLw.cons x e w).length = w.length + 1 := by
  induction w with
  | nil u => simp [TsiLw.cons]
  | concat w e u ih => simp [ih, TsiLw.cons, length]

@[simp]
lemma TsiLw.length_fromWList : (fromWList w).length = w.length := by
  induction w with
  | nil u => rfl
  | cons u e w ih => simp [fromWList, cons_length, ih]

@[simp]
lemma TsiLw.length_toWList {w : TsiLw α β} : (toWList w).length = w.length := by
  induction w with
  | nil u => rfl
  | concat w e u ih => simp [ih, TsiLw.length]

-- set_option linter.unusedVariables false in
-- def append' (w1 w2 : WList α β) : WList α β :=
--   match h1 : fromWList w1 with
--   | .nil _ => w2
--   | .concat w e u => cons u e (append' (toWList w) w2)
--   termination_by w1.length
--   decreasing_by
--     apply_fun TsiLw.length at h1
--     simp only [TsiLw.length_fromWList, TsiLw.length] at h1
--     simp [h1]

/-- Glue two wLists `w₁, w₂` together. The last vertex of `w₁` is ignored,
so this is most reasonable if `w₁.last = w₂.first` -/
def append : WList α β → WList α β → WList α β
| nil _x, w => w
| cons x e w, w' => cons x e (w.append w')

instance instAppend : Append (WList α β) where
  append := append

/-- Properties of concat operation -/
@[simp, grind =]
lemma nil_concat : (nil x).concat e y = cons x e (nil y) := rfl

@[simp, grind =]
lemma cons_concat : (cons x e w).concat f y = cons x e (w.concat f y) := rfl

@[simp, grind =]
lemma concat_first : (w.concat e v).first = w.first := by
  cases w with simp [concat]

@[simp, grind =]
lemma concat_last : (w.concat e v).last = v := by
  induction w with | nil => rfl | cons => simpa [concat]

@[simp, grind =]
lemma concat_vertex : (w.concat e v).vertex = w.vertex ++ [v] := by
  induction w with | nil => rfl | cons => simpa [concat]

@[simp, grind =]
lemma concat_edge : (w.concat e v).edge = w.edge ++ [e] := by
  induction w with | nil => rfl | cons => simpa [concat]

@[simp, grind =]
lemma concat_edgeSet : E(w.concat e v) = insert e E(w)  := by
  simp [Set.ext_iff, or_comm]

@[simp]
lemma mem_concat : x ∈ w.concat e y ↔ x ∈ w ∨ x = y := by
  induction w with simp_all [or_assoc]

@[simp]
lemma concat_nonempty (w : WList α β) (e x) : (w.concat e x).Nonempty := by
  induction w with simp_all

@[simp, grind =]
lemma concat_vertexSet_eq (w : WList α β) (e x) : V(w.concat e x) = insert x V(w) := by
  induction w with | nil => simp [pair_comm] | cons _ _ _ ih => simp [ih, insert_comm]

@[simp]
lemma idxOf_concat_of_mem [DecidableEq α] (hx : x ∈ w) : (w.concat e y).idxOf x = w.idxOf x := by
  induction w with | nil u => simp_all | cons u f w ih =>
  obtain rfl | hu := eq_or_ne x u
  · rw [cons_concat, idxOf_cons_self, idxOf_cons_self]
  rw [cons_concat, idxOf_cons_ne hu.symm, idxOf_cons_ne hu.symm]
  simp_all

@[simp]
lemma idxOf_concat_of_notMem [DecidableEq α] (hx : x ∉ w) :
    (w.concat e x).idxOf x = w.length + 1 := by
  induction w with
  | nil u => simp [nil_concat, nil_length, zero_add, (ne_of_not_mem_cons hx).symm]
  | cons u f w ih =>
  simp only [mem_cons_iff, not_or, ← ne_eq] at hx
  simp [hx.1.symm, ih hx.2]

lemma idxOf_cons_concat_of_ne [DecidableEq α] (hvu : v ≠ u) (hv : v ∈ cons u e (w.concat f u)) :
    v ∈ w ∧ (cons u e (w.concat f u)).idxOf v = w.idxOf v + 1 := by
  simp only [mem_cons_iff, mem_concat] at hv
  obtain (rfl | hvw | rfl) := hv
  · contradiction
  · exact ⟨hvw, by simp [idxOf_cons_ne hvu.symm, idxOf_concat_of_mem hvw]⟩
  · contradiction

lemma get_concat (w : WList α β) (e x) {n} (hn : n ≤ w.length) :
    (w.concat e x).get n = w.get n := by
  induction n generalizing w with | zero => simp | succ n IH => cases w with
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
    grind
  | cons v g w ih =>
    simp only [cons_concat, dInc_cons_iff, concat_first, ih, last_cons]
    grind

lemma isLink_concat_iff : (w.concat f u).IsLink e x y ↔
    w.IsLink e x y ∨ (f = e ∧ (x = w.last ∧ y = u ∨ x = u ∧ y = w.last)) := by
  rw [isLink_iff_dInc, dInc_concat_iff, dInc_concat_iff, isLink_iff_dInc]
  tauto

protected lemma concat_inj_left : w₁.concat e x = w₂.concat e x ↔ w₁ = w₂ := by
  refine ⟨fun h ↦ ext_vertex_edge ?_ ?_, fun h ↦ h ▸ rfl⟩
  · apply_fun WList.vertex at h
    simpa using h
  apply_fun WList.edge at h
  simpa using h

lemma concat_injective : Injective (WList.concat · e x : WList α β → WList α β) :=
  fun _ _ ↦ WList.concat_inj_left.1

protected lemma concat_inj_right : w.concat e x = w.concat e y ↔ x = y := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  apply_fun WList.vertex at h
  simpa using h

@[simp]
lemma dIncFirst_concat_of_mem [DecidableEq β] (w : WList α β) (he : e ∈ w.edge) :
    (w.concat f x).dIncFirst (by grind [concat_edge] : e ∈ _) = w.dIncFirst he := by
  induction w with
  | nil u => simp at he
  | cons u f w ih =>
    obtain (rfl | hef) := eq_or_ne e f
    · simp [dIncFirst]
    simp only [cons_edge, mem_cons, hef, false_or] at he
    simp [dIncFirst, hef, ih he]

lemma dIncFirst_concat [DecidableEq β] (w : WList α β) (he : e ∈ (w.concat f x).edge) :
    (w.concat f x).dIncFirst he = if hew : e ∈ w.edge then w.dIncFirst hew else (w.last, x) := by
  induction w with
  | nil u =>
    simp only [nil_concat, cons_edge, nil_edge, mem_cons, not_mem_nil, or_false] at he
    simp [dIncFirst, he]
  | cons u e' w ih =>
    rw [cons_concat, cons_edge, mem_cons] at he
    obtain (rfl | hef) := eq_or_ne e e'
    · simp [dIncFirst]
    simp [dIncFirst, ih (he.resolve_left hef), hef]

/- Properties of append operation -/
@[simp]
lemma append_notation : append w₁ w₂ = w₁ ++ w₂ := rfl

@[simp, grind =]
lemma nil_append : nil x ++ w₂ = w₂ := rfl

@[simp, grind =]
lemma cons_append : cons x e w₁ ++ w₂ = cons x e (w₁ ++ w₂) := rfl

lemma append_assoc (w₁ w₂ w₃ : WList α β) : (w₁ ++ w₂) ++ w₃ = w₁ ++ (w₂ ++ w₃) := by
  induction w₁ with simp_all

instance : Std.Associative (· ++ · : WList α β → WList α β → WList α β) where
  assoc := append_assoc

@[simp, grind =]
lemma append_vertex : (w₁ ++ w₂).vertex = w₁.vertex.dropLast ++ w₂.vertex := by
  induction w₁ with
  | nil => simp
  | cons x e w ih =>
      rw [cons_append, cons_vertex, cons_vertex, List.dropLast_cons_of_ne_nil vertex_ne_nil,
        List.cons_append]
      simpa

lemma append_vertex' {w₁ w₂ : WList α β} (heq : w₁.last = w₂.first) :
    (w₁ ++ w₂).vertex = w₁.vertex ++ w₂.vertex.tail := by
  rw [append_vertex, ← w₁.vertex.dropLast_concat_getLast (by simp), List.append_assoc,
    vertex_getLast, dropLast_concat, heq, ← vertex_head]
  simp [- vertex_head]

protected lemma concat_eq_append (w : WList α β) (e) (x) :
    w.concat e x = w ++ (cons w.last e (nil x)) := by
  induction w with simp_all

@[simp, grind =]
protected lemma concat_append (w₁ w₂ : WList α β) (e) (x) :
    w₁.concat e x ++ w₂ = w₁ ++ cons w₁.last e w₂ := by
  rw [WList.concat_eq_append, append_assoc, cons_append, nil_append]

@[simp, grind =]
lemma append_edge {w₁ w₂ : WList α β} : (w₁ ++ w₂).edge = w₁.edge ++ w₂.edge := by
  induction w₁ with simp_all

@[simp, grind =]
lemma append_edgeSet (w₁ w₂ : WList α β) : E(w₁ ++ w₂) = E(w₁) ∪ E(w₂) := by
  ext; simp

@[simp, grind =]
lemma append_length : (w₁ ++ w₂).length = w₁.length + w₂.length := by
  induction w₁ with simp_all [add_right_comm]

lemma idxOf_append_right_of_notMem [DecidableEq α] {P Q : WList α β} {uf : α} (huf : uf ∉ P) :
    (P ++ Q).idxOf uf = P.length + Q.idxOf uf := by
  induction P with
  | nil y => simp [nil_append, nil_length]
  | cons y e P ih =>
    rw [mem_cons_iff, not_or, ← ne_eq] at huf
    grind [idxOf_cons_ne huf.1.symm, ih huf.2]

@[simp, grind =]
lemma append_nil (h : w.last = x) : w ++ (nil x) = w := by
  induction w with simp_all

@[simp]
lemma append_first_of_eq (h : w₁.last = w₂.first) : (w₁ ++ w₂).first = w₁.first := by
  induction w₁ with simp_all

@[simp]
lemma append_first_of_nonempty (h : w₁.Nonempty) : (w₁ ++ w₂).first = w₁.first := by
  induction w₁ with simp_all

@[simp, grind =]
lemma append_last : (w₁ ++ w₂).last = w₂.last := by
  induction w₁ with simp_all

@[simp, grind =]
protected lemma append_concat (w₁ w₂ : WList α β) (e) (x) :
    w₁ ++ (w₂.concat e x) = (w₁ ++ w₂).concat e x := by
  rw [WList.concat_eq_append, WList.concat_eq_append, ← append_assoc, append_last]

lemma append_right_injective : Injective (w ++ ·) :=
  fun w₁ w₂ h ↦ by induction w with simp_all

@[simp]
lemma append_vertexSet_of_eq (h : w₁.last = w₂.first) : V(w₁ ++ w₂) = V(w₁) ∪ V(w₂) := by
  induction w₁ with
  | nil u => simp [show u = w₂.first from h]
  | cons u e w ih =>
    simp only [last_cons] at h
    simp [ih h, insert_union]

lemma edgeSet_disjoint_of_append_nodup (h : (w₁ ++ w₂).edge.Nodup) : Disjoint E(w₁) E(w₂) := by
  rw [append_edge, List.nodup_append] at h
  rw [disjoint_iff_forall_ne]
  exact h.2.2

lemma mem_of_mem_append (hx : x ∈ w₁ ++ w₂) : x ∈ w₁ ∨ x ∈ w₂ := by
  rw [← mem_vertex, append_vertex, List.mem_append] at hx
  exact hx.imp (w₁.vertex.dropLast_subset ·) id

@[simp]
lemma mem_append_iff (w₁ w₂ : WList α β) (x : α) :
    x ∈ w₁ ++ w₂ ↔ x ∈ w₁.vertex.dropLast ∨ x ∈ w₂ := by
  rw [← mem_vertex, append_vertex, List.mem_append, mem_vertex]

@[simp]
lemma mem_append_iff_of_eq (h : w₁.last = w₂.first) (x : α) : x ∈ w₁ ++ w₂ ↔ x ∈ w₁ ∨ x ∈ w₂ := by
  rw [← mem_vertexSet_iff, append_vertexSet_of_eq h]
  simp

@[simp]
lemma append_nonempty : (w₁ ++ w₂).Nonempty ↔ w₁.Nonempty ∨ w₂.Nonempty := by
  cases w₁ with simp

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

/-- See `prefixUntilVertex_append_suffixFromVertex`. The `u ∈ w` assumption isn't needed. -/
lemma eq_append_of_vertex_mem {w : WList α β} {u : α} (hmem : u ∈ w) :
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

lemma append_dInc_iff (h : w₁.last = w₂.first) :
    (w₁ ++ w₂).DInc e x y ↔ w₁.DInc e x y ∨ w₂.DInc e x y := by
  induction w₁ with
  | nil => simp
  | cons u f w₁ ih =>
    simp
    rw [append_first_of_eq (by simpa using h), ih (by simpa using h)]
    tauto

lemma append_isLink_iff (h : w₁.last = w₂.first) :
    (w₁ ++ w₂).IsLink e x y ↔ w₁.IsLink e x y ∨ w₂.IsLink e x y := by
  simp_rw [isLink_iff_dInc, append_dInc_iff h]
  tauto

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

@[simp, grind =]
lemma reverse_first : (reverse w).first = w.last := by
  induction w with
  | nil x => simp [reverse]
  | cons x e w ih => simp [reverse, ih]

@[simp, grind =]
lemma reverse_last : (reverse w).last = w.first := by
  induction w with
  | nil x => simp [reverse]
  | cons x e w ih => simp [reverse]

@[simp, grind =]
lemma reverse_vertex : (reverse w).vertex = w.vertex.reverse := by
  induction w with
  | nil x => simp [reverse]
  | cons x e w ih => simp [reverse, ih]

@[simp, grind =]
lemma reverse_edge {w : WList α β} : (reverse w).edge = w.edge.reverse := by
  induction w with
  | nil x => simp [reverse]
  | cons x e w ih => simp [reverse, ih]

@[simp, grind =]
lemma reverse_edgeSet : E(reverse w) = E(w) := by
  ext; simp

@[simp, grind =]
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

@[simp, grind =]
lemma concat_reverse (w : WList α β) (e) (x) : (w.concat e x).reverse = cons x e w.reverse := by
  rw [WList.concat_eq_append, reverse_append (by simp)]
  simp

@[simp]
lemma zip_reverse (a : List α) (b : List β) (h : b.length + 1 = a.length) :
    (WList.zip a b h).reverse = WList.zip a.reverse b.reverse (by simpa) :=
  ext_vertex_edge (by simp) (by simp)

lemma Nonempty.firstEdge_concat (hw : w.Nonempty) :
    (concat_nonempty w e x).firstEdge = hw.firstEdge := by
  induction w with | nil u => simp at hw | cons => simp

@[simp, grind =]
lemma reverse_reverse (w : WList α β) : w.reverse.reverse = w := by
  induction w with | nil => simp | cons => simpa

lemma reverse_inj (h : w₁.reverse = w₂.reverse) : w₁ = w₂ := by
  rw [← reverse_reverse w₁, h, reverse_reverse]

@[simp, grind =]
lemma reverse_inj_iff : w₁.reverse = w₂.reverse ↔ w₁ = w₂ :=
  ⟨reverse_inj, fun h ↦ by rw [h]⟩

@[simp]
lemma reverse_injective : Injective (reverse : WList α β → WList α β) :=
  fun _ _ ↦ reverse_inj

lemma reverse_eq_comm : w₁.reverse = w₂ ↔ w₁ = w₂.reverse := by
  rw [← reverse_reverse w₂, reverse_inj_iff, reverse_reverse]

@[simp, grind =]
lemma reverse_nontrivial_iff : w.reverse.Nontrivial ↔ w.Nontrivial := by
  rw [← one_lt_length_iff, reverse_length, one_lt_length_iff]

alias ⟨_, Nontrivial.reverse⟩ := reverse_nontrivial_iff

@[simp, grind =]
lemma mem_reverse : x ∈ w.reverse ↔ x ∈ w := by
  induction w with
  | nil => simp
  | cons u e w ih => simp [ih, or_comm]

@[simp, grind =]
lemma reverse_vertexSet (w : WList α β) : V(w.reverse) = V(w) := by
  simp [WList.vertexSet]

lemma DInc.reverse (h : w.DInc e x y) : w.reverse.DInc e y x := by
  induction h with
  | cons_left x e w =>
    simpa [reverse_cons, reverse_last] using dInc_concat w.reverse e x
  | cons _ _ _ ih => exact ih.concat ..

@[simp, grind =]
lemma dInc_reverse_iff : w.reverse.DInc e x y ↔ w.DInc e y x :=
  ⟨fun h ↦ by simpa using h.reverse, DInc.reverse⟩

lemma dInc_iff_eq_of_dInc_of_vertex_nodup_right (hw : w.vertex.Nodup) (hv : w.DInc e u v) :
    w.DInc f x v ↔ f = e ∧ x = u := by
  generalize hw_def' : w.reverse = w'
  rw [← dInc_reverse_iff, hw_def', dInc_iff_eq_of_dInc_of_vertex_nodup_left (by simpa [← hw_def'])]
  simpa [← hw_def']

lemma DInc.left_mem_vertex_dropLast (h : w.DInc e x y) : x ∈ w.vertex.dropLast := by
  simpa [reverse_vertex, List.tail_reverse] using h.reverse.right_mem_vertex_tail

@[simp, grind =]
lemma isLink_reverse_iff : w.reverse.IsLink e x y ↔ w.IsLink e x y := by
  simp [isLink_iff_dInc, or_comm]

lemma concat_induction {motive : WList α β → Prop} (nil : ∀ u, motive (nil u))
    (concat : ∀ w e x, motive w → motive (w.concat e x)) (w : WList α β) : motive w := by
  suffices h : ∀ (w' : WList α β), motive w'.reverse by simpa using (h w.reverse)
  intro w'
  induction w' with
  | nil u => exact nil u
  | cons u e w ih => exact concat _ _ _ ih

lemma wellFormed_reverse_iff : w.reverse.WellFormed ↔ w.WellFormed := by
  simp [WellFormed]

alias ⟨_, WellFormed.reverse⟩ := wellFormed_reverse_iff

@[simp]
lemma idxOf_reverse [DecidableEq α] (hw : w.vertex.Nodup) (hx : x ∈ w) :
    w.reverse.idxOf x = w.length - w.idxOf x := by
  fun_induction WList.idxOf with
  | case1 => simp
  | case2 => simp_all
  | case3 e w x =>
    have hw' : (w.reverse.concat e x).vertex.Nodup := by
      simp_all [← concat_eq_append, List.nodup_concat]
    simp only [reverse_cons, cons_length, tsub_zero]
    rw [← reverse_length, ← @concat_length _ _ x e w.reverse, idxOf_eq_length_iff hw']
    simp
  | case4 u e w x hne IH =>
    simp_all only [cons_vertex, nodup_cons, mem_vertex, mem_cons_iff, reverse_cons, cons_length,
      reduceSubDiff, forall_const]
    replace hx : x ∈ w := by tauto
    rw [← IH hx]
    refine idxOf_concat_of_mem (by simpa)

@[simp]
lemma idxOf_reverse_add_idxOf [DecidableEq α] (hw : w.vertex.Nodup) (hx : x ∈ w) :
    w.reverse.idxOf x + w.idxOf x = w.length := by
  have h₁ := idxOf_reverse hw hx
  have h₂ : w.idxOf x ≤ w.length := idxOf_mem_le hx
  omega

@[simp]
lemma idxOf_add_idxOf_reverse [DecidableEq α] (hw : w.vertex.Nodup) (hx : x ∈ w) :
    w.idxOf x + w.reverse.idxOf x = w.length := by
  rw [add_comm]
  exact idxOf_reverse_add_idxOf hw hx

def dIncLast [DecidableEq β] (w : WList α β) {e : β} (he : e ∈ w.edge) : α × α :=
  (w.reverse.dIncFirst (e := e) (by rw [reverse_edge, List.mem_reverse]; exact he)).swap

lemma dIncLast_dInc [DecidableEq β] (w : WList α β) {e : β} (he : e ∈ w.edge) :
    w.DInc e (w.dIncLast he).1 (w.dIncLast he).2 := by
  simp only [dIncLast, Prod.fst_swap, Prod.snd_swap]
  rw [← dInc_reverse_iff]
  exact dIncFirst_dInc (e := e) _ (by rw [reverse_edge, List.mem_reverse]; exact he)

@[simp]
lemma dIncLast_cons_of_mem [DecidableEq β] (w : WList α β) {e : β} (he : e ∈ w.edge) :
    (cons x f w).dIncLast (by simp; grind : e ∈ _) = w.dIncLast he := by
  simp only [dIncLast, reverse_cons, Prod.swap_inj]
  exact dIncFirst_concat_of_mem (e := e) _
    (by rw [reverse_edge, List.mem_reverse]; exact he)

lemma dIncLast_cons [DecidableEq β] (w : WList α β) {e : β} (he : e ∈ (cons x f w).edge) :
    (cons x f w).dIncLast he = if hew : e ∈ w.edge then w.dIncLast hew else (x, w.first) := by
  split_ifs with hew
  · exact dIncLast_cons_of_mem w hew
  simp [dIncLast, reverse_cons, dIncFirst_concat, hew]

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

-- simp path way to auto find lastEdge given an explicit WList.
@[simp]
lemma lastEdge_cons_cons :
    (cons_nonempty x e (cons y f w)).lastEdge = (cons_nonempty y f w).lastEdge :=
  (cons_nonempty y f w).lastEdge_cons

@[simp]
lemma lastEdge_cons_nil : (cons_nonempty x e (nil y)).lastEdge = e := lastEdge_concat (nil x) e y

variable {α' : Type*} {f : α → α'}

def map (f : α → α') : WList α β → WList α' β
| nil x => nil (f x)
| cons x e w => cons (f x) e (w.map f)

@[simp]
lemma map_nil (f : α → α') : (nil x : WList α β).map f = nil (f x) := rfl

@[simp]
lemma map_cons (f : α → α') (x : α) (e : β) (w : WList α β) :
    (cons x e w).map f = cons (f x) e (w.map f) := rfl

@[simp]
lemma map_concat (w : WList α β) (f : α → α') (e : β) (x : α) :
    (w.concat e x).map f = (w.map f).concat e (f x) := by
  induction w with
  | nil u => simp [concat, map]
  | cons u g w ih => simp [concat, map, ih]

@[simp]
lemma map_append (w₁ w₂ : WList α β) (f : α → α') : (w₁ ++ w₂).map f = w₁.map f ++ w₂.map f := by
  induction w₁ with
  | nil u => simp [map]
  | cons u e w ih => simp [map, ih]

@[simp]
lemma map_reverse (w : WList α β) (f : α → α') : (w.reverse).map f = (w.map f).reverse := by
  induction w with
  | nil x => simp [reverse, map]
  | cons x e w ih => simp [reverse, map_concat, ih]

@[simp]
lemma map_first (w : WList α β) (f : α → α') : (w.map f).first = f w.first := by
  induction w with
  | nil x => simp [map]
  | cons x e w ih => simp [map]

@[simp]
lemma map_last (w : WList α β) (f : α → α') : (w.map f).last = f w.last := by
  induction w with
  | nil x => simp [map]
  | cons x e w ih => simp [map, ih]

@[simp]
lemma map_vertex (w : WList α β) (f : α → α') : (w.map f).vertex = w.vertex.map f := by
  induction w with
  | nil x => simp [map]
  | cons x e w ih => simp [map, ih]

@[simp]
lemma map_invFunOn_map [Nonempty α] {s : Set α} {w : WList α' β}
    (hw : V(w) ⊆ f '' s) : (w.map (invFunOn f s)).map f = w := by
  induction w with
  | nil x => simp [(surjOn_image f s).rightInvOn_invFunOn (hw (by simp : x ∈ _))]
  | cons x e w ih => simp [(surjOn_image f s).rightInvOn_invFunOn (hw (by simp : x ∈ _)),
    ih fun y hy ↦ hw (by simp [hy])]

@[simp]
lemma mem_map_iff (w : WList α β) (f : α → α') (x : α') : x ∈ w.map f ↔ ∃ y, y ∈ w ∧ f y = x := by
  rw [← mem_vertex, map_vertex]
  simp

@[simp]
lemma map_edge (w : WList α β) (f : α → α') : (w.map f).edge = w.edge := by
  induction w with
  | nil x => simp [map]
  | cons x e w ih => simp [map, ih]

@[simp]
lemma edgeSet_map (w : WList α β) (f : α → α') : E(w.map f) = E(w) := by
  ext e
  simp [WList.edgeSet, map_edge]

@[simp]
lemma map_length (w : WList α β) (f : α → α') : (w.map f).length = w.length := by
  induction w with
  | nil x => simp [map]
  | cons x e w ih => simp [map, ih]

@[simp]
lemma map_nonempty (w : WList α β) (f : α → α') : (w.map f).Nonempty ↔ w.Nonempty := by
  simp [nonempty_iff_exists_edge]

variable {β' : Type*}

def edgeMap (k : β → β') : WList α β → WList α β'
| nil x => nil x
| cons x e w => cons x (k e) (w.edgeMap k)

@[simp]
lemma edgeMap_nil (k : β → β') (x : α) : (nil x : WList α β).edgeMap k = nil x := rfl

@[simp]
lemma edgeMap_cons (k : β → β') (x : α) (e : β) (w : WList α β) :
    (cons x e w).edgeMap k = cons x (k e) (w.edgeMap k) := rfl

@[simp]
lemma edgeMap_concat (w : WList α β) (k : β → β') (e : β) (x : α) :
    (w.concat e x).edgeMap k = (w.edgeMap k).concat (k e) x := by
  induction w with
  | nil u => simp [concat, edgeMap]
  | cons u g w ih => simp [concat, edgeMap, ih]

@[simp]
lemma edgeMap_append (w₁ w₂ : WList α β) (k : β → β') :
    (w₁ ++ w₂).edgeMap k = w₁.edgeMap k ++ w₂.edgeMap k := by
  induction w₁ with
  | nil u => simp [edgeMap]
  | cons u e w ih => simp [edgeMap, ih]

@[simp]
lemma edgeMap_reverse (w : WList α β) (k : β → β') :
    (w.reverse).edgeMap k = (w.edgeMap k).reverse := by
  induction w with
  | nil x => simp [reverse, edgeMap]
  | cons x e w ih => simp [reverse, edgeMap_concat, ih]

@[simp]
lemma edgeMap_first (w : WList α β) (k : β → β') : (w.edgeMap k).first = w.first := by
  induction w with
  | nil x => simp [edgeMap]
  | cons x e w ih => simp [edgeMap]

@[simp]
lemma edgeMap_last (w : WList α β) (k : β → β') : (w.edgeMap k).last = w.last := by
  induction w with
  | nil x => simp [edgeMap]
  | cons x e w ih => simp [edgeMap, ih]

@[simp]
lemma edgeMap_vertex (w : WList α β) (k : β → β') : (w.edgeMap k).vertex = w.vertex := by
  induction w with
  | nil x => simp [edgeMap]
  | cons x e w ih => simp [edgeMap, ih]

@[simp]
lemma edgeMap_edge (w : WList α β) (k : β → β') : (w.edgeMap k).edge = w.edge.map k := by
  induction w with
  | nil x => simp [edgeMap]
  | cons x e w ih => simp [edgeMap, ih]

@[simp]
lemma edgeedgeSet_map (w : WList α β) (k : β → β') : E(w.edgeMap k) = k '' E(w) := by
  ext e
  constructor
  · intro he
    have : e ∈ w.edge.map k := by simpa [WList.edgeSet, edgeMap_edge] using he
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp this
    exact ⟨e', by simpa [WList.edgeSet] using he', rfl⟩
  · rintro ⟨e', he', rfl⟩
    have : k e' ∈ w.edge.map k := by
      refine List.mem_map.mpr ?_
      exact ⟨e', by simpa [WList.edgeSet] using he', rfl⟩
    simpa [WList.edgeSet, edgeMap_edge]

@[simp]
lemma edgeMap_length (w : WList α β) (k : β → β') : (w.edgeMap k).length = w.length := by
  induction w with
  | nil x => simp [edgeMap]
  | cons x e w ih => simp [edgeMap, ih]

@[simp]
lemma map_edgeMap (w : WList α β) (f : α → α') (k : β → β') :
    (w.edgeMap k).map f = (w.map f).edgeMap k := by
  induction w with
  | nil x => simp [edgeMap, map]
  | cons x e w ih => simp [edgeMap, map, ih]

@[simp]
lemma mem_edgeMap (w : WList α β) (k : β → β') (x : α) : x ∈ w.edgeMap k ↔ x ∈ w := by
  change x ∈ (w.edgeMap k).vertex ↔ x ∈ w.vertex
  simp [edgeMap_vertex]

@[simp]
lemma edgeMap_nonempty (w : WList α β) (σ : β → β') : (w.edgeMap σ).Nonempty ↔ w.Nonempty := by
  simp [nonempty_iff_exists_edge]

end WList

end

/-! ## Sublists, prefixes, infixes, and decompositions -/

section

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
  | nil {x w : _} (h : x ∈ w) : IsSublist (nil x) w
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

@[grind →]
lemma IsSublist.nonempty (h : w₁.IsSublist w₂) (hne : w₁.Nonempty) : w₂.Nonempty := by
  obtain ⟨e, he⟩ := nonempty_iff_exists_edge.mp hne
  exact nonempty_iff_exists_edge.mpr ⟨e, h.mem_edge he⟩

@[grind →]
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

lemma IsSublist.append_right (h : w₁.IsSublist w₂) (hw : w₂.last = w.first) :
    w₁.IsSublist (w₂ ++ w) := by
  induction h generalizing w with
  | nil h => simp [nil_isSublist_iff, mem_append_iff_of_eq hw, h]
  | cons x e h ih =>
    rw [cons_append]
    exact cons x e (ih hw)
  | cons₂ x e h h_eq ih =>
    rw [cons_append]
    exact cons₂ x e (ih hw) <| h_eq.trans <| Eq.symm (append_first_of_eq hw)

lemma IsSublist.append_left (h : w₁.IsSublist w₂) (w : WList α β) :
    w₁.IsSublist (w ++ w₂) := by
  induction w with
  | nil => simp [h]
  | cons x e w ih =>
    rw [cons_append]
    exact cons x e ih

@[gcongr]
lemma IsSublist.append_right₂ (h : w₁.IsSublist w₂) (hlast : w₁.last = w₂.last)
    (hw : w₂.last = w.first) : (w₁ ++ w).IsSublist (w₂ ++ w) := by
  induction h generalizing w with
  | @nil y w₂ h => exact (isSublist_refl w).append_left w₂
  | @cons x e w₁ w₂ h ih =>
    rw [cons_append]
    exact (ih (by simpa using hlast) (by simpa using hw)).cons x e
  | @cons₂ x e w₁ w₂ h h_eq ih =>
    refine (ih (by simpa using hlast) (by simpa using hw)).cons₂ x e ?_
    simp only [last_cons] at hlast hw
    rwa [append_first_of_eq (hlast.trans hw), append_first_of_eq hw]

@[gcongr]
lemma IsSublist.append_left₂ (h : w₁.IsSublist w₂) (hfirst : w₁.first = w₂.first)
    (w : WList α β) : (w ++ w₁).IsSublist (w ++ w₂) := by
  induction w with
  | nil => simpa using h
  | cons x e w ih =>
    rw [cons_append, cons_append]
    refine ih.cons₂ x e ?_
    match w with
    | .nil u => simpa using hfirst
    | .cons u e w => simp

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
  | cons (x : _) (e) (w₁ w₂ : WList α β) (h : IsPrefix w₁ w₂) : IsPrefix (cons x e w₁) (cons x e w₂)

attribute [gcongr] IsPrefix.cons

lemma IsPrefix.first_eq (h : IsPrefix w₁ w₂) : w₁.first = w₂.first := by
  induction h with simp

lemma isPrefix_append_right (hw : w₁.last = w₂.first) : w₁.IsPrefix (w₁ ++ w₂) := by
  induction w₁ with
  | nil =>
    convert IsPrefix.nil w₂ <;> grind
  | cons u e w₁ ih => simpa using (ih hw).cons ..

@[gcongr]
lemma IsPrefix.append_left (h : w₁.IsPrefix w₂) (w : WList α β) : (w ++ w₁).IsPrefix (w ++ w₂) := by
  induction w with
  | nil u => simpa
  | cons u e w ih =>
    rw [cons_append]
    exact cons u e (w ++ w₁) (w ++ w₂) ih

lemma isPrefix_iff_exists_eq_append : w₁.IsPrefix w₂ ↔
    ∃ w₁', w₁.last = w₁'.first ∧ w₁ ++ w₁' = w₂ := by
  refine ⟨fun h ↦ ?_, fun ⟨w₁', hL, hEq⟩ ↦ hEq ▸ isPrefix_append_right hL⟩
  induction h with | nil => simp | cons => simpa

@[grind →]
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

@[trans]
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
  | concat (e x w₁ w₂ : _) (h : IsSuffix w₁ w₂) : IsSuffix (w₁.concat e x) (w₂.concat e x)

attribute [gcongr] IsSuffix.concat

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

@[grind →]
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

lemma IsSuffix.last_eq (h : w₁.IsSuffix w₂) : w₁.last = w₂.last := by
  simpa using h.reverse_isPrefix_reverse.first_eq

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

lemma isSuffix_iff_exists_eq_append : w₁.IsSuffix w₂ ↔
    ∃ w', w'.last = w₁.first ∧ w' ++ w₁ = w₂ := by
  refine ⟨fun h ↦ ?_, fun ⟨w', hL, hEq⟩ ↦ hEq ▸ isSuffix_append_left w' w₁⟩
  obtain ⟨w', hL, hEq⟩ := isPrefix_iff_exists_eq_append.mp h.reverse_isPrefix_reverse
  refine ⟨w'.reverse, ?_, ?_⟩
  · simpa [reverse_last, reverse_first] using hL.symm
  · rw [← reverse_reverse w₂, ← hEq, reverse_append hL, reverse_reverse]

@[gcongr]
lemma IsSuffix.append_right (h : w₁.IsSuffix w₂) (w : WList α β) :
    (w₁ ++ w).IsSuffix (w₂ ++ w) := by
  induction w using concat_induction with
  | nil u =>
    match h with
    | .nil w => simp
    | .concat e x w₁ w₂ h =>
      simp only [WList.concat_append, ← WList.concat_eq_append]
      exact h.concat e u
  | concat w e x ih =>
    simp only [WList.append_concat]
    apply ih.concat ..

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
    obtain ⟨rfl, rfl, rfl⟩ | h := by simpa only [dInc_cons_iff] using h
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
    obtain rfl : w₁.last = head := by simpa only [← wR.vertex_head, hwR, head_cons] using hR
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

lemma IsPrefix.isInfix (h : w₁.IsPrefix w₂) : w₁.IsInfix w₂ := by
  obtain ⟨wR, hR, rfl⟩ := isPrefix_iff_exists_eq_append.mp h
  use (WList.nil w₁.first), wR, rfl, hR
  simp

lemma IsSuffix.isInfix (h : w₁.IsSuffix w₂) : w₁.IsInfix w₂ := by
  obtain ⟨wL, hL, rfl⟩ := isSuffix_iff_exists_eq_append.mp h
  use wL, (WList.nil w₁.last), hL
  simp

@[simp]
lemma reverse_infix_reverse_iff : w₁.reverse.IsInfix w₂.reverse ↔ w₁.IsInfix w₂ :=
  ⟨fun h ↦ by simpa using h.reverse, fun h ↦ h.reverse⟩

lemma reverse_infix_iff : w₁.reverse.IsInfix w₂ ↔ w₁.IsInfix w₂.reverse := by
  nth_rw 2 [← w₁.reverse_reverse]
  rw [reverse_infix_reverse_iff]

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

lemma isInfix_iff_exists_isSuffix_isPrefix (w₁ w₂ : WList α β) :
    w₁.IsInfix w₂ ↔ ∃ w, w₁.IsSuffix w ∧ w.IsPrefix w₂ := by
  refine ⟨fun h ↦ ?_, fun ⟨w, h₁, h₂⟩ ↦ ?_⟩
  · rcases h with ⟨wL, wR, hL, hR, rfl⟩
    use wL ++ w₁, by simp, isPrefix_append_right (by simpa)
  obtain ⟨wL, hwL, rfl⟩ := isSuffix_iff_exists_eq_append.mp h₁
  obtain ⟨wR, hwR, rfl⟩ := isPrefix_iff_exists_eq_append.mp h₂
  exact ⟨wL, wR, hwL, by simpa using hwR, rfl⟩

lemma isInfix_iff_exists_isPrefix_isSuffix (w₁ w₂ : WList α β) :
    w₁.IsInfix w₂ ↔ ∃ w, w₁.IsPrefix w ∧ w.IsSuffix w₂ := by
  refine ⟨fun h ↦ ?_, fun ⟨w, h₁, h₂⟩ ↦ ?_⟩
  · rcases h with ⟨wL, wR, hL, hR, rfl⟩
    use w₁ ++ wR, isPrefix_append_right hR, ?_
    rw [append_assoc]
    exact isSuffix_append_left wL (w₁ ++ wR)
  obtain ⟨wR, hwR, rfl⟩ := isPrefix_iff_exists_eq_append.mp h₁
  obtain ⟨wL, hwL, rfl⟩ := isSuffix_iff_exists_eq_append.mp h₂
  refine ⟨wL, wR, ?_, by simpa using hwR, append_assoc ..⟩
  rwa [append_first_of_eq hwR] at hwL

lemma IsInfix.eq_of_first_eq_last_eq (hnd : w₂.vertex.Nodup) (hf : w₁.first = w₂.first)
    (hl : w₁.last = w₂.last) (h : w₁.IsInfix w₂) : w₁ = w₂ := by
  obtain ⟨w, h₁, h₂⟩ := (isInfix_iff_exists_isSuffix_isPrefix w₁ w₂).mp h
  obtain rfl := h₂.eq_of_last_mem hnd (hl ▸ h₁.last_eq ▸ last_mem)
  exact h₁.eq_of_first_mem hnd (hf ▸ first_mem)

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
    rw [List.foldl_assoc]

@[simp↓]
lemma appendList_nil_cons [Inhabited α] (x : α) {L : List (WList α β)} (hne : L ≠ []) :
    (nil x :: L)⁺ = L⁺ := by
  unfold appendList
  simp [hne]

@[simp↓]
lemma appendList_concat [Inhabited α] (l : WList α β) (L : List (WList α β)) :
    (L.concat l)⁺ = L⁺ ++ l := by
  simp [appendList]

lemma appendList_append [Inhabited α] {L : List (WList α β)} (L₁ : List (WList α β))
    (hne : L ≠ []) : (L₁ ++ L)⁺ = L₁⁺ ++ L⁺ := by
  obtain ⟨l, L, rfl⟩ := List.exists_cons_of_ne_nil hne
  simp only [appendList, List.foldl_append, List.foldl_cons, nil_append]
  rw [List.foldl_assoc]

lemma length_appendList_take_succ [Inhabited α] {L : List (WList α β)} {i : ℕ}
    (hi : i < L.length) :
    ((L.take (i + 1))⁺).length = ((L.take i)⁺).length + L[i].length := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, ← List.concat_eq_append,
    appendList_concat, append_length]

lemma length_appendList_take_mono [Inhabited α] (L : List (WList α β)) :
    Monotone fun i ↦ ((L.take i)⁺).length := by
  refine monotone_nat_of_le_succ fun i ↦ ?_
  obtain hi | hi := lt_or_ge i L.length
  · simp [length_appendList_take_succ hi]
  rw [List.take_of_length_le hi, List.take_of_length_le (by omega)]

lemma length_appendList_take_lt [Inhabited α] {L : List (WList α β)} {i j : ℕ}
    (hne : ∀ P ∈ L, P.Nonempty) (hij : i < j) (hj : j ≤ L.length) :
    ((L.take i)⁺).length < ((L.take j)⁺).length := by
  have hi : i < L.length := by omega
  have h1 := length_appendList_take_succ hi
  have h2 : ((L.take (i + 1))⁺).length ≤ ((L.take j)⁺).length :=
    length_appendList_take_mono L (by omega)
  have h3 := (hne _ (List.getElem_mem hi)).length_pos
  omega

@[simp]
lemma appendList_first [Inhabited α] {L : List (WList α β)} (hne : L ≠ [])
    (h : L.IsChain (·.last = ·.first)) : L⁺.first = (L.head hne).first := by
  match L with
  | [] => simp at hne
  | [l] => simp
  | l₁ :: l₂ :: L =>
    have : l₁.last = ((l₂ :: L)⁺).first := by
      rw [appendList_first (by simp) (isChain_of_isChain_cons h), head_cons]
      exact h.rel
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
      exact h.rel
    apply_fun reverse using reverse_injective
    rw [reverse_reverse, appendList_cons hrel, List.map_cons, List.reverse_cons', appendList_concat,
      reverse_append ?_, reverse_reverse, ← appendList_reverse (isChain_of_isChain_cons h),
      reverse_reverse]
    rw [← appendList_reverse (isChain_of_isChain_cons h)]
    simp only [reverse_last, reverse_first, hrel]

@[simp]
lemma appendList_cons_cons [Inhabited α] {l₁ l₂ : WList α β} {L : List (WList α β)}
    (h : (l₁ :: l₂ :: L).IsChain (·.last = ·.first)) : (l₁ :: l₂ :: L)⁺ = l₁ ++ (l₂ :: L)⁺ := by
  rw [appendList_cons (by simp [isChain_of_isChain_cons h, h.rel])]

@[simp]
lemma appendList_edge [Inhabited α] (L : List (WList α β)) :
    L⁺.edge = (L.map edge).foldl (· ++ ·) [] := by
  match L with
  | [] => simp
  | [l] => simp
  | l₁ :: l₂ :: L =>
    have := appendList_edge (l₂ :: L)
    simp only [appendList, foldl_cons, nil_append, List.map_cons, List.nil_append] at this ⊢
    rw [foldl_assoc, foldl_assoc, append_edge, ← this]


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
    obtain rfl := nil_last ▸ (hl ▸ h.chain_eq).rel
    simpa [hl] using (hl ▸ h).nil_cons (by simp) |>.head_first_eq_first
  | cons u e w', [] =>
    subst L
    simp [h.append]
  | cons u e w', l' :: L' =>
    subst L
    simp only [appendList, head_cons, first_cons, h.append, foldl_cons, nil_append]
    rw [List.foldl_assoc]
    simp
termination_by L
decreasing_by simp [hl]

@[simp]
lemma append_cons_iff (heq : w.last = w'.first) (hL : L ≠ []) :
    (w ++ w').DecomposeTo (w :: L) ↔ w'.DecomposeTo L := by
  refine ⟨fun h => h.append_cons hL, fun h => ⟨by simp, ?_, ?_⟩⟩
  · obtain ⟨l, L', rfl⟩ := List.exists_cons_of_ne_nil hL
    simp [h.append, appendList, L'.foldl_assoc]
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
    rw [List.foldl_assoc]
    apply WList.isPrefix_append_right
    rw [h.chain_eq.rel]
    have := h.append ▸ h
    simp only [foldl_cons, appendList, nil_append] at this
    rw [List.foldl_assoc] at this
    simpa using (this.append_cons (by simp)).head_first_eq_first

lemma isSublist_of_mem {L : List (WList α β)} {w l : WList α β} (h : w.DecomposeTo L) (hl : l ∈ L) :
    l.IsSublist w := by
  match L with
  | [] => simp at hl
  | l' :: L' =>
    obtain rfl | hl := (by simpa using hl) <;>
      have := by simpa only [head_cons] using h.head_isPrefix
    · exact this.isSublist
    obtain ⟨w', hw', rfl⟩ := isPrefix_iff_exists_eq_append.mp this; clear this
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
    obtain ⟨w', hw', rfl⟩ := by
      simpa only [head_cons, isPrefix_iff_exists_eq_append] using h.head_isPrefix
    have h' := h.append_cons (by simp)
    have hnd := by simpa only [append_edge, nodup_append] using hw
    exact ⟨fun l' hl' ↦ (edgeSet_disjoint_of_append_nodup hw).mono_right (h'.isSublist_of_mem hl'
    |>.edge_subset), disjoint_of_edge_nodup h' hnd.2.1⟩

end DecomposeTo
end WList

end
