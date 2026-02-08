import Matroid.Graph.WList.Defs

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
lemma concat_vertex : (w.concat e v).vertex = w.vertex ++ [v] := by
  induction w with | nil => rfl | cons => simpa [concat]

@[simp]
lemma concat_edge : (w.concat e v).edge = w.edge ++ [e] := by
  induction w with | nil => rfl | cons => simpa [concat]

@[simp]
lemma concat_edgeSet : E(w.concat e v) = insert e E(w)  := by
  simp [Set.ext_iff, or_comm]

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
    tauto
  | cons v g w ih =>
    simp only [cons_concat, dInc_cons_iff, concat_first, ih, last_cons]
    tauto

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

/- Properties of append operation -/
@[simp]
lemma append_notation : append w₁ w₂ = w₁ ++ w₂ := rfl

@[simp]
lemma nil_append : nil x ++ w₂ = w₂ := rfl

@[simp]
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

@[simp]
lemma append_length : (w₁ ++ w₂).length = w₁.length + w₂.length := by
  induction w₁ with simp_all [add_right_comm]

@[simp]
lemma append_nil (h : w.last = x) : w ++ (nil x) = w := by
  induction w with simp_all

@[simp]
lemma append_first_of_eq (h : w₁.last = w₂.first) : (w₁ ++ w₂).first = w₁.first := by
  induction w₁ with simp_all

@[simp]
lemma append_first_of_nonempty (h : w₁.Nonempty) : (w₁ ++ w₂).first = w₁.first := by
  induction w₁ with simp_all

@[simp]
lemma append_last : (w₁ ++ w₂).last = w₂.last := by
  induction w₁ with simp_all

@[simp]
protected lemma append_concat (w₁ w₂ : WList α β) (e) (x) :
    w₁ ++ (w₂.concat e x) = (w₁ ++ w₂).concat e x := by
  rw [WList.concat_eq_append, WList.concat_eq_append, ← append_assoc, append_last]

lemma append_right_injective : Injective (w ++ ·) :=
  fun w₁ w₂ h ↦ by induction w with simp_all

@[simp]
lemma append_vertexSet_of_eq (h : w₁.last = w₂.first) : V(w₁ ++ w₂) = V(w₁) ∪ V(w₂) := by
  induction w₁ with
  | nil u => simp [insert_eq_of_mem, show u = w₂.first from h]
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

@[simp]
lemma reverse_first : (reverse w).first = w.last := by
  induction w with
  | nil x => simp [reverse]
  | cons x e w ih => simp [reverse, ih]

@[simp]
lemma reverse_last : (reverse w).last = w.first := by
  induction w with
  | nil x => simp [reverse]
  | cons x e w ih => simp [reverse]

@[simp]
lemma reverse_vertex : (reverse w).vertex = w.vertex.reverse := by
  induction w with
  | nil x => simp [reverse]
  | cons x e w ih => simp [reverse, ih]

@[simp]
lemma reverse_edge {w : WList α β} : (reverse w).edge = w.edge.reverse := by
  induction w with
  | nil x => simp [reverse]
  | cons x e w ih => simp [reverse, ih]

@[simp]
lemma reverse_edgeSet : E(reverse w) = E(w) := by
  ext; simp

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

@[simp]
lemma reverse_injective : Injective (reverse : WList α β → WList α β) :=
  fun _ _ ↦ reverse_inj

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
lemma reverse_vertexSet (w : WList α β) : V(w.reverse) = V(w) := by
  simp [WList.vertexSet]

lemma DInc.reverse (h : w.DInc e x y) : w.reverse.DInc e y x := by
  induction h with
  | cons_left x e w =>
    convert dInc_concat _ _ _ using 1
    simp
  | cons _ _ _ ih => exact ih.concat ..

@[simp]
lemma dInc_reverse_iff : w.reverse.DInc e x y ↔ w.DInc e y x :=
  ⟨fun h ↦ by simpa using h.reverse, DInc.reverse⟩

lemma dInc_iff_eq_of_dInc_of_vertex_nodup_right (hw : w.vertex.Nodup) (hv : w.DInc e u v) :
    w.DInc f x v ↔ f = e ∧ x = u := by
  generalize hw_def' : w.reverse = w'
  rw [← dInc_reverse_iff, hw_def', dInc_iff_eq_of_dInc_of_vertex_nodup_left (by simpa [← hw_def'])]
  simpa [← hw_def']

@[simp]
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
lemma mem_map_iff (w : WList α β) (f : α → α') (x : α') : x ∈ w.map f ↔ ∃ y, y ∈ w ∧ f y = x := by
  rw [← mem_vertex, map_vertex]
  simp

@[simp]
lemma map_edge (w : WList α β) (f : α → α') : (w.map f).edge = w.edge := by
  induction w with
  | nil x => simp [map]
  | cons x e w ih => simp [map, ih]

@[simp]
lemma map_edgeSet (w : WList α β) (f : α → α') : E(w.map f) = E(w) := by
  ext e
  simp [WList.edgeSet, map_edge]

@[simp]
lemma map_length (w : WList α β) (f : α → α') : (w.map f).length = w.length := by
  induction w with
  | nil x => simp [map]
  | cons x e w ih => simp [map, ih]

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
lemma edgeMap_edgeSet (w : WList α β) (k : β → β') : E(w.edgeMap k) = k '' E(w) := by
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

end WList
