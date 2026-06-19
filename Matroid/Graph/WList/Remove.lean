import Matroid.Graph.WList.Sublist

open Set Function List Nat WList

variable {α β : Type*} {u v x y z : α} {e e' f g : β} {S T U: Set α}
  {F F' : Set β} {w w' w₀ w₁ w₂ w₃ l l₁ l₂ l₃ : WList α β}

namespace WList

section edgeRemove

/-- Remove edges from a `WList` that belong to a given edge set `F`. -/
def edgeRemove (F : Set β) [DecidablePred (· ∈ F)] : WList α β → WList α β
  | nil x => nil x
  | cons x e w => if e ∈ F then edgeRemove F w else cons x e (edgeRemove F w)

variable [DecidablePred (· ∈ F)]

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

lemma deloop_noLoop (w : WList α β) : w.deloop.NoLoop := by
  cases w with
  | nil => simp
  | cons u e w =>
    by_cases heq : u = w.first
    · rw [deloop_cons_of_eq_first heq]
      apply deloop_noLoop
    simp only [deloop_cons_of_ne_first heq, noLoop_cons, deloop_first, ne_eq]
    exact ⟨heq, w.deloop_noLoop⟩

@[simp]
lemma deloop_eq_self (hw : w.NoLoop) : w.deloop = w := by
  induction w with
  | nil => simp
  | cons u e w ih =>
    simp only [noLoop_cons] at hw
    rw [deloop_cons_of_ne_first hw.1, ih hw.2]

@[simp]
lemma deloop_eq_self_iff : w.deloop = w ↔ w.NoLoop :=
  ⟨fun h ↦ by rw [← h]; exact deloop_noLoop w, deloop_eq_self⟩

end deloop

end WList
