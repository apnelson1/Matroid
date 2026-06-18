import Matroid.Graph.WList.TakeDrop.Defs

open Set Function List Nat WList

variable {α β : Type*} {u v x y z : α} {e e' f g : β} {S T U: Set α}
  {F F' : Set β} {w w' w₀ w₁ w₂ w₃ l l₁ l₂ l₃ : WList α β}

namespace WList

variable [DecidablePred (· ∈ F)]
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

end WList
