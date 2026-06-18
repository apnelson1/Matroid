import Matroid.Graph.WList.TakeDrop.Defs
import Matroid.Graph.WList.TakeDrop.PrefixSuffix

open Set Function List Nat WList

variable {α β : Type*} {u v x y z : α} {e e' f g : β} {S T U: Set α}
  {F F' : Set β} {w w' w₀ w₁ w₂ w₃ l l₁ l₂ l₃ : WList α β}

namespace WList

variable [DecidableEq α]

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
    exact ⟨mt w.dedup_isSublist.sublist.mem huw, w.dedup_vertex_nodup⟩
termination_by w.length

lemma dedup_eq_self (hw : w.vertex.Nodup) : w.dedup = w := by
  induction w with
  | nil => simp
  | cons u e w ih =>
    simp only [cons_vertex, nodup_cons, mem_vertex] at hw
    rw [dedup_cons_of_notMem hw.1, ih hw.2]

lemma dedup_eq_self_iff : w.dedup = w ↔ w.vertex.Nodup :=
  ⟨fun h ↦ by rw [← h]; exact dedup_vertex_nodup w, dedup_eq_self⟩

end WList
