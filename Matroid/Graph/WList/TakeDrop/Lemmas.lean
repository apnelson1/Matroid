import Matroid.Graph.WList.TakeDrop.Index
import Matroid.Graph.WList.TakeDrop.Pred
import Matroid.Graph.WList.Remove

open Set Function List Nat WList

variable {α β : Type*} {u v x y z : α} {e e' f g : β} {S T U: Set α}
  {F F' : Set β} {w w' w₀ w₁ w₂ w₃ l l₁ l₂ l₃ : WList α β} {n : ℕ}

namespace WList

@[gcongr]
lemma IsPrefix.tail (h : w₁.IsPrefix w₂) (hne : w₁.Nonempty) : w₁.tail.IsPrefix w₂.tail := by
  simp_rw [← WList.drop_one]
  exact h.drop <| one_le_length_iff.mpr hne

@[gcongr] lemma IsSuffix.tail (h : w₁.IsSuffix w₂) : w₁.tail.IsSuffix w₂.tail := by
  simp_rw [← WList.drop_one]
  exact h.drop 1

@[gcongr] lemma IsInfix.tail (h : w₁.IsInfix w₂) (hne : w₁.Nonempty) : w₁.tail.IsInfix w₂.tail := by
  rw [isInfix_iff_exists_isPrefix_isSuffix] at h ⊢
  obtain ⟨w, h₁, h₂⟩ := h
  use w.tail, h₁.tail hne, h₂.tail

@[gcongr] lemma IsPrefix.dropLast (h : w₁.IsPrefix w₂) : w₁.dropLast.IsPrefix w₂.dropLast := by
  induction h with
  | nil w => simp
  | cons x e w₁ w₂ h ih =>
    obtain ⟨y, rfl⟩ | hne := w₁.exists_eq_nil_or_nonempty
    · simp
    rw [hne.dropLast_cons, (h.isSublist.nonempty hne).dropLast_cons]
    exact cons x e w₁.dropLast w₂.dropLast ih

@[gcongr] lemma IsSuffix.dropLast (h : w₁.IsSuffix w₂) (hne : w₁.Nonempty) :
    w₁.dropLast.IsSuffix w₂.dropLast := by
  rw [← reverse_isPrefix_reverse_iff, ← reverse_tail, ← reverse_tail]
  exact h.reverse_isPrefix_reverse.tail hne.reverse

@[gcongr] lemma IsInfix.dropLast (h : w₁.IsInfix w₂) (hne : w₁.Nonempty) :
    w₁.dropLast.IsInfix w₂.dropLast := by
  rw [isInfix_iff_exists_isPrefix_isSuffix] at h ⊢
  obtain ⟨w, h₁, h₂⟩ := h
  use w.dropLast, h₁.dropLast, h₂.dropLast (h₁.isSublist.nonempty hne)

@[simp]
lemma take_prefixUntilVertex [DecidableEq α] (hx : x ∈ w) :
    w.take (w.idxOf x) = w.prefixUntilVertex x := by
  induction w with
  | nil u =>
    simp only [mem_nil_iff] at hx
    subst hx
    simp [take, prefixUntilVertex, prefixUntil]
  | cons u e w ih =>
    obtain rfl | hne := eq_or_ne x u
    · simp [prefixUntilVertex, prefixUntil, idxOf_cons_self]
    · simp only [mem_cons_iff, hne, false_or] at hx
      simp only [idxOf_cons_ne hne.symm, take_cons_succ, prefixUntilVertex_cons_of_ne _ hne.symm,
        cons.injEq, true_and]
      exact ih hx

@[simp]
lemma drop_suffixFromVertex [DecidableEq α] (hx : x ∈ w) :
    w.drop (w.idxOf x) = w.suffixFromVertex x := by
  induction w with
  | nil u =>
    simp only [mem_nil_iff] at hx
    subst hx
    simp [suffixFromVertex]
  | cons u e w ih =>
    obtain rfl | hne := eq_or_ne x u
    · simp [suffixFromVertex, idxOf_cons_self]
    · simp only [mem_cons_iff, hne, false_or] at hx
      simp only [drop_cons_succ, idxOf_cons_ne hne.symm, suffixFromVertex_cons_of_ne _ hne.symm]
      exact ih hx

lemma suffixFromVertex_isSuffix_of_idxOf_le [DecidableEq α] {w : WList α β} {vl uf : α}
    (hvl : vl ∈ w) (huf : uf ∈ w) (hle : w.idxOf vl ≤ w.idxOf uf) :
    (w.suffixFromVertex uf).IsSuffix (w.suffixFromVertex vl) := by
  rw [← drop_suffixFromVertex hvl, ← drop_suffixFromVertex huf, ← Nat.sub_add_cancel hle,
    ← drop_drop]
  exact drop_isSuffix (w.drop (w.idxOf vl)) (w.idxOf uf - w.idxOf vl)

lemma drop_eq_suffixFromVertex_of_idxOf [DecidableEq α] (hx : x ∈ w) (hn : n = w.idxOf x) :
    w.drop n = w.suffixFromVertex x := by
  rw [hn, drop_suffixFromVertex hx]

lemma take_length_prefixUntilVertex [DecidableEq α] (hx : x ∈ w) :
    w.take (w.prefixUntilVertex x).length = w.prefixUntilVertex x := by
  rw [prefixUntilVertex_length hx, take_prefixUntilVertex hx]


section Dedup

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

lemma dedup_isSublist_deloop (w : WList α β) : w.dedup.IsSublist w.deloop := by
  match w with
  | nil x => simp
  | cons u e w' =>
    by_cases huw : u ∈ w'
    · have hle := (w'.suffixFromVertex_isSuffix u).length_le
      rw [dedup_cons_of_mem huw, deloop_cons_eq_ite]
      split_ifs with heq
      · subst heq
        exact (w'.suffixFromVertex w'.first).dedup_isSublist_deloop.trans
          (deloop_isSublist_mono (w'.suffixFromVertex_isSuffix _).isSublist)
      exact (w'.suffixFromVertex u).dedup_isSublist_deloop.trans
      <| (deloop_isSublist_mono (w'.suffixFromVertex_isSuffix _).isSublist).cons ..
    rw [dedup_cons_of_notMem huw, deloop_cons_eq_ite]
    split_ifs with heq
    · subst heq
      exact absurd (w'.deloop_first ▸ first_mem : w'.first ∈ w'.deloop) (mt mem_deloop_iff.mp huw)
    exact w'.dedup_isSublist_deloop.cons₂ _ _ (by simp)
termination_by w.length

end Dedup

end WList
