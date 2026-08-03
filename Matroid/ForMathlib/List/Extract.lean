module

public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.TakeDrop

@[expose] public section

variable {α : Type*} {L l : List α} {x : α} {i j p q n : ℕ}

open Set

namespace List

lemma extract_isInfix (L : List α) (a b : ℕ) : L.extract a b <:+: L :=
  (take_prefix ..).isInfix.trans <| (drop_suffix ..).isInfix

lemma extract_zero (L : List α) (stop : ℕ) : L.extract 0 stop = L.take stop := by
  simp

lemma extract_zero_right (L : List α) (a : ℕ) : L.extract a 0 = [] := by
  simp

lemma extract_of_length_le (L : List α) (start : ℕ) {stop : ℕ} (h : L.length ≤ stop) :
    L.extract start stop = L.drop start := by
  obtain hle | hgt := le_or_gt start stop
  · simpa [Nat.sub_add_cancel hle]
  simp only [extract_eq_take_drop, take_eq_self_iff, length_drop, tsub_le_iff_right]
  grw [Nat.sub_eq_zero_of_le hgt.le, zero_add, ← hgt, h]

lemma extract_eq_nil (L : List α) {start stop : ℕ} (hlt : stop ≤ start) :
    L.extract start stop = [] := by
  grind [extract_eq_take_drop, take_eq_nil_iff, drop_eq_nil_iff]

lemma extract_eq_nil' (L : List α) {start stop : ℕ} (hlt : L.length ≤ start) :
    L.extract start stop = [] := by
  simp [hlt]

lemma extract_succ_cons (L : List α) (x : α) (a b : ℕ) :
    (x :: L).extract (a + 1) (b + 1) = L.extract a b := by
  rw [extract_eq_drop_take', take_succ_cons, drop_succ_cons, extract_eq_drop_take']

lemma map_extract {β : Type*} (L : List α) (f : α → β) (a b : ℕ) :
    (L.extract a b).map f = (L.map f).extract a b := by
  simp

lemma mem_extract_iff_getElem {L : List α} {p q : ℕ} :
    x ∈ L.extract p q ↔ ∃ (i : ℕ) (hi : i < L.length), p ≤ i ∧ i < q ∧ L[i] = x := by
  simp only [extract_eq_take_drop, mem_take_iff_getElem, getElem_drop, length_drop, lt_inf_iff,
    exists_and_left]
  refine ⟨by grind, ?_⟩
  rintro ⟨i, hpi, hiq, hi, rfl⟩
  obtain ⟨d, rfl⟩ := exists_add_of_le hpi
  grind

@[simp]
lemma Nodup.getElem_mem_extract_iff (hL : L.Nodup) {i p q : ℕ} {hi : i < L.length} :
    L[i] ∈ L.extract p q ↔ p ≤ i ∧ i < q := by
  simp [mem_extract_iff_getElem, hL.getElem_inj_iff, hi]

lemma extract_min_right (L : List α) (p q : ℕ) :
    L.extract p (min q L.length) = L.extract p q := by
  obtain hq | hq := le_or_gt q L.length
  · rw [min_eq_left hq]
  rw [extract_eq_drop_take', take_of_length_le (by lia), extract_eq_drop_take',
    take_of_length_le (by lia)]

lemma extract_min_left (L : List α) (p q : ℕ) :
    L.extract (min p L.length) q = L.extract p q := by
  obtain hp | hp := le_or_gt p L.length
  · rw [min_eq_left hp]
  rw [← extract_min_right, extract_eq_nil _ (by lia), ← extract_min_right,
    extract_eq_nil _ (by lia)]

lemma extract_min_min (L : List α) (p q : ℕ) :
    L.extract (min p L.length) (min q L.length) = L.extract p q := by
  rw [extract_min_left, extract_min_right]

lemma extract_reverse (L : List α) (p q : ℕ) :
    L.reverse.extract p q = (L.extract (L.length - q) (L.length - p)).reverse := by
  wlog hq : p ≤ L.length ∧ q ≤ L.length generalizing p q with aux
  · rw [← extract_min_min, aux _ _ (by simp), length_reverse]
    convert rfl using 3 <;> lia
  rw [eq_comm, extract_eq_drop_take', reverse_drop, length_take, min_eq_left (by simp),
    show L.length - p - (L.length - q) = q - p by lia, reverse_take, Nat.sub_sub_self (by lia)]

lemma extract_add_one_right (L : List α) {p q : ℕ} (hpq : p ≤ q) (hq : q < L.length) :
    L.extract p (q + 1) = (L.extract p q) ++ [L[q]] := by
  induction L generalizing p q with
  | nil => simp at hq
  | cons x L ih =>
    obtain rfl | q := q
    · simp [show p = 0 by simpa using hpq]
    obtain rfl | p := p
    · simp
    rw [extract_succ_cons, extract_succ_cons, getElem_cons_succ, ih (by lia) (by grind)]

lemma cons_extract_add_one_left (L : List α) {p q : ℕ} (hpq : p < q) (hp : p < L.length) :
    L[p] :: L.extract (p + 1) q = L.extract p q := by
  induction L generalizing p q with
  | nil => grind
  | cons x L ih =>
    obtain rfl | q := q
    · simp at hpq
    obtain rfl | p := p
    · simp
    rw [extract_succ_cons, extract_succ_cons, getElem_cons_succ, ih (by lia) (by grind)]

lemma extract_suffix_take (L : List α) (p q) : L.extract p q <:+ L.take q := by
  rw [extract_eq_drop_take']
  exact drop_suffix p (take q L)

lemma extract_prefix_drop (L : List α) (p q) : L.extract p q <+: L.drop p := by
  rw [extract_eq_take_drop]
  exact take_prefix (q - p) (drop p L)

lemma extract_suffix_extract (L : List α) {p'} (hpp' : p ≤ p') :
    L.extract p' q <:+ L.extract p q := by
  rw [extract_eq_drop_take', extract_eq_drop_take']
  exact drop_suffix_drop_left _ hpp'

lemma extract_prefix_extract (L : List α) {q'} (hqq' : q ≤ q') :
    L.extract p q <+: L.extract p q' := by
  rw [extract_eq_take_drop, extract_eq_take_drop]
  exact take_prefix_take_left <| by lia
