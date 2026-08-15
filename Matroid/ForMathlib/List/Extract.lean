module

public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.TakeDrop
public import Mathlib.Data.List.Rotate

@[expose] public section

set_option linter.style.longLine false

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

lemma length_extract (L : List α) {p q : ℕ} (hq : q ≤ L.length) :
    (L.extract p q).length = q - p := by
  obtain hle | hgt := le_or_gt q p
  · rw [extract_eq_nil _ hle, Nat.sub_eq_zero_of_le hle, length_nil]
  replace hgt := hgt.le
  induction q, hgt using Nat.le_induction with
  | base => simp
  | succ q hpq ih => rw [extract_add_one_right _ (by lia) (by lia), length_append, length_singleton,
      ih (by lia), Nat.sub_add_comm hpq]

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



-- /-- Take the list `L[p], L[p + 1], ..., L[L.length - 1], L[0], ..., L[q - 1]`, where `p` and `q`
-- are interpreted as cyclic indices. If `p ≅ q (mod L.length)`, then this is equal to
-- `L[p], ..., L[p]`. -/
-- def extractC (L : List α) (p q : ℕ) := if p % L.length < q % L.length then
--     L.extract (p % L.length) (q % L.length) else L.drop (p % L.length) ++ L.take (q % L.length)

-- lemma extractC_mod_left (L : List α) (p q : ℕ) : L.extractC (p % L.length) q = L.extractC p q := by
--   simp [extractC]

-- lemma extractC_mod_right (L : List α) (p q : ℕ) : L.extractC p (q % L.length) = L.extractC p q := by
--   simp [extractC]

-- lemma extract_eq_extractC (L : List α) (hpq : p < q) (hq : q ≤ L.length) :
--     L.extract p q = L.extractC p q := by
--   obtain rfl | hq := hq.eq_or_lt
--   · rw [extractC, if_neg (by simp), Nat.mod_eq_of_lt hpq, Nat.mod_self]
--     simp
--   rw [extractC, if_pos (by simpa [Nat.mod_eq_of_lt, hq, (hpq.trans hq)]), Nat.mod_eq_of_lt hq,
--     Nat.mod_eq_of_lt (hpq.trans hq)]

-- lemma extractC_eq_drop_append_take (L : List α) (hpq : q ≤ p) (hp : p < L.length) :
--     L.extractC p q = L.drop p ++ L.take q := by
--   rw [extractC, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt (hpq.trans_lt hp), if_neg (by lia)]

-- @[simp]
-- lemma extractC_self (L : List α) (p : ℕ) : L.extractC p p = L.rotate p := by
--   rw [extractC, if_neg (by simp), rotate_eq_drop_append_take_mod]

-- @[simp]
-- lemma extractC_zero_right (L : List α) (p : ℕ) (hp : p < L.length) : L.extractC p 0 = L.drop p := by
--   simp [extractC, Nat.mod_eq_of_lt hp]

-- lemma extractC_zero_left (L : List α) (p : ℕ) (hp : p < L.length) (h0 : p ≠ 0) :
--     L.extractC 0 p = L.take p := by
--   simp [extractC, Nat.mod_eq_of_lt hp, h0]

-- @[simp]
-- lemma extractC_zero_zero (L : List α) : L.extractC 0 0 = L := by
--   simp [extractC]

-- lemma extractC_add_one_right (L : List α) (p q : ℕ) (hq : q < L.length) (hpq : p % L.length ≠ q) :
--     L.extractC p (q + 1) = L.extractC p q ++ [L[q]] := by
--   wlog hp : p < L.length generalizing p with aux
--   · rw [← extractC_mod_left, aux _ (by simpa) (Nat.mod_lt _ (by lia)), extractC_mod_left]
--   rw [Nat.mod_eq_of_lt hp] at hpq
--   by_cases hqL : L.length = q + 1
--   · simp only [extractC, Nat.mod_eq_of_lt hp, ← hqL, Nat.mod_self, not_lt_zero, ↓reduceIte,
--       take_zero, append_nil, Nat.mod_eq_of_lt hq]
--     rw! [if_pos (by grind), extract_eq_drop_take', ← L.dropLast_concat_getLast (by grind),
--       drop_append_of_le_length, dropLast_concat_getLast, getLast_eq_getElem, hqL, dropLast_eq_take,
--       hqL, Nat.add_sub_cancel]
--     · rfl
--     grw [length_dropLast]
--     lia
--   rw [extractC, extractC, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt (by lia), take_add_one,
--     getElem?_eq_getElem (by lia), Option.toList_some, Nat.mod_eq_of_lt (by lia)]
--   by_cases hpq' : p < q
--   · rw [if_pos (by lia), if_pos hpq', extract_add_one_right _ hpq'.le]
--   rw [if_neg (by lia), if_neg (by lia), append_assoc]

-- lemma extractC_length (L : List α) {p q : ℕ} (hp : p ≤ L.length) (hq : q ≤ L.length) :
--     (L.extractC p q).length = if p < q then q - p else q + L.length - p := by
--   obtain rfl | hq := hq.eq_or_lt
--   · rw [extractC, if_neg (by simp), Nat.mod_self, take_zero, append_nil]
--     obtain rfl | hp := hp.eq_or_lt
--     · simp
--     rw [Nat.mod_eq_of_lt hp, if_pos hp, length_drop]
--   obtain rfl | hp := hp.eq_or_lt
--   · rw [extractC, if_neg (by simp), Nat.mod_self, drop_zero, Nat.mod_eq_of_lt hq, if_neg (by lia)]
--   rw [extractC]
--   split_ifs with h
--   · rw [length_extract _ hq]
--   rw [length_append, length_drop, length_take, min_eq_left hq]
--   lia

-- lemma extractC_length_eq_mod (L : List α) (p q : ℕ) (hp : p < L.length) (hq : q < L.length)
--     (hpq : p ≠ q) : (L.extractC p q).length = (L.length + q - p) % L.length := by
--   rw [extractC_length _ hp.le hq.le, eq_comm, Nat.mod_eq_iff]
--   right
--   split_ifs with h
--   · exact ⟨by lia, 1, by lia⟩
--   exact ⟨by lia, 0, by lia⟩


-- lemma extractC_add_one_self (L : List α) (p : ℕ) (hp : p < L.length) :
--     L.extractC p (p + 1) = [L[p]] := by
--   rw [extractC, if_pos (by lia), extract_add_one_right _ rfl.le hp, extract_eq_nil _ rfl.le,
--     nil_append]

-- lemma extractC_prefix_rotate (L : List α) (p q : ℕ) (hp : p < L.length) :
--     L.extractC p q <+: L.rotate p := by
--   obtain hq | hq := le_or_gt L.length q
--   · rw [extractC_of_length_le_right hp hq, rotate_eq_drop_append_take hp.le]
--     exact prefix_append ..
--   obtain hlt | hge := lt_or_ge p q
--   · rw [extractC, if_pos hlt, extract_eq_take_drop, rotate_eq_drop_append_take hp.le]
--     exact (take_prefix ..).trans <| prefix_append ..
--   rw [extractC, if_neg (by lia), rotate_eq_drop_append_take hp.le, prefix_append_right_inj]
--   exact take_prefix_take_left hge

-- lemma extractC_rotate (L : List α) (p q k : ℕ) (hp : p ≤ L.length) (hq : q ≤ L.length) :
--     (L.rotate k).extractC p q = L.extractC ((p + k) % L.length) ((q + k) % L.length) := by
--   _
