import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Order.Interval.Set.Fin
import Matroid.ForMathlib.Parity

variable {n : ℕ}

open Set

@[simp]
lemma Nat.one_mod' [h : Fact (1 < n)] : 1 % n = 1 := by
  rw [Nat.mod_eq_of_lt h.elim]

lemma Fin.range_val_eq_Iic (n : ℕ) [NeZero n] : range (Fin.val (n := n)) = Iic (n - 1) := by
  obtain rfl | n := n
  · exact False.elim <| NeZero.ne 0 rfl
  rw [Fin.range_val, Nat.add_sub_cancel]
  simp [Iio, Iic]

lemma Fin.eq_rev_iff {n : ℕ} (a b : Fin n) : a = rev b ↔ a.1 + b.1 + 1 = n := by
  rw [← Fin.val_inj, Fin.val_rev]
  lia

lemma Fin.rev_add_self {n : ℕ} [NeZero n] (a : Fin n) : a.rev + a = ⊤ := by
  rw [← Fin.val_inj, Fin.val_add_eq_ite, if_neg]
  · simp only [val_rev, val_top]
    lia
  simp only [val_rev, not_le]
  lia

lemma Fin.neg_one {n : ℕ} [NeZero n] : (-1 : Fin n) = ⊤ := by
  obtain rfl | rfl | n := n
  · grind
  · grind
  simp [← Fin.val_inj, val_top, val_neg]

lemma Fin.rev_eq_neg {n : ℕ} [NeZero n] (a : Fin n) : a.rev = - 1 - a := by
  rw [← add_left_inj a, sub_add_cancel, Fin.rev_add_self, Fin.neg_one]

lemma Fin.neg_eq_rev_add_one {n : ℕ} [NeZero n] (a : Fin n) : - a = a.rev + 1 := by
  simp only [rev_eq_neg]
  grind

lemma Fin.add_eq_top_iff {n} [NeZero n] {a b : Fin n} : a + b = ⊤ ↔ a = rev b := by
  rw [Fin.rev_eq_neg, eq_sub_iff_add_eq, Fin.neg_one]

@[simp]
lemma Fin.one_ne_zero {n : ℕ} [hn : Fact (1 < n)] : (1 : Fin n) ≠ 0 := by
  simp [hn.1.ne']

@[simp]
lemma Fin.zero_ne_one'' {n : ℕ} [hn : Fact (1 < n)] : 0 ≠ (1 : Fin n) := by
  simp [hn.1.ne']

@[simp]
lemma Fin.zero_ne_top {n : ℕ} [hn : Fact (1 < n)] : 0 ≠ (⊤ : Fin n) := by
  simp [hn.1.ne']

@[simp]
lemma Fin.top_ne_zero {n : ℕ} [hn : Fact (1 < n)] : (⊤ : Fin n) ≠ 0 := by
  simp [hn.1.ne']

lemma Fin.one_ne_top {n : ℕ} [NeZero n] (hn : 2 < n) : (1 : Fin n) ≠ ⊤ := by
  rw [Ne, ← Fin.val_inj, val_top, coe_ofNat_eq_mod, Nat.mod_eq_of_lt (by lia)]
  lia

lemma Fin.ofNat_ne_top {n k : ℕ} [NeZero n] [k.AtLeastTwo] (hn : k + 1 < n) :
    (ofNat(k) : Fin n) ≠ ⊤ := by
  rw [Ne, ← Fin.val_inj, coe_ofNat_eq_mod, val_top, Nat.mod_eq_of_lt (by grind)]
  change ¬ (k = n - 1)
  lia

lemma Fin.ofNat_add' {n k l : ℕ} [NeZero n] :
    (ofNat(k) : Fin n) + ofNat(l) = ofNat(k + l) := by
  rw [← Fin.val_inj, Fin.val_add, Fin.coe_ofNat_eq_mod, Fin.coe_ofNat_eq_mod, Fin.coe_ofNat_eq_mod]
  change (k % n + l % n) % n = (k + l) % n
  simp

lemma Fin.ofNat_eq_zero_iff [NeZero n] {k : ℕ} [k.AtLeastTwo] :
    (ofNat(k) : Fin n) = 0 ↔ (n ∣ k) := by
  rw [← Fin.val_inj, coe_ofNat_eq_mod, Nat.dvd_iff_mod_eq_zero]
  rfl

lemma Fin.ofNat_ne_zero [NeZero n] {k : ℕ} [hk : k.AtLeastTwo] (hkn : k < n) :
    (ofNat(k) : Fin n) ≠ 0 := by
  rw [Ne, Fin.ofNat_eq_zero_iff]
  contrapose! hkn
  exact Nat.le_of_dvd (by grind [hk.1]) hkn

@[simp]
lemma Fin.one_add_one {n : ℕ} [NeZero n] : (1 : Fin n) + 1 = 2 := by
  exact ofNat_add'

@[simp]
lemma Fin.cast_eq_top_iff {m n : ℕ} [NeZero n] [NeZero m] {hmn : m = n} (i : Fin m) :
    (i.cast hmn) = ⊤ ↔ i = ⊤ := by
  simp [← Fin.val_inj, hmn]

@[simp]
lemma Fin.rev_eq_top_iff {n : ℕ} [NeZero n] (i : Fin n) :
    i.rev = ⊤ ↔ i = 0 := by
  rw [← Fin.val_inj, ← Fin.val_inj, val_rev, val_top, val_zero]
  lia

@[simp]
lemma Fin.rev_eq_zero_iff {n : ℕ} [NeZero n] (i : Fin n) :
    i.rev = 0 ↔ i = ⊤ := by
  rw [← Fin.rev_eq_top_iff, rev_rev]

lemma Fin.cast_add_one {m n : ℕ} [NeZero n] [NeZero m] {hmn : m = n} (i : Fin m) :
    (i + 1).cast hmn = i.cast hmn + 1 := by
  subst hmn
  rfl

lemma Fin.cast_add_ofNat {m n k : ℕ} [NeZero n] [NeZero m] [k.AtLeastTwo] {hmn : m = n}
    (i : Fin m) :
    (i + ofNat(k)).cast hmn = i.cast hmn + ofNat(k) := by
  subst hmn
  rfl

lemma Fin.cast_sub_ofNat {m n k : ℕ} [NeZero n] [NeZero m] [k.AtLeastTwo] {hmn : m = n}
    (i : Fin m) :
    (i - ofNat(k)).cast hmn = i.cast hmn - ofNat(k) := by
  subst hmn
  rfl

lemma Fin.cast_sub_one {m n k : ℕ} [NeZero n] [NeZero m] [k.AtLeastTwo] {hmn : m = n}
    (i : Fin m) :
    (i - 1).cast hmn = i.cast hmn - 1 := by
  subst hmn
  rfl

lemma Fin.top_eq_neg_one {n : ℕ} [NeZero n] : (⊤ : Fin n) = - 1 := by
  obtain rfl | rfl | n := n <;> simp [← Fin.val_inj, Fin.val_neg]

lemma Fin.top_add {n : ℕ} [NeZero n] (a : Fin n) : (⊤ : Fin n) + a = a - 1 := by
  rw [add_comm, Fin.top_eq_neg_one, sub_eq_add_neg]

@[simp]
lemma Fin.top_add_one {n : ℕ} [NeZero n] : (⊤ : Fin n) + 1 = 0 := by
  simp [Fin.top_add]

lemma Fin.add_top {n : ℕ} [NeZero n] (a : Fin n) : a + ⊤ = a - 1 := by
  rw [Fin.top_eq_neg_one, sub_eq_add_neg]

lemma Fin.le_add_right_iff {n : ℕ} (i k : Fin n) : i ≤ i + k ↔ i.val + k.val < n := by
  rw [Fin.le_def, Fin.val_add_eq_ite]
  split_ifs <;> grind

lemma Fin.bodd_val_sub_one {n} [NeZero n] {i : Fin n} (hi : i ≠ 0) :
    (i - 1).1.bodd = !i.1.bodd := by
  rw [Fin.val_sub_one_of_ne_zero hi, Nat.bodd_sub (by grind)]
  simp only [Nat.bodd_succ, Nat.bodd_zero, Bool.not_false, Bool.bne_true]

lemma Fin.bodd_val_add_one {n} [NeZero n] {i : Fin n} (hi : i ≠ ⊤) :
    (i + 1).1.bodd = !i.1.bodd := by
  rw [Fin.val_add_one_of_lt' (by grind), Nat.bodd_succ]

lemma Fin.bodd_val_top {n} [NeZero n] : (⊤ : Fin n).1.bodd = !n.bodd := by
  have := NeZero.ne n
  simp [Nat.bodd_sub (show 1 ≤ n by lia)]

lemma Fin.bodd_val_add_of_even (hn : n.bodd = false) (a b : Fin n) :
    (a + b).1.bodd = (a.1.bodd ^^ b.1.bodd) := by
  rw [val_add, Nat.mod_bodd hn]
  simp

lemma Fin.bodd_val_sub_of_even (hn : n.bodd = false) (a b : Fin n) :
    (a - b).1.bodd = (a.1.bodd ^^ b.1.bodd) := by
  rw [val_sub, Nat.mod_bodd hn, Nat.bodd_add, Nat.bodd_sub b.2.le]
  simp [hn, Bool.xor_comm]

lemma Fin.bodd_val_neg_of_even (hn : n.bodd = false) (a : Fin n) : (-a).val.bodd = a.val.bodd := by
  simp [Fin.val_neg', Nat.mod_bodd hn, Nat.bodd_sub a.2.le, hn]

lemma Fin.bodd_val_rev_of_even (hn : n.bodd = false) (a : Fin n) :
    a.rev.val.bodd = !a.val.bodd := by
  simp [Fin.val_rev, Nat.bodd_sub (show a + 1 ≤ n by lia), hn]

lemma Fin.val_add_one_of_ne_top {n} [NeZero n] {a : Fin n} (ha : a ≠ ⊤) :
    (a + 1).val = a.val + 1 := by
  obtain rfl | rfl | n := n
  · grind
  · grind
  rw [← lt_top_iff_ne_top, Fin.lt_def, Fin.val_top] at ha
  rw [Fin.val_add_eq_of_add_lt (by simp [show a.1 ≤ n by lia])]
  simp

lemma Fin.val_add_two_of_ne {n} [NeZero n] {a : Fin n} (ha : a ≠ ⊤) (ha' : a ≠ Fin.rev 1) :
    (a + 2).val = a.val + 2 := by
  rw [show a + 2 = (a + 1 + 1) by simp [add_assoc], val_add_one_of_ne_top
    (by simpa [add_eq_top_iff]), val_add_one_of_ne_top ha]

lemma Fin.val_sub_two_of_ne {n} [NeZero n] {a : Fin n} (ha : a ≠ 0) (ha' : a ≠ 1) :
    (a - 2).val = a.val - 2 := by
  rw [show a - 2 = a - 1 - 1 by simp [sub_sub], val_sub_one_of_ne_zero (by simpa [sub_eq_zero]),
    val_sub_one_of_ne_zero ha]
  lia

lemma Fin.lt_iff_le_sub_one {n : ℕ} [NeZero n] {a b : Fin n} (hb : b ≠ 0) :
    a < b ↔ a ≤ b - 1 := by
  obtain rfl | rfl | n := n
  · grind
  · grind [cases Fin]
  rw [lt_def, le_def, Fin.sub_val_of_le (Fin.one_le_of_ne_zero hb), Fin.val_one',
    Nat.mod_eq_of_lt (by lia)]
  lia

lemma Fin.add_one_le_of_lt' {n : ℕ} [NeZero n] {a b : Fin n} (hab : a < b) : a + 1 ≤ b := by
  obtain rfl | n := n
  · grind
  exact add_one_le_of_lt hab

lemma Fin.lt_iff_add_one_le {n : ℕ} [NeZero n] {a b : Fin n} (ha : a ≠ ⊤) :
    a < b ↔ a + 1 ≤ b := by
  obtain rfl | rfl | n := n
  · grind
  · grind [cases Fin]
  rw [lt_def, le_def, Fin.val_add_one_of_lt' (by grind)]
  lia

lemma Fin.lt_add_one_iff_le {n : ℕ} [NeZero n] {a b : Fin n} (hb : b ≠ ⊤) : a < b + 1 ↔ a ≤ b := by
  rw [Fin.lt_iff_le_sub_one, add_sub_cancel_right]
  simpa [add_eq_zero_iff_eq_neg, neg_eq_rev_add_one, rev_add_self]

@[simp]
lemma Fin.le_add_one_self_iff {n : ℕ} {b : Fin (n + 2)} : b ≤ b + 1 ↔ b ≠ ⊤ := by
  obtain rfl | hb := eq_or_ne b ⊤
  · simp
  simpa [Fin.le_def, Fin.val_add_one_of_ne_top hb]

@[simp]
lemma Fin.le_add_one_self_iff' {n : ℕ} [Fact (1 < n)] {b : Fin n} : b ≤ b + 1 ↔ b ≠ ⊤ := by
  obtain rfl | rfl | n := n
  · grind
  · grind [Fact.elim]
  simp

lemma Fin.cast_add {m} (a b : Fin n) (hnm : n = m) :
    (a + b).cast hnm = a.cast hnm + b.cast hnm := by
  subst m
  rfl

lemma Fin.cast_sub {m} (a b : Fin n) (hnm : n = m) :
    (a - b).cast hnm = a.cast hnm - b.cast hnm := by
  subst m
  rfl

@[simp]
lemma Fin.cast_one [NeZero n] {m} [NeZero m] (hnm : n = m) : (1 : Fin n).cast hnm = 1 := by
  subst m
  rfl

@[simp]
lemma Fin.cast_ofNat [NeZero n] {m k} [NeZero m] [Nat.AtLeastTwo k] (hnm : n = m) :
    (ofNat(k) : Fin n).cast hnm = ofNat(k) := by
  subst m
  rfl

lemma Fin.Icc_add_one_right_eq_insert {n : ℕ} [NeZero n] {a b : Fin n} (hab : a ≤ b) (hb : b ≠ ⊤) :
    Icc a (b + 1) = insert (b + 1) (Icc a b) := by
  obtain rfl | rfl | n := n
  · grind
  · grind
  rw! [Icc, ofPred_and, Icc, ofPred_and, ← inter_insert_of_mem]
  · convert rfl
    ext i
    simp only [Set.mem_insert_iff, mem_ofPred_eq, le_iff_lt_or_eq (b := b + 1),
      Fin.lt_add_one_iff_le hb, or_comm]
  exact (hab.trans (by simpa))

open Fin.NatCast in
lemma List.rotate_getElem_fin {α : Type*} {L : List α} {k : ℕ} [NeZero L.length]
    (i : Fin (L.rotate k).length) : (L.rotate k)[i.1] = L[(i.cast (length_rotate L k) + k).1] := by
  simp [getElem_rotate, Fin.val_add]

lemma List.rotate_getElem_fin' {α : Type*} {L : List α} {k : Fin L.length} [NeZero L.length]
    (i : Fin (L.rotate k).length) : (L.rotate k)[i.1] = L[(i.cast (length_rotate L k) + k).1] := by
  rw [List.rotate_getElem_fin, Fin.cast_val_eq_self]

lemma List.rotate_rotate_fin {α : Type*} (L : List α) (a b : Fin L.length) :
    (L.rotate a).rotate b = L.rotate (a + b).1 := by
  rw [List.rotate_rotate, Fin.val_add, rotate_mod]

lemma List.rotate_rotate_neg_fin {α : Type*} (L : List α) (a b : Fin L.length) :
    (L.rotate a).rotate (-b).1 = (L.rotate (a - b).1)  := by
  rw [L.rotate_rotate_fin, Fin.sub_eq_add_neg]

lemma List.rotate_rotate_neg_fin_self {α : Type*} (L : List α) (a : Fin L.length) :
    (L.rotate a).rotate (-a).1 = L := by
  have := a.neZero
  simp [L.rotate_rotate_fin, add_neg_cancel]


lemma List.reverse_getElem_fin {α : Type*} {L : List α} {i : Fin L.reverse.length} :
    L.reverse[i.1] = L[(i.rev.cast (by simp) : Fin L.length).1] := by
  simp [Nat.sub_sub, add_comm 1]

lemma List.getElem_rev_fin {α : Type*} {L : List α} {i : Fin L.length} :
    L[i.rev.1] = L.reverse[(i.cast (by simp) : Fin L.reverse.length).1] := by
  rw! [L.reverse_getElem_fin]
  simp

@[simp]
lemma Fin.val_comp_cast {m n} (h : m = n) : Fin.val ∘ Fin.cast h = Fin.val := rfl

open Fin.NatCast in
@[simp]
lemma Fin.cast_natCast {m n} [NeZero m] [NeZero n] (h : m = n) (k : ℕ) :
    (k : Fin m).cast h = k := by
  subst h
  rfl

@[simps]
def Fin.negPerm {n : ℕ} : Equiv.Perm (Fin n) where
  toFun x := -x
  invFun x := -x
  left_inv x := by simp
  right_inv x := by simp

-- lemma Fin.le_neg_iff {a b : Fin n} : a ≤ -b ↔ b ≤ - a := by
--   have := a.neZero
--   rw [Fin.le_def, Fin.le_def, Fin.val_neg, Fin.val_neg]
--   split_ifs with hb ha
--   grind
--   simp [hb]

-- lemma Fin.preimage_rev_Icc {a b : Fin n} : (fun x ↦ - x) ⁻¹' Icc a b = Icc (-b) (-a) := by
--   ext i
