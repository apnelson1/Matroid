module

public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Order.Interval.Set.Fin
public import Matroid.ForMathlib.Parity
public import Mathlib.Order.Circular.ZMod
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

variable {n : ℕ}

open Set

lemma Icc_zero_left {α : Type*} [Preorder α] [Bot α] [Zero α] [IsBotZeroClass α] (a : α) :
    Icc 0 a = Iic a := by
  simp [Icc, Iic]

lemma Ico_zero_left {α : Type*} [Preorder α] [Bot α] [Zero α] [IsBotZeroClass α] (a : α) :
    Ico 0 a = Iio a := by
  simp [Ico, Iio]

@[simp]
lemma Nat.one_mod' [h : Fact (1 < n)] : 1 % n = 1 := by
  rw [Nat.mod_eq_of_lt h.elim]

@[simp]
lemma Fin.mod_val_eq (i : Fin n) : i.1 % n = i.1 :=
  Nat.mod_eq_of_lt i.2

@[simp]
lemma Nat.mod_lt' (a n : ℕ) [hn : NeZero n] : a % n < n :=
  Nat.mod_lt _ <| by grind [hn.1]

lemma Fin.range_val_eq_Iic (n : ℕ) [NeZero n] : range (Fin.val (n := n)) = Iic (n - 1) := by
  obtain rfl | n := n
  · exact False.elim <| NeZero.ne 0 rfl
  rw [Fin.range_val, Nat.add_sub_cancel]
  simp [Iio, Iic]

lemma Fin.eq_rev_iff {n : ℕ} (a b : Fin n) : a = rev b ↔ a.1 + b.1 + 1 = n := by
  rw [← Fin.val_inj, Fin.val_rev]
  lia

lemma Fin.rev_add_self {n : ℕ} [NeZero n] (a : Fin n) : a.rev + a = ⊤ := by
  rw [← Fin.val_inj, Fin.val_add_eq_ite, ite_eq_right]
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

@[simp]
lemma Fin.rev_neg [NeZero n] (a : Fin n) : (-a).rev = a - 1 := by
  simp [rev_eq_neg, add_comm _ a, sub_eq_add_neg]

@[simp]
lemma Fin.neg_rev [NeZero n] (a : Fin n) : -a.rev = a + 1 := by
  simp [rev_eq_neg]

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

lemma Fin.cast_sub_one {m n : ℕ} [NeZero n] [NeZero m] {hmn : m = n} (i : Fin m) :
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

lemma Fin.top_sub {n : ℕ} [NeZero n] (a : Fin n) : (⊤ : Fin n) - a = a.rev := by
  rw [Fin.top_eq_neg_one, rev_eq_neg]

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

lemma Fin.add_one_le_add_one_iff [NeZero n] {a b : Fin n} :
    a + 1 ≤ b + 1 ↔ a = ⊤ ∨ (a ≤ b ∧ b ≠ ⊤) := by
  obtain rfl | hb := eq_or_ne b ⊤
  · simp [add_eq_zero_iff_eq_neg, neg_one]
  obtain rfl | ha := eq_or_ne a ⊤
  · simp
  simp_rw [Fin.le_def, val_add_one_of_ne_top ha, val_add_one_of_ne_top hb, or_iff_right ha,
    and_iff_left hb, Nat.add_one_le_add_one_iff]

lemma Fin.sub_one_le_sub_one_iff [NeZero n] {a b : Fin n} :
    a - 1 ≤ b - 1 ↔ b = 0 ∨ (a ≤ b ∧ a ≠ 0) := by
  obtain rfl | ha := eq_or_ne a 0
  · simp [neg_one, sub_eq_iff_eq_add]
  obtain rfl | hb := eq_or_ne b 0
  · simp [neg_one]
  simp_rw [Fin.le_def, val_sub_one_of_ne_zero ha, val_sub_one_of_ne_zero hb]
  lia

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

lemma Fin.one_le_iff_ne_zero {n : ℕ} [Fact (1 < n)] {a : Fin n} : 1 ≤ a ↔ a ≠ 0 := by
  rw [← zero_add 1, ← Fin.lt_iff_add_one_le zero_ne_top, lt_iff_le_and_ne, and_iff_right (by simp),
    ne_comm]

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

lemma Fin.cast_neg {m n : ℕ} (hmn : m = n) (a : Fin m) : (-a).cast hmn = - a.cast hmn := by
  subst hmn
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

open Fin.NatCast in
lemma List.rotate_getElem_fin' {α : Type*} {L : List α} {k : ℕ} [NeZero L.length]
    (i : Fin L.length) : (L.rotate k)[i.1] = L[(i + k).1] := by
  simp [getElem_rotate, Fin.val_add]

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

lemma Fin.val_sub_eq_ite (a b : Fin n) :
    (a - b).1 = if b ≤ a then a.1 - b.1 else n + a.1 - b.1 := by
  simp_rw [val_sub, Fin.le_def]
  split_ifs with ha
  · simp [show n - b.1 + a.1 = n + (a.1 - b.1) by lia, Nat.mod_eq_of_lt (show a.1 - b.1 < n by lia)]
  rw [Nat.mod_eq_of_lt (by lia)]
  lia

lemma Fin.preimage_add_Icc [NeZero n] {a b d : Fin n} (hab : a ≤ b) (hle : d ≤ a ∨ b ≤ d - 1) :
    (fun x ↦ x + d) ⁻¹' Icc a b = Icc (a - d) (b - d) := by
  obtain rfl | h0 := eq_or_ne d 0
  · simp
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  obtain ⟨d, hd⟩ := d
  obtain ⟨s, rfl⟩ := exists_add_of_le (show a ≤ b from hab)
  ext i
  obtain ⟨i, hi⟩ := i
  simp_rw [Fin.le_def, Fin.val_sub_one_of_ne_zero h0] at hle
  simp_rw [mem_preimage, mem_Icc, Fin.le_def, Fin.val_add_eq_ite, Fin.val_sub_eq_ite, Fin.le_def]
  grind

lemma Fin.preimage_sub_Icc [NeZero n] {a b d : Fin n} (hab : a ≤ b)
    (hd : a.rev < d ∨ d ≤ b.rev) : (fun x ↦ x - d) ⁻¹' Icc a b = Icc (a + d) (b + d) := by
  have := a.neZero
  obtain rfl | hne := eq_or_ne d 0
  · simp
  simp_rw [sub_eq_add_neg]
  rw [Fin.preimage_add_Icc hab, sub_neg_eq_add, sub_neg_eq_add]
  rw [neg_eq_rev_add_one, add_sub_cancel_right, le_rev_iff, Fin.le_def, Fin.val_add_one_of_ne_top
    (by simpa), Fin.val_rev, show n - (d.1 + 1) + 1 ≤ a.1 ↔ n - (a.1 + 1) + 1 ≤ d.1 by lia,
    ← Fin.val_rev]
  rwa [Fin.lt_def, ← Nat.add_one_le_iff] at hd

lemma Fin.preimage_add_Ici {a d : Fin n} (hda : d ≤ a) :
    (fun x ↦ x + d) ⁻¹' Ici a = Icc (a - d) d.rev := by
  have := a.neZero
  rw [← Icc_top, Fin.preimage_add_Icc (by simp) (.inl hda), Fin.top_sub]

lemma Fin.preimage_sub_Iic {a d : Fin n} (hd : d ≤ a.rev) :
    (fun x ↦ x - d) ⁻¹' Iic a = Icc d (a + d) := by
  have hnz := a.neZero
  rw [← Icc_zero_left, preimage_sub_Icc (by simp) (.inr hd), zero_add]



theorem btw_iff_sbtw {α : Type*} [CircularOrder α] {a b c : α} (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) : btw a b c ↔ sbtw a b c := by
  refine ⟨fun h ↦ by_contra fun hcon ↦ ?_, fun h ↦ h.btw⟩
  rw [← btw_iff_not_sbtw] at hcon
  grind [h.antisymm hcon]

theorem btw_iff_not_btw {α : Type*} [CircularOrder α] {a b c : α} (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) : btw a b c ↔ ¬ btw a c b := by
  rw [btw_iff_sbtw hab hbc hac, sbtw_iff_not_btw, btw_cyclic]

theorem SBtw.sbtw.ne₁₂ {α : Type*} [CircularPreorder α] {a b c : α} (habc : sbtw a b c) :
    a ≠ b := by
  rintro rfl
  exact sbtw_irrefl_left habc

theorem SBtw.sbtw.ne₂₃ {α : Type*} [CircularPreorder α] {a b c : α} (habc : sbtw a b c) :
    b ≠ c := by
  rintro rfl
  exact sbtw_irrefl_right habc

theorem SBtw.sbtw.ne₁₃ {α : Type*} [CircularPreorder α] {a b c : α} (habc : sbtw a b c) :
    a ≠ c := by
  rintro rfl
  exact sbtw_irrefl_left_right habc

open Fin.NatCast in
/-- An induction principle for `Fin n` where successor is `Fin` addition,
and the base case is anything. -/
@[elab_as_elim]
theorem Fin.induction_add_one {n : ℕ} [NeZero n] {motive : Fin n → Prop} (ex : ∃ i, motive i)
    (succ : ∀ s (_ih : motive s), motive (s + 1)) (a : Fin n) : motive a := by
  obtain ⟨i₀, hi₀⟩ := ex
  suffices aux : ∀ k : ℕ, motive (i₀ + k) by simpa using aux (a - i₀).1
  intro k
  induction k with
  | zero => simpa
  | succ k ih => simpa [add_assoc] using succ _ ih

theorem Fin.btw_zero_left_iff [NeZero n] {a b : Fin n} : btw 0 a b ↔ a ≤ b ∨ b = 0 := by
  simp only [btw_iff, _root_.zero_le, true_and, nonpos_iff_eq_zero, and_true]
  lia

theorem Fin.sbtw_iff_zero_left [NeZero n] {a b : Fin n} : sbtw 0 a b ↔ a ≠ 0 ∧ a < b := by
  simp [Fin.sbtw_iff, lt_iff_le_and_ne, eq_comm (a := a)]

theorem Fin.sbtw_iff_top_right [NeZero n] {a b : Fin n} : sbtw a b ⊤ ↔ a < b ∧ b ≠ ⊤ := by
  simp [Fin.sbtw_iff, lt_iff_le_and_ne, eq_comm (a := a)]

@[simp]
theorem Fin.btw_add_right_iff {a b c k : Fin n} : btw (a + k) (b + k) (c + k) ↔ btw a b c := by
  have hnz := k.neZero
  suffices aux : ∀ (x y z : Fin n), btw x y z ↔ btw (x + 1) (y + 1) (z + 1) by
    induction k using Fin.induction_add_one with
    | ex => exact ⟨0, by simp⟩
    | succ s ih => simp_rw [← ih, ← add_assoc, ← aux]
  intro x y z
  simp only [btw_iff, add_one_le_add_one_iff, ne_eq]
  cases hx : eq_or_ne x ⊤ with cases hy : eq_or_ne y ⊤ with cases hz : eq_or_ne z ⊤ with grind

@[simp]
theorem Fin.sbtw_add_right_iff {a b c k : Fin n} : sbtw (a + k) (b + k) (c + k) ↔ sbtw a b c := by
  rw [sbtw_iff_not_btw, btw_add_right_iff, sbtw_iff_not_btw]

@[simp]
theorem Fin.btw_sub_right_iff {a b c k : Fin n} : btw (a - k) (b - k) (c - k) ↔ btw a b c := by
  have := k.neZero
  rw [← btw_add_right_iff (k := k), sub_add_cancel, sub_add_cancel, sub_add_cancel]

@[simp]
theorem Fin.sbtw_sub_right_iff {a b c k : Fin n} : sbtw (a - k) (b - k) (c - k) ↔ sbtw a b c := by
  rw [sbtw_iff_not_btw, btw_sub_right_iff, sbtw_iff_not_btw]

theorem Fin.btw_rev_iff {a b c : Fin n} : btw a.rev b.rev c.rev ↔ btw c b a := by
  simp only [btw_iff, rev_le_rev]
  tauto

theorem Fin.btw_iff_of_lt {a b x : Fin n} (hab : a < b) : btw a x b ↔ a ≤ x ∧ x ≤ b := by
  simp [btw_iff, hab.not_ge]

theorem Fin.btw_iff_of_ge {a b x : Fin n} (hab : b ≤ a) : btw a x b ↔ x ≤ b ∨ a ≤ x := by
  rw [btw_iff, and_iff_left hab, and_iff_right hab]
  obtain hax | hxa := le_or_gt a x
  · simp [hax]
  simp [hxa.not_ge]

theorem Fin.sbtw_iff_of_le {a b x : Fin n} (hab : a ≤ b) : sbtw a x b ↔ a < x ∧ x < b := by
  simp [sbtw_iff, hab.not_gt]

theorem Fin.sbtw_iff_of_gt {a b x : Fin n} (hab : b < a) : sbtw a x b ↔ x < b ∨ a < x := by
  simp only [sbtw_iff, hab, and_true, true_and, or_iff_right_iff_imp, and_imp]
  exact fun hax hxb ↦ False.elim <| (hax.trans hxb).not_ge hab.le

theorem Fin.ofPred_btw_of_lt {a b : Fin n} (hab : a < b) : {x | btw a x b} = Icc a b := by
  simp [Set.ext_iff, Fin.btw_iff_of_lt hab]

theorem Fin.ofPred_btw_of_ge {a b : Fin n} (hab : b ≤ a) : {x | btw a x b} = Iic b ∪ Ici a := by
  simp [Set.ext_iff, Fin.btw_iff_of_ge hab]

theorem Fin.ofPred_sbtw_of_le {a b : Fin n} (hab : a ≤ b) : {x | sbtw a x b} = Ioo a b := by
  simp [Set.ext_iff, Fin.sbtw_iff_of_le hab]

theorem Fin.ofPred_sbtw_of_gt {a b : Fin n} (hab : b < a) : {x | sbtw a x b} = Iio b ∪ Ioi a := by
  simp [Set.ext_iff, Fin.sbtw_iff_of_gt hab]

@[simp]
theorem Fin.btw_cast_iff {m n : ℕ} {a b c : Fin m} {hmn : m = n} :
    btw (a.cast hmn) (b.cast hmn) (c.cast hmn) ↔ btw a b c := by
  subst hmn
  rfl

@[simp]
theorem Fin.sbtw_cast_iff {m n : ℕ} {a b c : Fin m} {hmn : m = n} :
    sbtw (a.cast hmn) (b.cast hmn) (c.cast hmn) ↔ sbtw a b c := by
  subst hmn
  rfl

instance Fin.btw_decidable (a b c : Fin n) : Decidable (btw a b c) := by
  rw [btw_iff]
  infer_instance

instance Fin.sbtw_decidable (a b c : Fin n) : Decidable (sbtw a b c) := by
  rw [sbtw_iff]
  infer_instance

lemma finRange_congr {m n} (hmn : m = n) :
    List.finRange m = (List.finRange n).map (Fin.cast hmn.symm) := by
  subst hmn
  simp

@[simp]
lemma finRange_one : List.finRange 1 = [0] := rfl

@[simp]
lemma finRange_two : List.finRange 2 = [0, 1] := rfl

@[simp]
lemma finTwoEquiv_apply (n : Fin 2) : finTwoEquiv n = n.1.bodd := by
  obtain ⟨rfl | rfl | n, hn⟩ := n
  · simp [finTwoEquiv]
  · simp [finTwoEquiv]
  simp at hn

lemma image_image_fin_getElem {α β : Type*} (L : List α) (f : β → Fin L.length)
    (s : Set β) : (fun i ↦ L[(f i).1]) '' s = (fun (i : Fin L.length) ↦ L[i.1]) '' (f '' s) := by
  simp [image_image]

open Fin.NatCast in
lemma rotate_get_image {α : Type*} (L : List α) [NeZero L.length] (k : ℕ)
    (s : Set (Fin (L.rotate k).length)) : (L.rotate k).get '' s =
    L.get '' (fun i ↦ i - (k : Fin L.length)) ⁻¹' (Fin.cast (by simp) ⁻¹' s) := by
  ext a
  rw [preimage_preimage, mem_image, mem_image]
  simp_rw [List.get_rotate, mem_preimage, ← Fin.val_natCast, Nat.cast_add]
  refine ⟨fun ⟨i, his, hi⟩ ↦ ⟨_, ?_, hi⟩, fun ⟨i, hix, hia⟩ ↦ ⟨_, hix, by simpa using hia⟩⟩
  convert his
  simp [← Fin.val_inj, Nat.mod_eq_of_lt (show i.1 < L.length by simpa using i.2)]
