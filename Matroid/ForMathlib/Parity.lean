module

public import Mathlib.Data.Nat.Bits
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Order.Basic
public import Matroid.ForMathlib.Bool
public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Order.Interval.Set.SuccPred

@[expose] public section

lemma Nat.bodd_eq_odd (n : ℕ) : n.bodd = Odd n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [bodd_succ, Bool.not_eq_eq_eq_not, Bool.not_true, eq_iff_iff]
    grind

lemma Nat.bodd_eq_ite (n : ℕ) : n.bodd = if Odd n then true else false := by
  simp [← n.bodd_eq_odd]

@[simp]
lemma Bool.dcond_true {α : Sort*} (x : true = true → α) (y : true = false → α) :
    Bool.dcond true x y = x rfl := rfl

@[simp]
lemma Bool.dcond_false {α : Sort*} (x : false = true → α) (y : false = false → α) :
    Bool.dcond false x y = y rfl := rfl

lemma Odd.bodd {n : ℕ} (hn : Odd n) : n.bodd = true := by
  rwa [n.bodd_eq_odd]

lemma Even.bodd {n : ℕ} (hn : Even n) : n.bodd = false := by
  rw [Nat.bodd_eq_ite, ite_eq_right (by rwa [Nat.not_odd_iff_even])]

@[grind! .]
lemma Bool.toNat_le_one (b : Bool) : b.toNat ≤ 1 := by
  cases b with simp

@[simp, grind =]
lemma Bool.toNat_bodd (b : Bool) : b.toNat.bodd = b := by
  cases b with rfl

@[grind! .]
lemma Nat.bodd_toNat_le (n : ℕ) : n.bodd.toNat ≤ n := by
  cases n with grind

lemma Nat.bodd_sub {a b : ℕ} (hab : a ≤ b) : (b - a).bodd = (b.bodd != a.bodd) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  simp

lemma Nat.add_one_lt_of_bodd_eq {a b : ℕ} (hab : a < b) (hab' : a.bodd = b.bodd) : a + 1 < b := by
  have := eq_or_lt_of_le (show a + 1 ≤ b from hab)
  refine (show a + 1 ≤ b from hab).eq_or_lt.elim ?_ id
  rintro rfl
  simp at hab'

lemma Nat.mod_bodd {n : ℕ} (hn : n.bodd = false) (i) : (i % n).bodd = i.bodd := by
  nth_rw 1 [eq_comm, ← i.mod_add_div n, bodd_add, bodd_mul, hn]
  simp

lemma div2_add (a b : ℕ) : (a + b).div2 = a.div2 + b.div2 + (a.bodd && b.bodd).toNat := by
  nth_rw 1 [← a.bodd_add_div2, ← b.bodd_add_div2]
  cases ha : a.bodd
  · cases hb : b.bodd
    · simp [← mul_add]
    simp [show 2 * a.div2 + (1 + 2 * b.div2) = 2 * (a.div2 + b.div2) + 1 by lia]
  cases hb : b.bodd
  · simp only [Bool.toNat_true, Bool.toNat_false, zero_add, add_assoc, ← mul_add, Bool.and_false,
      add_zero]
    rw [add_comm 1]
    simp
  simp [show (1 + 2 * a.div2 + (1 + 2 * b.div2)) = 2 * (a.div2 + b.div2 + 1) by lia]

@[simp]
lemma div2_add_left (m n : ℕ) : (2 * m + n).div2 = m + n.div2 := by
  simp [div2_add]

@[simp]
lemma div2_add_right (m n : ℕ) : (m + 2 * n).div2 = m.div2 + n := by
  simp [div2_add]

lemma div2_mod (m : ℕ) {n} (hn : n.bodd = false) : (m % n).div2 = m.div2 % n.div2 := by
  have hn' : Even n := by rwa [← Nat.not_odd_iff_even, ← Nat.bodd_eq_odd, Bool.not_eq_true]
  obtain ⟨a, rfl⟩ : ∃ a, n = 2 * a := (even_iff_exists_two_nsmul n).mp hn'
  clear hn hn'
  induction m using Nat.strong_induction_on with | h m ih =>
  obtain rfl | hne := eq_or_ne a 0
  · simp
  obtain hlt | hle := lt_or_ge m (2 * a)
  · rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt]
    grind [Nat.div2_bit0]
  obtain ⟨d, rfl⟩ := exists_add_of_le hle
  simp only [Nat.add_mod_left, Nat.div2_bit0, ih d (by lia), div2_add_left]

lemma encard_Ico_inter_bodd {x y : ℕ} (hxy : x ≤ y) (b : Bool) :
    2 * (Set.Ico x y ∩ {i | i.bodd = b}).encard + x + (b != x.bodd).toNat =
    y + (b != y.bodd).toNat := by
  obtain ⟨d, rfl⟩ := exists_add_of_le hxy
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← add_assoc, ← Set.insert_Ico_right_eq_Ico_add_one (by simp)]
    obtain rfl | rfl := b.eq_or_eq_not (x + d).bodd
    · rw [Set.insert_inter_of_mem (by simp), Set.encard_insert_of_notMem (by simp), mul_add,
        add_right_comm (b := 2 * 1), add_right_comm, ih (by simp)]
      simp [add_assoc, one_add_one_eq_two]
    rw [Set.insert_inter_of_notMem (by cases h : x.bodd with simp [h]), ih (by simp)]
    cases h : x.bodd with simp [h]

lemma encard_Icc_inter_bodd {x y : ℕ} (hxy : x ≤ y + 1) (b : Bool) :
    2 * (Set.Icc x y ∩ {i | i.bodd = b}).encard + x + (b != x.bodd).toNat =
    y + 1 + (b == y.bodd).toNat := by
  rw [← Set.Ico_add_one_right_eq_Icc, encard_Ico_inter_bodd hxy]
  simp

lemma encard_Iio_inter_bodd (y : ℕ) (b : Bool) :
    2 * (Set.Iio y ∩ {i | i.bodd = b}).encard + b.toNat = y + (b != y.bodd).toNat := by
  rw [show Set.Iio y = Set.Ico 0 y by grind, ← encard_Ico_inter_bodd (x := 0) (by simp)]
  simp

lemma encard_Iio_inter_bodd_of_even {y : ℕ} (hy : y.bodd = false) (b : Bool) :
    2 * (Set.Iio y ∩ {i | i.bodd = b}).encard = y := by
  simpa [hy] using encard_Iio_inter_bodd y b

lemma Fin.encard_Icc_inter_set_of_bodd {n : ℕ} {p q : Fin n} (hpq : p ≤ q) (d : Bool) :
    2 * (Set.Icc p q ∩ {i : Fin n | i.1.bodd = d}).encard + p + (d != p.1.bodd).toNat =
      q + 1 + (d == q.1.bodd).toNat := by
  rw [← Fin.val_injective.encard_image, ← encard_Icc_inter_bodd (x := p) (by grind)]
  convert rfl
  ext i
  simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_ofPred_eq, Set.mem_image]
  refine ⟨fun ⟨⟨hpi, hiq⟩, hi⟩ ↦ ⟨⟨i, by grind⟩, ⟨⟨hpi, hiq⟩, hi⟩, rfl⟩, ?_⟩
  rintro ⟨x, hx, rfl⟩
  assumption

lemma Fin.encard_setOf_bodd (n : ℕ) (d : Bool) :
    2 * {i : Fin n | i.1.bodd = d}.encard + d.toNat = n + (d != n.bodd).toNat := by
  obtain rfl | n := n
  · simp [Set.eq_empty_of_isEmpty]
  simpa using Fin.encard_Icc_inter_set_of_bodd (show (0 : Fin (n + 1)) ≤ ⊤ by simp) d

lemma Fin.encard_setOf_bodd_of_even {n : ℕ} (hn : n.bodd = false) (d : Bool) :
    2 * {i : Fin n | i.1.bodd = d}.encard = n := by
  simpa [hn] using Fin.encard_setOf_bodd n d

lemma Fin.add_bodd {n : ℕ} (hn : n.bodd = false) (a b : Fin n) :
    (a + b).1.bodd = (a.1.bodd ^^ b.1.bodd) := by
  rw [Fin.val_add, Nat.mod_bodd hn, Nat.bodd_add]

lemma Fin.sub_bodd {n : ℕ} (hn : n.bodd = false) (a b : Fin n) :
    (a - b).1.bodd = (a.1.bodd ^^ b.1.bodd) := by
  rw [Fin.val_sub, Nat.mod_bodd hn, Nat.bodd_add, Nat.bodd_sub b.2.le]
  simp [hn, Bool.xor_comm]

lemma Fin.rev_bodd {n : ℕ} (a : Fin n) : a.rev.1.bodd = (n.bodd == a.1.bodd) := by
  rw [Fin.val_rev, Nat.bodd_sub (by grind)]
  simp

lemma Fin.rev_bodd_of_even {n : ℕ} (hn : n.bodd = false) (a : Fin n) :
    a.rev.1.bodd = !a.1.bodd := by
  rw [a.rev_bodd]
  simp [hn]
