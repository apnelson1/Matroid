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
  rw [Nat.bodd_eq_ite, if_neg (by rwa [Nat.not_odd_iff_even])]

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
