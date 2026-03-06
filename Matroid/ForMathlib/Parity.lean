import Mathlib.Data.Nat.Bits
import Mathlib.Algebra.Ring.Parity

-- variable {α : Type*} {X Y C K T : Set α} {e f g x y : α} {b c d : Bool}
--     {J : Bool → List α} {L : List α} {n i j : ℕ}

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
