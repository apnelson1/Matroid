import Mathlib.Data.ENat.Basic
import Matroid.ForMathlib.ENat
import Matroid.ForMathlib.Tactic.ENatGrindPrelude

set_option linter.style.longLine false

namespace ENat.Grind

variable {a b c : ℕ∞} {r : ℕ → ℕ → Prop}

/- The idea is that we take every `ℕ∞` (inequality) `h`, and rephrase it in the form
`(h ∧ h₀) ∨ h₁`, where `h₀` is a statement that to the effect that all terms appearing in `h`
are finite, and `h₁` is a boolean combination of equalities of the form `_ = 0` and `_ = ⊤`.

For example, the statement `a * b = c` would become something like
`(a * b = c ∧ ((a ≠ ⊤ ∧ b ≠ ⊤ ∧ c ≠ ⊤) ∨ (b = 0 ∧ c = 0) ∨ (a = 0 ∧ c = 0))`
`∨ (a = ⊤ ∧ b ≠ 0 ∧ c = ⊤) ∨ (a ≠ 0 ∧ b = ⊤ ∧ c = ⊤)`

This is done with a specialized `enat_grind_canonize` simpset.
To stop the simping process looping forever on on `h` and statements like `a = 0` and `a = ⊤`,
we use `IsZero`/`IsNat` predicates and a `Rel` wrapper for the relation `h` in the simplified form.
For example, `a < b` will become `(Rel (· < ·) a b ∧ IsNat a ∧ IsNat b) ∨ (IsNat a ∧ ¬ IsNat b)`.

Once this is done, there is a good amount of transparent logical information on which variables
are known to be zero/nonzero and finite/infinite. From here, we use `grind` to attempt to
deduce that individual variables are (non)zero or (in)finite. Whenever we can do this for
a variable, we can substitute it out and repeat.

The standard use case is where the goal is
trivial in all cases except where every variable is `Nat`; if this is the case, then
this process should end with a purely `Nat` goal. -/

/-- `a : ℕ∞` is finite. -/
def IsNat (a : ℕ∞) := ∃ a₀ : ℕ, a = a₀

/-- `a : ℕ∞` is zero. -/
def IsZero (a : ℕ∞) := a = 0

lemma isNat_iff : IsNat a ↔ a ≠ ⊤ := by cases a with simp [IsNat]

-- simp lemmas
lemma isNat_add_iff : IsNat (a + b) ↔ IsNat a ∧ IsNat b := by simp [isNat_iff, ENat.add_eq_top]
lemma isNat_mul_iff : IsNat (a * b) ↔ (IsNat a ∧ IsNat b) ∨ IsZero a ∨ IsZero b := by
  grind [isNat_iff, ENat.mul_eq_top_iff, IsZero, ENat.top_ne_zero]
lemma isNat_sub_iff : IsNat (a - b) ↔ IsNat a ∨ ¬ IsNat b := by
  grind [isNat_iff, sub_eq_top_iff]
lemma isNat_pow_iff {b : ℕ} : IsNat (a ^ b) ↔ IsNat a ∨ b = 0 := by
  grind [isNat_iff, pow_eq_top_iff]
lemma isZero_add_iff : IsZero (a + b) ↔ IsZero a ∧ IsZero b := by simp [IsZero]
lemma isZero_mul_iff : IsZero (a * b) ↔ IsZero a ∨ IsZero b := by simp [IsZero]
lemma isZero_sub_iff : IsZero (a - b) ↔ a ≤ b := by
  cases a <;> cases b <;> simp [← ENat.coe_sub, IsZero, Nat.sub_eq_zero_iff_le]
lemma isZero_pow_iff {b : ℕ} : IsZero (a ^ b) ↔ IsZero a ∧ b ≠ 0 := by simp [IsZero]
lemma isNat_zero : IsNat 0 := isNat_iff.2 zero_ne_top
lemma isNat_one : IsNat 1 := isNat_iff.2 one_ne_top
lemma isNat_ofNat (a : ℕ) [a.AtLeastTwo] : IsNat ofNat(a) := by simp [isNat_iff]
lemma isNat_coe {a : ℕ} : IsNat a := by simp [IsNat]
lemma not_isNat_top : ¬ IsNat ⊤ := by simp [IsNat]
lemma not_isZero_top : ¬ IsZero ⊤ := by simp [IsZero]
lemma isZero_zero : IsZero 0 := rfl
lemma not_isZero_one : ¬ IsZero 1 := by simp [IsZero]
lemma not_isZero_ofNat {a : ℕ} [a.AtLeastTwo] : ¬ IsZero ofNat(a) := by simp [IsZero]
lemma isZero_coe {a : ℕ} : IsZero a ↔ a = 0 := by simp [IsZero]

attribute [enat_grind_canonize] isNat_zero isNat_one isNat_ofNat isNat_coe not_isNat_top isZero_zero
isNat_add_iff isNat_mul_iff isNat_sub_iff isNat_pow_iff not_isZero_one not_isZero_ofNat isZero_coe
not_isZero_top isZero_add_iff isZero_mul_iff isZero_sub_iff isZero_pow_iff

-- grind lemmaa
@[grind.]
lemma IsZero.isNat (h : IsZero a) : IsNat a := by obtain rfl := h; simp [isNat_iff]

/-- for a relation `r` on `ℕ`, `Rel r` is a wrapper for the lift of `r` to `ℕ∞`. -/
@[mk_iff]
structure Rel (r : ℕ → ℕ → Prop) (a b : ℕ∞) : Prop where
  ne_left : a ≠ ⊤
  ne_right : b ≠ ⊤
  rel : r a.toNat b.toNat


lemma rel_le_iff : Rel (· ≤ ·) a b ↔ a ≤ b ∧ IsNat a ∧ IsNat b := by
  cases a with cases b with simp [rel_iff, IsNat]

lemma rel_eq_iff : Rel (· = ·) a b ↔ a = b ∧ IsNat a ∧ IsNat b := by
  cases a with cases b with simp [rel_iff, IsNat]

lemma rel_lt_iff : Rel (· < ·) a b ↔ a < b ∧ IsNat a ∧ IsNat b := by
  cases a with cases b with simp [rel_iff, IsNat]

lemma rel_ne_iff : Rel (· ≠ ·) a b ↔ a ≠ b ∧ IsNat a ∧ IsNat b := by
  cases a with cases b with simp [rel_iff, IsNat]

-- simp lemmas for the interaction of `Rel` with coercions, infinities, numerals, zeroes and ones.
lemma rel_swap : Rel r a b ↔ Rel (Function.swap r) b a := by grind only [rel_iff]
lemma not_rel_top_left : ¬ Rel r ⊤ a := fun h ↦ h.ne_left rfl
lemma not_rel_top_right : ¬ Rel r a ⊤ := fun h ↦ h.ne_right rfl
lemma rel_coe_coe {a b : ℕ} : Rel r a b ↔ r a b := by simp [rel_iff]
lemma rel_ofNat_coe {a b : ℕ} [a.AtLeastTwo] : Rel r ofNat(a) b ↔ r a b := by simp [rel_iff]
lemma rel_coe_ofNat {a b : ℕ} [b.AtLeastTwo] : Rel r a ofNat(b) ↔ r a b := by simp [rel_iff]
lemma rel_ofNat_ofNat {a b : ℕ} [a.AtLeastTwo] [b.AtLeastTwo] :
    Rel r ofNat(a) ofNat(b) ↔ r a b := by simp [rel_iff]
lemma rel_one_ofNat {a : ℕ} [a.AtLeastTwo] : Rel r 1 ofNat(a) ↔ r 1 a := by simp [rel_iff]
lemma rel_ofNat_one {a : ℕ} [a.AtLeastTwo] : Rel r 1 ofNat(a) ↔ r 1 a := by simp [rel_iff]
lemma rel_one_coe {a : ℕ} : Rel r 1 a ↔ r 1 a := by simp [rel_iff]
lemma rel_coe_one {a : ℕ} : Rel r 1 a ↔ r 1 a := by simp [rel_iff]
lemma rel_zero_le {a : ℕ∞} : Rel (· ≤ ·) 0 a ↔ IsNat a := by simp [isNat_iff, rel_iff]
lemma rel_one_le : Rel (· ≤ ·) 1 a ↔ ¬ IsZero a ∧ IsNat a := by
  simp [rel_iff, IsZero, Nat.one_le_iff_ne_zero, isNat_iff]
lemma rel_zero_lt : Rel (· < ·) 0 a ↔ ¬ IsZero a ∧ IsNat a := by
  simp [rel_iff, IsZero, Nat.pos_iff_ne_zero, isNat_iff]
lemma rel_zero_ne : Rel (· ≠ ·) 0 a ↔ ¬ IsZero a ∧ IsNat a :=  by
  simp [rel_iff, IsZero, eq_comm, isNat_iff]
lemma rel_ne_zero : Rel (· ≠ ·) a 0 ↔ ¬ IsZero a ∧ IsNat a := by
  simp [rel_iff, IsZero, isNat_iff]
lemma rel_lt_zero : ¬ Rel (· < ·) a 0 := by simp [rel_iff]
lemma rel_lt_one : Rel (· < ·) a 1 ↔ IsZero a := by simp +contextual [rel_iff, IsZero, iff_def]
lemma rel_le_zero : Rel (· ≤ ·) a 0 ↔ IsZero a := by simp +contextual [rel_iff, IsZero, iff_def]
lemma rel_eq_zero : Rel (· = ·) a 0 ↔ IsZero a := by simp +contextual [rel_iff, IsZero, iff_def]
lemma rel_zero_eq : Rel (· = ·) 0 a ↔ IsZero a := by
  simp +contextual [rel_iff, IsZero, iff_def, eq_comm]


attribute [enat_grind_canonize] rel_coe_coe rel_ofNat_coe rel_coe_ofNat rel_one_ofNat rel_ofNat_one
rel_one_coe rel_coe_one rel_zero_le rel_zero_lt rel_one_le rel_zero_ne rel_ne_zero rel_lt_zero
rel_lt_one rel_le_zero rel_eq_zero rel_zero_eq not_rel_top_left not_rel_top_right

-- Optimizations


lemma rel_top_mul_left {a b : ℕ∞} : Rel r (⊤ * a) b ↔ IsZero a ∧ Rel r 0 b := by
  obtain rfl | (hne : ¬ IsZero a) := eq_or_ne a 0
  · simp [isZero_zero]
  simp [top_mul hne, hne, rel_iff]

lemma rel_top_mul_right {a b : ℕ∞} : Rel r a (⊤ * b) ↔ IsZero b ∧ Rel r a 0 := by
  rw [← rel_swap, rel_top_mul_left, rel_swap]

lemma rel_mul_top_left {a b : ℕ∞} : Rel r (a * ⊤) b ↔ IsZero a ∧ Rel r 0 b := by
  rw [mul_comm, rel_top_mul_left]

lemma rel_mul_top_right {a b : ℕ∞} : Rel r a (b * ⊤) ↔ IsZero b ∧ Rel r a 0 := by
  rw [mul_comm, rel_top_mul_right]

lemma rel_top_sub_left {a b : ℕ∞} : Rel r (⊤ - a) b ↔ ¬ IsNat a ∧ Rel r 0 b := by
  cases a with
  | top => simp [not_isNat_top]
  | coe a => simp [rel_iff, isNat_iff]

lemma rel_top_sub_right : Rel r a (⊤ - b) ↔ ¬ IsNat b ∧ Rel r a 0 := by
  rw [← rel_swap, rel_top_sub_left, rel_swap]

lemma rel_le_add_self : Rel (· ≤ ·) b (a + b) ↔ IsNat a ∧ IsNat b := by
  simp [rel_le_iff, isNat_iff]

lemma rel_le_self_add : Rel (· ≤ ·) a (a + b) ↔ IsNat a ∧ IsNat b := by
  rw [add_comm, rel_le_add_self, and_comm]

lemma rel_le_add_right : Rel (· ≤ ·) (a + b) a ↔ IsNat a ∧ IsZero b := by
  grind [rel_le_iff, ENat.add_le_left_iff, isNat_iff, ENat.add_eq_top, IsZero, zero_ne_top]

lemma rel_le_add_left : Rel (· ≤ ·) (a + b) b ↔ IsZero a ∧ IsNat b := by
  rw [add_comm, rel_le_add_right, and_comm]

lemma rel_eq_add_right : Rel (· = ·) a (a + b) ↔ IsNat a ∧ IsZero b := by
  grind [rel_eq_iff, ENat.add_eq_left_iff, isNat_iff, ENat.add_eq_top, IsZero, zero_ne_top]

lemma rel_eq_add_left : Rel (· = ·) a (b + a) ↔ IsNat a ∧ IsZero b := by
  rw [add_comm, rel_eq_add_right]

lemma rel_add_right_eq : Rel (· = ·) (a + b) a ↔ IsNat a ∧ IsZero b := by
  rw [add_comm, rel_eq_iff, and_comm (a := IsNat ..), eq_comm, ← rel_eq_iff, rel_eq_add_left]

lemma rel_add_left_eq : Rel (· = ·) (a + b) b ↔ IsZero a ∧ IsNat b := by
  rw [add_comm, rel_add_right_eq, and_comm]

lemma rel_add_eq_add_left : Rel (· = ·) (a + b) (a + c) ↔ Rel (· = ·) b c ∧ IsNat a := by
  grind [rel_eq_iff, ENat.add_eq_add_left_iff, isNat_iff, ENat.add_eq_top]

lemma rel_add_eq_add_right : Rel (· = ·) (a + c) (b + c) ↔ Rel (· = ·) a b ∧ IsNat c := by
  rw [add_comm a, add_comm b, rel_add_eq_add_left]

lemma rel_add_le_add_left : Rel (· ≤ ·) (a + b) (a + c) ↔ Rel (· ≤ ·) b c ∧ IsNat a := by
  grind [rel_le_iff, ENat.add_le_add_left_iff, isNat_iff, ENat.add_eq_top]

lemma rel_add_le_add_right : Rel (· ≤ ·) (a + c) (b + c) ↔ Rel (· ≤ ·) a b ∧ IsNat c := by
  rw [add_comm a, add_comm b, rel_add_le_add_left]

lemma rel_add_lt_add_left : Rel (· < ·) (a + b) (a + c) ↔ Rel (· < ·) b c ∧ IsNat a := by
  grind [rel_lt_iff, ENat.add_lt_add_left_iff, isNat_iff, ENat.add_eq_top]

lemma rel_add_lt_add_right : Rel (· < ·) (a + c) (b + c) ↔ Rel (· < ·) a b ∧ IsNat c := by
  rw [add_comm a, add_comm b, rel_add_lt_add_left]


attribute [enat_grind_canonize] rel_top_mul_left rel_top_mul_right rel_mul_top_left
rel_mul_top_right rel_top_sub_left rel_top_sub_right not_rel_top_left not_rel_top_right
rel_le_add_self rel_le_self_add rel_le_add_right rel_le_add_left rel_eq_add_right rel_eq_add_left
rel_add_right_eq rel_add_left_eq rel_add_eq_add_left rel_add_eq_add_right rel_add_le_add_left
rel_add_le_add_right rel_add_lt_add_left rel_add_lt_add_right

-- grind lemmas for `Rel` + `IsZero`. I don't think we need these for `Rel` + `IsNat`,
-- since `Rel` is always given in conjunction with explicit `IsNat` proofs.
/-- If `2 ≤ a`, and `a ≤ b`, then -/
@[grind.] lemma Rel.not_isZero_of_ofNat_le {a : ℕ} [a.AtLeastTwo] (h : Rel (· ≤ ·) ofNat(a) b) :
    ¬ IsZero b := by
  rintro rfl
  simp [rel_le_zero, not_isZero_ofNat] at h

@[grind.] lemma Rel.not_isZero_of_lt (h : Rel (· < ·) a b) : ¬ IsZero b := by
  rintro rfl
  simp [rel_lt_zero] at h

@[grind.] lemma Rel.isZero_of_le (h : Rel (· ≤ ·) a b) (hb : IsZero b) : IsZero a :=
  rel_le_zero.1 <| hb ▸ h

-- Canonizing lemmas for `Rel`. These take (in)equalities in `ℕ∞` and convert them to
-- statements in terms of `Rel` and `IsNat`/`IsZero`.
protected theorem le_iff : a ≤ b ↔ ¬ IsNat b ∨ Rel (· ≤ ·) a b ∧ IsNat a ∧ IsNat b := by
  cases a with cases b with simp [IsNat, rel_coe_coe]

protected theorem eq_iff : a = b ↔ ¬ IsNat a ∧ ¬ IsNat b ∨ Rel (· = ·) a b ∧ IsNat a ∧ IsNat b := by
  cases a with cases b with simp [IsNat, rel_coe_coe]

protected theorem lt_iff : a < b ↔ (IsNat a ∧ ¬ IsNat b) ∨ Rel (· < ·) a b ∧ IsNat a ∧ IsNat b := by
  cases a with cases b with simp [IsNat, rel_coe_coe]

protected theorem ne_iff :
    a ≠ b ↔ (Rel (· ≠ ·) a b ∧ IsNat a ∧ IsNat b) ∨ (IsNat a ↔ ¬ IsNat b) := by
  cases a with cases b with simp [IsNat, rel_coe_coe, eq_comm]

attribute [enat_grind_canonize] ENat.Grind.le_iff ENat.Grind.lt_iff ENat.Grind.eq_iff
  ENat.Grind.ne_iff

-- Logic lemmas for canonization
attribute [enat_grind_canonize] le_top not_false or_false false_or false_and and_false and_true
  true_and not_false_iff not_true true_or not_not imp_false true_imp_iff false_imp_iff true_iff
  false_iff iff_false iff_true

-- These next four lemmas are workarounds for the `norm_cast` + `grind` bug.
lemma ofNat_mul_cast (a : ℕ) (b : ℕ) [a.AtLeastTwo] : ofNat(a) * (b : ℕ∞) = a * b := rfl
lemma mul_cast_ofNat (a : ℕ) (b : ℕ) [b.AtLeastTwo] : (a : ℕ∞) * ofNat(b) = a * b := rfl
lemma ofNat_add_cast (a : ℕ) (b : ℕ) [a.AtLeastTwo] : ofNat(a) + (b : ℕ∞) = a + b := rfl
lemma add_cast_ofNat (a : ℕ) (b : ℕ) [b.AtLeastTwo] : (a : ℕ∞) + ofNat(b) = a + b := rfl

attribute [enat_grind_canonize] ofNat_mul_cast mul_cast_ofNat ofNat_add_cast add_cast_ofNat

-- lemma to simplify once a variable is known to be infinite.
lemma eq_top_of_not_isNat (h : ¬ IsNat a) : a = ⊤ := by
  simpa [isNat_iff] using h


macro "preprocess" : tactic => `(tactic | simp only [enat_grind_presimp] at *)

/-- `process` applies `enat_to_nat_top` lemmas everywhere to canonicalize `ℕ∞` equalities and
inequalities into certain boolean combinations of `IsNat`, `IsZero`, and `Rel`.
It should use `norm_cast` to simplify coercions, but there is currently a bug with `grind`.  -/
macro "process" : tactic => `(tactic| focus (
    (try simp only [enat_grind_canonize, ← Nat.cast_add, ← Nat.cast_mul] at *)
  )
)

end ENat.Grind

open ENat.Grind

/-
Tactic pseudocode :

`try preprocess`
repeat :
  `process`
  try to resolve the goal by `grind`
  if goal is all `Nat`, try to resolve by `omega`.
  repeat :
    let `a` be an `ENat` in the context, in the goal if possible.
    try to show `IsNat a`/`IsZero a`/`¬ IsNat a` by `grind`.
    If successful, then substitute out `a`.
  if above loop is unsuccessful, pick an `ENat` `a` in the context, in the goal if possible.
  case split on `IsNat a`.
-/

section Examples
variable {a b c d e f : ℕ∞}

example (h1 : a * b = c) (h2 : c < d) (h3 : b ≠ 0) : a ≠ ⊤ := by
  process
  grind

example (hb : a < b) : b ≠ 0 := by
  process
  grind

example (h1 : a + 2 ≤ a) : a = ⊤ := by
  -- without preprocessing, this will require a case split on a.
  process
  grind

example (h1 : a + 2 ≤ a) : a = ⊤ := by
  process
  -- this is the case split.
  by_cases ha : IsNat a
  · obtain ⟨a, rfl⟩ := ha
    process
  grind

example (h1 : a + b ≤ a + c) (h2 : d + c ≤ d) (ha : a < ⊤) (hd : d ≠ ⊤) : b = 0 := by
  process
  obtain rfl : IsZero c := by grind
  process
  grind

example (h1 : a + b + c = c + a) (h2 : 1 ≤ b) : a = ⊤ ∨ c = ⊤ := by
  process
  cases a with
  | top => process
  | coe a =>
  process
  cases c with
  | top => process
  | coe c =>
  process
  cases b with
  | top => process
  | coe b =>
  process
  omega

example (h1 : a + b * c ≠ ⊤) (hc : 1 ≤ c) : b ≠ ⊤ := by
  process
  grind

example (h : a + b = 0) : a ≤ b := by
  process
  obtain rfl : IsZero a := by grind
  process
  grind

example (h1 : a * b = c) (h2 : 2 ≤ a) (h3 : 3 ≤ b) (h4 : c < 4 * a + 5 * b) : 6 ≤ c := by
  try preprocess -- does nothing
  process
  have ha : IsNat a := by grind
  have hb : IsNat b := by grind
  have hc : IsNat c := by grind
  obtain ⟨a,rfl⟩ := ha
  obtain ⟨b,rfl⟩ := hb
  obtain ⟨c,rfl⟩ := hc
  process
  -- nice `Nat` goal now. Unfortunately `omega` can't handle it.
  exact h1 ▸ Nat.mul_le_mul h2 h3

-- The same example with branching.
example (h1 : a * b = c) (h2 : 2 ≤ a) (h3 : 3 ≤ b) (h4 : c < 4 * a + 5 * b) : 6 ≤ c := by
  process
  cases a with
  | top => process; grind
  | coe a =>
  process
  cases b with
  | top => process; grind
  | coe b =>
  process
  cases c with
  | top => process
  | coe c =>
  process
  -- Nat goal
  exact h1 ▸ Nat.mul_le_mul h2 h3


end Examples
