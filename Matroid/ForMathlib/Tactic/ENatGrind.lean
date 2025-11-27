import Mathlib.Data.ENat.Basic
import Matroid.ForMathlib.Tactic.ENatGrindPrelude

set_option linter.style.longLine false

namespace ENat.Grind

variable {a b : ℕ∞}

/- These lemmas look for low-hanging fruit in the existing `ENat` (in)equalities to deduce
logical information about variables being `⊤` or `0`. For instance, `a + b ≤ a + c` will
be simplified to `b ≤ c ∨ a = ⊤`. Arguably many of these could be `@[simp]` lemmas unconditionally.

This is run as a preprocessing step; after the loop in the tactic has started running,
the hypotheses will not be in a form that these lemmas can see, so there is no point trying
them again. Rephrasing them in a form that they can be applied in the middle of the run
would probably be a modest speedup, but what they are achieving will be cleaned up by `omega`
and brute force anyway. -/
attribute [enat_grind_presimp] ENat.add_le_right_iff ENat.add_le_left_iff ENat.add_eq_right_iff
  ENat.add_eq_left_iff ENat.eq_left_add_iff ENat.eq_right_add_iff ENat.lt_add_left_iff
  ENat.lt_add_right_iff ENat.add_eq_add_left_iff ENat.add_eq_add_right_iff
  ENat.add_le_add_left_iff ENat.add_le_add_right_iff ENat.add_lt_add_left_iff
  ENat.add_lt_add_right_iff self_le_add_right self_le_add_left

/- After the preprocessing step above,
the idea is that we take every `ℕ∞` (inequality) `h`, and rephrase it in the form
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
a variable, we can substitute it out and repeat. The standard use case is where the goal is
trivial in all cases except where every variable is `Nat`; if this is the case, then
this process should end with a purely `Nat` goal. -/

/-- `a : ℕ∞` is finite. -/
def IsNat (a : ℕ∞) := a ≠ ⊤

/-- `a : ℕ∞` is zero. -/
def IsZero (a : ℕ∞) := a = 0

-- simp lemmas
lemma isNat_add_iff : IsNat (a + b) ↔ IsNat a ∧ IsNat b := by
  simp [IsNat, ENat.add_eq_top]
lemma isNat_mul_iff : IsNat (a * b) ↔ (IsNat a ∧ IsNat b) ∨ IsZero a ∨ IsZero b := by
  grind [IsNat, ENat.mul_eq_top_iff, IsZero, ENat.top_ne_zero]
lemma isNat_sub_iff : IsNat (a - b) ↔ IsNat a ∨ ¬ IsNat b := by
  grind [IsNat, sub_eq_top_iff]
lemma isNat_zero : IsNat 0 := zero_ne_top
lemma isNat_one : IsNat 1 := one_ne_top
lemma isNat_ofNat (a : ℕ) [a.AtLeastTwo] : IsNat ofNat(a) := by simp [IsNat]
lemma isNat_coe {a : ℕ} : IsNat a := by simp [IsNat]
lemma not_isNat_top : ¬ IsNat ⊤ := by simp [IsNat]
lemma isZero_zero : IsZero 0 := rfl
lemma not_isZero_one : ¬ IsZero 1 := by simp [IsZero]
lemma not_isZero_ofNat {a : ℕ} [a.AtLeastTwo] : ¬ IsZero ofNat(a) := by simp [IsZero]
lemma isZero_coe {a : ℕ} : IsZero a ↔ a = 0 := by simp [IsZero]

attribute [enat_grind_canonize] isNat_zero isNat_one isNat_ofNat isNat_coe not_isNat_top isZero_zero
isNat_add_iff isNat_mul_iff isNat_sub_iff not_isZero_one not_isZero_ofNat isZero_coe

-- grind lemmaa
@[grind.]
lemma IsZero.isNat (h : IsZero a) : IsNat a := by obtain rfl := h; simp [IsNat]

/-- for a relation `r` on `ℕ`, `Rel r` is a wrapper for the lift of `r` to `ℕ∞`.
It will appear only in conjunction with proofs that `a` and `b` are not `⊤`. -/
@[mk_iff]
structure Rel (r : ℕ → ℕ → Prop) (a b : ℕ∞) : Prop where
  ne_left : a ≠ ⊤
  ne_right : b ≠ ⊤
  rel : r a.toNat b.toNat

-- simp lemmas for the interaction of `Rel` with coercions, numerals, zeroes and ones.
lemma rel_coe_coe {r} {a b : ℕ} : Rel r a b ↔ r a b := by simp [rel_iff]
lemma rel_ofNat_coe {r} {a b : ℕ} [a.AtLeastTwo] : Rel r ofNat(a) b ↔ r a b := by simp [rel_iff]
lemma rel_coe_ofNat {r} {a b : ℕ} [b.AtLeastTwo] : Rel r a ofNat(b) ↔ r a b := by simp [rel_iff]
lemma rel_ofNat_ofNat {r} {a b : ℕ} [a.AtLeastTwo] [b.AtLeastTwo] :
    Rel r ofNat(a) ofNat(b) ↔ r a b := by simp [rel_iff]
lemma rel_one_ofNat {r} {a : ℕ} [a.AtLeastTwo] : Rel r 1 ofNat(a) ↔ r 1 a := by simp [rel_iff]
lemma rel_ofNat_one {r} {a : ℕ} [a.AtLeastTwo] : Rel r 1 ofNat(a) ↔ r 1 a := by simp [rel_iff]
lemma rel_one_coe {r} {a : ℕ} : Rel r 1 a ↔ r 1 a := by simp [rel_iff]
lemma rel_coe_one {r} {a : ℕ} : Rel r 1 a ↔ r 1 a := by simp [rel_iff]
lemma rel_zero_le {a : ℕ∞} : Rel (· ≤ ·) 0 a ↔ IsNat a := by simp [IsNat, rel_iff]
lemma rel_one_le {a : ℕ∞} : Rel (· ≤ ·) 1 a ↔ ¬ IsZero a ∧ IsNat a := by
  simp [rel_iff, IsZero, Nat.one_le_iff_ne_zero, IsNat]
lemma rel_zero_lt {a : ℕ} : Rel (· < ·) 0 a ↔ ¬ IsZero a ∧ IsNat a := by
  simp [rel_iff, IsZero, Nat.pos_iff_ne_zero, IsNat]
lemma rel_zero_ne {a : ℕ∞} : Rel (· ≠ ·) 0 a ↔ ¬ IsZero a ∧ IsNat a :=  by
  simp [rel_iff, IsZero, eq_comm, IsNat]
lemma rel_ne_zero {a : ℕ∞} : Rel (· ≠ ·) a 0 ↔ ¬ IsZero a ∧ IsNat a := by
  simp [rel_iff, IsZero, IsNat]
lemma rel_lt_zero {a : ℕ∞} : ¬ Rel (· < ·) a 0 := by simp [rel_iff]
lemma rel_le_zero {a : ℕ∞} : Rel (· ≤ ·) a 0 ↔ IsZero a := by
  simp +contextual [rel_iff, IsZero, iff_def]
lemma rel_eq_zero {a : ℕ∞} : Rel (· = ·) a 0 ↔ IsZero a := by
  simp +contextual [rel_iff, IsZero, iff_def]
lemma rel_zero_eq {a : ℕ∞} : Rel (· = ·) 0 a ↔ IsZero a := by
  simp +contextual [rel_iff, IsZero, iff_def, eq_comm]

attribute [enat_grind_canonize] rel_coe_coe rel_ofNat_coe rel_coe_ofNat rel_one_ofNat rel_ofNat_one
rel_one_coe rel_coe_one rel_zero_le rel_zero_lt rel_zero_ne rel_ne_zero rel_lt_zero rel_le_zero
rel_eq_zero rel_zero_eq

-- grind lemmas for `Rel`
/-- If `2 ≤ a`, and `a ≤ b`, then -/
@[grind.] lemma Rel.not_isZero_of_ofNat_le {a : ℕ} [a.AtLeastTwo] (h : Rel (· ≤ ·) ofNat(a) b) :
    ¬ IsZero b := by
  rintro rfl
  simp [rel_le_zero, not_isZero_ofNat] at h

@[grind.] lemma Rel.not_isZero_of_lt (h : Rel (· < ·) a b) : ¬ IsZero b := by
  rintro rfl
  simp [rel_lt_zero] at h

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

-- lemmas to simplify once a variable is known to be finite/infinite.
lemma IsNat.exists_eq_coe (h : IsNat a) : ∃ a₀ : ℕ, a = a₀ := by
  lift a to ℕ using h
  simp

lemma eq_top_of_not_isNat (h : ¬ IsNat a) : a = ⊤ := by
  simpa [IsNat] using h


macro "preprocess" : tactic => `(tactic | simp only [enat_grind_presimp] at *)

/-- `process` applies `enat_to_nat_top` lemmas everywhere to canonicalize `ℕ∞` equalities and
inequalities into boolean combinations of `IsNat`, `IsZero`, and `Rel`.
It should use `norm_cast` to simplify coercions, but there is currently a bug with `grind`.  -/
macro "process" : tactic => `(tactic| focus (
    (try simp only [enat_grind_canonize, ← Nat.cast_add, ← Nat.cast_mul] at *)
  )
)

end ENat.Grind

open ENat.Grind

section Examples
variable {a b c d e f : ℕ∞}

example (h1 : a * b = c) (h2 : c < d) (h3 : b ≠ 0) : a ≠ ⊤ := by
  process
  grind

example (hb : a < b) : b ≠ 0 := by
  process
  grind

example (h1 : a + 2 ≤ a) : a = ⊤ := by
  preprocess
  -- without preprocessing, this will require a case split on a.
  process
  grind

example (h1 : a + 2 ≤ a) : a = ⊤ := by
  process
  -- this is the case split.
  by_cases ha : IsNat a
  · obtain ⟨a, rfl⟩ := ha.exists_eq_coe
    process
    omega
  grind

example (h1 : a + b ≤ a + c) (h2 : d + c ≤ d) (ha : a < ⊤) (hd : d ≠ ⊤) : b = 0 := by
  preprocess
  process
  obtain rfl : IsZero c := by grind
  process
  grind

example (h1 : a * b = c) (h2 : 2 ≤ a) (h3 : 3 ≤ b) (h4 : c < 4 * a + 5 * b) : 6 ≤ c := by
  try preprocess -- does nothing
  process
  have ha : IsNat a := by grind
  have hb : IsNat b := by grind
  have hc : IsNat c := by grind
  obtain ⟨a,rfl⟩ := ha.exists_eq_coe
  obtain ⟨b,rfl⟩ := hb.exists_eq_coe
  obtain ⟨c,rfl⟩ := hc.exists_eq_coe
  process
  -- nice `Nat` goal now. Unfortunately `omega` can't handle it.
  exact h1 ▸ Nat.mul_le_mul h2 h3

example (h1 : a + b * c ≠ ⊤) : a ≠ ⊤ := by
  process
  grind

end Examples
