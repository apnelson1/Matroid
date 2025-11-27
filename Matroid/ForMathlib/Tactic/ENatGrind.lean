import Mathlib.Data.ENat.Basic
import Matroid.ForMathlib.Tactic.ENatGrindAttr

set_option linter.style.longLine false
namespace ENat

section ENat

variable {a b : ℕ∞}

-- Some `ENat` lemmas that should exist anyway.

protected theorem top_mul_eq_ite (a : ℕ∞) : ⊤ * a = if a = 0 then 0 else ⊤ := by
  split_ifs with h
  · simp [h]
  simp [top_mul h]

protected theorem mul_top_eq_ite (a : ℕ∞) : a * ⊤ = if a = 0 then 0 else ⊤ := by
  rw [mul_comm, ENat.top_mul_eq_ite]

protected theorem mul_eq_top_iff : a * b = ⊤ ↔ (a = ⊤ ∧ b ≠ 0) ∨ (a ≠ 0 ∧ b = ⊤) := by
  cases a with
  | top => simp +contextual [ENat.top_mul_eq_ite]
  | coe a =>
  cases b with
  | top => simp +contextual [ENat.mul_top_eq_ite]
  | coe b => simp only [coe_ne_top, ne_eq, Nat.cast_eq_zero, false_and, and_false, or_self,
    ← coe_mul]

-- `WithTop.add_eq_top` doesn't work with simp.
protected theorem add_eq_top : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ := WithTop.add_eq_top

@[simp]
protected theorem add_one_eq_top : a + 1 = ⊤ ↔ a = ⊤ := by
  simp [ENat.add_eq_top]

-- The lemmas below can be used in a first pass to rephrase some
-- low-hanging fruit in terms of zero/top equalities.

protected theorem add_le_left_iff : a + b ≤ a ↔ a = ⊤ ∨ b = 0 := by
  cases a with
  | top => simp
  | coe a => cases b with
    | top => simp
    | coe b => norm_cast; simp

protected theorem add_le_right_iff : a + b ≤ b ↔ a = 0 ∨ b = ⊤ := by
  rw [add_comm, ENat.add_le_left_iff, or_comm]

protected theorem add_eq_left_iff : a + b = a ↔ a = ⊤ ∨ b = 0 := by
  rw [← ENat.add_le_left_iff, le_antisymm_iff, and_iff_left (self_le_add_right ..)]

protected theorem add_eq_right_iff : a + b = b ↔ a = 0 ∨ b = ⊤ := by
  rw [← add_comm, ENat.add_eq_left_iff, or_comm]

protected theorem eq_left_add_iff : a = a + b ↔ a = ⊤ ∨ b = 0 := by
  rw [eq_comm, ENat.add_eq_left_iff]

protected theorem eq_right_add_iff : b = a + b ↔ b = ⊤ ∨ a = 0 := by
  rw [eq_comm, ENat.add_eq_right_iff, or_comm]

protected theorem lt_add_left_iff : a < a + b ↔ a ≠ ⊤ ∧ b ≠ 0 := by
  simp [lt_iff_le_and_ne, ENat.eq_left_add_iff]

protected theorem lt_add_right_iff : a < b + a ↔ a ≠ ⊤ ∧ b ≠ 0 := by
  rw [add_comm, ENat.lt_add_left_iff, and_comm]

attribute [enat_grind_presimp] ENat.add_le_right_iff ENat.add_le_left_iff ENat.add_eq_right_iff
  ENat.add_eq_left_iff ENat.eq_left_add_iff ENat.eq_right_add_iff ENat.lt_add_left_iff
  ENat.lt_add_right_iff

end ENat

namespace Grind

variable {a b : ℕ∞}

/-
The idea is that we take every `ℕ∞` (inequality) `h`, and rephrase it in the form
`h₀ ∨ h₁`, where `h₀` is the statement that `h` holds and all relevant terms are finite,
and `h₁` is some boolean combination of terms of the form `x ≠ ⊤` and `x = 0`.

This
-/

--the predicates for `ℕ∞` corresponding to the properties of being finite, and being zero.
/-- `a : ℕ∞` is finite. -/
def IsNat (a : ℕ∞) := a ≠ ⊤

/-- `a : ℕ∞` is zero. -/
def IsZero (a : ℕ∞) := a = 0

lemma isNat_add_iff : IsNat (a + b) ↔ IsNat a ∧ IsNat b := by
  simp [IsNat, ENat.add_eq_top]

lemma isNat_mul_iff : IsNat (a * b) ↔ (IsNat a ∧ IsNat b) ∨ IsZero a ∨ IsZero b := by
  grind [IsNat, ENat.mul_eq_top_iff, IsZero, ENat.top_ne_zero]

lemma isNat_zero : IsNat 0 := zero_ne_top

lemma isNat_one : IsNat 1 := one_ne_top

lemma isNat_ofNat (a : ℕ) [a.AtLeastTwo] : IsNat ofNat(a) := by
  simp [IsNat]

lemma isNat_coe {a : ℕ} : IsNat a := by
  simp [IsNat]

lemma not_isNat_top : ¬ IsNat ⊤ := by
  simp [IsNat]

lemma isZero_zero : IsZero 0 := rfl

lemma IsZero.isNat (h : IsZero a) : IsNat a := by
  obtain rfl := h
  simp [IsNat]

lemma not_isZero_one : ¬ IsZero 1 := by
  simp [IsZero]

lemma not_isZero_ofNat {a : ℕ} [a.AtLeastTwo] : ¬ IsZero ofNat(a) := by
  simp [IsZero]

lemma isZero_coe {a : ℕ} : IsZero a ↔ a = 0 := by
  simp [IsZero]

def NatCmp (r : ℕ → ℕ → Prop) (a b : ℕ∞) := ∃ a₀ b₀, r a₀ b₀ ∧ a₀ = a ∧ b₀ = b

lemma NatCmp.isNat_left {r} (h : NatCmp r a b) : IsNat a := by
  obtain ⟨a₀, -, -, rfl, -⟩ := h
  simp [IsNat]

lemma NatCmp.isNat_right {r} (h : NatCmp r a b) : IsNat b := by
  obtain ⟨-, b₀, -, -, rfl⟩ := h
  simp [IsNat]

lemma NatCmp.ne_left {r} (h : NatCmp r a b) : a ≠ ⊤ := by
  obtain ⟨a₀, -, -, rfl, -⟩ := h
  simp

lemma NatCmp.ne_right {r} (h : NatCmp r a b) : b ≠ ⊤ := by
  obtain ⟨-, b₀, -, -, rfl⟩ := h
  simp

lemma not_natCmp_left {r} : ¬ NatCmp r ⊤ a :=
  fun h ↦ h.ne_left rfl

lemma not_natCmp_right {r} : ¬ NatCmp r a ⊤ :=
  fun h ↦ h.ne_right rfl

lemma natCmp_coe_coe {r} {a b : ℕ} : NatCmp r a b ↔ r a b := by
  simp [NatCmp]

lemma natCmp_ofNat {r} {a b : ℕ} [a.AtLeastTwo] [b.AtLeastTwo] :
    NatCmp r ofNat(a) ofNat(b) ↔ r a b :=
  ⟨fun ⟨a₀, b₀, hr, ha, hb⟩ ↦ by rwa [← coe_inj.1 ha, ← coe_inj.1 hb],
    fun hr ↦ ⟨a, b, hr, rfl, rfl⟩⟩

lemma natCmp_ofNat_coe {r} {a b : ℕ} [a.AtLeastTwo] : NatCmp r ofNat(a) b ↔ r a b :=
  ⟨fun ⟨a₀, b₀, hr, ha, hb⟩ ↦ by rwa [← coe_inj.1 ha, ← coe_inj.1 hb],
    fun hr ↦ ⟨a, b, hr, rfl, rfl⟩⟩

lemma natCmp_coe_ofNat {r} {a b : ℕ} [b.AtLeastTwo] : NatCmp r a ofNat(b) ↔ r a b :=
  ⟨fun ⟨a₀, b₀, hr, ha, hb⟩ ↦ by rwa [← coe_inj.1 ha, ← coe_inj.1 hb],
    fun hr ↦ ⟨a, b, hr, rfl, rfl⟩⟩

lemma natCmp_one_coe {r} {a : ℕ} : NatCmp r 1 a ↔ r 1 a := by
  simp [NatCmp]

lemma natCmp_zero_coe {r} {a : ℕ} : NatCmp r 0 a ↔ r 0 a := by
  simp [NatCmp]

lemma natCmp_coe_one {r} {a : ℕ} : NatCmp r a 1 ↔ r a 1 := by
  simp [NatCmp]

lemma natCmp_coe_zero {r} {a : ℕ} : NatCmp r a 0 ↔ r a 0 := by
  simp [NatCmp]

lemma natCmp_eq_zero : NatCmp (· = ·) a 0 ↔ IsZero a := by
  cases a with simp +contextual [NatCmp, IsZero]

lemma natCmp_zero_eq : NatCmp (· = ·) 0 a ↔ IsZero a := by
  cases a with simp +contextual [NatCmp, IsZero, eq_comm]

lemma natCmp_zero_le : NatCmp (· ≤ ·) 0 a ↔ IsNat a := by
  cases a with simp +contextual [NatCmp, IsNat]

lemma natCmp_one_le : NatCmp (· ≤ ·) 1 a ↔ IsNat a ∧ ¬ IsZero a := by
  cases a with simp [NatCmp, IsNat, IsZero, Nat.one_le_iff_ne_zero]

lemma natCmp_zero_lt : NatCmp (· < ·) 0 a ↔ IsNat a ∧ ¬ IsZero a := by
  cases a with simp [NatCmp, IsNat, IsZero, Nat.pos_iff_ne_zero]

lemma natCmp_le_zero : NatCmp (· ≤ ·) a 0 ↔ IsZero a := by
  cases a with simp [NatCmp, IsZero, eq_comm]

lemma natCmp_lt_one : NatCmp (· < ·) a 1 ↔ IsZero a := by
  cases a with simp [NatCmp, IsZero, eq_comm]

lemma natCmp_ne_zero : NatCmp (· ≠ ·) a 0 ↔ ¬ IsZero a ∧ IsNat a := by
  cases a with simp [NatCmp, IsNat, IsZero]

lemma natCmp_zero_ne : NatCmp (· ≠ ·) 0 a ↔ ¬ IsZero a ∧ IsNat a := by
  cases a with simp [NatCmp, IsNat, IsZero, eq_comm]

lemma NatCmp.not_isZero_of_ofNat_le {a : ℕ} [a.AtLeastTwo] (h : NatCmp (· ≤ ·) ofNat(a) b) :
    ¬ IsZero b := by
  cases b with
  | top => simp [IsZero]
  | coe b =>
    simp only [IsZero, Nat.cast_eq_zero]
    rintro rfl
    simp [NatCmp] at h

lemma NatCmp.not_isZero_of_lt (h : NatCmp (· < ·) a b) : ¬ IsZero b := by
  rintro rfl
  simp [NatCmp] at h

@[enat_grind_canonize]
protected theorem le_iff :
    a ≤ b ↔ ¬ IsNat b ∨ NatCmp (· ≤ ·) a b ∧ IsNat a ∧ IsNat b := by
  cases a with cases b with simp [NatCmp, IsNat]

@[enat_grind_canonize]
protected theorem eq_iff :
    a = b ↔ ¬ IsNat a ∧ ¬ IsNat b ∨ NatCmp (· = ·) a b ∧ IsNat a ∧ IsNat b := by
  cases a with cases b with simp [NatCmp, IsNat]

@[enat_grind_canonize]
protected theorem lt_iff :
    a < b ↔ (IsNat a ∧ ¬ IsNat b) ∨ NatCmp (· < ·) a b ∧ IsNat a ∧ IsNat b := by
  cases a with cases b with simp [NatCmp, IsNat]

@[enat_grind_canonize]
protected theorem ne_iff : a ≠ b ↔ (IsNat a ∧ ¬ IsNat b) ∨
    (IsNat b ∧ ¬ IsNat a) ∨ NatCmp (· ≠ ·) a b := by
  cases a with cases b with simp [NatCmp, IsNat]

-- These next four lemmas are workarounds for the norm_cast bug.
@[enat_grind_canonize]
lemma ofNat_mul_cast (a : ℕ) (b : ℕ) [a.AtLeastTwo] : ofNat(a) * (b : ℕ∞) = a * b := by
  rfl

@[enat_grind_canonize]
lemma mul_cast_ofNat (a : ℕ) (b : ℕ) [b.AtLeastTwo] : (a : ℕ∞) * ofNat(b) = a * b := by
  rfl

@[enat_grind_canonize]
lemma ofNat_add_cast (a : ℕ) (b : ℕ) [a.AtLeastTwo] : ofNat(a) + (b : ℕ∞) = a + b := by
  rfl

@[enat_grind_canonize]
lemma add_cast_ofNat (a : ℕ) (b : ℕ) [b.AtLeastTwo] : (a : ℕ∞) + ofNat(b) = a + b := by
  rfl

attribute [grind.] NatCmp.ne_left NatCmp.ne_right not_natCmp_left not_natCmp_right IsZero.isNat
  NatCmp.isNat_left NatCmp.isNat_right NatCmp.not_isZero_of_ofNat_le NatCmp.not_isZero_of_lt

attribute [enat_grind_canonize] isNat_add_iff isNat_mul_iff isNat_zero isNat_one
  isNat_ofNat isNat_coe not_isNat_top isZero_zero not_isZero_one not_isZero_ofNat isZero_coe
  natCmp_ofNat natCmp_coe_coe natCmp_coe_coe natCmp_zero_lt natCmp_one_le natCmp_lt_one
  natCmp_le_zero natCmp_one_le natCmp_zero_le natCmp_zero_ne natCmp_ne_zero natCmp_eq_zero
  natCmp_zero_eq not_natCmp_left not_natCmp_right natCmp_one_coe natCmp_zero_coe
  natCmp_coe_one natCmp_coe_zero natCmp_coe_ofNat natCmp_ofNat_coe

attribute [enat_grind_canonize] le_top not_false or_false false_or false_and and_false and_true
  true_and not_false_iff not_true true_or not_not


lemma IsNat.exists_eq_coe (h :IsNat a) : ∃ a₀ : ℕ, a = a₀ := by
  lift a to ℕ using h
  simp

lemma eq_top_of_not_isNat (h : ¬ IsNat a) : a = ⊤ := by
  simpa [IsNat] using h



-- protected theorem coe_mul_symm (a b : ℕ) : (a : ℕ∞) * (b : ℕ∞) =

-- attribute [grind.]
--  ENat.Grind.eqTop_top ENat.Grind.not_eqTop_cast ENat.Grind.not_eqTop_one
--     ENat.Grind.not_eqTop_zero ENat.Grind.eqTop_mul
-- lemma natEq_expand (a b : ℕ∞) : NatEq a b ↔ NatEq a b

-- variable {a b d e f g : ℕ∞}


macro "preprocess" : tactic => `(tactic | simp only [enat_grind_presimp] at *)

/-- `process` applies `enat_to_nat_top` lemmas everywhere to canonicalize `ℕ∞` equalities and
inequalities into boolean combinations of `EqTop` and `NatLE`/`NatLT`/`NatNe`/`NatEq`.
It will also convert `ENat` literals into coerced `Nat` literals,
and use `norm_cast` to simplify coercions. -/
macro "process" : tactic => `(tactic| focus (
    -- (try simp only [← Nat.cast_add, ← Nat.cast_mul] at *);
    (try simp only [enat_grind_canonize, ← Nat.cast_add, ← Nat.cast_mul] at *)
  )
)

end Grind


open Grind

section Examples
variable {a b c d e f : ℕ∞}



/-- The hypotheses imply that `a` is finite. -/
example (h1 : a * b = c) (h2 : c < d) (h3 : b ≠ 0) : a ≠ ⊤ := by
  process
  grind

example (hb : 2 ≤ b) : b ≠ 0 := by
  process
  grind

example (h1 : a * b = c) (h2 : 2 ≤ a) (h3 : 3 ≤ b) (h4 : c < 4 * a + 5 * b) : 6 ≤ c := by
  try preprocess
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
