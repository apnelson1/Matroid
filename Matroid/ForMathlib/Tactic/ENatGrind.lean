import Mathlib.Data.ENat.Lattice

variable {a b c : ℕ∞}

namespace ENat

def recTopZeroSucc {C : ℕ∞ → Sort*} (top : C ⊤) (zero : C 0) (succ : (a : ℕ) → C (a + 1)) (n : ℕ∞) :
    C n := by
  cases n with
  | top => assumption
  | coe n =>
  · cases n with
  | zero => assumption
  | succ n => exact succ n

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

lemma mul_top_eq_iff : a * ⊤ = b ↔ (a = 0 ∧ b = 0) ∨ (a ≠ 0 ∧ b = ⊤) := by
  cases b using ENat.recTopZeroSucc with
  | top => simp [ENat.mul_top_eq_ite]
  | zero => simp
  | succ b =>
    suffices ¬ (if a = 0 then 0 else (⊤ : ℕ∞)) = b + 1 by simpa [ENat.mul_top_eq_ite]
    split_ifs <;> {rw [eq_comm]; simp}

lemma top_mul_eq_iff : ⊤ * a = b ↔ (a = 0 ∧ b = 0) ∨ (a ≠ 0 ∧ b = ⊤) := by
  rw [mul_comm, mul_top_eq_iff]


namespace Grind

-- @[enat_to_nat_top]
-- protected theorem add_eq_top_iff :
--     a + b = ⊤ ↔ (a = ⊤ ∧ b ≠ ⊤) ∨ (a ≠ ⊤ ∧ b = ⊤) ∨ (a = ⊤ ∧ b = ⊤) := by
--   rw [WithTop.add_eq_top]
--   grind

-- @[enat_to_nat_top]
-- protected theorem mul_eq_top_iff : a * b = ⊤ ↔
--     (a = ⊤ ∧ b ≠ 0 ∧ b ≠ ⊤) ∨
--     (a ≠ 0 ∧ a ≠ ⊤ ∧ b = ⊤) ∨
--     (a = ⊤ ∧ b = ⊤) := by
--   grind [ENat.zero_ne_top, ENat.mul_eq_top_iff]

-- @[enat_to_nat_top]
-- protected theorem sub_eq_top_iff : a - b = ⊤ ↔ a = ⊤ ∧ b ≠ ⊤ := by simp



def NatEq (a b : ℕ∞) : Prop := a = b ∧ a ≠ ⊤ ∧ b ≠ ⊤

def NatLE (a b : ℕ∞) : Prop := a ≤ b ∧ a ≠ ⊤ ∧ b ≠ ⊤

def NatLT (a b : ℕ∞) : Prop := a < b ∧ a ≠ ⊤ ∧ b ≠ ⊤

def NatNe (a b : ℕ∞) : Prop := a ≠ b ∧ a ≠ ⊤ ∧ b ≠ ⊤

def EqTop (a : ℕ∞) : Prop := a = ⊤

def NeTop (a : ℕ∞) : Prop := a ≠ ⊤

def EqZero (a : ℕ∞) : Prop := a = 0

protected theorem NatEq.neTop_left (h : NatEq a b) : NeTop a := h.2.1

protected theorem NatEq.neTop_right (h : NatEq a b) : NeTop b := h.2.2

@[enat_to_nat_top]
protected theorem neTop_iff (a : ℕ∞) : NeTop a ↔ ¬ EqTop a := sorry

@[enat_to_nat_top]
protected theorem le_iff : a ≤ b ↔ EqTop b ∨ (NatLE a b ∧ NeTop a ∧ NeTop b) := sorry

@[enat_to_nat_top]
protected theorem eq_iff : a = b ↔ (EqTop a ∧ EqTop b) ∨ (NatEq a b ∧ NeTop a ∧ NeTop b) := sorry

@[enat_to_nat_top]
protected theorem lt_iff : a < b ↔ (NeTop a ∧ EqTop b) ∨ (NatLT a b ∧ NeTop a ∧ NeTop b) := sorry

@[enat_to_nat_top]
protected theorem ne_iff : a ≠ b ↔ (EqTop a ∧ NeTop b) ∨ (EqTop b ∧ NeTop a) ∨
    (NatNe a b ∧ NeTop a ∧ NeTop b) := sorry

@[enat_to_nat_top]
protected theorem eqTop_add : EqTop (a + b) ↔ EqTop a ∨ EqTop b := sorry

@[enat_to_nat_top]
protected theorem eqTop_mul :
  EqTop (a * b) ↔ (EqTop a ∧ ¬ EqZero b) ∨ (¬ EqZero a ∧ EqTop b) := sorry

@[enat_to_nat_top, grind.]
protected theorem EqTop.not_eqZero (h : EqTop a) : ¬ EqZero a := sorry

@[enat_to_nat_top, grind.]
protected theorem EqZero.not_eqTop (h : EqZero a) : ¬ EqTop a := sorry

@[enat_to_nat_top]
protected theorem not_eqTop_zero : ¬ EqTop 0 := sorry

@[enat_to_nat_top]
protected theorem not_eqTop_one : ¬ EqTop 1 := sorry

@[enat_to_nat_top]
protected theorem not_eqTop_cast {n : ℕ} : ¬ EqTop n := sorry

@[enat_to_nat_top]
protected theorem eqTop_top : EqTop ⊤ := sorry

@[enat_to_nat_top]
protected theorem natNe_zero : NatNe b 0 ↔ ¬ EqZero b := sorry

@[enat_to_nat_top]
protected theorem zero_natNe : NatNe 0 b ↔ ¬ EqZero b := sorry

-- attribute [grind.]
--  ENat.Grind.eqTop_top ENat.Grind.not_eqTop_cast ENat.Grind.not_eqTop_one
--     ENat.Grind.not_eqTop_zero ENat.Grind.eqTop_mul
-- lemma natEq_expand (a b : ℕ∞) : NatEq a b ↔ NatEq a b

variable {a b d e f g : ℕ∞}

attribute [enat_to_nat_top] le_top not_false or_false false_or false_and and_false and_true true_and
  not_false_iff

macro "prepro": tactic =>
  `(tactic | (simp only [enat_to_nat_top] at *))

example (h1 : a * b = c) (h2 : c < d) (h3 : b ≠ 0) : False := by
  prepro
  have ha : ¬ EqTop a := by grind
  simp [ha] at *
  have hc : ¬ EqTop c := by grind
  simp [hc] at *








-- @[enat_to_nat_top]
-- protected theorem add_eq_iff : a + b = c ↔
--     (a = ⊤ ∧ b = ⊤ ∧ c = ⊤) ∨
--     (a = ⊤ ∧ b ≠ ⊤ ∧ c = ⊤) ∨
--     (a ≠ ⊤ ∧ b = ⊤ ∧ c = ⊤) ∨
--     (a + b = c ∧ a ≠ ⊤ ∧ b ≠ ⊤ ∧ c ≠ ⊤) := by
--   cases c with
--   | top => grind [WithTop.add_eq_top]
--   | coe c => simp +contextual [imp_and, imp_not_comm (a := _ + _ = _)]

-- @[enat_to_nat_top]
-- protected theorem eq_add_iff : a = b + c ↔
--     (a = ⊤ ∧ c = ⊤) ∨
--     (a = ⊤ ∧ b = ⊤) ∨
--     (a = b + c ∧ a ≠ ⊤ ∧ b ≠ ⊤ ∧ c ≠ ⊤) := by
--   rw [eq_comm, ENat.Grind.add_eq_iff]
--   tauto

-- @[enat_to_nat_top]
-- protected theorem mul_eq_iff : a * b = c ↔
--     (a = ⊤ ∧ b ≠ 0 ∧ c = ⊤) ∨
--     (a ≠ 0 ∧ b = ⊤ ∧ c = ⊤) ∨
--     (a = 0 ∧ c = 0)          ∨
--     (b = 0 ∧ c = 0)          ∨
--     (a * b = c ∧ a ≠ ⊤ ∧ b ≠ ⊤ ∧ c ≠ ⊤) := by
--   cases c using ENat.recTopZeroSucc with
--   | top => grind [ENat.zero_ne_top, ENat.mul_eq_top_iff]
--   | zero => grind [ENat.zero_ne_top, Nat.cast_zero, mul_eq_zero]
--   | succ c => simp +contextual [imp_and, imp_not_comm (b := _ = ⊤), top_mul_eq_iff, mul_top_eq_iff]

-- @[enat_to_nat_top]
-- protected theorem add_le_iff : a + b ≤ c ↔
--     (c = ⊤) ∨ (a + b ≤ c ∧ a ≠ ⊤ ∧ b ≠ ⊤ ∧ c ≠ ⊤) := by
--   cases c with
--   | top => grind [le_top]
--   | coe c => simp +contextual [imp_and, imp_not_comm (b := _ = ⊤)]

-- @[enat_to_nat_top]
-- protected theorem le_add_iff : a ≤ b + c ↔
--     (b = ⊤) ∨ (c = ⊤) ∨ (a ≤ b + c ∧ a ≠ ⊤ ∧ b ≠ ⊤ ∧ c ≠ ⊤) := by
--   cases c with
--   | top => simp
--   | coe c =>
--   simp only [coe_ne_top, ne_eq, not_false_eq_true, and_true, false_or]
--   cases b with
--   | top => simp
--   | coe b => simp +contextual [imp_not_comm (b := _ = ⊤), ← Nat.cast_add]

-- @[enat_to_nat_top]
-- protected theorem mul_le_iff : a * b ≤ c ↔
--     (c = ⊤) ∨ (a = 0) ∨ (b = 0) ∨ (a * b ≤ c ∧ a ≠ ⊤ ∧ b ≠ ⊤ ∧ c ≠ ⊤) := by
--   cases c using ENat.recTopZeroSucc with
--   | top => simp
--   | zero => grind [nonpos_iff_eq_zero, mul_eq_zero, zero_ne_top]
--   | succ c =>
--   cases a with
--   | top =>
--     suffices (if b = 0 then 0 else (⊤ : ℕ∞)) ≤ c + 1 ↔ b = 0 by simpa [ENat.top_mul_eq_ite]
--     split_ifs <;> simpa
--   | coe a =>
--   cases b with
--   | top =>
--     suffices (if a = 0 then 0 else ⊤ : ℕ∞) ≤ c + 1 ↔ a = 0 by simpa [ENat.mul_top_eq_ite]
--     split_ifs <;> simpa
--   | coe b => simp +contextual [iff_def, or_imp]

-- @[enat_to_nat_top]
-- protected theorem le_mul_iff : a ≤ b * c ↔
--     (b = ⊤ ∧ c ≠ 0) ∨ (b ≠ 0 ∧ c = ⊤) ∨ (a = 0) ∨ (a ≤ b * c ∧ a ≠ ⊤ ∧ b ≠ ⊤ ∧ c ≠ ⊤) := by
--   have aux {x y : ℕ} : x ≤ y * (⊤ : ℕ∞) ↔ y ≠ 0 ∨ x = 0 := by
--     simp_rw [ENat.mul_top_eq_ite, Nat.cast_eq_zero]
--     split_ifs with h <;> simp [h]
--   cases a with
--   | top => simp [ENat.mul_eq_top_iff]
--   | coe a =>
--   cases b with
--   | top =>
--     cases c with
--     | top => simp
--     | coe c => simp [mul_comm ⊤, aux]
--   | coe b =>
--   cases c with
--   | top => simp [aux]
--   | coe c => simp +contextual [iff_def, or_imp]


-- -- @[enat_to_nat_top]
-- -- protected theorem lt_add_iff : a < b + c ↔

-- -- example {a b c d : ℕ∞} (h1 : a + 2 * b = c + d) (h2 : )
