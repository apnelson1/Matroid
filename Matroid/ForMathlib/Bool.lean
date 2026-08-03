module

public import Mathlib.Data.Bool.Basic

@[expose] public section

variable {b c : Bool}

namespace Bool

@[simp]
lemma bne_right_self (b c : Bool) : (b != (c != b)) = c := by
  rw [bne_comm, bne_self_right]

@[simp]
lemma beq_not_self_beq (b c : Bool) : (b == !b == c) = !c := by
  grind [cases Bool]

@[simp]
lemma bnot_bne (b c : Bool) : !b != c = (b == c) := by
  grind [cases Bool]

@[simp]
lemma beq_right_self (b c : Bool) : (b == (c == b)) = c := by
  grind [cases Bool]

@[simp]
lemma xor_self_beq (b c : Bool) : (b ^^ b == c) = !c := by
  grind [cases Bool]

@[simp]
lemma xor_beq_self (b c : Bool) : (b ^^ c == b) = !c := by
  grind [cases Bool]

@[simp]
lemma beq_self_xor (b c : Bool) : (b == (b ^^ c)) = !c := by
  grind [cases Bool]

@[simp]
lemma beq_xor_self (b c : Bool) : (b == (c ^^ b)) = !c := by
  grind [cases Bool]
