import Mathlib.Data.Bool.Basic

variable {b c : Bool}

@[simp]
lemma Bool.bne_right_self (b c : Bool) : (b != (c != b)) = c := by
  rw [bne_comm, Bool.bne_self_right]

@[simp]
lemma Bool.beq_not_self_beq (b c : Bool) : (b == !b == c) = !c := by
  grind [cases Bool]

@[simp]
lemma Bool.bnot_bne (b c : Bool) : !b != c = (b == c) := by
  grind [cases Bool]

@[simp]
lemma Bool.beq_right_self (b c : Bool) : (b == (c == b)) = c := by
  grind [cases Bool]

@[simp]
lemma Bool.xor_self_beq (b c : Bool) : (b ^^ b == c) = !c := by
  grind [cases Bool]

@[simp]
lemma Bool.xor_beq_self (b c : Bool) : (b ^^ c == b) = !c := by
  grind [cases Bool]

@[simp]
lemma Bool.beq_self_xor (b c : Bool) : (b == (b ^^ c)) = !c := by
  grind [cases Bool]

@[simp]
lemma Bool.beq_xor_self (b c : Bool) : (b == (c ^^ b)) = !c := by
  grind [cases Bool]
