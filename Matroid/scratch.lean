import Mathlib

@[ext] structure MyStruct where
  (some_nat : ℕ)
  (some_set : Set ℕ)
  (h : some_nat ∉ some_set)



@[simps] def struct1 (m n : ℕ) : MyStruct where
  some_nat := m + n
  some_set := {0,m,n}
  h := sorry

@[simps] def struct2 (m n : ℕ) : MyStruct where
  some_nat := m + n + 2
  some_set := {m,n}
  h := sorry

@[simps!] def struct3 (m n : ℕ) : MyStruct := struct1 (m + n) 0



-- @[simp] lemma struct1_some_nat_eq (m n : ℕ) :
--   (struct1 m n).some_nat = m + n := rfl

example (m n : ℕ) : (struct1 m n).some_nat ≠ (struct2 m n).some_nat := by
  simp
  -- change m + n ≠ m + n + 2
