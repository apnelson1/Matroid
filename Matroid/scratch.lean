import Mathlib


set_option linter.style.longLine false

example {m n R : Type*} (A : Matrix m n R) (s : Finset m) (t : Finset n) : Matrix s t R :=
  A.submatrix (fun x : s ↦ x.1) (fun x : t ↦ x.1)
