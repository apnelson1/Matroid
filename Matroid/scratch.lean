--import Mathlib.LinearAlgebra.LinearIndependent
import Mathlib.LinearAlgebra.Dual

open Set Submodule 

variable {α β W W' 𝔽 R : Type _} {e f x : α} {I B X Y : Set α} [Field 𝔽]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']

