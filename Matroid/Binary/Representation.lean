import Matroid.Representation.FundamentalMatrix
import Matroid.Binary.Crossing
import Matroid.Order.Quotient


variable {α β W W' 𝔽 R : Type*} {e f x : α} {I E B X Y : Set α} {M : Matroid α} [DivisionRing 𝔽]
[DivisionRing R]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W'] [M.Finitary]

open Function Set Submodule FiniteDimensional BigOperators Matrix Set.Notation

theorem foo (hM : M.Binary) (hB : M.Base B) :
    (Matroid.ofFun (ZMod 2) M.E (hB.fundCoord (ZMod 2))) = M := by
  _


namespace Matroid
