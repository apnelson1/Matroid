import Matroid.Representation.FundamentalMatrix
import Matroid.Binary.Crossing
import Matroid.Order.Quotient


variable {α β W W' 𝔽 R ι : Type*} {e f x : α} {I E B X Y : Set α} {M : Matroid α} [DivisionRing 𝔽]
[DivisionRing R]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W'] [M.Finitary]

open Function Set Submodule FiniteDimensional BigOperators Matrix Set.Notation

lemma Rep.foo (v : M.Rep (ZMod 2) (ι →₀ ZMod 2)) {C : Finset α} (hCE : (C : Set α) ⊆ M.E)
    (h_even : ∀ i, Even {x ∈ C | v x i = 1}.card) : M.Cyclic C := by
  sorry

lemma Rep.foo2 (v : M.Rep (ZMod 2) (ι →₀ ZMod 2)) {C : Finset α} (hC : M.Circuit C) (i : ι) :
    Even {x ∈ C | v x i = 1}.card := by
  sorry


namespace Matroid

/-- The Binary matroid that should be `M`. -/
def BinaryProxy (hB : M.Base B) := (Matroid.ofFun (ZMod 2) M.E (hB.fundCoord (ZMod 2)))
