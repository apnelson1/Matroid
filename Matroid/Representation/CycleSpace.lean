import Matroid.Representation.Minor

variable {α β W W' 𝔽 R : Type*} {e f x : α} {I C E B X Y : Set α} {M : Matroid α} [DivisionRing 𝔽]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']

open Set Function Submodule

namespace Matroid

noncomputable def Rep.cycleSpace (v : M.Rep 𝔽 W) :=
    (LinearMap.ker (Finsupp.linearCombination 𝔽 v) ⊓ Finsupp.supported 𝔽 𝔽 M.E)

lemma Rep.supported_finiteDimensional [M.Finite] (_ : M.Rep 𝔽 W) :
    FiniteDimensional 𝔽 <| Finsupp.supported 𝔽 𝔽 M.E :=
  have := M.ground_finite.to_subtype
  Module.Finite.equiv (Finsupp.supportedEquivFinsupp M.E).symm

lemma Rep.cycleSpace_finiteDimensional [M.Finite] (v : M.Rep 𝔽 W) :
    FiniteDimensional 𝔽 v.cycleSpace := by
  have := v.supported_finiteDimensional
  exact Submodule.finiteDimensional_inf_right ..

lemma Rep.exists_mem_cycleSpace_of_isCircuit (v : M.Rep 𝔽 W) (hC : M.IsCircuit C) :
    ∃ w ∈ v.cycleSpace, w.support = C := by
  have := v.finitary
  have := v.exists_finsupp_of_isCircuit hC
