import Mathlib.LinearAlgebra.LinearIndependent
import Matroid.Simple
import Matroid.Representation.StandardRep
import Matroid.Binary.Crossing
import Matroid.Order.Quotient
import Mathlib.Data.Finsupp.Indicator

variable {α β W W' 𝔽 R : Type*} {e f x : α} {I E B X Y : Set α} {M : Matroid α} [Field 𝔽]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']

open Function Set Submodule FiniteDimensional BigOperators Matrix Set.Notation

namespace Matroid

/-- The intersection of `M.fundCircuit e B` with `B` as a `Finset B` in a finitary matroid. -/
noncomputable def Base.fundCct_finset_inter [Finitary M] (hB : M.Base B) (e : α) : Finset B :=
    Finite.toFinset (s := (B ↓∩ M.fundCircuit e B) ∩ {x | e ∈ M.E})
    (by
      by_cases heE : e ∈ M.E
      · refine Finite.inter_of_left (Finite.preimage Subtype.val_injective.injOn ?_) _
        by_cases heB : e ∈ B
        · simp [fundCircuit_eq_of_mem heB]
        exact (hB.fundCircuit_circuit heE heB).finite
      simp [heE] )

noncomputable def foo [Finitary M] (hB : M.Base B) (e : (M.E \ B : Set α)) : B →₀ ZMod 2 :=
  Finsupp.indicator (hB.fundCircuit_circuit e.2.1 e.2.2).finite.toFinset 1

noncomputable def Base.binaryRepFun (_hB : M.Base B) [∀ e, DecidablePred (· ∈ M.fundCircuit e B)] :
    α → B → ZMod 2 :=
  fun e b ↦ if b.1 ∈ M.fundCircuit e B then 1 else 0

lemma foo (hM : M.Binary) [Finitary M] (hB : M.Base B)
    [∀ e, DecidablePred (· ∈ M.fundCircuit e B)] : M = Matroid.ofFun (ZMod 2) E hB.binaryRepFun := by
  refine Eq.symm <| Quotient.eq_of_base_indep ?_ hB ?_
