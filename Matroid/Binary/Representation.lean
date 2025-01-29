import Mathlib.LinearAlgebra.LinearIndependent
import Matroid.Simple
import Matroid.Representation.StandardRep
import Matroid.Binary.Crossing
import Matroid.Order.Quotient
import Mathlib.Data.Finsupp.Indicator

variable {α β W W' 𝔽 R : Type*} {e f x : α} {I E B X Y : Set α} {M : Matroid α} [DivisionRing 𝔽]
[DivisionRing R]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W'] [M.Finitary]

open Function Set Submodule FiniteDimensional BigOperators Matrix Set.Notation

namespace Matroid

/-- The intersection of `M.fundCircuit e B` with `B` as a `Finset B` in a finitary matroid.
Defined hackishly to equal `{e}` for `e ∈ B`, and equal `∅` if `e ∉ M.e` -/
noncomputable def Base.fundCircuit_finset_inter (hB : M.Base B) (e : α) : Finset B :=
  Finite.toFinset (s := (B ↓∩ M.fundCircuit e B) ∩ {x | e ∈ M.E})
  (by
    by_cases heE : e ∈ M.E
    · refine Finite.inter_of_left (Finite.preimage Subtype.val_injective.injOn ?_) _
      by_cases heB : e ∈ B
      · simp [fundCircuit_eq_of_mem heB]
      exact (hB.fundCircuit_circuit heE heB).finite
    simp [heE])

lemma Base.fundCircuit_finset_inter_of_mem (hB : M.Base B) (he : e ∈ B) :
    hB.fundCircuit_finset_inter e = {⟨e, he⟩} := by
  ext ⟨x, hx⟩
  simp [fundCircuit_finset_inter, hB.subset_ground he, fundCircuit_eq_of_mem' he]

lemma Base.fundCircuit_finset_inter_of_not_mem_ground (hB : M.Base B) (he : e ∉ M.E) :
    hB.fundCircuit_finset_inter e = ∅ := by
  ext ⟨x, hx⟩
  simp [fundCircuit_finset_inter, he]

/-- The column of the `B`-fundamental matrix of `M` corresponding to `e`, as a `Finsupp`. -/
noncomputable def fundCoord (R : Type*) [Semiring R] (hB : M.Base B) (e : α) :
    B →₀ R :=
  Finsupp.indicator (hB.fundCircuit_finset_inter e) (fun _ _ ↦ 1)

variable {R : Type*} [DivisionRing R]

lemma Base.fundCoord_of_mem (hB : M.Base B) (he : e ∈ B) :
    fundCoord R hB e = Finsupp.single ⟨e, he⟩ 1 := by
  rw [fundCoord, fundCircuit_finset_inter_of_mem hB he, Finsupp.single_eq_indicator]

lemma Base.fundCoord_of_not_mem_ground (hB : M.Base B) (he : e ∉ M.E) :
    fundCoord R hB e = 0 := by
  rw [fundCoord, fundCircuit_finset_inter_of_not_mem_ground hB he]
  rfl

lemma fundCoord_base (hB : M.Base B) (e : α) : (Matroid.ofFun R M.E (M.fundCoord R hB)).Base B := by
  refine Indep.base_of_forall_insert ?_ ?_
  · rw [ofFun_indep_iff, and_iff_left hB.subset_ground]
    convert (Finsupp.basisSingleOne (ι := B) (R := R)).linearIndependent
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp [hB.fundCoord_of_mem hi]



    -- have := B.restrict (fundCoord R hB)







-- noncomputable def Base.binaryRepFun (_hB : M.Base B) [∀ e, DecidablePred (· ∈ M.fundCircuit e B)] :
--     α → B → ZMod 2 :=
--   fun e b ↦ if b.1 ∈ M.fundCircuit e B then 1 else 0

-- lemma foo (hM : M.Binary) [Finitary M] (hB : M.Base B)
--     [∀ e, DecidablePred (· ∈ M.fundCircuit e B)] : M = Matroid.ofFun (ZMod 2) E hB.binaryRepFun := by
--   refine Eq.symm <| Quotient.eq_of_base_indep ?_ hB ?_
