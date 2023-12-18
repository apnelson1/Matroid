import Matroid.Constructions.Uniform
import Matroid.ForMathlib.ENatTopology
import Matroid.Flat

open Set

variable {α : Type*} {M : Matroid α}
namespace Matroid

noncomputable def numPoints (M : Matroid α) : ℕ∞ := {P | M.Point P}.encard

theorem numPoints_eq_encard_parallelClasses (M : Matroid α) :
    M.numPoints = (M.parallelClasses : Set (Set α)).encard := by
  rw [numPoints, ← encard_univ_coe, M.parallelPointEquiv.symm.encard_univ_eq, encard_univ_coe]

theorem numPoints_eq_encard_ground_simplification (M : Matroid α) :
    M.numPoints = M.simplification.E.encard := by
  rw [numPoints_eq_encard_parallelClasses, M.simplification_equiv.encard_eq]

@[simp] theorem numPoints_eq_encard_ground (M : Matroid α) [Simple M] :
    M.numPoints = M.E.encard := by
  simp [numPoints_eq_encard_ground_simplification]

theorem encard_ground_eq_sum_encard_lines_through [Simple M] {e : α} (he : e ∈ M.E) :
    M.E.encard = 1 + ∑' L : {L // M.Line L ∧ e ∈ L}, ((L : Set α) \ {e}).encard := by
  rw [← encard_diff_add_encard_of_subset (singleton_subset_iff.2 he), add_comm, encard_singleton]
  apply congr_arg (1 + ·)
  convert (ENat.tsum_encard_eq_encard_sUnion (M ⧸ e).parallelClasses.pairwiseDisjoint).symm using 1
  · simp only [contract_elem, Partition.sUnion_eq, contract_nonloop_iff, mem_diff]
    congr
    rw [cl_singleton_eq]
  convert ENat.tsum_comp_eq_tsum_of_equiv (M ⧸ e).parallelPointEquiv.symm (g := fun x ↦ x.1.encard)
    using 1
  rw [← ENat.tsum_comp_eq_tsum_of_equiv (toNonloop he).lineContractPointEquiv]
  refine tsum_congr (fun ⟨P,hP⟩ ↦ ?_)
  simp [Nonloop.lineContractPointEquiv, cl_singleton_eq he,
    diff_singleton_eq_self (fun heP ↦ (hP.subset_ground heP).2 rfl)]

theorem kung {q : ℕ} (M : Matroid α) (hM : ¬ (unif 2 (q+2) ≤i M)) : 
    M.numPoints ≤ ∑' i : {i : ℕ // i ≤ M.erk}, q ^ (i : ℕ) := by
  _





  -- have : ∀ L, (M.Line L ∧ e ∈ L) ↔ (M.cl {e} ⋖[M] L)
  -- · intro L

  -- rw [tsum_congr_subtype (Q := fun L ↦ M.cl {e} ⋖[M] L)]






-- /-- Any partition `Xs` of the nonloops of `M` that is coarser than the partition into
--   parallel classes gives a decomposition of `M.numPoints` as a sum over the parts of `Xs`. -/
-- theorem foo' (M : Matroid α) (Xs : Partition {e | M.Nonloop e}) (hP : M.parallelClasses ≤ Xs) :
--     M.numPoints = ∑' X : Xs, (M ↾ X).numPoints := by
--   _

-- theorem foo [Simple M] {e : α} (he : e ∈ M.E) :
--     M.E.encard = 1 + ∑' L : {L // M.Line L ∧ e ∈ L}, ((L : Set α) \ {e}).encard := by


-- theorem Point.foo {P : Set α} (hP : M.Point P) :
--     M.numPoints = 1 + ∑' L : {L // P ⋖[M] L}, (M ↾ (L \ P)).numPoints := by
