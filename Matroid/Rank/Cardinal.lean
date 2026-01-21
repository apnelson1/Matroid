/-
Copyright (c) 2025 Peter Nelson and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Junyan Xu
-/
import Mathlib.Combinatorics.Matroid.Closure
import Mathlib.Combinatorics.Matroid.Map
import Mathlib.Combinatorics.Matroid.Rank.Cardinal
import Matroid.ForMathlib.Card
import Matroid.Rank.Nat
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Cardinal-valued rank

In a finitary matroid, all bases have the same cardinality.
In fact, something stronger holds: if `I` and `J` are both bases for a set `X`,
then `#(I \ J) = #(J \ I)` and (consequently) `#I = #J`.
This file introduces a typeclass `InvariantCardinalRank` that applies to any matroid
such that this property holds for all `I`, `J` and `X`.

A matroid satisfying this condition has a well-defined cardinality-valued rank function,
both for itself and all its minors.

# Main Declarations

* `Matroid.InvariantCardinalRank` : a typeclass capturing the idea that a matroid and all its minors
  have a well-behaved cardinal-valued rank function.
* `Matroid.cRank M` is the supremum of the cardinalities of the bases of matroid `M`.
* `Matroid.cRk M X` is the supremum of the cardinalities of the bases of a set `X` in a matroid `M`.
* `invariantCardinalRank_of_finitary` is the instance
   showing that `Finitary` matroids are `InvariantCardinalRank`.
* `cRk_inter_add_cRk_union_le` states that cardinal rank is submodular.

# Notes

It is not the case that all matroids are `InvariantCardinalRank`,
since the equicardinality of bases in general matroids is independent of ZFC
(see the module docstring of `Mathlib.Combinatorics.Matroid.Basic`).
Lemmas like `Matroid.IsBase.cardinalMk_diff_comm` become true for all matroids
only if they are weakened by replacing `Cardinal.mk`
with the cruder `ℕ∞`-valued `Set.encard`; see, for example, `Matroid.IsBase.encard_diff_comm`.

# Implementation Details

Since the functions `cRank` and `cRk` are defined as suprema,
independently of the `Matroid.InvariantCardinalRank` typeclass,
they are well-defined for all matroids.
However, for matroids that do not satisfy `InvariantCardinalRank`, they are badly behaved.
For instance, in general `cRk` is not submodular,
and its value may differ on a set `X` and the closure of `X`.
We state and prove theorems without the instance whenever possible,
which sometime makes their proofs longer than they would be with the instance.

# TODO

* Higgs' theorem : if the generalized continuum hypothesis holds,
  then every matroid is `InvariantCardinalRank`.

-/

universe u v

variable {α : Type u} {β : Type v} {f : α → β} {M : Matroid α} {I J B B' X Y : Set α}

open Cardinal Set

namespace Matroid

section Rank

variable {κ : Cardinal}

end Rank

section Finite

@[simp] theorem cRank_eq_zero : M.cRank = 0 ↔ ∃ E, M = loopyOn E := by
  rw [← nonpos_iff_eq_zero, cRank_le_iff]
  simp only [nonpos_iff_eq_zero, mk_eq_zero_iff, isEmpty_coe_sort, eq_loopyOn_iff,
    exists_and_right, exists_eq', true_and]
  refine ⟨fun h X hX hXi ↦ ?_, fun h B hB ↦ h _ hB.subset_ground hB.indep⟩
  obtain ⟨B, hB, hXB⟩ := hXi.exists_isBase_superset
  simpa [h hB] using hXB

theorem cRank_eq_zero_iff : M.cRank = 0 ↔ M = loopyOn M.E := by
  rw [cRank_eq_zero]
  exact ⟨by rintro ⟨E, rfl⟩; rfl, fun h ↦ ⟨M.E, h⟩⟩

/-- A version of `Matroid.cRk_eq_zero_iff` applying to sets not contained in the ground set. -/
theorem cRk_eq_zero_iff' : M.cRk X = 0 ↔ X ∩ M.E ⊆ M.loops := by
  rw [cRk, cRank_eq_zero_iff, ← closure_empty_eq_ground_iff, restrict_closure_eq', empty_inter,
    restrict_ground_eq, subset_antisymm_iff, loops]
  simp only [union_subset_iff, inter_subset_right, diff_subset, and_self, true_and]
  rw [union_comm, ← diff_subset_iff, diff_diff_right_self, subset_inter_iff,
    and_iff_left inter_subset_left]

theorem cRk_le_one_iff [Nonempty α] (hX : X ⊆ M.E := by aesop_mat) :
    M.cRk X ≤ 1 ↔ ∃ e, X ⊆ M.closure {e} := by
  simp_rw [cRk_le_iff, mk_le_one_iff_set_subsingleton]
  refine ⟨fun h ↦ ?_, fun ⟨e, he⟩ I hIX ↦ ?_⟩
  · obtain ⟨I, hI⟩ := M.exists_isBasis X
    obtain rfl | ⟨e, rfl⟩ := (h hI.isBasis').eq_empty_or_singleton
    · exact ⟨Classical.arbitrary α, hI.subset_closure.trans (M.closure_subset_closure (by simp))⟩
    exact ⟨e, hI.subset_closure⟩
  obtain ⟨J, hJ, hIJ⟩ := hIX.indep.subset_isBasis_of_subset (hIX.subset.trans he)
  obtain ⟨J', hJ'⟩ := M.exists_isBasis' {e}
  refine encard_le_one_iff_subsingleton.1 ((encard_le_encard hIJ).trans ?_)
  rw [← hJ'.isBasis_closure_right.encard_eq_encard hJ]
  exact (encard_le_encard hJ'.subset).trans (by simp)

lemma crk_lt_aleph0_iff : M.cRk X < aleph0 ↔ M.IsRkFinite X := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨I, hI⟩ := M.exists_isBasis' X
    exact hI.isRkFinite_of_finite <| by simpa using hI.cardinalMk_le_cRk.trans_lt h

  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  refine lt_of_le_of_lt ?_ (mk_lt_aleph0_iff.2 (hI.finite_of_isRkFinite h))
  rw [cRk_le_iff]
  intro J hJ
  rw [← toENat_strictMonoOn.le_iff_le, toENat_cardinalMk, toENat_cardinalMk,
    hI.encard_eq_encard hJ]
  · simp [(hJ.finite_of_isRkFinite h).countable]
  simp [(hI.finite_of_isRkFinite h).countable]

lemma cRank_lt_aleph0_iff :  M.cRank < aleph0 ↔ M.RankFinite := by
  rw [← cRk_ground, crk_lt_aleph0_iff, isRkFinite_ground_iff_rankFinite]

@[simp] lemma cRank_toENat (M : Matroid α) : M.cRank.toENat = M.eRank := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  obtain (h | h) := M.rankFinite_or_rankInfinite
  · rw [← hB.cardinalMk_eq_cRank, ← hB.encard_eq_eRank, toENat_cardinalMk]
  rw [← hB.encard_eq_eRank, hB.infinite.encard_eq, toENat_eq_top, ← not_lt, cRank_lt_aleph0_iff]
  exact M.not_rankFinite

@[simp] lemma cRk_toENat (M : Matroid α) (X : Set α) : (M.cRk X).toENat = M.eRk X := by
  rw [cRk, cRank_toENat, eRk]

@[simp] lemma cRank_toNat (M : Matroid α) : M.cRank.toNat = M.rank := by
  rw [rank, ← cRank_toENat]
  rfl

@[simp] lemma cRk_toNat (M : Matroid α) (X : Set α) : (M.cRk X).toNat = M.rk X := by
  rw [cRk, cRank_toNat, rk, eRk]

end Finite

end Matroid
