module

public import Matroid.ForMathlib.Geometry.SegmentFigure.Affine
public import Matroid.ForMathlib.Analysis.InnerProductSpace.TwoDim

/-!
# Directions transverse to a segment figure

`o.areaForm v p` is Mathlib's area form on an oriented real inner-product plane.
Its level sets, for `v ≠ 0`, are the lines parallel to `v`. A direction is transverse to a
nondegenerate segment precisely when this coordinate differs at the endpoints.

A finite segment figure admits a nonzero direction transverse to every nondegenerate segment
contained in it, not just the segments of one chosen presentation. Every level set in such
a direction meets the figure in finitely many points.
-/

@[expose] public section

open Set Function Module

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

namespace Orientation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (finrank ℝ E = 2)] (o : Orientation ℝ E (Fin 2)) {S : Set E}

theorem exists_transverse_direction {S : Set E} (hS : IsSegmentFigure S) :
    ∃ v : E, v ≠ 0 ∧ ∀ a b, a ≠ b → segment ℝ a b ⊆ S →
      o.areaForm v a ≠ o.areaForm v b := by
  have hdim : 1 < Module.rank ℝ E := by
    let : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ 1
    rw [← Module.finrank_eq_rank, (Fact.out : Module.finrank ℝ E = 2)]
    norm_num
  have hnontrivial : Nontrivial E := rank_pos_iff_nontrivial.mp (lt_trans zero_lt_one hdim)
  obtain ⟨v, hv, htrans⟩ := hS.exists_direction_not_parallel_iff.mpr
    ⟨hnontrivial, Or.inr hdim⟩
  refine ⟨v, hv, fun a b hab hseg heq ↦ ?_⟩
  have hz : o.areaForm v (b - a) = 0 := by simp [map_sub, heq]
  obtain ⟨t, ht⟩ := (o.areaForm_eq_zero_iff hv).mp hz
  exact htrans a b hab hseg t ht

end Orientation
