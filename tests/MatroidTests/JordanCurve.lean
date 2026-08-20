module

public import Matroid.ForMathlib.Topology.JordanCurve

/-!
# Regression tests: `IsJordanCurve` tags

Each `example` fails if the tag named above it is removed; the `grind` block below was ablation
checked as a group (all three fail with the three `@[grind =]` tags dropped).

These examples use the Jordan curve theorem, which
`Matroid/ForMathlib/Topology/JordanCurve.lean` assumes as an axiom. They test that the tags fire,
not that the mathematics is proved.
-/

open Set Bornology Topology

namespace IsJordanCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fact (Module.finrank ℝ E = 2)]
  {J : Set E} (hJ : IsJordanCurve J)

section Simp

-- `frontier_inside`, `frontier_outside`, `frontier_insideOnePoint`, `frontier_outsideOnePoint`.
-- Unconditional and headed by this file's definitions, so the simp question is the normal-form
-- question: `frontier` of a side is eliminated in favour of the curve.
example : frontier hJ.inside = J := by simp
example : frontier hJ.outside = J := by simp
example : frontier hJ.insideOnePoint = (↑) '' J := by simp
example : frontier hJ.outsideOnePoint = (↑) '' J := by simp

-- `inside_union_outside`, `insideOnePoint_union_outsideOnePoint`.
example : hJ.inside ∪ hJ.outside = Jᶜ := by simp
example : hJ.insideOnePoint ∪ hJ.outsideOnePoint = ((↑) '' J : Set (OnePoint E))ᶜ := by simp

-- `closure_inside`, `closure_outside`.
example : closure hJ.inside = hJ.inside ∪ J := by simp
example : closure hJ.outside = hJ.outside ∪ J := by simp

-- `infty_notMem_insideOnePoint`, `infty_mem_outsideOnePoint`.
example : OnePoint.infty ∉ hJ.insideOnePoint := by simp
example : OnePoint.infty ∈ hJ.outsideOnePoint := by simp

-- The shapes a caller actually holds, rather than the lemmas restated.
example {x : E} (hx : x ∈ frontier hJ.inside) : x ∈ J := by simp_all
example {x : E} (hx : x ∉ J) : x ∈ hJ.inside ∪ hJ.outside := by simp_all

end Simp

section Grind

-- `mem_outside_iff_notMem_inside`, `mem_inside_iff_isBounded_connectedComponentIn`,
-- `connectedComponentIn_eq_inside_iff_isBounded`. All three carry the side condition `a ∉ J`,
-- which lives in the caller's hypotheses, so plain `simp` can never discharge it — these are
-- `@[grind =]` and not `@[simp]`.
example {x : E} (hx : x ∉ J) (h : x ∉ hJ.inside) : x ∈ hJ.outside := by grind

example {x : E} (hx : x ∉ J) (h : ¬ IsBounded (connectedComponentIn Jᶜ x)) : x ∈ hJ.outside := by
  grind

example {x : E} (hx : x ∈ frontier hJ.outside) : x ∈ J := by grind

end Grind

end IsJordanCurve
