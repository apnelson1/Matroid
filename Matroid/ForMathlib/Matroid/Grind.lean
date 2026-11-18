module

public import Mathlib.Combinatorics.Matroid.Loop
public import Matroid.ForMathlib.Tactic.GrindMatAttr

@[expose] public section

attribute [matroid_ground ←] Set.union_subset Matroid.closure_subset_ground
attribute [matroid_ground =] Set.iUnion_subset_iff

attribute [matroid_ground →] Matroid.IsBase.subset_ground Matroid.Indep.subset_ground
  Matroid.Dep.subset_ground Matroid.IsBasis.subset_ground Matroid.IsBasis.left_subset_ground
  Matroid.IsCircuit.subset_ground Matroid.IsFlat.subset_ground Matroid.Spanning.subset_ground
  Matroid.IsLoop.mem_ground Matroid.IsNonloop.mem_ground Matroid.IsColoop.mem_ground

attribute [matroid_ground =] Matroid.dual_ground Matroid.loopyOn_ground Matroid.freeOn_ground
  Matroid.uniqueBaseOn_ground Matroid.restrict_ground_eq Matroid.comap_ground_eq
  Matroid.comapOn_ground_eq

grind_pattern [matroid_ground] Matroid.closure_subset_ground => M.closure X
grind_pattern [matroid_ground] Matroid.loops_subset_ground => M.loops
grind_pattern [matroid_ground] Matroid.coloops_subset_ground => M.coloops

/-- Prove matroid ground-set side conditions using `grind` and the
`matroid_ground` theorem collection. The matroid, set, and element arguments
should be determined before invoking the tactic. -/
macro "grind_mat" : tactic =>
  `(tactic| grind [$(Lean.mkIdent `matroid_ground):term])
