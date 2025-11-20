import Mathlib.Tactic.TautoSet

-- a version of `tauto_set` that uses `grind` instead of `tauto`.
macro "tauto_set!" : tactic => `(tactic|
  · simp_all -failIfUnchanged only [
      Set.ext_iff, Set.subset_def,
      Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff,
      Set.symmDiff_def, Set.diff_eq, Set.disjoint_iff
    ]
    try intro x
    try specialize_all x
    <;> grind
)
