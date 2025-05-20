import Matroid.Connectivity.Basic

variable {α : Type*} {e f : α} {I X S : Set α}

namespace Matroid

lemma foo (M : Matroid α) (hI : M.Indep I) : M.Indep (I \ {e}) := by
  apply Indep.subset hI
  exact Set.diff_subset
