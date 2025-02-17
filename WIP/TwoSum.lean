import Mathlib.Data.Matroid.Sum
import Matroid.Extension

namespace Matroid

variable {α β : Type*} {e : α} {f : β}



def TwoSum (M : Matroid α) (N : Matroid β) (e : α) (f : β) : Matroid (α ⊕ β) :=
  let MN := M.sum N
  let L : Set (α ⊕ β) := {.inl e, .inr f}
  ((MN.projectBy <| ModularCut.principal MN L) ＼ L)

lemma twoSum_indep_iff (M : Matroid α) (N : Matroid β) (e : α) (f : β) (I : Set (α ⊕ β)) :
    (M.TwoSum N e f).Indep I ↔ M.Indep (.inl ⁻¹' I) ∧ N.Indep (.inr ⁻¹' I) := by
  simp only [TwoSum, delete_indep_iff, projectBy_indep_iff_of_ne_top sorry, sum_indep_iff, ne_eq,
    ModularCut.mem_principal_iff, closure_isFlat, true_and]

-- def InternalTwoSumIndepMatroid (M N : Matroid α) (e : α) (hMN : M.E ∩ N.E = {e}) :
--     IndepMatroid α where
--   E := M.E ∪ N.E
--   Indep I := I ⊆ M.E ∪ N.E ∧ M.Indep (I ∩ M.E) ∧ N.Indep (I ∩ N.E)
--   indep_empty := sorry
--   indep_subset := sorry
--   indep_aug := sorry
--   indep_maximal := sorry
--   subset_ground := sorry

-- def InternalTwoSum (M N : Matroid α) (e : α) (hMN : M.E ∩ N.E = {e}) : Matroid α :=
--   (InternalTwoSumIndepMatroid M N e hMN).matroid

-- @[simp] lemma internalTwoSum_indep_iff (M N : Matroid α) e hMN (I : Set α) :
--     (InternalTwoSum M N e hMN).Indep I ↔ I ⊆ M.E ∪ N.E ∧ M.Indep (I ∩ M.E) ∧ N.Indep (I ∩ N.E) := by
--   rfl

-- def ModularSum (M N : Matroid α) (A : Set α) (h : M.E ∩ N.E = A) (hAMN : M ↾ A = N ↾ A) :
--   Matroid α



-- ( ........  e)    g     (f ........ )

--         α       e  |      β        f  |   g
-- [  * * * * * *  1  |   0 0 0 0 0 0 0  |   1   ]
-- [  * * * * * *  3  |   0 0 0 0 0 0 0  |   3   ]
-- [  0 0 0 0 0 0  0  |   * * * * * * 3  |   3t  ]
-- [  0 0 0 0 0 0  0  |   * * * * * * 6  |   6t  ]
-- [  0 0 0 0 0 0  0  |   * * * * * * 8  |   8t  ]
