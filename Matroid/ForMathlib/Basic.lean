import Mathlib.Data.Matroid.Basic

open Set

/-- This is the same as `Indep.exists_insert_of_not_base`, but phrased so the statement is
  defeq to the augmentation axiom for independent sets -/
theorem Matroid.aug_property (M : Matroid α) :
    ∀⦃I B⦄, M.Indep I → I ∉ maximals (· ⊆ ·) (setOf M.Indep) →
      B ∈ maximals (· ⊆ ·) (setOf M.Indep) → ∃ x ∈ B \ I, M.Indep (insert x I) := by
  intro I B hI hImax hB
  simp only [mem_maximals_iff, mem_setOf_eq, not_and, not_forall, exists_prop,
    exists_and_left, iff_true_intro hI, true_imp_iff] at hB hImax
  refine hI.exists_insert_of_not_base (fun hIb ↦ ?_) ?_
  · obtain ⟨I', hII', hI', hne⟩ := hImax
    exact hne <| hIb.eq_of_subset_indep hII' hI'
  exact hB.1.base_of_maximal fun J hJ hBJ ↦ hB.2 hJ hBJ
