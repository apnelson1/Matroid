import Mathlib.Data.Matroid.Sum
import Matroid.Modular.Basic

variable {α β : Type*} {M N : Matroid α}

open Set

namespace Matroid

@[reducible] def ModularSumIndep (M N : Matroid α) (F I : Set α) :=
  M.Indep (I ∩ M.E) ∧ (N ／ (M.closure I)).Indep ((I ∩ N.E) \ F) ∧ I ⊆ M.E ∪ N.E

lemma ModularSumIndep.subset {F I J : Set α} (hJ : M.ModularSumIndep N F J) (hIJ : I ⊆ J) :
    M.ModularSumIndep N F I := by
  refine ⟨hJ.1.subset (inter_subset_inter_left _ hIJ), ?_, hIJ.trans hJ.2.2⟩
  refine (hJ.2.1.of_minor ?_).subset (diff_subset_diff_left (inter_subset_inter_left _ hIJ))
  exact contract_minor_of_subset  _ <| M.closure_subset_closure hIJ

def foo (M N : Matroid α) (F : Set α) (hFE : F = M.E ∩ N.E) (hF : M ↾ F = N ↾ F) (hMF : M.ModularSet F) : IndepMatroid α where
  E := M.E ∪ N.E
  Indep := M.ModularSumIndep N F
  indep_empty := by simp [ModularSumIndep]
  indep_subset I J hJ hIJ := hJ.subset hIJ
  indep_aug := by
    intro I B ⟨hIM, hIn, hIE⟩ hInotmax hBmax
    simp only [maximal_iff_forall_insert (fun _ _ ↦ ModularSumIndep.subset), not_and, not_forall,
      Classical.not_imp, not_not, and_imp, hIM, hIn, hIE, and_self, true_implies,
      exists_prop, exists_and_left, insert_subset_iff, and_true] at hInotmax



  indep_maximal := _
  subset_ground := _
