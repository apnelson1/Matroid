import Mathlib.Data.Matroid.Constructions

namespace Matroid

open Set

variable {α : Type*} {E I : Set α}

instance uniqueBaseOn_finitary : Finitary (uniqueBaseOn I E) := by
  refine ⟨fun K hK ↦ ?_⟩
  simp only [uniqueBaseOn_indep_iff'] at hK ⊢
  exact fun e heK ↦ singleton_subset_iff.1 <| hK _ (by simpa) (by simp)

instance freeOn_finitary : Finitary (freeOn E) := by
  rw [← uniqueBaseOn_self]; infer_instance

instance loopyOn_finiteRk : FiniteRk (loopyOn E) :=
  ⟨∅, by simp⟩

lemma uniqueBaseOn_finiteRk (hI : I.Finite) : FiniteRk (uniqueBaseOn I E) := by
  rw [← uniqueBaseOn_inter_ground_eq]
  refine ⟨I ∩ E, ?_⟩
  rw [uniqueBaseOn_base_iff inter_subset_right, and_iff_right rfl]
  exact hI.subset inter_subset_left

lemma uniqueBaseOn_rkPos (hIE : I ⊆ E) (hI : I.Nonempty) : RkPos (uniqueBaseOn I E) where
  empty_not_base := by simpa [uniqueBaseOn_base_iff hIE] using Ne.symm <| hI.ne_empty

lemma freeOn_rkPos (hE : E.Nonempty) : RkPos (freeOn E) := by
  rw [← uniqueBaseOn_self]; exact uniqueBaseOn_rkPos Subset.rfl hE

end Matroid
