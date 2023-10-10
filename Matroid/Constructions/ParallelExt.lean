import Matroid.Constructions.Basic

namespace Matroid

open Set

variable {α β : Type _}

def parallel_preimage (M : Matroid β) (E : Set α) (f : α → β) : Matroid α := matroid_of_indep
  E 
  ( fun I ↦ M.Indep (f '' I) ∧ InjOn f I )
  ( by simp )
  ( fun I J ⟨h, h'⟩ hIJ ↦ ⟨h.subset (image_subset _ hIJ), InjOn.mono hIJ h'⟩ )
  sorry 
  sorry
  sorry 

@[simp] theorem parallel_preimage_indep_iff {M : Matroid β} {E : Set α} {f : α → β} {I : Set α} : 
    (M.parallel_preimage E f).Indep I ↔ (M.Indep (f '' I) ∧ InjOn f I) := by 
  simp [parallel_preimage]
  
