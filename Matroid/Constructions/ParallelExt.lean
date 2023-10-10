import Matroid.Constructions.Basic

namespace Matroid

open Set

variable {α β : Type _}

def parallel_preimage (M : Matroid β) (E : Set α) (f : α → β) : Matroid α := matroid_of_base
  sorry 
  sorry
  sorry 
  sorry 
  sorry 
  sorry 


-- def parallel_preimage (M : Matroid β) (E : Set α) (f : α → β) : Matroid α := matroid_of_indep
--   E 
--   ( fun I ↦ M.Indep (f '' I) ∧ InjOn f I ∧ I ⊆ E )
--   ( by simp )
--   ( fun I J ⟨h, h', hE⟩ hIJ ↦ ⟨h.subset (image_subset _ hIJ), InjOn.mono hIJ h', hIJ.trans hE⟩ )
--   ( by
--     rintro I J hI  hImax hJmax

--     --
--     -- simp [mem_maximals_iff, iff_true_intro hI, iff_true_intro hIinj, iff_true_intro hIE] at hImax
    
--   )
--   sorry
--   ( fun I h ↦ h.2.2 )

@[simp] theorem parallel_preimage_indep_iff {M : Matroid β} {E : Set α} {f : α → β} {I : Set α} : 
    (M.parallel_preimage E f).Indep I ↔ (M.Indep (f '' I) ∧ InjOn f I ∧ I ⊆ E) := by 
  sorry 
  
