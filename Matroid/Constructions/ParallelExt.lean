import Matroid.Constructions.Basic

namespace Matroid

open Set

variable {α β : Type _}
 


def parallel_preimage (M : Matroid β) (E : Set α) (f : α → β) : Matroid α := matroid_of_indep
  E 
  ( fun I ↦ M.Indep (f '' I) ∧ InjOn f I ∧ I ⊆ E )
  ( by simp )
  ( fun I J ⟨h, h', hE⟩ hIJ ↦ ⟨h.subset (image_subset _ hIJ), InjOn.mono hIJ h', hIJ.trans hE⟩ )
  ( by
    rintro I J ⟨hI, hIinj, hIE⟩ hImax hJmax

    have hI1 : ¬M.Base (f '' I)
    · refine fun hI' ↦ hImax ⟨⟨hI, hIinj, hIE⟩, fun B ⟨hB, hBinj, hBE⟩ (hB' : _ ⊆ _) x hxB ↦ 
        hBinj.mem_of_mem_image hB' hxB ?_⟩
      rw [hI'.eq_of_subset_indep hB (image_subset _ hB')]
      exact mem_image_of_mem _ hxB
    simp only [mem_maximals_iff, mem_setOf_eq, and_imp] at hJmax 
    have' := hI.exists_insert_of_not_basis (J := f '' J) (subset_union_right (f '' J) _) sorry sorry
    obtain ⟨_, ⟨⟨x,hx,rfl⟩,h'⟩, he'⟩ := this
    refine' ⟨x, ⟨hx, fun hxI ↦ h' (by exact mem_image_of_mem f hxI)⟩, _, _, _⟩ 
    · rwa [image_insert_eq]
    · rw []
    exact insert_subset (hJmax.1.2.2 hx) hIE





    -- have hB1 : M.Base (f '' J)
    -- · simp only [mem_maximals_iff, mem_setOf_eq, and_imp] at hJmax 
    --   refine hJmax.1.1.base_of_maximal (fun K hK hss ↦ ?_)
    --   have := hJmax.2 (y := (f ⁻¹' K) ∩ E) (hK.subset ?_)

    --   rw [hJmax.2 (y := (f ⁻¹' K) ∩ E)]
      
      
    

    --
    -- simp [mem_maximals_iff, iff_true_intro hI, iff_true_intro hIinj, iff_true_intro hIE] at hImax
    
  )
  sorry
  ( fun I h ↦ h.2.2 )



@[simp] theorem parallel_preimage_indep_iff {M : Matroid β} {E : Set α} {f : α → β} {I : Set α} : 
    (M.parallel_preimage E f).Indep I ↔ (M.Indep (f '' I) ∧ InjOn f I ∧ I ⊆ E) := by 
  sorry 

@[simp] theorem parallel_preimage_ground_eq {M : Matroid β} {E : Set α} {f : α → β} : 
    (M.parallel_preimage E f).E = E := rfl 
  
  
