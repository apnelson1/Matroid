import Matroid.Simple
import Matroid.Minor

open Set
namespace Matroid

variable {M : Matroid α}

def ParallelExt (M : Matroid α) (e f : α) : Matroid α := 
  matroid_of_indep (insert f M.E) 
  (fun I ↦ (f ∉ I ∧ M.Indep I) ∨ (f ∈ I ∧ M.Indep (insert e (I \ {e}))))
  (by
    left
    refine ⟨Set.not_mem_empty _, M.empty_indep⟩
  )
  (by
    rintro I I' (⟨hI, hIY⟩ | ⟨hI, hIY⟩) Isub
    left
    refine' ⟨_, Indep.subset hIY Isub⟩
    exact not_mem_subset Isub hI
    right
    by_cases fmI: f ∈ I
    · refine' ⟨fmI, _⟩
      apply Indep.subset hIY _
      rw [insert_diff_singleton, insert_diff_singleton]
      exact insert_subset_insert Isub
  )
  (by
    rintro I X ⟨hIE, B, hB, hIB⟩ hI_not_max hX_max
    dsimp
    rw [mem_maximals_setOf_iff] at hI_not_max hX_max
    obtain ⟨(fnotinx | finx), hX_max⟩ := hX_max
    · push_neg at hI_not_max
      have I_ind : M.Indep I
      · use B
      obtain ⟨R, (⟨fnotinR, Rind⟩ | finR), hR₁, hR₂⟩ := hI_not_max (Or.inl ⟨hIE, I_ind⟩)
      by_cases xb : X = B
      have IssubB : I ⊂ B
      · apply ssubset_iff_subset_ne.2 ⟨hIB, _⟩
        intro h_f
        rw [h_f] at hR₁ hR₂
        apply (Indep.not_dep Rind) (Base.dep_of_ssubset hB (ssubset_iff_subset_ne.2 ⟨hR₁, hR₂⟩))
      

      

        --obtain ⟨x, hx1, hx2⟩ := exists_of_ssubset (ssubset_iff_subset_ne.2 ⟨hR₁, hR₂⟩)

    

    
    


    
  )
    sorry sorry

theorem eq_parallelExt_del {M : Matroid α} {e f : α} (h_para : M.Parallel e f) : 
    M = ParallelExt (M ⟍ f) e f := 
  sorry 
  
