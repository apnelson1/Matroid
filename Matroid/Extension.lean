import Matroid.Simple
import Matroid.Minor

open Set
namespace Matroid

variable {M : Matroid α}

def ParallelExt (M : Matroid α) (e : α) (S : Set α) (S_disj: Disjoint S M.E) : Matroid α := 
  matroid_of_indep (M.E ∪ S) 
  (fun I ↦ (Disjoint S I ∧ M.Indep I) ∨ (e ∉ I ∧ ∃ f ∈ I, f ∈ S ∧ Disjoint S (I \ {f}) ∧ M.Indep (insert e (I \ {f}))))
  (by
    left
    refine ⟨disjoint_empty S, M.empty_indep⟩
  )
  (by
    rintro I I' (⟨hI, hIY⟩ | ⟨e_ni_I, f, f_I, f_s, I_d, h_Indep⟩) Isub
    left
    refine' ⟨_, Indep.subset hIY Isub⟩
    exact disjoint_of_subset_right Isub hI
    --exact not_mem_subset Isub hI
    by_cases fmI: f ∈ I
    · right
      refine ⟨not_mem_subset Isub e_ni_I, ?_⟩
      use f
      refine ⟨fmI, ⟨f_s, ⟨?_, ?_⟩⟩⟩
      apply disjoint_of_subset_right _ I_d
      apply diff_subset_diff_left Isub
      apply Indep.subset h_Indep _
      apply insert_subset_insert _
      apply diff_subset_diff_left Isub
    · left
      refine ⟨disjoint_of_subset_right (subset_diff_singleton Isub fmI) I_d, ?_⟩
      apply Indep.subset h_Indep _
      apply subset_union_of_subset_right (subset_diff_singleton Isub fmI)
  )   
  (by
    rintro I X ⟨hIE, B, hB, hIB⟩ hI_not_max hX_max
    dsimp
    rw [mem_maximals_setOf_iff] at hI_not_max hX_max
    obtain ⟨(⟨XdisjI, X_Ind⟩ | finx), hX_max⟩ := hX_max
    · push_neg at hI_not_max
      have I_ind : M.Indep I
      · use B
      have X_b : M.Base X
      · apply Indep.base_of_maximal X_Ind
        intro J J_Ind XsubJ
        apply hX_max (Or.inl ⟨_, J_Ind⟩) XsubJ
        exact disjoint_of_subset_right (Indep.subset_ground J_Ind) S_disj
      have I_ssub_B : I ⊂ B
      · apply ssubset_iff_subset_ne.2 ⟨hIB, _⟩
        intro I_eq_B
        obtain ⟨R, (⟨fnotinR, Rind⟩ | finR), hR₁, hR₂⟩ := hI_not_max (Or.inl ⟨hIE, I_ind⟩)
        apply Indep.not_dep Rind
        apply Base.dep_of_ssubset hB
        rw [←I_eq_B]
        apply ssubset_iff_subset_ne.2 ⟨hR₁, hR₂⟩
        obtain ⟨e_not_mem_I, f, finR, finS, fdisj, fIndep⟩ := finR
        have IssubefR : I ⊂ insert e (R \ {f})
        have IsubfR : I ⊆ (R \ {f})
        · apply subset_diff_singleton hR₁ _
          apply disjoint_left.1 _ finS
          apply disjoint_of_subset_right (Indep.subset_ground I_ind) S_disj
        apply ssubset_iff_subset_ne.2 ⟨_, _⟩
        apply subset_union_of_subset_right IsubfR
        apply ne_of_ssubset
        apply ssubset_of_subset_of_ssubset IsubfR (ssubset_insert _)
        rw []


      /-by_cases xb : X = B
      have IssubB : I ⊂ B
      · apply ssubset_iff_subset_ne.2 ⟨hIB, _⟩
        intro h_f
        rw [h_f] at hR₁ hR₂
        apply (Indep.not_dep Rind) (Base.dep_of_ssubset hB (ssubset_iff_subset_ne.2 ⟨hR₁, hR₂⟩))
      -/

      

        --obtain ⟨x, hx1, hx2⟩ := exists_of_ssubset (ssubset_iff_subset_ne.2 ⟨hR₁, hR₂⟩)

    

    
    


    
  )
    sorry sorry

theorem eq_parallelExt_del {M : Matroid α} {e f : α} (h_para : M.Parallel e f) : 
    M = ParallelExt (M ⟍ f) e f := 
  sorry 
  
