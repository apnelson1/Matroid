import Matroid.Simple
import Matroid.Minor

open Set
namespace Matroid

variable {M : Matroid α}

def ParallelExt (M : Matroid α) (e : α) (S : Set α) : Matroid α := 
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
    rintro I X (⟨I_disj, I_ind⟩ | h_I) I_not_max X_max
    dsimp
    rw [mem_maximals_setOf_iff] at I_not_max X_max
    push_neg at I_not_max
    have I_nB : ¬ M.Base I
    · sorry 
    obtain ⟨(⟨X_disj, X_ind⟩ | ⟨e_nX, f, f_X, f_S, f_disj, f_ind⟩), X_max⟩ := X_max
    have X_B : M.Base X
    · sorry
    obtain ⟨e, e_Xdiff, e_Ind⟩ := Indep.exists_insert_of_not_base I_ind I_nB X_B
    use e
    refine ⟨e_Xdiff, Or.inl ⟨?_, e_Ind⟩⟩
    apply Disjoint.union_right _ I_disj
    apply disjoint_of_subset_right _ X_disj
    intro a (h_a : a = e)
    rw [h_a]
    apply mem_of_mem_diff e_Xdiff
    have X_B: M.Base (insert e (X \ {f}))
    · sorry
    obtain ⟨x, x_Xdiff, x_Ind⟩ := Indep.exists_insert_of_not_base I_ind I_nB X_B
    by_cases x_eq_e : x=e
    have e_nI : e ∉ I
    · rw [←x_eq_e]
      exact ((Set.mem_diff _).2 x_Xdiff).2
    use f
    rw [mem_diff]
    refine ⟨⟨f_X, ?_⟩, ?_⟩
    apply disjoint_left.1 I_disj f_S
    right
    constructor
    rw [mem_insert_iff]
    push_neg
    refine ⟨?_, e_nI⟩
    intro e_eq_f
    apply e_nX
    rw [e_eq_f]
    apply f_X
    use f
    refine ⟨Set.mem_insert _ _, f_S, ?_⟩
    
    /-
    dsimp
    rw [mem_maximals_setOf_iff] at hI_not_max hX_max
    push_neg at hI_not_max
    have I_ind : M.Indep I
      · use B
    have I_ssub_B : I ⊂ B
    · apply ssubset_iff_subset_ne.2 ⟨hIB, _⟩
      intro I_eq_B
      obtain ⟨R, (⟨fnotinR, Rind⟩ | finR), hR₁, hR₂⟩ := hI_not_max (Or.inl ⟨hIE, I_ind⟩)
      apply Indep.not_dep Rind
      apply Base.dep_of_ssubset hB
      rw [←I_eq_B]
      apply ssubset_iff_subset_ne.2 ⟨hR₁, hR₂⟩
      obtain ⟨e_not_mem_I, f, finR, finS, fdisj, fIndep⟩ := finR
      have hI : M.Base I
      · rw [I_eq_B]
        exact hB
      have rfind: M.Indep (R \ {f})
      · apply Indep.subset fIndep (subset_union_right _ _)
      have rdep: M.Dep R
      · apply Base.dep_of_ssubset I (ssubset_iff_subset_ne.2 ⟨hR₁, hR₂⟩)
    
    obtain ⟨(⟨XdisjI, X_Ind⟩ | finx), hX_max⟩ := hX_max
    -/
        


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
  
