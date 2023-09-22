import Matroid.Simple
import Matroid.Minor

open Set
namespace Matroid

variable {M : Matroid α}

def ParallelExt (M : Matroid α) (e : α) (S : Set α) (S_j : Disjoint S M.E): Matroid α := 
  matroid_of_indep (M.E ∪ S) 
  (fun I ↦ M.Indep I ∨ (e ∉ I ∧ ∃ f ∈ I, f ∈ S ∧ Disjoint S (I \ {f}) ∧ M.Indep (insert e (I \ {f}))))
  ( Or.inl M.empty_indep )
  (by
    rintro I I' (hIY | ⟨e_ni_I, f, f_I, f_S, I_d, h_Indep⟩) Isub
    exact (Or.inl (Indep.subset hIY Isub))
    by_cases fmI: f ∈ I
    right
    refine' ⟨not_mem_subset Isub e_ni_I , _⟩
    use f
    refine' ⟨fmI, f_S, _, Indep.subset h_Indep _⟩
    apply disjoint_of_subset_right (diff_subset_diff_left Isub) I_d
    apply insert_subset_insert (diff_subset_diff_left Isub)
    apply Or.inl (Indep.subset h_Indep _)
    apply subset_union_of_subset_right (subset_diff.2 ⟨Isub, _⟩)
    rwa [disjoint_singleton_right]
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
    rintro I X (⟨I_disj, I_ind⟩ | ⟨e_nI, f, f_I, f_S, f_disj, f_ind⟩) I_not_max X_max
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
    apply singleton_subset_iff.2 _
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
    have fif_eq: (insert f I) \ {f} = I \ {f}
    apply insert_diff_of_mem _ (mem_singleton _)
    refine ⟨Set.mem_insert _ _, f_S, ?_, ?_⟩
    rw [fif_eq]
    apply disjoint_of_subset_right _ I_disj
    apply diff_subset _ _
    apply Indep.subset x_Ind
    rw [x_eq_e, fif_eq]
    apply insert_subset_insert (diff_subset _ _)
    use x
    rw [mem_diff] at *
    constructor
    obtain h := mem_of_mem_insert_of_ne x_Xdiff.1 x_eq_e
    exact ⟨mem_of_mem_diff h, x_Xdiff.2⟩
    left
    refine ⟨?_, x_Ind⟩
    apply Disjoint.union_right
    apply disjoint_singleton_right.2
    apply disjoint_right.1 f_disj
    apply mem_of_mem_insert_of_ne x_Xdiff.1 x_eq_e
    exact I_disj
    -- part 2
    dsimp
    rw [mem_maximals_setOf_iff] at I_not_max X_max
    have I_nB : ¬ M.Base (insert e (I \ {f}))
    · sorry 
    have I_nB₂ : ¬ M.Base I
    · sorry
    obtain ⟨(⟨X_disj, X_ind⟩ | ⟨e_nX, f, f_X, f_S, f_disj, f_ind⟩), X_max⟩ := X_max
    have e_ne_f: e ≠ f
    · intro h_f
      apply e_nI
      rw [h_f]
      exact f_I
    have X_B : M.Base X
    · sorry
    obtain ⟨x, x_Xdiff, x_ind⟩ := Indep.exists_insert_of_not_base f_ind I_nB X_B
    by_cases x_eq_f : x = f
    rw [x_eq_f] at x_ind
    have I_ind : M.Indep I
    · apply Indep.subset x_ind    
      rw [insert_def]
      intro y h_y
      by_cases y_f : y = f
      exact (Or.inl y_f)
      right
      apply mem_insert_of_mem
      exact ⟨h_y, y_f⟩
    obtain ⟨y, y_Xdiff, y_ind⟩ := Indep.exists_insert_of_not_base I_ind I_nB₂ X_B
    use y
    refine ⟨y_Xdiff, Or.inl ⟨?_, y_ind⟩⟩
    apply disjoint_of_subset_right (y_ind.subset_ground) S_j
    use x
    refine' ⟨_, _⟩
    rw [mem_diff] at x_Xdiff ⊢
    refine' ⟨x_Xdiff.1, _⟩
    intro x_I
    apply x_Xdiff.2
    apply mem_union_right
    rw [mem_diff]
    refine' ⟨x_I, _⟩
    rw [mem_singleton_iff]
    exact x_eq_f
    left








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
  
