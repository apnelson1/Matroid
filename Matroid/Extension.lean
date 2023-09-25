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
  )   
  (by
    rintro I X (I_ind | ⟨e_nI, f, f_I, f_S, f_disj, f_ind⟩) I_not_max X_max
    dsimp
    rw [mem_maximals_setOf_iff] at I_not_max X_max
    push_neg at I_not_max
    have I_nB : ¬ M.Base I
    · sorry 
    obtain ⟨(X_ind | ⟨e_nX, f, f_X, f_S, f_disj, f_ind⟩), X_max⟩ := X_max
    have X_B : M.Base X
    · sorry
    obtain ⟨e, e_Xdiff, e_Ind⟩ := Indep.exists_insert_of_not_base I_ind I_nB X_B
    use e
    refine ⟨e_Xdiff, Or.inl e_Ind⟩
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
    apply disjoint_left.1 _ f_S
    apply disjoint_of_subset_right (by aesop_mat) S_j
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
    apply disjoint_of_subset_right (subset_trans (diff_subset _ _) (by aesop_mat)) S_j
    rw [fif_eq, ←x_eq_e]
    apply Indep.subset x_Ind
    apply insert_subset_insert (diff_subset _ _)
    use x
    rw [mem_diff] at *
    refine' ⟨⟨mem_of_mem_diff (mem_of_mem_insert_of_ne x_Xdiff.1 x_eq_e), x_Xdiff.2⟩, _⟩
    exact Or.inl x_Ind

    -- part 2
    dsimp
    rw [mem_maximals_setOf_iff] at I_not_max X_max
    have I_nB : ¬ M.Base (insert e (I \ {f}))
    · sorry 
    have I_nB₂ : ¬ M.Base I
    · sorry
    obtain ⟨(X_ind | ⟨e_nX, l, l_X, l_S, l_disj, l_ind⟩), X_max⟩ := X_max
    have e_ne_f: e ≠ f
    · intro h_f
      apply e_nI
      rw [h_f]
      exact f_I
    have X_B : M.Base X
    · sorry
    obtain ⟨x, x_Xdiff, x_ind⟩ := Indep.exists_insert_of_not_base f_ind I_nB X_B
    have x_ne_f : x ≠ f
    · intro h_f
      rw [h_f] at x_ind
      apply disjoint_left.1 S_j f_S
      rw [←singleton_subset_iff]
      apply Indep.subset_ground (Indep.subset x_ind _)
      simp
    use x
    refine' ⟨_, Or.inr _⟩
    rw [mem_diff] at x_Xdiff ⊢
    refine' ⟨x_Xdiff.1, fun h_f ↦ _⟩
    apply x_Xdiff.2
    apply mem_union_right
    exact (mem_diff x).2 ⟨h_f, x_ne_f⟩
    have e_ne_x : e ≠ x
    · intro h_f
      rw [mem_diff] at x_Xdiff
      apply x_Xdiff.2
      rw [mem_insert_iff]
      exact (Or.inl h_f.symm)
    rw [mem_insert_iff]
    push_neg
    refine' ⟨⟨e_ne_x, e_nI⟩, f, mem_insert_of_mem x f_I, f_S, _⟩
    rw [insert_comm _ _ _, insert_diff_singleton_comm x_ne_f _] at x_ind
    refine' ⟨_, x_ind⟩
    rw [←insert_diff_singleton_comm x_ne_f _]
    apply Disjoint.union_right _ f_disj
    apply disjoint_singleton_right.2
    apply disjoint_right.1 S_j _
    rw [←singleton_subset_iff]
    apply Indep.subset_ground (Indep.subset X_ind _)
    rw [singleton_subset_iff]
    exact ((mem_diff x).1 x_Xdiff).1
    have X_B : M.Base (insert e (X \ {l}))
    · sorry
    obtain ⟨x, x_Xdiff, x_ind⟩ := Indep.exists_insert_of_not_base f_ind I_nB X_B
    use x
    rw [mem_diff] at x_Xdiff ⊢
    have x_in_X : x ∈ X
    · apply mem_of_mem_diff (mem_of_mem_insert_of_ne x_Xdiff.1 _)
      intro h_f
      apply x_Xdiff.2
      rw [h_f]
      exact mem_insert e _
    have x_notin_I : x ∉ I
    · intro h_f
      apply x_Xdiff.2
      apply mem_insert_of_mem
      rw [mem_diff, mem_singleton_iff]
      refine' ⟨h_f, fun h_f₂ ↦ _⟩
      apply disjoint_left.1 S_j f_S
      rw [←h_f₂]
      rw [←singleton_subset_iff]
      apply Indep.subset_ground (Indep.subset x_ind _)
      rw [singleton_subset_iff]
      exact mem_insert x _
    refine' ⟨⟨x_in_x, x_notin_I⟩, _⟩
    







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
  
