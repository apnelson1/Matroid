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
    · intro h_f
      obtain ⟨R, (R_ind | ⟨e_notin_R, f, f_in_R, f_in_S, f_disj, f_ind⟩), I_sub_R, I_ne_R⟩:= I_not_max (Or.inl I_ind)
      obtain R_dep := h_f.dep_of_ssubset (ssubset_of_subset_of_ne I_sub_R I_ne_R)
      exact R_ind.not_dep R_dep
      have I_ssub_R' : I ⊂ insert e (R \ {f})
      apply ssubset_of_subset_of_ssubset (subset_diff_singleton I_sub_R _) (ssubset_insert _)
      apply disjoint_right.1 (Disjoint.symm _) f_in_S
      apply disjoint_of_subset_right (by aesop_mat) S_j
      rw [mem_diff]
      exact fun h ↦ e_notin_R h.1
      have:= Indep.subset_ground f_ind
      obtain R'_dep := h_f.dep_of_ssubset I_ssub_R'
      exact f_ind.not_dep R'_dep
    obtain ⟨(X_ind | ⟨e_nX, f, f_X, f_S, f_disj, f_ind⟩), X_max⟩ := X_max
    have X_B : M.Base X
    · rw [base_iff_maximal_indep]
      refine ⟨X_ind, fun J J_ind J_sub ↦ (X_max (Or.inl J_ind) J_sub)⟩
    obtain ⟨e, e_Xdiff, e_Ind⟩ := Indep.exists_insert_of_not_base I_ind I_nB X_B
    use e
    refine ⟨e_Xdiff, Or.inl e_Ind⟩
    have X_B: M.Base (insert e (X \ {f}))
    · rw [base_iff_maximal_indep]
      refine' ⟨f_ind, fun J J_ind J_sub ↦ _⟩
      have X_sub_J' : X ⊆ insert f (J \ {e})
      intro x x_in_X
      by_cases x_eq_f : x = f
      rw [x_eq_f]
      exact mem_insert _ _
      apply mem_union_right _
      rw [mem_diff_singleton]
      refine' ⟨J_sub (mem_union_right _ ((mem_diff x).2 ⟨x_in_X, x_eq_f⟩)), ne_of_mem_of_not_mem x_in_X e_nX⟩
      obtain J'_eq_X := X_max (Or.inr _) X_sub_J'
      have e_J : e ∈ J := J_sub (mem_insert _ _)
      have f_nJ : f ∉ J:= disjoint_right.1 (Disjoint.symm (disjoint_of_subset_right (by aesop_mat) S_j)) f_in_S
      rw [J'_eq_X]
      simp [e_J, f_nJ, (ne_of_mem_of_not_mem f_X e_nX)]
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
    push_neg at I_not_max
    have I_nB : ¬ M.Base (insert e (I \ {f}))
    · intro h_f
      obtain ⟨R, (R_ind | ⟨e_notin_R, l, l_in_R, l_in_S, l_disj, l_ind⟩), I_sub_R, I_ne_R⟩:=
      I_not_max (Or.inr ⟨e_nI, f, f_I, f_S, f_disj, f_ind⟩)
      apply disjoint_left.1 S_j f_S
      rw [←singleton_subset_iff]
      apply Indep.subset_ground (Indep.subset R_ind _)
      exact singleton_subset_iff.2 (I_sub_R f_I)
      apply l_ind.not_dep (h_f.dep_of_ssubset (ssubset_of_subset_of_ne (insert_subset_insert _) _) _)
      apply subset_diff_singleton
      exact subset_trans (diff_subset _ _) I_sub_R
      apply disjoint_left.1 (disjoint_of_subset_right ((f_ind.subset (subset_insert _ _)).subset_ground) S_j) l_in_S
      rw [insert_eq, insert_eq]
      by_cases f_eq_l : f = l
      rw [←f_eq_l]
      intro h_f₂
      apply I_ne_R
      rw [union_eq_union_iff_left] at h_f₂
      apply subset_antisymm I_sub_R
      intro r r_R
      by_cases r_eq_f : r = f
      rwa [r_eq_f]
      obtain r_mem_union := h_f₂.2 ((mem_diff r).2 ⟨r_R, r_eq_f⟩)
      rw [←insert_eq] at r_mem_union
      apply mem_of_mem_diff (mem_of_mem_insert_of_ne r_mem_union (ne_of_mem_of_not_mem r_R e_notin_R))
      apply ne_of_not_superset
      rw [not_subset]
      refine' ⟨f, mem_union_right _ _, _⟩
      exact ((mem_diff f).2 ⟨I_sub_R f_I, f_eq_l⟩)
      rw [← insert_eq, mem_insert_iff]
      push_neg
      exact ⟨ne_of_mem_of_not_mem f_I e_nI, not_mem_diff_of_mem (mem_singleton _)⟩
      exact l_ind.subset_ground
    obtain ⟨(X_ind | ⟨e_nX, l, l_X, l_S, l_disj, l_ind⟩), X_max⟩ := X_max
    have e_ne_f: e ≠ f
    · intro h_f
      apply e_nI
      rw [h_f]
      exact f_I
    have X_B : M.Base X
    · rw [base_iff_maximal_indep]
      refine ⟨X_ind, fun J J_ind J_sub ↦ (X_max (Or.inl J_ind) J_sub)⟩
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
    have x_in_E : x ∈ M.E
    · rw [←singleton_subset_iff]
      apply Indep.subset_ground (Indep.subset X_ind _)
      rw [singleton_subset_iff]
      exact ((mem_diff x).1 x_Xdiff).1
    exact x_in_E
    have X_B : M.Base (insert e (X \ {l}))
    · rw [base_iff_maximal_indep]
      refine' ⟨l_ind, fun J J_ind J_sub ↦ _⟩
      have X_sub_J' : X ⊆ insert l (J \ {e})
      intro x x_in_X
      by_cases x_eq_l : x = l
      rw [x_eq_l]
      exact mem_insert _ _
      apply mem_union_right _
      rw [mem_diff_singleton]
      refine' ⟨J_sub (mem_union_right _ ((mem_diff x).2 ⟨x_in_X, x_eq_l⟩)), ne_of_mem_of_not_mem x_in_X e_nX⟩
      obtain J'_eq_X := X_max (Or.inr _) X_sub_J'
      have e_J : e ∈ J := J_sub (mem_insert _ _)
      have l_nJ : l ∉ J:= disjoint_right.1 (Disjoint.symm (disjoint_of_subset_right _ S_j)) l_S
      rw [J'_eq_X]
      simp [e_J, l_nJ, (ne_of_mem_of_not_mem l_X e_nX)]
    obtain ⟨x, x_Xdiff, x_ind⟩ := Indep.exists_insert_of_not_base f_ind I_nB X_B
    have x_in_E : x ∈ M.E
    · rw [←singleton_subset_iff]
      apply Indep.subset_ground (Indep.subset x_ind _)
      rw [singleton_subset_iff]
      exact mem_insert x _
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
      exact x_in_E
    refine' ⟨⟨x_in_X, x_notin_I⟩, Or.inr _⟩
    rw [mem_insert_iff]
    push_neg
    refine' ⟨⟨(ne_of_mem_of_not_mem x_in_X e_nX).symm, e_nI⟩, f, mem_insert_of_mem _ f_I, _⟩
    refine' ⟨f_S, ⟨_, _⟩⟩
    rw [←(insert_diff_singleton_comm _ _)]
    apply Disjoint.union_right _ f_disj
    apply disjoint_singleton_right.2
    exact disjoint_right.1 S_j x_in_E
    exact (ne_of_mem_of_not_mem f_S (disjoint_right.1 S_j x_in_E)).symm
    apply Indep.subset x_ind
    rw [insert_comm, ←(insert_diff_singleton_comm _ _)]
    exact (ne_of_mem_of_not_mem f_S (disjoint_right.1 S_j x_in_E)).symm

  )
  (by
    rintro X X_ground I (I_indep | ⟨e_nI, f, f_S, f_I, f_disj, f_ind⟩) I_sub_X
    rw [nonempty_def]
    obtain h := M.maximality' (X ∩ M.E) (inter_subset_right X M.E) (I ∩ M.E) (I_indep.subset (inter_subset_left I M.E))
    obtain ⟨Y, h_Y⟩ := h (inter_subset_inter_left _ I_sub_X)
    rw [mem_maximals_iff] at h_Y
    obtain ⟨⟨(Y_ind : M.Indep Y), I'_sub_Y, Y_sub_X'⟩, Y_max⟩ := h_Y
    by_cases X_disj : Disjoint X S
    





    





  )
   sorry

theorem eq_parallelExt_del {M : Matroid α} {e f : α} (h_para : M.Parallel e f) : 
    M = ParallelExt (M ⟍ f) e f := 
  sorry 
  
