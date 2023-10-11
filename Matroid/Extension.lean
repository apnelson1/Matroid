import Matroid.Simple
import Matroid.Minor
import Matroid.Constructions.ParallelExt
open Set
open Classical
namespace Matroid

variable {M : Matroid α}

def ParallelExt (M : Matroid α) (e : α) (S : Set α): Matroid α := 
    M.parallel_preimage (M.E ∪ S) (fun x ↦ if (x ∈ S) then e else x)

theorem Indep.parallel_substitute (hI : M.Indep I) (h_para : M.Parallel e f) (hI_e : e ∈ I):
    M.Indep (insert f (I \ {e})) := by
  by_cases e_ne_f : e = f
  · rwa [←e_ne_f, insert_diff_singleton, insert_eq_of_mem hI_e]
  · rw [indep_iff_forall_subset_not_circuit']
    refine' ⟨fun C C_sub C_circ ↦ _, _⟩
    · have f_c : f ∈ C
      · by_contra h_f
        rw [subset_insert_iff_of_not_mem h_f, subset_diff, disjoint_singleton_right] at C_sub 
        exact (hI.subset C_sub.1).not_dep C_circ.1
      have e_notin_C : e ∉ C := fun e_in_C ↦ (mem_of_mem_insert_of_ne (C_sub e_in_C) e_ne_f).2 rfl
      have C_ne_ef : C ≠ {e, f}
      · intro h_f
        rw [h_f] at e_notin_C
        exact e_notin_C (mem_insert e _)
      obtain ⟨C', C'_circ, C'_sub⟩ := C_circ.elimination ((parallel_iff_circuit e_ne_f).1 h_para) C_ne_ef f
      have C'_sub_I : C' ⊆ I
      intro c c_sub_C'
      obtain ⟨(c_sub_C | c_sub_ef), (c_ne_f : c ≠ f)⟩ := C'_sub c_sub_C'
      · exact (mem_of_mem_insert_of_ne (C_sub c_sub_C) c_ne_f).1
      · have c_eq_e : c = e
        · apply eq_of_not_mem_of_mem_insert c_sub_ef _
          rwa [mem_singleton_iff]
        rwa [c_eq_e]
      exact (hI.subset C'_sub_I).not_dep C'_circ.1
    · rintro i (i_eq_f | i_sub_I)
      · rw [i_eq_f]
        exact h_para.mem_ground_right
      · exact hI.subset_ground i_sub_I.1    
  
theorem parallel_automorphism {M : Matroid α} {e f : α} (h_para : M.Parallel e f) : 
Iso M (M.parallel_preimage M.E (fun x ↦ if (x = e) then f else (if (x = f) then e else x))) := by
  sorry


theorem eq_parallelExt_del {M : Matroid α} {e f : α} (h_para : M.Parallel e f) (h_ne : e ≠ f): 
    M = ParallelExt (M ⟍ f) e {f} := by
  rw [ParallelExt, eq_iff_indep_iff_indep_forall, parallel_preimage_ground_eq]
  refine' ⟨_, fun I I_ground ↦ ⟨fun I_Ind ↦ _, _⟩⟩
  · simp
    exact (insert_eq_of_mem (Parallel.mem_ground_right h_para)).symm
  · rw [parallel_preimage_indep_iff]
    simp only [delete_elem, mem_singleton_iff, delete_indep_iff, disjoint_singleton_right, 
      mem_image, not_exists, not_and, delete_ground, union_singleton, mem_diff, not_true, and_false, 
      insert_diff_singleton]
    constructor
    · constructor
      · by_cases f_in_I : f ∈ I
        · have image_eq : (fun a ↦ if a = f then e else a) '' I = insert e (I \ {f})
          · apply subset_antisymm 
            · rintro i ⟨a, a_I, h_a₁⟩
              dsimp at h_a₁
              by_cases a_eq_f : a = f
              · rw [if_pos a_eq_f] at h_a₁
                rw [←h_a₁]
                exact mem_insert _ _
              · rw [if_neg a_eq_f] at h_a₁
                rw [←h_a₁]
                exact mem_insert_of_mem _ (mem_diff_singleton.2 ⟨a_I, a_eq_f⟩)
            · rintro i (i_eq_e | ⟨i_in_I, (i_ne_f : i ≠ f)⟩)
              · refine' ⟨f, f_in_I, _⟩
                rw [i_eq_e]
                exact if_pos rfl
              · refine ⟨i, i_in_I, if_neg i_ne_f⟩
          rw [image_eq]
          apply I_Ind.parallel_substitute h_para.symm f_in_I
        · have image_eq : (fun a ↦ if a = f then e else a) '' I = I
          · apply subset_antisymm
            · rintro i ⟨a, a_I, h_a₁⟩
              dsimp at h_a₁
              rw [if_neg (ne_of_mem_of_not_mem a_I f_in_I)] at h_a₁
              rwa [←h_a₁]
            · rintro i i_in_I
              refine' ⟨i, i_in_I, if_neg (ne_of_mem_of_not_mem i_in_I f_in_I)⟩
          rwa [image_eq]
      · intro x _
        by_cases x_eq_f : x = f
        · rwa [if_pos x_eq_f]
        · rwa [if_neg x_eq_f]
    refine' ⟨_, subset_trans I_ground (subset_insert f M.E)⟩
    rintro a a_I b b_I f_ab
    dsimp at f_ab
    by_cases b_eq_f : b = f
    · rw [if_pos b_eq_f, ite_eq_left_iff] at f_ab
      by_cases a_eq_f : a = f
      · rwa [b_eq_f]
      · have ef_sub_I : {e, f} ⊆ I
        · rintro i (i_eq_e | (i_eq_f : i = f)) 
          · rwa [i_eq_e, ←(f_ab a_eq_f)]
          · rwa [i_eq_f, ←b_eq_f]
        exfalso
        apply I_Ind.not_dep _
        rw [dep_iff_supset_circuit]
        exact ⟨{e, f}, ef_sub_I, (parallel_iff_circuit h_ne).1 h_para⟩
    · rw [if_neg b_eq_f] at f_ab
      by_cases a_eq_f : a = f 
      · rw [if_pos a_eq_f] at f_ab
        have ef_sub_I : {e, f} ⊆ I
        · rintro i (i_eq_e | (i_eq_f : i = f)) 
          · rwa [i_eq_e, f_ab]
          · rwa [i_eq_f, ←a_eq_f]
        exfalso
        apply I_Ind.not_dep _
        rw [dep_iff_supset_circuit]
        exact ⟨{e, f}, ef_sub_I, (parallel_iff_circuit h_ne).1 h_para⟩
      · rwa [if_neg a_eq_f] at f_ab
  -- part 2
  rw [parallel_preimage_indep_iff]
  simp [delete_ground]
  rintro I_image_Indep h_not_f h_inj I_sub
  by_cases f_in_I : f ∈ I
  · have image_eq : (fun a ↦ if a = f then e else a) '' I = insert e (I \ {f})
    · apply subset_antisymm 
      · rintro i ⟨a, a_I, h_a₁⟩
        dsimp at h_a₁
        by_cases a_eq_f : a = f
        · rw [if_pos a_eq_f] at h_a₁
          rw [←h_a₁]
          exact mem_insert _ _
        · rw [if_neg a_eq_f] at h_a₁
          rw [←h_a₁]
          exact mem_insert_of_mem _ (mem_diff_singleton.2 ⟨a_I, a_eq_f⟩)
      · rintro i (i_eq_e | ⟨i_in_I, (i_ne_f : i ≠ f)⟩)
        · refine' ⟨f, f_in_I, _⟩
          rw [i_eq_e]
          exact if_pos rfl
        · refine ⟨i, i_in_I, if_neg i_ne_f⟩
    rw [image_eq] at I_image_Indep
    have:= I_image_Indep.parallel_substitute h_para (mem_insert e _)
    have e_notin_I : e ∉ I
    · intro e_in_I
      apply h_ne (h_inj e_in_I f_in_I _)
      dsimp
      rw [if_pos rfl, if_neg h_ne]
    simp [e_notin_I, f_in_I, h_ne] at this
    exact this
  · have image_eq : (fun a ↦ if a = f then e else a) '' I = I
    · apply subset_antisymm
      · rintro i ⟨a, a_I, h_a₁⟩
        dsimp at h_a₁
        rw [if_neg (ne_of_mem_of_not_mem a_I f_in_I)] at h_a₁
        rwa [←h_a₁]
      · intro i i_in_I
        refine' ⟨i, i_in_I, _⟩
        exact if_neg (ne_of_mem_of_not_mem i_in_I f_in_I)
    rwa [image_eq] at I_image_Indep




    




   
          











    --rintro X X_ground I (I_indep | ⟨e_nI, f, f_S, f_I, f_ind⟩) I_sub_X
    /-rw [nonempty_def]
    obtain h := M.maximality' (X ∩ M.E) (inter_subset_right X M.E) (I ∩ M.E) 
      (I_indep.subset (inter_subset_left I M.E))
    obtain ⟨Y, h_Y⟩ := M.maximality' (X ∩ M.E) (inter_subset_right X M.E) (I ∩ M.E) 
      (I_indep.subset (inter_subset_left I M.E)) (inter_subset_inter_left _ I_sub_X)
    simp_rw [mem_maximals_iff] at h_Y ⊢
    obtain ⟨⟨(Y_ind : M.Indep Y), I'_sub_Y, Y_sub_X'⟩, Y_max⟩ := h_Y
    have I_sub_Y : I ⊆ Y
    · rwa [←(inter_eq_left.2 I_indep.subset_ground)]
    by_cases X_disj : Disjoint X S
    use Y    
    refine' ⟨⟨Or.inl Y_ind, _, subset_trans Y_sub_X' (inter_subset_left X M.E)⟩, _⟩
    exact I_sub_Y
    rintro y ⟨(y_ind | ⟨e_nY, f, f_y, f_s, f_ind⟩), I_sub_y, y_sub_X⟩ Y_sub_y
    apply Y_max ⟨y_ind, _⟩ Y_sub_y
    exact ⟨subset_trans (inter_subset_left I M.E) I_sub_y, 
      subset_inter y_sub_X (y_ind.subset_ground)⟩
    apply absurd f_s (disjoint_left.1 X_disj (y_sub_X f_y))
    have:  eY_nind : ¬ M.Indep (insert e Y) ∧ e ∉ Y
    -/
    


    
    --refine' ⟨disjoint_of_subset_right S_j _, insert_subset f_X (subset_trans Y_sub_X' (inter_subset_left X M.E))⟩
    







    








  
/-  matroid_of_indep (M.E ∪ S) 
  (fun I ↦ M.Indep I ∨ (e ∉ I ∧ ∃ f ∈ I, f ∈ S ∧ M.Indep (insert e (I \ {f}))))
  ( Or.inl M.empty_indep )
  (by
    rintro I I' (hIY | ⟨e_ni_I, f, f_I, f_S, h_Indep⟩) Isub
    exact (Or.inl (Indep.subset hIY Isub))
    by_cases fmI: f ∈ I
    · right
      refine' ⟨not_mem_subset Isub e_ni_I , _⟩
      refine' ⟨f, fmI, f_S, Indep.subset h_Indep _⟩
      apply insert_subset_insert (diff_subset_diff_left Isub)
    · apply Or.inl (Indep.subset h_Indep _)
      apply subset_union_of_subset_right (subset_diff.2 ⟨Isub, _⟩)
      rwa [disjoint_singleton_right]
    
  )   
  (by
    rintro I X (I_ind | ⟨e_nI, f, f_I, f_S, f_ind⟩) I_not_max X_max
    · dsimp  
      rw [mem_maximals_setOf_iff] at I_not_max X_max
      push_neg at I_not_max
      have I_nB : ¬ M.Base I
      · intro h_f
        obtain ⟨R, (R_ind | ⟨e_notin_R, f, f_in_R, f_in_S, f_ind⟩), I_sub_R, I_ne_R⟩:=
         I_not_max (Or.inl I_ind)
        · obtain R_dep := h_f.dep_of_ssubset (ssubset_of_subset_of_ne I_sub_R I_ne_R)
          exact R_ind.not_dep R_dep
        · have I_ssub_R' : I ⊂ insert e (R \ {f})
          · apply ssubset_of_subset_of_ssubset (subset_diff_singleton I_sub_R _) (ssubset_insert _)
            apply disjoint_right.1 (Disjoint.symm _) f_in_S
            apply disjoint_of_subset_right (by aesop_mat) S_j
            rw [mem_diff]
            exact fun h ↦ e_notin_R h.1
          have:= Indep.subset_ground f_ind
          obtain R'_dep := h_f.dep_of_ssubset I_ssub_R'
          exact f_ind.not_dep R'_dep
      obtain ⟨(X_ind | ⟨e_nX, f, f_X, f_S, f_ind⟩), X_max⟩ := X_max
      have X_B : M.Base X
      · rw [base_iff_maximal_indep]
        refine ⟨X_ind, fun J J_ind J_sub ↦ (X_max (Or.inl J_ind) J_sub)⟩
      obtain ⟨e, e_Xdiff, e_Ind⟩ := Indep.exists_insert_of_not_base I_ind I_nB X_B
      refine ⟨e, e_Xdiff, Or.inl e_Ind⟩
      have X_B: M.Base (insert e (X \ {f}))
      · rw [base_iff_maximal_indep]
        refine' ⟨f_ind, fun J J_ind J_sub ↦ _⟩
        have X_sub_J' : X ⊆ insert f (J \ {e})
        · intro x x_in_X
          by_cases x_eq_f : x = f
          · rw [x_eq_f]
            exact mem_insert _ _
          apply mem_union_right _
          rw [mem_diff_singleton]
          exact ⟨J_sub (mem_union_right _ ((mem_diff x).2 ⟨x_in_X, x_eq_f⟩)),
           ne_of_mem_of_not_mem x_in_X e_nX⟩
        obtain J'_eq_X := X_max (Or.inr _) X_sub_J'
        have e_J : e ∈ J := J_sub (mem_insert _ _)
        have f_nJ : f ∉ J:= disjoint_right.1 (Disjoint.symm (disjoint_of_subset_right (by aesop_mat) S_j)) f_S
        rw [J'_eq_X]
        simp [e_J, f_nJ, (ne_of_mem_of_not_mem f_X e_nX)]
      obtain ⟨x, x_Xdiff, x_Ind⟩ := Indep.exists_insert_of_not_base I_ind I_nB X_B
      by_cases x_eq_e : x=e
      · have e_nI : e ∉ I
        · rw [←x_eq_e]
          exact ((Set.mem_diff _).2 x_Xdiff).2
        use f
        rw [mem_diff]
        refine' ⟨⟨f_X, _⟩, _⟩
        · apply disjoint_left.1 _ f_S
          apply disjoint_of_subset_right (by aesop_mat) S_j
        · right
          constructor
          rw [mem_insert_iff]
          push_neg
          refine' ⟨fun e_eq_f ↦ e_nX _, e_nI⟩
          rw [e_eq_f]
          apply f_X
          use f
          have fif_eq: (insert f I) \ {f} = I \ {f}
          · apply insert_diff_of_mem _ (mem_singleton _)
          refine' ⟨Set.mem_insert f I, f_S, _⟩
          rw [fif_eq, ←x_eq_e]
          apply Indep.subset x_Ind
          apply insert_subset_insert (diff_subset _ _)
      use x
      rw [mem_diff] at *
      refine' ⟨⟨mem_of_mem_diff (mem_of_mem_insert_of_ne x_Xdiff.1 x_eq_e), x_Xdiff.2⟩, Or.inl x_Ind⟩
    · dsimp
      rw [mem_maximals_setOf_iff] at I_not_max X_max
      push_neg at I_not_max
      have I_nB : ¬ M.Base (insert e (I \ {f}))
      · intro h_f
        obtain ⟨R, (R_ind | ⟨e_notin_R, l, l_in_R, l_in_S, l_ind⟩), I_sub_R, I_ne_R⟩:= I_not_max (Or.inr ⟨e_nI, f, f_I, f_S, f_ind⟩)
        · apply disjoint_left.1 S_j f_S
          rw [←singleton_subset_iff]
          apply Indep.subset_ground (Indep.subset R_ind _)
          exact singleton_subset_iff.2 (I_sub_R f_I)
        · apply l_ind.not_dep (h_f.dep_of_ssubset (ssubset_of_subset_of_ne (insert_subset_insert _) _) _)
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
      obtain ⟨(X_ind | ⟨e_nX, l, l_X, l_S, l_ind⟩), X_max⟩ := X_max
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
      rwa [insert_comm _ _ _, insert_diff_singleton_comm x_ne_f _] at x_ind
      
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
        have l_nJ : l ∉ J:= disjoint_right.1 (Disjoint.symm (disjoint_of_subset_right ?_ S_j)) l_S
        rw [J'_eq_X]
        simp [e_J, l_nJ, (ne_of_mem_of_not_mem l_X e_nX)]
        exact J_ind.subset_ground
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
      refine' ⟨f_S, _⟩
      apply Indep.subset x_ind
      rw [insert_comm, ←(insert_diff_singleton_comm _ _)]
      exact (ne_of_mem_of_not_mem f_S (disjoint_right.1 S_j x_in_E)).symm

  )
  (by
    rintro X X_ground I (I_indep | ⟨e_nI, f, f_I, f_S, f_ind⟩) I_sub_X
    · obtain ⟨Y, h_Y⟩ := M.maximality' (X ∩ M.E) (inter_subset_right X M.E) (I ∩ M.E) 
        (I_indep.subset (inter_subset_left I M.E)) (inter_subset_inter_left _ I_sub_X)
      rw [mem_maximals_iff] at h_Y
      obtain ⟨⟨(Y_ind : M.Indep Y), I'_sub_Y, Y_sub_X'⟩, Y_max⟩ := h_Y
      have I_sub_Y : I ⊆ Y
      · rwa [←(inter_eq_left.2 I_indep.subset_ground)]
      by_cases X_disj : Disjoint S X
      use Y
      rw [mem_maximals_iff]
      refine' ⟨⟨Or.inl Y_ind, I_sub_Y, subset_trans Y_sub_X' (inter_subset_left X M.E)⟩, _⟩
      rintro y ⟨(y_ind | ⟨e_nY, f, f_y, f_s, f_ind⟩), I_sub_y, y_sub_X⟩ Y_sub_y
      apply Y_max ⟨y_ind, _⟩ Y_sub_y
      · exact ⟨subset_trans (inter_subset_left _ _) I_sub_y, subset_inter y_sub_X y_ind.subset_ground⟩
      apply absurd f_s (disjoint_right.1 X_disj (y_sub_X f_y))
      by_cases e_ind : M.Indep (insert e Y) ∧ e ∉ Y
      obtain ⟨eY_ind, e_notin_Y⟩ := e_ind 
      obtain ⟨f, f_S, f_X⟩ := not_disjoint_iff.1 X_disj
      have f_ne_e : f ≠ e
      · apply ne_of_mem_of_not_mem f_S _
        apply disjoint_right.1 S_j _
        rw [←singleton_subset_iff]
        apply Indep.subset_ground (eY_ind.subset _)
        rw [singleton_subset_iff]
        exact mem_insert _ _
      have f_notin_Y : f ∉ Y
      · apply disjoint_left.1 _ f_S
        apply disjoint_of_subset_right (subset_trans Y_sub_X' (inter_subset_right _ _)) S_j
      use (insert f Y)
      rw [mem_maximals_iff]
      refine' ⟨⟨Or.inr ⟨_, f, mem_insert f Y, f_S, _⟩, _⟩, _⟩
      · rw [mem_insert_iff]
        push_neg
        exact ⟨f_ne_e.symm, e_notin_Y⟩
      · rwa [insert_diff_self_of_not_mem f_notin_Y]
      · refine' ⟨subset_trans I_sub_Y (subset_insert _ _), insert_subset f_X _⟩
        exact subset_trans Y_sub_X' (inter_subset_left _ _)
      rintro y ⟨(y_ind | ⟨e_nY, l, l_y, l_s, l_ind⟩), I_sub_y, y_sub_X⟩ Y_sub_y
      have f_ground : f ∈ M.E
      · rw [←singleton_subset_iff] 
        apply (y_ind.subset (subset_trans _ Y_sub_y)).subset_ground
        rw [singleton_subset_iff]
        exact mem_insert f Y
      exact absurd f_ground (disjoint_left.1 S_j f_S)
      have y_l_mem_inter : y \ {l} ⊆ X ∩ M.E
      · apply subset_inter
        · exact subset_trans (diff_subset y {l}) y_sub_X
        · exact (l_ind.subset (subset_insert _ _)).subset_ground 
      have f_eq_l : f = l
      · by_contra h_f
        apply disjoint_left.1 S_j f_S
        apply (y_l_mem_inter _).2
        rw [mem_diff_singleton]
        exact ⟨Y_sub_y (mem_insert f Y), h_f⟩
      rw [f_eq_l]
      have Y_sub_y' : Y ⊆ y \ {l}
      · apply subset_diff_singleton (subset_trans (subset_insert f Y) Y_sub_y) _
        rwa [←f_eq_l]
      have Y_eq_yl: Y = y \ {l}
      · apply Y_max _ Y_sub_y'
        exact ⟨l_ind.subset (subset_insert _ _), subset_trans I'_sub_Y Y_sub_y', y_l_mem_inter⟩ 
      rw [Y_eq_yl, insert_diff_singleton, insert_eq_of_mem l_y]
      use Y
      rw [mem_maximals_iff]
      refine' ⟨⟨Or.inl Y_ind, I_sub_Y, subset_trans Y_sub_X' (inter_subset_left X M.E)⟩, _⟩
      rintro y ⟨(y_ind | ⟨e_nY, f, f_y, f_s, f_ind⟩), I_sub_y, y_sub_X⟩ Y_sub_y
      apply Y_max ⟨y_ind, _⟩ Y_sub_y
      · exact ⟨subset_trans (inter_subset_left _ _) I_sub_y, subset_inter y_sub_X y_ind.subset_ground⟩
      push_neg at e_ind
      apply absurd (Y_sub_y (e_ind _)) e_nY
      apply f_ind.subset (insert_subset_insert (subset_diff_singleton Y_sub_y _))
      apply disjoint_left.1 (disjoint_of_subset_right Y_ind.subset_ground S_j) f_s
    --part 2, I is unconventionally independent
    have e_ne_f : e ≠ f := (ne_of_mem_of_not_mem f_I e_nI).symm
    obtain ⟨Y, h_Y⟩:= M.maximality' (insert e (X ∩ M.E)) (insert_subset ?_ (inter_subset_right X M.E)) (insert e (I \ {f})) f_ind (insert_subset_insert ?_)
    · rw [mem_maximals_iff] at h_Y
      obtain ⟨⟨(Y_ind : M.Indep Y), I'_sub_Y, Y_sub_X'⟩, Y_max⟩ := h_Y
      use (insert f (Y \ {e}))
      refine' ⟨⟨Or.inr ⟨_, f, mem_insert f _, f_S, _⟩, _, _⟩, _⟩
      · rw [mem_insert_iff]
        push_neg
        exact ⟨e_ne_f, not_mem_diff_of_mem (mem_singleton _)⟩
      · have f_notin_Y : f ∉ (Y \ {e})
        · intro h_f
          apply disjoint_left.1 S_j f_S
          exact (mem_of_mem_insert_of_ne (Y_sub_X' ((mem_diff _).1 h_f).1) e_ne_f.symm).2
        rwa [insert_diff_self_of_not_mem f_notin_Y, insert_diff_singleton, insert_eq_of_mem (I'_sub_Y (mem_insert _ _))]
      · intro i i_in_I
        by_cases i_eq_f : i = f
        rw [i_eq_f]
        exact mem_insert _ _
        apply mem_insert_of_mem
        rw [mem_diff_singleton]
        refine' ⟨I'_sub_Y (mem_insert_of_mem _ _), ne_of_mem_of_not_mem i_in_I e_nI⟩
        exact mem_diff_singleton.2 ⟨i_in_I, i_eq_f⟩
      · apply insert_subset (I_sub_X f_I) _
        rintro y ⟨y_in_Y, (y_ne_e : y ≠ e)⟩
        apply inter_subset_left X M.E
        exact mem_of_mem_insert_of_ne (Y_sub_X' y_in_Y) y_ne_e
      rintro y ⟨(y_ind | ⟨e_nY, l, l_y, l_s, l_ind⟩), I_sub_y, y_sub_X⟩ Y_sub_y
      · apply absurd _ (disjoint_left.1 S_j f_S)
        rw [←singleton_subset_iff]
        apply (y_ind.subset _).subset_ground
        rw [singleton_subset_iff]
        exact Y_sub_y (mem_insert f _)
      · have y_l_mem_inter : y \ {l} ⊆ X ∩ M.E
        · apply subset_inter
          · exact subset_trans (diff_subset y {l}) y_sub_X
          · exact (l_ind.subset (subset_insert _ _)).subset_ground 
        have f_eq_l : f = l
        · by_contra h_f
          apply disjoint_left.1 S_j f_S
          apply (y_l_mem_inter _).2
          rw [mem_diff_singleton]
          refine ⟨Y_sub_y (mem_insert f _), h_f⟩
        rw [f_eq_l]
        have Y_eq_y_e_l : Y = insert e (y \ {l})
        · apply Y_max ⟨l_ind, _, _⟩ _
          rintro x (x_eq_e | ⟨x_in_I, (x_ne_f : x ≠ f)⟩)
          · rw [x_eq_e]
            exact mem_insert e _
            -/