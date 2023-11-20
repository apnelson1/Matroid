import Matroid.Simple
import Matroid.Closure
import Matroid.ForMathlib.Other

namespace Matroid
open Set

@[pp_dot] def Modular_pair (M : Matroid α) (X Y : Set α) : Prop :=
    ∃ B, M.Modular {X, Y} B

@[pp_dot] def Modular_set (M : Matroid α) (X : Set α) : Prop :=
    ∀ Y, M.Flat Y → M.Modular_pair X Y

@[pp_dot] def Modular_matroid (M : Matroid α) : Prop :=
    ∀ X, M.Flat X → M.Modular_set X

def Modular_flat (M : Matroid α) (X : Set α) : Prop :=
    ∀ Y, M.Flat Y → Modular_pair M X Y

def Modular_cut (M : Matroid α) (C : Set (Set α)) : Prop :=
    (∀ F ∈ C, M.Flat F) ∧ (∀ F F', F ∈ C → F ⊆ F' → M.Flat F' → F' ∈ C) ∧
    (∀ F₁ F₂, F₁ ∈ C → F₂ ∈ C → M.Modular_pair F₁ F₂ → F₁ ∩ F₂ ∈ C)

theorem union_insert_eq {A : Set α} {b c : α} :
    (insert b A) ∪ (insert c A) = insert c (insert b A) := by
  rw [insert_eq, insert_eq, ←union_union_distrib_right, @union_comm _ {b} _,
    union_assoc, ←insert_eq, ←insert_eq]

theorem inter_insert_eq {A : Set α} {b c : α} (hne : b ≠ c):
    (insert b A) ∩ (insert c A) = A := by
  rw [insert_eq, insert_eq, ←union_distrib_right, Disjoint.inter_eq _, empty_union]
  rwa [disjoint_singleton]




@[simp] theorem Modular_ground (M : Matroid α) : M.Modular_set M.E := by
  intro Y Y_flat
  obtain ⟨B, h_B⟩ := M.exists_basis Y
  obtain ⟨B', B'_base, B_sub_B'⟩ := h_B.indep
  refine' ⟨B', B'_base, _⟩
  have B'_inter : B' ∩ Y = B
  · apply subset_antisymm _ _
    · rintro x ⟨x_B, x_Y⟩
      by_contra h_f
      apply ((B'_base.indep).subset (insert_subset x_B B_sub_B')).not_dep
      exact h_B.insert_dep ⟨x_Y, h_f⟩
    · intro x x_B
      exact ⟨B_sub_B' x_B, h_B.subset x_B⟩
  rintro X X_sub X_ne
  obtain (X_eq_E | X_eq_Y | X_eq_pair) := (Nonempty.subset_pair_iff X_ne).1 X_sub
  · rwa [X_eq_E, sInter_singleton, inter_eq_self_of_subset_right B'_base.subset_ground,
     basis_ground_iff]
  · rwa [X_eq_Y, sInter_singleton, inter_comm, B'_inter]
  · rwa [X_eq_pair, sInter_pair, inter_eq_self_of_subset_right Y_flat.subset_ground, inter_comm,
     B'_inter]

@[simp] theorem Modular_pair_comm (h : Modular_pair M X Y) : Modular_pair M Y X := by
  obtain ⟨B, B_Base, B_modular⟩ := h
  refine' ⟨B, B_Base, _⟩
  intro Ys Ys_sub Ys_ne
  rw [pair_comm] at Ys_sub
  exact B_modular Ys_sub Ys_ne

@[simp] theorem Modular_cl_empty (M : Matroid α) : Modular_flat M (M.cl ∅) := by
  intro Y Y_flat
  obtain ⟨B, h_B⟩ := M.exists_basis Y
  obtain ⟨B', B'_base, B_sub_B'⟩ := h_B.indep
  have B'_inter : Y ∩ B' = B
  · apply subset_antisymm _ _
    · rintro x ⟨x_B, x_Y⟩
      by_contra h_f
      apply ((B'_base.indep).subset (insert_subset x_Y B_sub_B')).not_dep
      exact h_B.insert_dep ⟨x_B, h_f⟩
    · intro x x_B
      exact ⟨h_B.subset x_B, B_sub_B' x_B⟩
  refine' ⟨B', B'_base, fun Ys Ys_sub Ys_ne ↦ _⟩
  obtain (Ys_eq_cl | Ys_eq_Y | Ys_eq_pair) := (Nonempty.subset_pair_iff Ys_ne).1 Ys_sub
  · rw [Ys_eq_cl, sInter_singleton, Disjoint.inter_eq _, empty_basis_iff]
    · rw [disjoint_left]
      intro a a_cl a_B'
      rw [←loop_iff_mem_cl_empty, loop_iff_not_mem_base_forall] at a_cl
      exact a_cl B' B'_base a_B'
  · rwa [Ys_eq_Y, sInter_singleton, B'_inter]
  · rw [Ys_eq_pair, sInter_pair, ←Y_flat.cl, inter_eq_self_of_subset_left
    (M.cl_subset_cl (empty_subset _)), Disjoint.inter_eq _, empty_basis_iff]
    rw [disjoint_left]
    intro a a_cl a_B'
    rw [←loop_iff_mem_cl_empty, loop_iff_not_mem_base_forall] at a_cl
    exact a_cl B' B'_base a_B'

theorem Modular_pair_closure (M : Matroid α) (X Y : Set α) (h_union : M.Indep (X ∪ Y)) :
    M.Modular_pair (M.cl X) (M.cl Y) := by
  obtain ⟨B, B_Base, B_sub⟩ := h_union
  refine' ⟨B, B_Base, fun Ys Ys_sub Ys_ne ↦ _⟩
  obtain (eq_X | eq_Y | eq_inter) := (Nonempty.subset_pair_iff Ys_ne).1 Ys_sub
  · rw [eq_X, sInter_singleton, B_Base.indep.cl_inter_eq_self_of_subset
   (union_subset_iff.1 B_sub).1]
    exact (((M.indep_iff_subset_base).2 ⟨B, B_Base, B_sub⟩).subset
     (subset_union_left _ _)).basis_cl
  · rw [eq_Y, sInter_singleton, B_Base.indep.cl_inter_eq_self_of_subset
   (union_subset_iff.1 B_sub).2]
    exact (((M.indep_iff_subset_base).2 ⟨B, B_Base, B_sub⟩).subset
     (subset_union_right _ _)).basis_cl
  · rw [eq_inter, sInter_pair, ←Indep.cl_inter_eq_inter_cl, B_Base.indep.cl_inter_eq_self_of_subset]
    · exact Indep.basis_cl (((M.indep_iff_subset_base).2 ⟨B, B_Base, B_sub⟩).subset
       (subset_union_of_subset_right (inter_subset_right _ _) _))
    · exact subset_trans (inter_subset_left _ _ ) (subset_trans (subset_union_left _ _) B_sub)
    · exact (M.indep_iff_subset_base).2 ⟨B, B_Base, B_sub⟩

open Classical
def matroid_of_cut (M : Matroid α) (C : Set (Set α)) (hC : M.Modular_cut C) (e : α) (e_nE : e ∉ M.E) :
    Matroid α :=
  matroid_of_indep (insert e M.E)
  (fun X ↦ if (e ∈ X) then (M.Indep (X \ {e}) ∧ M.cl (X \ {e}) ∉ C) else M.Indep X)
  (by
    dsimp
    rw [if_neg (not_mem_empty _)]
    exact M.empty_indep
  )
  (by
    intro I J J_ind I_sub
    split_ifs with e_mem_I
    · rw [if_pos (I_sub e_mem_I)] at J_ind
      refine' ⟨J_ind.1.subset (diff_subset_diff_left I_sub), fun clI_mem ↦ _⟩
      apply J_ind.2 (hC.2.1 (M.cl (I \ {e})) (M.cl (J \ {e}))
       clI_mem (M.cl_subset_cl (diff_subset_diff_left I_sub)) (M.cl_flat (J \ {e})))
    split_ifs at J_ind with e_mem_J
    · exact J_ind.1.subset (subset_diff_singleton I_sub e_mem_I)
    exact J_ind.subset I_sub
  )
  (by
    rintro I J I_ind I_nmax ⟨J_ind, J_max⟩
    have J_base_of_not_mem_e : e ∉ J → M.Base J
    · intro e_in_J
      rw [base_iff_maximal_indep]
      dsimp at J_ind
      rw [if_neg e_in_J] at J_ind
      refine' ⟨J_ind, fun X X_ind X_sub ↦ _⟩
      apply subset_antisymm X_sub (J_max _ X_sub)
      dsimp
      rwa [if_neg (not_mem_subset (X_ind.subset_ground) e_nE)]
    rw [mem_maximals_iff] at I_nmax
    push_neg at I_nmax
    obtain ⟨Y, Y_ind, I_sub_Y, I_ne_Y⟩ := I_nmax I_ind
    dsimp at Y_ind J_ind
    split_ifs at I_ind with e_in_I
    · rw [if_pos (I_sub_Y e_in_I)] at Y_ind
      split_ifs at J_ind with e_in_J --hardest case i think, leave for last
      · have J_b : M.Basis (J \ {e}) ((I ∪ J) \ {e})


      have I_nb : ¬ M.Base (I \ {e})
      · intro I_Base
        apply (I_Base.dep_of_ssubset _ Y_ind.1.subset_ground).not_indep Y_ind.1
        rw [ssubset_iff_subset_ne]
        refine' ⟨diff_subset_diff_left I_sub_Y, fun diff_eq ↦ _⟩
        apply I_ne_Y (subset_antisymm I_sub_Y _)
        intro y y_in_Y
        obtain (rfl | hne) := eq_or_ne y e
        · assumption
        apply diff_subset I {e}
        rw [diff_eq]
        exact ⟨y_in_Y, hne⟩
      obtain ⟨j₂, hj₂⟩ := I_ind.1.exists_insert_of_not_base I_nb (J_base_of_not_mem_e e_in_J)
      rw [diff_diff_right, Disjoint.inter_eq (disjoint_singleton_right.2 e_in_J), union_empty] at hj₂
      by_cases j₂I_b : M.Base (insert j₂ (I \ {e}))
      · refine' ⟨j₂, hj₂.1, _⟩
        dsimp
        rw [if_pos ((subset_insert _ _) e_in_I), ←insert_diff_singleton_comm (ne_of_mem_of_not_mem hj₂.1.1 e_in_J),
         and_iff_right hj₂.2]
        obtain ⟨y, hy⟩ := Set.exists_of_ssubset (ssubset_iff_subset_ne.2 ⟨I_sub_Y, I_ne_Y⟩)
        obtain (rfl | ne) := eq_or_ne j₂ y
        · intro hf
          apply Y_ind.2 (hC.2.1 _ _ hf (M.cl_subset_cl _) (M.cl_flat _))
          exact (insert_subset (⟨hy.1, ne_of_mem_of_not_mem hj₂.1.1 e_in_J⟩) (diff_subset_diff_left I_sub_Y))
        have y_notin : y ∉ insert j₂ (I \ {e})
        · rw [mem_insert_iff, not_or, mem_diff, not_and_or]
          exact ⟨ne.symm, Or.inl hy.2⟩
        have base_insert:= @Matroid.Base.exchange_base_of_indep _ _ _ _ j₂ j₂I_b y_notin
        rw [insert_diff_self_of_not_mem (not_mem_subset (diff_subset _ _) hj₂.1.2)] at base_insert
        rw [j₂I_b.cl_eq]
        rw [Spanning.cl_eq _] at Y_ind
        · exact Y_ind.2
        have insert_y_subset_Y : insert y (I \ {e}) ⊆ Y \ {e}
        · rw [insert_diff_singleton_comm (ne_of_mem_of_not_mem e_in_I hy.2).symm]
          exact diff_subset_diff_left (insert_subset hy.1 I_sub_Y)
        apply Base.superset_spanning (base_insert (Y_ind.1.subset insert_y_subset_Y))
         insert_y_subset_Y Y_ind.1.subset_ground
      obtain ⟨j₁, j₁_mem, j₁_ind⟩:=hj₂.2.exists_insert_of_not_base j₂I_b (J_base_of_not_mem_e e_in_J)
      have hne : j₂ ≠ j₁:= fun (rfl) ↦ j₁_mem.2 (mem_insert _ _)
      --case involving finding 2 to add from j and using modularity to contradict I independence, not so
      --bad
      by_cases j₁_cl_mem_c : M.cl (insert j₁ (I \ {e})) ∈ C
      · by_cases j₂_cl_mem_c : M.cl (insert j₂ (I \ {e})) ∈ C
        · have pair := M.Modular_pair_closure (insert j₂ (I \ {e})) (insert j₁ (I \ {e}))
          rw [union_insert_eq] at pair
          have inter_mem_c:= hC.2.2 _ _ j₂_cl_mem_c j₁_cl_mem_c (pair j₁_ind)
          rw [←Indep.cl_inter_eq_inter_cl _, inter_insert_eq hne] at inter_mem_c
          · exact absurd inter_mem_c I_ind.2
          · rwa [union_insert_eq]
        refine' ⟨j₂, hj₂.1, _⟩
        dsimp
        rw [if_pos (mem_insert_of_mem _ e_in_I), ←insert_diff_singleton_comm
         (ne_of_mem_of_not_mem hj₂.1.1 e_in_J) _]
        exact ⟨j₁_ind.subset (subset_insert _ _), j₂_cl_mem_c⟩
      refine' ⟨j₁, ⟨j₁_mem.1, fun hf ↦ j₁_mem.2 (mem_insert_of_mem _ ⟨hf, ne_of_mem_of_not_mem
       j₁_mem.1 e_in_J⟩)⟩, _⟩
      dsimp
      rw [if_pos (mem_insert_of_mem _ e_in_I), ←insert_diff_singleton_comm
       (ne_of_mem_of_not_mem j₁_mem.1 e_in_J) _, ]
      exact ⟨j₁_ind.subset (insert_subset_insert (subset_insert _ _)), j₁_cl_mem_c⟩
    split_ifs at J_ind with e_in_J --2nd hardest case
    · by_cases cl_I_mem : M.cl I ∈ C --if cl(I) ∈ C, and every member of J-e cant be added, then J ⊂ cl(I)
      · by_contra' h_f
        have J_diff_sub_cl_I : J \ {e} ⊆ M.cl I
        · rintro j ⟨j_J, (j_ne : j ≠ e)⟩
          rw [I_ind.mem_cl_iff, or_comm, or_iff_not_imp_left]
          intro j_nI
          have not_ind:= h_f j ⟨j_J, j_nI⟩
          rw [if_neg _] at not_ind
          · apply dep_of_not_indep not_ind _
            rintro x (x_eq | x_sub)
            · rw [x_eq]
              apply (J_ind.1.subset_ground) ⟨j_J, j_ne⟩
            · apply I_ind.subset_ground x_sub
          rintro (e_eq | e_mem)
          · exact j_ne e_eq.symm
          · exact e_in_I e_mem
        have I_J_exch : ∃ i ∈ I \ (J \ {e}), M.Indep (insert i (J \ {e}))
        · apply J_ind.1.exists_insert_of_not_basis (subset_union_left _ I)
          · intro h_f
            apply J_ind.2 (hC.2.1 _ _ cl_I_mem _ (M.cl_flat _))
            rw [h_f.cl_eq_cl]
            exact M.cl_subset_cl (subset_union_right _ _)
          rw [basis_iff_indep_subset_cl]
          refine' ⟨I_ind, subset_union_right _ _, fun x ↦ _⟩
          rintro (x_J | x_I)
          · exact J_diff_sub_cl_I x_J
          · exact M.mem_cl_of_mem x_I
        obtain ⟨i, i_mem, i_ind⟩ := I_J_exch
        split_ifs at Y_ind with e_in_Y
        · apply Y_ind.2 (hC.2.1 _ _ cl_I_mem (M.cl_subset_cl _) (M.cl_flat _))
          exact subset_diff_singleton I_sub_Y e_in_I
        have Y_insert : ∃ y ∈ Y \ I, M.Indep (insert y (insert i (J \ {e})))
        · obtain ⟨y, hy⟩ := Set.exists_of_ssubset (ssubset_iff_subset_ne.2 ⟨I_sub_Y, I_ne_Y⟩)
          refine' ⟨y, ⟨hy.1, hy.2⟩, _⟩
          rw [i_ind.insert_indep_iff_of_not_mem, mem_diff]
          · refine' ⟨Y_ind.subset_ground hy.1, fun y_cl ↦ _⟩
            obtain (mem_c | y_in_I) := I_ind.insert_indep_iff.1 (Y_ind.subset
              (insert_subset hy.1 I_sub_Y))
            · apply mem_c.2 (cl_subset_cl_of_subset_cl (insert_subset (M.mem_cl_of_mem i_mem.1
              I_ind.subset_ground) J_diff_sub_cl_I) y_cl)
            · exact hy.2 y_in_I
          · rintro (y_I | ⟨y_J, (y_ne_e : y ≠ e)⟩)
            · apply hy.2
              rw [y_I]
              exact i_mem.1
            apply h_f y ⟨y_J, hy.2⟩
            rw [mem_insert_iff, or_iff_left e_in_I, if_neg y_ne_e.symm]
            apply Y_ind.subset (insert_subset hy.1 I_sub_Y)
        obtain ⟨y, y_mem, y_ind⟩ := Y_insert
        have pair_cl:= hC.2.2 (M.cl (insert i (J \ {e}))) (M.cl (insert y (J \ {e})))
        have union_indep : M.Indep ((insert i (J \ {e})) ∪ (insert y (J \ {e})))
        · rwa [union_insert_eq]
        rw [←Indep.cl_inter_eq_inter_cl union_indep, inter_insert_eq (ne_of_mem_of_not_mem i_mem.1 y_mem.2)] at pair_cl
        apply J_ind.2 (pair_cl _ _ _)
        · by_contra insert_not_mem
          apply (J \ {e}).ne_insert_of_not_mem (J \ {e}) i_mem.2 (subset_antisymm (subset_insert _ _) _)
          rw [insert_diff_singleton_comm (ne_of_mem_of_not_mem i_mem.1 e_in_I) _] at insert_not_mem ⊢
          apply diff_subset_diff_left (J_max _ (subset_insert _ _))
          dsimp
          rw [if_pos (mem_insert_of_mem _ e_in_J)]
          refine' ⟨y_ind.subset (subset_trans _ (subset_insert _ _)), insert_not_mem⟩
          rw [insert_diff_singleton_comm (ne_of_mem_of_not_mem i_mem.1 e_in_I) _]
        · by_contra insert_not_mem
          apply (J \ {e}).ne_insert_of_not_mem (J \ {e}) _ (subset_antisymm (subset_insert y _) _)
          · rintro ⟨y_J, (y_ne_e : y ≠ e)⟩
            apply h_f y ⟨y_J, y_mem.2⟩
            rw [mem_insert_iff, or_iff_left e_in_I, if_neg y_ne_e.symm]
            apply Y_ind.subset (insert_subset y_mem.1 I_sub_Y)
          rw [insert_diff_singleton_comm (ne_of_mem_of_not_mem y_mem.1 e_in_Y)] at insert_not_mem ⊢
          apply diff_subset_diff_left (J_max _ (subset_insert _ _))
          dsimp
          rw [if_pos (mem_insert_of_mem _ e_in_J)]
          rw [insert_comm] at y_ind
          refine' ⟨y_ind.subset (subset_trans _ (subset_insert _ _)), insert_not_mem⟩
          rw [insert_diff_singleton_comm (ne_of_mem_of_not_mem y_mem.1 e_in_Y)]
        apply M.Modular_pair_closure _ _ union_indep
      refine' ⟨e, ⟨e_in_J, e_in_I⟩, _⟩
      dsimp
      rw [if_pos (mem_insert e I), insert_diff_self_of_not_mem e_in_I]
      exact ⟨I_ind, cl_I_mem⟩
    have I_not_base : ¬ M.Base I --easiest case, e is in neither - requires some effort to show I not a base
    · intro h_f
      split_ifs at Y_ind with e_in_Y
      · rw [Spanning.cl_eq _] at Y_ind
        · apply (ne_insert_of_not_mem J e_in_J) (subset_antisymm (subset_insert e J) (J_max _ (subset_insert e J)))
          dsimp at J_ind ⊢
          rw [if_pos (mem_insert _ _), insert_diff_self_of_not_mem e_in_J, (J_base_of_not_mem_e e_in_J).cl_eq]
          exact ⟨J_ind, Y_ind.2⟩
        rw [spanning_iff_superset_base (Y_ind.1.subset_ground)]
        refine' ⟨I, h_f, subset_diff_singleton I_sub_Y e_in_I⟩
      apply (h_f.dep_of_ssubset (I_ne_Y.ssubset_of_subset I_sub_Y)
        Y_ind.subset_ground).not_indep Y_ind
    obtain ⟨x, x_mem, x_ind⟩ := I_ind.exists_insert_of_not_base I_not_base (J_base_of_not_mem_e e_in_J)
    refine' ⟨x, x_mem, _⟩
    dsimp
    rwa [if_neg _]
    rw [mem_insert_iff]; push_neg
    exact ⟨(ne_of_mem_of_not_mem x_mem.1 e_in_J).symm, e_in_I⟩








  )
  sorry sorry
