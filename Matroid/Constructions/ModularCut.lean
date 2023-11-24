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

def Modular_cut' (M : Matroid α) (C : Set (Set α)) : Prop := --old version for finite with pairs
    (∀ F ∈ C, M.Flat F) ∧ (∀ F F', F ∈ C → F ⊆ F' → M.Flat F' → F' ∈ C) ∧
    (∀ F₁ F₂, F₁ ∈ C → F₂ ∈ C → M.Modular_pair F₁ F₂ → F₁ ∩ F₂ ∈ C)

def Modular_cut (M : Matroid α) (C : Set (Set α)) : Prop := --version with infinite modular sets
    (∀ F ∈ C, M.Flat F) ∧ (∀ F F', F ∈ C → F ⊆ F' → M.Flat F' → F' ∈ C) ∧
    (∀ X ⊆ C, (∃ B, M.Modular X B) → sInter X ∈ C)

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

theorem Modular_cut_pair {M : Matroid α} {C : Set (Set α)} (hC : M.Modular_cut C) (a b : α)
    (X : Set α) (hne : a ≠ b) (h_ind : M.Indep (insert a (insert b X))) (h_a : M.cl (insert a X) ∈ C)
    (h_b : M.cl (insert b X) ∈ C) : M.cl X ∈ C := by
  rw [←union_insert_eq] at h_ind
  have ab_cl_inter_eq : sInter {M.cl (insert b X), M.cl (insert a X)} = M.cl X
  · rw [sInter_pair, ←h_ind.cl_inter_eq_inter_cl, inter_insert_eq hne.symm]
  rw [←ab_cl_inter_eq]
  apply hC.2.2
  · rw [pair_subset_iff]
    exact ⟨h_b, h_a⟩
  rw [union_insert_eq] at h_ind
  have:= h_ind
  obtain ⟨B, B_base, sub_B⟩ := this
  refine' ⟨B, B_base, fun Y Y_sub (Y_none : Y.Nonempty) ↦ _⟩
  obtain (rfl | rfl | rfl) := (Nonempty.subset_pair_iff Y_none).1 Y_sub
  · rw [sInter_singleton, B_base.indep.cl_inter_eq_self_of_subset ((subset_insert _ _).trans sub_B)]
    exact (h_ind.subset (subset_insert _ _)).basis_cl
  · rw [insert_comm] at h_ind sub_B
    rw [sInter_singleton, B_base.indep.cl_inter_eq_self_of_subset ((subset_insert _ _).trans sub_B)]
    exact (h_ind.subset (subset_insert _ _)).basis_cl
  rw [ab_cl_inter_eq, B_base.indep.cl_inter_eq_self_of_subset ((subset_insert _ _).trans ((subset_insert _ _).trans sub_B))]
  exact (h_ind.subset ((subset_insert _ _).trans (subset_insert _ _))).basis_cl

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
    sorry
    /-
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
      --proof sketch: extend I to basis in J. If extension is size 0, win by maximality
      --of J. If extension is size >2, win by modularity to show cl(I)∈C. Thus, extension
      --is of size 1. If cl(I)⊆cl(J), then win by cl(J)∉C. Thus cl(I)⊈cl(J), and ∃ i to be
      --added to J. Then, note that I∪J base, as if not find element y outside and use
      --modularity of J+i+y and maximality to contradict cl(J)∉C. Once we have J∪I base
      --we also have I+j base, and as I is nonmaximal we may find some x where cl(I+x)∉C
      --but since I+x base then M.E∉C and we win
      --
      · by_contra' h_f
        have J_insert_mem_C : ∀ x ∉ J, M.Indep (insert x (J \ {e})) → M.cl (insert x (J \ {e})) ∈ C
        · intro x x_notin_J x_ind
          by_contra not_mem_C
          apply (ne_insert_of_not_mem _ x_notin_J) (subset_antisymm (subset_insert _ _) (J_max _ (subset_insert _ _)))
          dsimp
          rw [if_pos (mem_insert_of_mem _ e_in_J), ←insert_diff_singleton_comm (ne_of_mem_of_not_mem e_in_J x_notin_J).symm]
          exact ⟨x_ind, not_mem_C⟩
        obtain ⟨y, hy⟩ := Set.exists_of_ssubset (ssubset_iff_subset_ne.2 ⟨I_sub_Y, I_ne_Y⟩)
        have y_ind : M.Indep ((insert y I) \ {e}) ∧ M.cl ((insert y I) \ {e}) ∉ C
        · refine' ⟨Y_ind.1.subset (diff_subset_diff_left (insert_subset hy.1 I_sub_Y)),
           fun cl_mem_C ↦ _⟩
          exact Y_ind.2 (hC.2.1 _ _ cl_mem_C (M.cl_subset_cl (diff_subset_diff_left (insert_subset
           hy.1 I_sub_Y))) (M.cl_flat _))
        have y_notin_J : y ∉ J
        · intro y_in_J
          apply h_f y ⟨y_in_J, hy.2⟩ _
          rwa [if_pos (mem_insert_of_mem y e_in_I)]
        have y_ground := (Y_ind.1.subset_ground (mem_diff_of_mem hy.1 (ne_of_mem_of_not_mem e_in_J y_notin_J).symm))
        have x := I_ind.1.subset_basis_of_subset (diff_subset_diff_left (subset_union_left I J)) ?_
        · obtain ⟨I', I'_basis, I_sub_I'⟩ := x
          have : (I \ {e} ⊂ I')
          · apply Ne.ssubset_of_subset _ I_sub_I'
            rintro rfl
            apply insert_ne_self.2 y_notin_J (subset_antisymm (J_max _ (subset_insert _ _)) (subset_insert _ _))
            dsimp
            rw [if_pos (mem_insert_of_mem _ e_in_J), ←insert_diff_singleton_comm
             (ne_of_mem_of_not_mem e_in_J y_notin_J).symm, ←J_ind.1.not_mem_cl_iff_of_not_mem _]
            refine' ⟨not_mem_subset (M.cl_subset_cl (diff_subset_diff_left (subset_union_right I J))) _, _⟩
            · rw [←I'_basis.cl_eq_cl, I_ind.1.not_mem_cl_iff_of_not_mem (not_mem_subset (diff_subset _ _) hy.2),
              insert_diff_singleton_comm (ne_of_mem_of_not_mem e_in_J y_notin_J).symm]
              exact y_ind.1
            rw [insert_diff_singleton_comm (ne_of_mem_of_not_mem e_in_J y_notin_J).symm]
            intro cl_mem_C
            apply y_ind.2 (hC.2.1 _ _ cl_mem_C _ (M.cl_flat _))
            rw [←insert_diff_singleton_comm (ne_of_mem_of_not_mem e_in_J y_notin_J).symm I,
             ←cl_insert_cl_eq_cl_insert, I'_basis.cl_eq_cl, cl_insert_cl_eq_cl_insert,
              ←insert_diff_singleton_comm (ne_of_mem_of_not_mem e_in_J y_notin_J).symm,
              ]
            · apply M.cl_subset_cl (insert_subset_insert (diff_subset_diff_left (subset_union_right _ _)))
            exact not_mem_subset (diff_subset _ _) y_notin_J
          obtain ⟨a, a_not_mem, a_insert_sub⟩ := ssubset_iff_insert.1 this
          have a_mem_JI : a ∈ J \ I
          · obtain ⟨(aI | aJ), a_ne_e⟩:= I'_basis.subset (a_insert_sub (mem_insert a _))
            apply absurd (⟨aI, a_ne_e⟩ : (a ∈ I \ {e})) a_not_mem
            apply (mem_diff _).2 ⟨aJ, _⟩
            intro aI
            apply a_not_mem ⟨aI, a_ne_e⟩
          obtain (ssubset | rfl) := ssubset_or_eq_of_subset a_insert_sub
          · obtain ⟨b, b_not_mem, b_insert_sub⟩ := ssubset_iff_insert.1 ssubset
            have:= hC.2.2 (M.cl (insert a (I \ {e}))) (M.cl (insert b (I \ {e}))) ?_ ?_ ?_
            · rw [←Indep.cl_inter_eq_inter_cl, inter_insert_eq] at this
              · exact I_ind.2 this
              · exact (ne_of_mem_of_not_mem (mem_insert a _) b_not_mem)
              rw [union_insert_eq]
              exact I'_basis.indep.subset b_insert_sub
            · have:= h_f a a_mem_JI
              · rw [if_pos (mem_insert_of_mem _ e_in_I), not_and, not_not_mem, ←insert_diff_singleton_comm] at this
                · exact this (I'_basis.indep.subset a_insert_sub)
                exact ne_of_mem_of_not_mem ((I'_basis.indep.subset a_insert_sub).subset_ground (mem_insert _ _)) e_nE
            · have:= h_f b ?_
              rw [insert_comm] at b_insert_sub
              · rw [if_pos (mem_insert_of_mem _ e_in_I), not_and, not_not_mem, ←insert_diff_singleton_comm] at this
                · exact this (I'_basis.indep.subset ((subset_insert _ _).trans b_insert_sub))
                exact ne_of_mem_of_not_mem ((I'_basis.indep.subset b_insert_sub).subset_ground (mem_insert_of_mem _ (mem_insert _ _))) e_nE
              obtain ⟨(bI | bJ), b_ne_e⟩:= I'_basis.subset (b_insert_sub (mem_insert b _))
              apply absurd (⟨bI, b_ne_e⟩ : (b ∈ I \ {e})) _
              apply not_mem_subset (subset_insert _ _) b_not_mem
              apply (mem_diff _).2 ⟨bJ, _⟩
              intro bI
              apply b_not_mem (mem_insert_of_mem _ ⟨bI, b_ne_e⟩)
            apply M.Modular_pair_closure _ _
            rw [union_insert_eq]
            exact I'_basis.indep.subset b_insert_sub
          have J_not_basis : ¬ M.Basis (J \ {e}) ((I ∪ J) \ {e})
          · intro J_basis
            apply h_f a a_mem_JI
            rw [if_pos (mem_insert_of_mem _ e_in_I), ←insert_diff_singleton_comm, I'_basis.cl_eq_cl,
             ←J_basis.cl_eq_cl]
            exact ⟨I'_basis.indep, J_ind.2⟩
            exact (ne_of_mem_of_not_mem e_in_I a_mem_JI.2).symm
          obtain ⟨i, hi⟩ := J_ind.1.exists_insert_of_not_basis (diff_subset_diff_left (subset_union_right _ _)) J_not_basis I'_basis
          have I'_base : M.Base (insert a (I \ {e}))
          · by_contra I'_not_base
            obtain ⟨B, hB⟩ := M.exists_base
            obtain ⟨b, hb⟩ := I'_basis.indep.exists_insert_of_not_base I'_not_base hB
            have b_notin_union : b ∉ I ∪ J
            · intro b_mem_union
              have : b ∈ (I ∪ J) \ {e}
              · rwa [mem_diff_singleton, and_iff_left (ne_of_mem_of_not_mem (hB.subset_ground hb.1.1) e_nE)]
              apply ((I'_basis.indep.insert_indep_iff_of_not_mem hb.1.2).1 hb.2).2
              rw [I'_basis.cl_eq_cl]
              apply M.mem_cl_of_mem this I'_basis.subset_ground
            have bi_J_indep : M.Indep (insert b (insert i (J \ {e})))
            · rw [hi.2.insert_indep_iff, mem_diff _, and_iff_right (hB.subset_ground hb.1.1)]
              rw [I'_basis.indep.insert_indep_iff_of_not_mem hb.1.2, I'_basis.cl_eq_cl] at hb
              apply Or.inl (not_mem_subset (M.cl_subset_cl _) hb.2.2)
              rw [insert_diff_singleton_comm (ne_of_mem_of_not_mem (hi.2.subset_ground (mem_insert _ _)) e_nE)]
              apply diff_subset_diff_left (insert_subset _ (subset_union_right _ _))
              obtain (rfl | i_Jd) := hi.1.1
              · apply (Or.inr a_mem_JI.1)
              apply (Or.inl i_Jd.1)
            have:= hC.2.2 (M.cl (insert i (J \ {e}))) (M.cl (insert b (J \ {e}))) ?_ ?_ ?_
            · rw [←Indep.cl_inter_eq_inter_cl, inter_insert_eq] at this
              exact J_ind.2 this
              exact ne_of_mem_of_not_mem hi.1.1 hb.1.2
              rwa [union_insert_eq]
            · apply J_insert_mem_C i _ hi.2
              intro i_J
              obtain (rfl | ine) := eq_or_ne i e
              · obtain (rfl | mem) := hi.1.1
                apply a_mem_JI.2 e_in_I
                apply mem.2 (by rfl)
              apply hi.1.2 ⟨i_J, ine⟩
            · apply J_insert_mem_C b (not_mem_subset (subset_union_right _ _) b_notin_union) _
              rw [insert_comm] at bi_J_indep
              exact bi_J_indep.subset (subset_insert _ _)
            · apply M.Modular_pair_closure
              rwa [union_insert_eq]
          have yI_base : M.Base (insert y (I \ {e}))
          · have base_insert:= @Matroid.Base.exchange_base_of_indep _ _ _ y a I'_base
            rw [insert_diff_self_of_not_mem a_not_mem] at base_insert
            apply base_insert
            · rintro (rfl | y_mem)
              · exact y_notin_J a_mem_JI.1
              exact hy.2 y_mem.1
            rw [insert_diff_singleton_comm (ne_of_mem_of_not_mem y_ground e_nE)]
            exact y_ind.1
          apply h_f a a_mem_JI
          rw [if_pos (mem_insert_of_mem _ e_in_I), ←insert_diff_singleton_comm (ne_of_mem_of_not_mem e_in_I a_mem_JI.2).symm,
          I'_base.cl_eq, ←yI_base.cl_eq, insert_diff_singleton_comm (ne_of_mem_of_not_mem y_ground e_nE)]
          exact ⟨I'_base.indep, y_ind.2⟩
        rintro x ⟨(x_I | x_J), (hne : x ≠ e)⟩
        · exact I_ind.1.subset_ground ⟨x_I, hne⟩
        exact J_ind.1.subset_ground ⟨x_J, hne⟩
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
    -/
)
(by
  intro X X_sub Y Y_ind Y_sub_X
  obtain (rfl | C_none) := eq_or_ne C ∅
  · split_ifs at Y_ind with e_in_Y
    · obtain ⟨B, hB⟩ := Y_ind.1.subset_basis_of_subset (diff_subset_diff_left Y_sub_X)
      refine' ⟨insert e B, _⟩
      rw [mem_maximals_iff]
      dsimp
      rw [if_pos (mem_insert e B), insert_diff_self_of_not_mem ((not_mem_subset hB.1.left_subset_ground) e_nE),
      and_iff_left (not_mem_empty _), and_iff_right hB.1.indep]
      refine' ⟨⟨_, _⟩, fun I I_ind sub_I ↦ _⟩
      · intro y y_mem
        obtain (rfl | hne) := eq_or_ne y e
        · exact mem_insert _ _
        apply hB.2.trans (subset_insert _ _) ⟨y_mem, hne⟩
      · rintro x (rfl | x_B)
        · exact Y_sub_X e_in_Y
        exact (hB.1.subset x_B).1
      rw [if_pos (sub_I (mem_insert _ _))] at I_ind
      apply subset_antisymm sub_I _
      obtain (rfl):= hB.1.eq_of_subset_indep I_ind.1.1 _ (diff_subset_diff_left I_ind.2.2)
      · simp
    by_cases e_in_X : e ∈ X
    · have Y_sub : Y ⊆ X \ {e} := subset_diff_singleton Y_sub_X e_in_Y
      obtain ⟨B, hB⟩ := Y_ind.subset_basis_of_subset Y_sub
      refine' ⟨insert e B, _⟩
      rw [mem_maximals_iff]
      dsimp
      rw [if_pos (mem_insert _ _), and_iff_left (not_mem_empty _), and_iff_right (hB.2.trans (subset_insert _ _))]
      refine' ⟨⟨_, _⟩, fun I I_ind sub_I ↦ _⟩
      · simp [hB, hB.1.indep.subset]
      · have:= hB.1.subset
        rw [subset_diff] at this
        apply insert_subset e_in_X this.1
      apply subset_antisymm sub_I _
      rw [if_pos (sub_I (mem_insert _ _))] at I_ind
      have B_sub : B ⊆ I \ {e}
      · rw [subset_diff, disjoint_singleton_right]
        exact ⟨(subset_insert _ _).trans sub_I, not_mem_subset (hB.1.left_subset_ground) e_nE⟩
      obtain (rfl):= hB.1.eq_of_subset_indep I_ind.1.1 B_sub (diff_subset_diff_left I_ind.2.2)
      · simp
    have := Y_ind.subset_basis_of_subset Y_sub_X ?_
    · obtain ⟨B, hB⟩ := this
      refine' ⟨B, _⟩
      rw [mem_maximals_iff]
      dsimp
      rw [if_neg (not_mem_subset hB.1.subset e_in_X)]
      refine' ⟨⟨hB.1.indep, hB.2, hB.1.subset⟩, fun I I_ind sub_I ↦ _⟩
      rw [if_neg (not_mem_subset I_ind.2.2 e_in_X)] at I_ind
      apply hB.1.eq_of_subset_indep I_ind.1 sub_I I_ind.2.2
    rwa [←diff_singleton_eq_self e_in_X, diff_singleton_subset_iff]
  · split_ifs at Y_ind with e_in_Y
    --proof sketch for e ∈ Y case: Find basis Y \ {e} ⊆ B for X, then try to find an element b ∈ B \ Y
    --where cl(B-b) ∉ C. If all are in C, then the closures of B minus all those elements are modular,
    --with their intersection being exactly Y \ {e}, so we may find contradiction of Y \ {e} ∉ C.
    --requires rewriting definition of modular cut to account for infinite intersection
    have Xdiff_ground : X \ {e} ⊆ M.E
    · rintro x ⟨x_sub_X, (x_ne_e : x ≠ e)⟩
      obtain (rfl | sub_ground) := (X_sub x_sub_X)
      · contradiction
      assumption
    obtain ⟨B, hB⟩ := Y_ind.1.subset_basis_of_subset (diff_subset_diff_left Y_sub_X)
    by_cases B_cl_mem : M.cl B ∉ C
    · refine' ⟨insert e B, _⟩
      rw [mem_maximals_iff]
      dsimp
      rw [if_pos (mem_insert _ _), insert_diff_self_of_not_mem (not_mem_subset (hB.1.left_subset_ground) e_nE),
       and_iff_left B_cl_mem, and_iff_right hB.1.indep, ←diff_singleton_subset_iff, insert_subset_iff,
       and_iff_right hB.2, and_iff_right (Y_sub_X e_in_Y), and_iff_right ((hB.1.subset).trans (diff_subset _ _))]
      rintro I ⟨I_ind, Y_sub_I, I_sub_X⟩ eb_sub_I
      rw [if_pos (Y_sub_I e_in_Y)] at I_ind
      have B_sub : B ⊆ I \ {e}
      · rw [subset_diff, disjoint_singleton_right]
        exact ⟨(subset_insert _ _).trans eb_sub_I, not_mem_subset (hB.1.left_subset_ground) e_nE⟩
      obtain (rfl):= hB.1.eq_of_subset_indep I_ind.1 B_sub (diff_subset_diff_left I_sub_X)
      simp [Y_sub_I e_in_Y]
    push_neg at B_cl_mem



)
 sorry
