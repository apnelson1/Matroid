import Matroid.Simple
import Matroid.ForMathlib.Other
import Matroid.Minor.Basic

namespace Matroid
open Set

def Modular_pair (M : Matroid α) (X Y : Set α) : Prop :=
    ∃ B, M.Modular {X, Y} B

def Modular_set (M : Matroid α) (X : Set α) : Prop :=
    ∀ Y, M.IsFlat Y → M.Modular_pair X Y

def Modular_matroid (M : Matroid α) : Prop :=
    ∀ X, M.IsFlat X → M.Modular_set X

def Modular_isFlat (M : Matroid α) (X : Set α) : Prop :=
    ∀ Y, M.IsFlat Y → Modular_pair M X Y

-- #check Matroid.Modular

-- structure ModularCut (M : Matroid α) where
--   (Fs : Set (Set α))
--   (forall_isFlat : ∀ F ∈ Fs, M.IsFlat F)
--   (modular : ∀ X ⊆ C, X.Nonempty  )


def Modular_cut (M : Matroid α) (C : Set (Set α)) : Prop := --version with infinite modular sets
    (∀ F ∈ C, M.IsFlat F) ∧ (∀ F F', F ∈ C → F ⊆ F' → M.IsFlat F' → F' ∈ C) ∧
    (∀ X ⊆ C, X.Nonempty → (∃ B, M.Modular X B) → sInter X ∈ C)

def Modular_cut' (M : Matroid α) (C : Set (Set α)) : Prop := --old version for finite with pairs
    (∀ F ∈ C, M.IsFlat F) ∧ (∀ F F', F ∈ C → F ⊆ F' → M.IsFlat F' → F' ∈ C) ∧
    (∀ F₁ F₂, F₁ ∈ C → F₂ ∈ C → M.Modular_pair F₁ F₂ → F₁ ∩ F₂ ∈ C)


lemma modular_finite_intersection {M : Matroid α} (C_mod : M.Modular_cut' C) (X_fin : X.Finite)
    (X_sub : X ⊆ C) (X_mod : ∃ B, M.Modular X B) (X_none : X.Nonempty) : sInter X ∈ C := by
  obtain (⟨x, rfl⟩ | X_nt) := X_none.exists_eq_singleton_or_nontrivial
  · rwa [sInter_singleton, ← singleton_subset_iff]
  obtain ⟨x, y, xy_ne, xy_sub⟩ := nontrivial_iff_pair_subset.1 X_nt
  have x_eq_insert : X = insert x (X \ {x})
  · simp [pair_subset_iff.1 xy_sub]
  rw [x_eq_insert, sInter_insert]
  obtain ⟨B, B_mod⟩ := X_mod
  apply C_mod.2.2 _ _ (X_sub (xy_sub (mem_insert _ _))) _
  · refine' ⟨B, B_mod.1, fun Ys Ys_sub Ys_none ↦ _⟩
    obtain (rfl | rfl | rfl) := (Nonempty.subset_pair_iff Ys_none).1 Ys_sub
    · apply B_mod.2 (singleton_subset_iff.2 (xy_sub (mem_insert _ _))) (singleton_nonempty _)
    · rw [sInter_singleton]
      apply B_mod.2 diff_subset ⟨y, ⟨(pair_subset_iff.1 xy_sub).2, _⟩⟩
      exact xy_ne.symm
    rw [sInter_pair, ← sInter_insert, ← x_eq_insert]
    exact B_mod.2 (rfl.subset) X_none
  have encard_lt : (X \ {x}).encard < X.encard
  · apply X_fin.encard_lt_encard ⟨diff_subset _ _, (not_subset.2 ⟨x, (xy_sub (mem_insert _ _)), _⟩)⟩
    exact fun x_mem ↦ absurd rfl x_mem.2
  have:= encard_lt
  apply modular_finite_intersection C_mod (X_fin.subset diff_subset) (diff_subset.trans
   X_sub) ⟨B, (B_mod.subset diff_subset)⟩ ⟨y, ⟨(pair_subset_iff.1 xy_sub).2, _⟩⟩
  exact xy_ne.symm
termination_by _ => X.encard


theorem modular_cut_iff_modular_cut'_finite {M : Matroid α} [M.Finite] :
    M.Modular_cut C ↔ M.Modular_cut' C := by
  unfold Modular_cut Modular_cut'
  refine' ⟨fun h_mod ↦ ⟨h_mod.1, h_mod.2.1, fun F₁ F₂ F₁_mem F₂_mem Fs_modular ↦ _⟩,
  fun h_mod  ↦ ⟨h_mod.1, h_mod.2.1, fun X X_sub X_none X_modular ↦ _⟩⟩
  · have:= h_mod.2.2 {F₁, F₂} (pair_subset F₁_mem F₂_mem) ⟨F₁, mem_insert _ _⟩ Fs_modular
    rwa [← sInter_pair]
  have X_fin : X.Finite
  · have isFlat_fin : {F | M.IsFlat F}.Finite
    · apply Finite.subset M.ground_finite.finite_subsets (fun F F_IsFlat ↦ F_IsFlat.subset_ground)
    apply Finite.subset (Finite.subset (flat_fin) (fun F F_C ↦ h_mod.1 F F_C)) X_sub
  apply modular_finite_intersection h_mod X_fin X_sub X_modular X_none



theorem union_insert_eq {A : Set α} {b c : α} :
    (insert b A) ∪ (insert c A) = insert c (insert b A) := by
  rw [insert_eq, insert_eq, ← union_union_distrib_right, @union_comm _ {b} _,
    union_assoc, ← insert_eq, ← insert_eq]

theorem inter_insert_eq {A : Set α} {b c : α} (hne : b ≠ c):
    (insert b A) ∩ (insert c A) = A := by
  rw [insert_eq, insert_eq, ← union_distrib_right, Disjoint.inter_eq _, empty_union]
  rwa [disjoint_singleton]

theorem IsBasis.exchange_isBase_of_indep {M : Matroid α} (hB : M.IsBasis B X) (hf : f ∈ X \ B)
    (hI : M.Indep (insert f (B \ {e}))) : M.IsBasis (insert f (B \ {e})) X := by
  have X_sub := hB.subset_ground
  rw [← base_restrict_iff] at hB ⊢
  · apply hB.exchange_isBase_of_indep hf.2 (hI.indep_restrict_of_subset (insert_subset hf.1
    (diff_subset.trans hB.subset_ground)))




@[simp] theorem Modular_ground (M : Matroid α) : M.Modular_set M.E := by
  intro Y Y_isFlat
  obtain ⟨B, h_B⟩ := M.exists_isBasis Y
  obtain ⟨B', B'_isBase, B_sub_B'⟩ := h_B.indep
  refine' ⟨B', B'_isBase, _⟩
  have B'_inter : B' ∩ Y = B
  · apply subset_antisymm _ _
    · rintro x ⟨x_B, x_Y⟩
      by_contra h_f
      apply ((B'_isBase.indep).subset (insert_subset x_B B_sub_B')).not_dep
      exact h_B.insert_dep ⟨x_Y, h_f⟩
    · intro x x_B
      exact ⟨B_sub_B' x_B, h_B.subset x_B⟩
  rintro X X_sub X_ne
  obtain (X_eq_E | X_eq_Y | X_eq_pair) := (Nonempty.subset_pair_iff X_ne).1 X_sub
  · rwa [X_eq_E, sInter_singleton, inter_eq_self_of_subset_right B'_isBase.subset_ground,
     basis_ground_iff]
  · rwa [X_eq_Y, sInter_singleton, inter_comm, B'_inter]
  · rwa [X_eq_pair, sInter_pair, inter_eq_self_of_subset_right Y_isFlat.subset_ground, inter_comm,
     B'_inter]

@[simp] theorem Modular_pair_comm (h : Modular_pair M X Y) : Modular_pair M Y X := by
  obtain ⟨B, B_Base, B_modular⟩ := h
  refine' ⟨B, B_Base, _⟩
  intro Ys Ys_sub Ys_ne
  rw [pair_comm] at Ys_sub
  exact B_modular Ys_sub Ys_ne

@[simp] theorem Modular_closure_empty (M : Matroid α) : Modular_isFlat M (M.loops) := by
  intro Y Y_isFlat
  obtain ⟨B, h_B⟩ := M.exists_isBasis Y
  obtain ⟨B', B'_isBase, B_sub_B'⟩ := h_B.indep
  have B'_inter : Y ∩ B' = B
  · apply subset_antisymm _ _
    · rintro x ⟨x_B, x_Y⟩
      by_contra h_f
      apply ((B'_isBase.indep).subset (insert_subset x_Y B_sub_B')).not_dep
      exact h_B.insert_dep ⟨x_B, h_f⟩
    · intro x x_B
      exact ⟨h_B.subset x_B, B_sub_B' x_B⟩
  refine' ⟨B', B'_isBase, fun Ys Ys_sub Ys_ne ↦ _⟩
  obtain (Ys_eq_closure | Ys_eq_Y | Ys_eq_pair) := (Nonempty.subset_pair_iff Ys_ne).1 Ys_sub
  · rw [Ys_eq_closure, sInter_singleton, Disjoint.inter_eq _, empty_isBasis_iff]
    · rw [disjoint_left]
      intro a a_closure a_B'
      rw [← isLoop_iff, isLoop_iff_notMem_isBase_forall] at a_closure
      exact a_closure B' B'_isBase a_B'
  · rwa [Ys_eq_Y, sInter_singleton, B'_inter]
  · rw [Ys_eq_pair, sInter_pair, ← Y_isFlat.closure, inter_eq_self_of_subset_left
    (M.closure_subset_closure (empty_subset _)), Disjoint.inter_eq _, empty_isBasis_iff]
    rw [disjoint_left]
    intro a a_closure a_B'
    rw [← isLoop_iff, isLoop_iff_notMem_isBase_forall] at a_closure
    exact a_closure B' B'_isBase a_B'

theorem Modular_cut_pair {M : Matroid α} {C : Set (Set α)} (hC : M.Modular_cut C) (a b : α)
    {X : Set α} (hne : a ≠ b) (h_ind : M.Indep (insert a (insert b X)))
    (h_a : M.closure (insert a X) ∈ C) (h_b : M.closure (insert b X) ∈ C) : M.closure X ∈ C := by
  rw [← union_insert_eq] at h_ind
  have ab_closure_inter_eq : sInter {M.closure (insert b X), M.closure (insert a X)} = M.closure X
  · rw [sInter_pair, ← h_ind.closure_inter_eq_inter_closure, inter_insert_eq hne.symm]
  rw [← ab_closure_inter_eq]
  apply hC.2.2
  · rw [pair_subset_iff]
    exact ⟨h_b, h_a⟩
  · refine' ⟨M.closure (insert b X), mem_insert _ _⟩
  rw [union_insert_eq] at h_ind
  have:= h_ind
  obtain ⟨B, B_isBase, sub_B⟩ := this
  refine' ⟨B, B_isBase, fun Y Y_sub (Y_none : Y.Nonempty) ↦ _⟩
  obtain (rfl | rfl | rfl) := (Nonempty.subset_pair_iff Y_none).1 Y_sub
  · rw [sInter_singleton, B_isBase.indep.closure_inter_eq_self_of_subset ((subset_insert _ _).trans sub_B)]
    exact (h_ind.subset (subset_insert _ _)).isBasis_closure
  · rw [insert_comm] at h_ind sub_B
    rw [sInter_singleton, B_isBase.indep.closure_inter_eq_self_of_subset ((subset_insert _ _).trans sub_B)]
    exact (h_ind.subset (subset_insert _ _)).isBasis_closure
  rw [ab_closure_inter_eq, B_isBase.indep.closure_inter_eq_self_of_subset ((subset_insert _ _).trans
   ((subset_insert _ _).trans sub_B))]
  exact (h_ind.subset ((subset_insert _ _).trans (subset_insert _ _))).isBasis_closure

open Classical

def indepmatroid_of_cut (M : Matroid α) (C : Set (Set α)) (hC : M.Modular_cut C) {e : α}
    (e_nE : e ∉ M.E) : IndepMatroid α where
  E := insert e M.E
  Indep I := if (e ∈ I) then (M.Indep (I \ {e}) ∧ M.closure (I \ {e}) ∉ C) else M.Indep I
  indep_empty := by
    dsimp
    rw [if_neg (notMem_empty _)]
    exact M.empty_indep
  indep_subset := by
    intro I J J_ind I_sub
    split_ifs with e_mem_I
    · rw [if_pos (I_sub e_mem_I)] at J_ind
      refine' ⟨J_ind.1.subset (diff_subset_diff_left I_sub), fun clI_mem ↦ _⟩
      apply J_ind.2 (hC.2.1 (M.closure (I \ {e})) (M.closure (J \ {e}))
       clI_mem (M.closure_subset_closure (diff_subset_diff_left I_sub)) (M.closure_isFlat (J \ {e})))
    split_ifs at J_ind with e_mem_J
    · exact J_ind.1.subset (subset_diff_singleton I_sub e_mem_I)
    exact J_ind.subset I_sub
  indep_aug := by
    rintro I J I_ind I_nmax ⟨J_ind, J_max⟩
    have J_isBase_of_notMem_e : e ∉ J → M.IsBase J
    · intro e_in_J
      rw [isBase_iff_maximal_indep]
      dsimp at J_ind
      rw [if_neg e_in_J] at J_ind
      refine' ⟨J_ind, fun X X_ind X_sub ↦ _⟩
      apply subset_antisymm X_sub (J_max _ X_sub)
      dsimp
      rwa [if_neg (notMem_subset (X_ind.subset_ground) e_nE)]
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
      · by_contra! h_f
        have J_insert_mem_C : ∀ x ∉ J, M.Indep (insert x (J \ {e})) → M.closure (insert x (J \ {e})) ∈ C
        · intro x x_notin_J x_ind
          by_contra notMem_C
          apply (ne_insert_of_notMem _ x_notin_J) (subset_antisymm (subset_insert _ _) (J_max _
           (subset_insert _ _)))
          dsimp
          rw [if_pos (mem_insert_of_mem _ e_in_J), ← insert_diff_singleton_comm (ne_of_mem_of_notMem
           e_in_J x_notin_J).symm]
          exact ⟨x_ind, notMem_C⟩
        obtain ⟨y, hy⟩ := Set.exists_of_ssubset (ssubset_iff_subset_ne.2 ⟨I_sub_Y, I_ne_Y⟩)
        have y_ind : M.Indep ((insert y I) \ {e}) ∧ M.closure ((insert y I) \ {e}) ∉ C
        · refine' ⟨Y_ind.1.subset (diff_subset_diff_left (insert_subset hy.1 I_sub_Y)),
           fun closure_mem_C ↦ _⟩
          exact Y_ind.2 (hC.2.1 _ _ closure_mem_C (M.closure_subset_closure (diff_subset_diff_left (insert_subset
           hy.1 I_sub_Y))) (M.closure_isFlat _))
        have y_notin_J : y ∉ J
        · intro y_in_J
          apply h_f y ⟨y_in_J, hy.2⟩ _
          rwa [if_pos (mem_insert_of_mem y e_in_I)]
        have y_ground := (Y_ind.1.subset_ground (mem_diff_of_mem hy.1 (ne_of_mem_of_notMem e_in_J
         y_notin_J).symm))
        have x := I_ind.1.subset_isBasis_of_subset (diff_subset_diff_left (subset_union_left I J)) ?_
        · obtain ⟨I', I'_isBasis, I_sub_I'⟩ := x
          have : (I \ {e} ⊂ I')
          · apply Ne.ssubset_of_subset _ I_sub_I'
            rintro rfl
            apply insert_ne_self.2 y_notin_J (subset_antisymm (J_max _ (subset_insert _ _))
             (subset_insert _ _))
            dsimp
            rw [if_pos (mem_insert_of_mem _ e_in_J), ← insert_diff_singleton_comm
             (ne_of_mem_of_notMem e_in_J y_notin_J).symm, ← J_ind.1.notMem_closure_iff_of_notMem _]
            refine' ⟨notMem_subset (M.closure_subset_closure (diff_subset_diff_left
             (subset_union_right I J))) _, _⟩
            · rw [← I'_isBasis.closure_eq_closure, I_ind.1.notMem_closure_iff_of_notMem (notMem_subset
              diff_subset hy.2),
              insert_diff_singleton_comm (ne_of_mem_of_notMem e_in_J y_notin_J).symm]
              exact y_ind.1
            rw [insert_diff_singleton_comm (ne_of_mem_of_notMem e_in_J y_notin_J).symm]
            intro closure_mem_C
            apply y_ind.2 (hC.2.1 _ _ closure_mem_C _ (M.closure_isFlat _))
            rw [← insert_diff_singleton_comm (ne_of_mem_of_notMem e_in_J y_notin_J).symm I,
             ← closure_insert_closure_eq_closure_insert, I'_isBasis.closure_eq_closure, closure_insert_closure_eq_closure_insert,
              ← insert_diff_singleton_comm (ne_of_mem_of_notMem e_in_J y_notin_J).symm]
            · apply M.closure_subset_closure (insert_subset_insert (diff_subset_diff_left
             subset_union_right))
            exact notMem_subset diff_subset y_notin_J
          obtain ⟨a, a_notMem, a_insert_sub⟩ := ssubset_iff_insert.1 this
          have a_mem_JI : a ∈ J \ I
          · obtain ⟨(aI | aJ), a_ne_e⟩:= I'_isBasis.subset (a_insert_sub (mem_insert a _))
            apply absurd (⟨aI, a_ne_e⟩ : (a ∈ I \ {e})) a_notMem
            apply (mem_diff _).2 ⟨aJ, _⟩
            intro aI
            apply a_notMem ⟨aI, a_ne_e⟩
          obtain (ssubset | rfl) := ssubset_or_eq_of_subset a_insert_sub
          · obtain ⟨b, b_notMem, b_insert_sub⟩ := ssubset_iff_insert.1 ssubset
            apply I_ind.2 (Modular_cut_pair hC b a _ (I'_isBasis.indep.subset b_insert_sub) _ _)
            · exact (ne_of_mem_of_notMem (mem_insert _ _) b_notMem).symm
            · rw [insert_comm] at b_insert_sub
              have:= h_f b ?_
              · rw [if_pos (mem_insert_of_mem _ e_in_I), not_and, not_notMem,
                 ← insert_diff_singleton_comm (ne_of_mem_of_notMem ((I'_isBasis.indep.subset
                 b_insert_sub).subset_ground (mem_insert_of_mem _ (mem_insert _ _))) e_nE)] at this
                exact this (I'_isBasis.indep.subset ((subset_insert _ _).trans b_insert_sub))
              rw [insert_comm] at b_insert_sub
              obtain ⟨(bI | bJ), b_ne_e⟩:= I'_isBasis.subset (b_insert_sub (mem_insert b _))
              · apply absurd (⟨bI, b_ne_e⟩ : (b ∈ I \ {e})) _
                apply notMem_subset (subset_insert _ _) b_notMem
              apply (mem_diff _).2 ⟨bJ, _⟩
              intro bI
              apply b_notMem (mem_insert_of_mem _ ⟨bI, b_ne_e⟩)
            have:= h_f a a_mem_JI
            rw [if_pos (mem_insert_of_mem _ e_in_I), not_and, not_notMem,
             ← insert_diff_singleton_comm] at this
            · exact this (I'_isBasis.indep.subset a_insert_sub)
            exact ne_of_mem_of_notMem ((I'_isBasis.indep.subset a_insert_sub).subset_ground
             (mem_insert _ _)) e_nE
          have J_not_isBasis : ¬ M.IsBasis (J \ {e}) ((I ∪ J) \ {e})
          · intro J_isBasis
            apply h_f a a_mem_JI
            rw [if_pos (mem_insert_of_mem _ e_in_I), ← insert_diff_singleton_comm, I'_isBasis.closure_eq_closure,
             ← J_isBasis.closure_eq_closure]
            exact ⟨I'_isBasis.indep, J_ind.2⟩
            exact (ne_of_mem_of_notMem e_in_I a_mem_JI.2).symm
          obtain ⟨i, hi⟩ := J_ind.1.exists_insert_of_not_isBasis (diff_subset_diff_left
           subset_union_right) J_not_isBasis I'_isBasis
          have I'_isBase : M.IsBase (insert a (I \ {e}))
          · by_contra I'_not_isBase
            obtain ⟨B, hB⟩ := M.exists_isBase
            obtain ⟨b, hb⟩ := I'_isBasis.indep.exists_insert_of_not_isBase I'_not_isBase hB
            have b_notin_union : b ∉ I ∪ J
            · intro b_mem_union
              have : b ∈ (I ∪ J) \ {e}
              · rwa [mem_diff_singleton, and_iff_left (ne_of_mem_of_notMem
                (hB.subset_ground hb.1.1) e_nE)]
              apply ((I'_isBasis.indep.insert_indep_iff_of_notMem hb.1.2).1 hb.2).2
              rw [I'_isBasis.closure_eq_closure]
              apply M.mem_closure_of_mem this I'_isBasis.subset_ground
            have bi_J_indep : M.Indep (insert b (insert i (J \ {e})))
            · rw [hi.2.insert_indep_iff, mem_diff _, and_iff_right (hB.subset_ground hb.1.1)]
              rw [I'_isBasis.indep.insert_indep_iff_of_notMem hb.1.2, I'_isBasis.closure_eq_closure] at hb
              apply Or.inl (notMem_subset (M.closure_subset_closure _) hb.2.2)
              rw [insert_diff_singleton_comm (ne_of_mem_of_notMem (hi.2.subset_ground
               (mem_insert _ _)) e_nE)]
              apply diff_subset_diff_left (insert_subset _ subset_union_right)
              obtain (rfl | i_Jd) := hi.1.1
              · apply (Or.inr a_mem_JI.1)
              apply (Or.inl i_Jd.1)
            apply J_ind.2 (Modular_cut_pair hC b i (ne_of_mem_of_notMem hi.1.1 hb.1.2).symm
             bi_J_indep _ _)
            · apply J_insert_mem_C b (notMem_subset subset_union_right b_notin_union) _
              rw [insert_comm] at bi_J_indep
              exact bi_J_indep.subset (subset_insert _ _)
            apply J_insert_mem_C i _ hi.2
            intro i_J
            apply hi.1.2 ⟨i_J, ne_of_mem_of_notMem (hi.2.subset_ground (mem_insert _ _)) e_nE⟩
          have yI_isBase : M.IsBase (insert y (I \ {e}))
          · have base_insert:= @Matroid.IsBase.exchange_isBase_of_indep _ _ _ y a I'_isBase
            rw [insert_diff_self_of_notMem a_notMem] at base_insert
            apply base_insert
            · rintro (rfl | y_mem)
              · exact y_notin_J a_mem_JI.1
              exact hy.2 y_mem.1
            rw [insert_diff_singleton_comm (ne_of_mem_of_notMem y_ground e_nE)]
            exact y_ind.1
          apply h_f a a_mem_JI
          rw [if_pos (mem_insert_of_mem _ e_in_I), ← insert_diff_singleton_comm
           (ne_of_mem_of_notMem e_in_I a_mem_JI.2).symm,
          I'_isBase.closure_eq, ← yI_isBase.closure_eq, insert_diff_singleton_comm
           (ne_of_mem_of_notMem y_ground e_nE)]
          exact ⟨I'_isBase.indep, y_ind.2⟩
        rintro x ⟨(x_I | x_J), (hne : x ≠ e)⟩
        · exact I_ind.1.subset_ground ⟨x_I, hne⟩
        exact J_ind.1.subset_ground ⟨x_J, hne⟩
      have I_nb : ¬ M.IsBase (I \ {e})
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
      obtain ⟨j₂, hj₂⟩ := I_ind.1.exists_insert_of_not_isBase I_nb (J_isBase_of_notMem_e e_in_J)
      rw [diff_diff_right, Disjoint.inter_eq (disjoint_singleton_right.2 e_in_J),
       union_empty] at hj₂
      by_cases j₂I_b : M.IsBase (insert j₂ (I \ {e}))
      · refine' ⟨j₂, hj₂.1, _⟩
        dsimp
        rw [if_pos ((subset_insert _ _) e_in_I), ← insert_diff_singleton_comm
         (ne_of_mem_of_notMem hj₂.1.1 e_in_J),
         and_iff_right hj₂.2]
        obtain ⟨y, hy⟩ := Set.exists_of_ssubset (ssubset_iff_subset_ne.2 ⟨I_sub_Y, I_ne_Y⟩)
        obtain (rfl | ne) := eq_or_ne j₂ y
        · intro hf
          apply Y_ind.2 (hC.2.1 _ _ hf (M.closure_subset_closure _) (M.closure_isFlat _))
          exact (insert_subset (⟨hy.1, ne_of_mem_of_notMem hj₂.1.1 e_in_J⟩)
           (diff_subset_diff_left I_sub_Y))
        have y_notin : y ∉ insert j₂ (I \ {e})
        · rw [mem_insert_iff, not_or, mem_diff, not_and_or]
          exact ⟨ne.symm, Or.inl hy.2⟩
        have base_insert:= @Matroid.IsBase.exchange_isBase_of_indep _ _ _ _ j₂ j₂I_b y_notin
        rw [insert_diff_self_of_notMem (notMem_subset diff_subset hj₂.1.2)] at base_insert
        rw [j₂I_b.closure_eq]
        rw [Spanning.closure_eq _] at Y_ind
        · exact Y_ind.2
        have insert_y_subset_Y : insert y (I \ {e}) ⊆ Y \ {e}
        · rw [insert_diff_singleton_comm (ne_of_mem_of_notMem e_in_I hy.2).symm]
          exact diff_subset_diff_left (insert_subset hy.1 I_sub_Y)
        apply IsBase.superset_spanning (base_insert (Y_ind.1.subset insert_y_subset_Y))
         insert_y_subset_Y Y_ind.1.subset_ground
      obtain ⟨j₁, j₁_mem, j₁_ind⟩:=hj₂.2.exists_insert_of_not_isBase j₂I_b
       (J_isBase_of_notMem_e e_in_J)
      have hne : j₁ ≠ j₂:= fun (rfl) ↦ j₁_mem.2 (mem_insert _ _)
      --case involving finding 2 to add from j and using modularity to contradict
      --I independence, not so bad
      by_cases j₁_closure_mem_c : M.closure (insert j₁ (I \ {e})) ∈ C
      · by_cases j₂_closure_mem_c : M.closure (insert j₂ (I \ {e})) ∈ C
        · apply absurd (Modular_cut_pair hC j₁ j₂ hne j₁_ind j₁_closure_mem_c j₂_closure_mem_c) I_ind.2
        refine' ⟨j₂, hj₂.1, _⟩
        dsimp
        rw [if_pos (mem_insert_of_mem _ e_in_I), ← insert_diff_singleton_comm
         (ne_of_mem_of_notMem hj₂.1.1 e_in_J) _]
        exact ⟨j₁_ind.subset (subset_insert _ _), j₂_closure_mem_c⟩
      refine' ⟨j₁, ⟨j₁_mem.1, fun hf ↦ j₁_mem.2 (mem_insert_of_mem _ ⟨hf, ne_of_mem_of_notMem
       j₁_mem.1 e_in_J⟩)⟩, _⟩
      dsimp
      rw [if_pos (mem_insert_of_mem _ e_in_I), ← insert_diff_singleton_comm
       (ne_of_mem_of_notMem j₁_mem.1 e_in_J) _, ]
      exact ⟨j₁_ind.subset (insert_subset_insert (subset_insert _ _)), j₁_closure_mem_c⟩
    split_ifs at J_ind with e_in_J --2nd hardest case
    · by_cases closure_I_mem : M.closure I ∈ C --if cl(I) ∈ C, and every member of J-e cant be added,
    --then J ⊂ cl(I)
      · by_contra! h_f
        have J_diff_sub_closure_I : J \ {e} ⊆ M.closure I
        · rintro j ⟨j_J, (j_ne : j ≠ e)⟩
          rw [I_ind.mem_closure_iff, or_comm, or_iff_not_imp_left]
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
        · apply J_ind.1.exists_insert_of_not_isBasis (subset_union_left _ I)
          · intro h_f
            apply J_ind.2 (hC.2.1 _ _ closure_I_mem _ (M.closure_isFlat _))
            rw [h_f.closure_eq_closure]
            exact M.closure_subset_closure subset_union_right
          rw [isBasis_iff_indep_subset_closure]
          refine' ⟨I_ind, subset_union_right, fun x ↦ _⟩
          rintro (x_J | x_I)
          · exact J_diff_sub_closure_I x_J
          · exact M.mem_closure_of_mem x_I
        obtain ⟨i, i_mem, i_ind⟩ := I_J_exch
        split_ifs at Y_ind with e_in_Y
        · apply Y_ind.2 (hC.2.1 _ _ closure_I_mem (M.closure_subset_closure _) (M.closure_isFlat _))
          exact subset_diff_singleton I_sub_Y e_in_I
        have Y_insert : ∃ y ∈ Y \ I, M.Indep (insert y (insert i (J \ {e})))
        · obtain ⟨y, hy⟩ := Set.exists_of_ssubset (ssubset_iff_subset_ne.2 ⟨I_sub_Y, I_ne_Y⟩)
          refine' ⟨y, ⟨hy.1, hy.2⟩, _⟩
          rw [i_ind.insert_indep_iff_of_notMem, mem_diff]
          · refine' ⟨Y_ind.subset_ground hy.1, fun y_closure ↦ _⟩
            obtain (mem_c | y_in_I) := I_ind.insert_indep_iff.1 (Y_ind.subset
              (insert_subset hy.1 I_sub_Y))
            · apply mem_c.2 (closure_subset_closure_of_subset_closure (insert_subset (M.mem_closure_of_mem i_mem.1
              I_ind.subset_ground) J_diff_sub_closure_I) y_closure)
            · exact hy.2 y_in_I
          · rintro (y_I | ⟨y_J, (y_ne_e : y ≠ e)⟩)
            · apply hy.2
              rw [y_I]
              exact i_mem.1
            apply h_f y ⟨y_J, hy.2⟩
            rw [mem_insert_iff, or_iff_left e_in_I, if_neg y_ne_e.symm]
            apply Y_ind.subset (insert_subset hy.1 I_sub_Y)
        obtain ⟨y, y_mem, y_ind⟩ := Y_insert
        apply J_ind.2 (Modular_cut_pair hC y i (ne_of_mem_of_notMem i_mem.1 y_mem.2).symm
         y_ind _ _)
        · by_contra insert_notMem
          apply (J \ {e}).ne_insert_of_notMem (J \ {e}) _ (subset_antisymm (subset_insert y _) _)
          · rintro ⟨y_J, (y_ne_e : y ≠ e)⟩
            apply h_f y ⟨y_J, y_mem.2⟩
            rw [mem_insert_iff, or_iff_left e_in_I, if_neg y_ne_e.symm]
            apply Y_ind.subset (insert_subset y_mem.1 I_sub_Y)
          rw [insert_diff_singleton_comm (ne_of_mem_of_notMem y_mem.1 e_in_Y)] at insert_notMem ⊢
          apply diff_subset_diff_left (J_max _ (subset_insert _ _))
          dsimp
          rw [if_pos (mem_insert_of_mem _ e_in_J)]
          rw [insert_comm] at y_ind
          refine' ⟨y_ind.subset (subset_trans _ (subset_insert _ _)), insert_notMem⟩
          rw [insert_diff_singleton_comm (ne_of_mem_of_notMem y_mem.1 e_in_Y)]
        by_contra insert_notMem
        apply (J \ {e}).ne_insert_of_notMem (J \ {e}) i_mem.2 (subset_antisymm
         (subset_insert _ _) _)
        rw [insert_diff_singleton_comm (ne_of_mem_of_notMem i_mem.1 e_in_I) _] at insert_notMem ⊢
        apply diff_subset_diff_left (J_max _ (subset_insert _ _))
        dsimp
        rw [if_pos (mem_insert_of_mem _ e_in_J)]
        refine' ⟨y_ind.subset (subset_trans _ (subset_insert _ _)), insert_notMem⟩
        rw [insert_diff_singleton_comm (ne_of_mem_of_notMem i_mem.1 e_in_I) _]
      refine' ⟨e, ⟨e_in_J, e_in_I⟩, _⟩
      dsimp
      rw [if_pos (mem_insert e I), insert_diff_self_of_notMem e_in_I]
      exact ⟨I_ind, closure_I_mem⟩
    have I_not_isBase : ¬ M.IsBase I
    --easiest case, e is in neither - requires some effort to show I not a base
    · intro h_f
      split_ifs at Y_ind with e_in_Y
      · rw [Spanning.closure_eq _] at Y_ind
        · apply (ne_insert_of_notMem J e_in_J) (subset_antisymm (subset_insert e J) (J_max _
          (subset_insert e J)))
          dsimp at J_ind ⊢
          rw [if_pos (mem_insert _ _), insert_diff_self_of_notMem e_in_J,
           (J_isBase_of_notMem_e e_in_J).closure_eq]
          exact ⟨J_ind, Y_ind.2⟩
        rw [spanning_iff_superset_isBase (Y_ind.1.subset_ground)]
        refine' ⟨I, h_f, subset_diff_singleton I_sub_Y e_in_I⟩
      apply (h_f.dep_of_ssubset (I_ne_Y.ssubset_of_subset I_sub_Y)
        Y_ind.subset_ground).not_indep Y_ind
    obtain ⟨x, x_mem, x_ind⟩ := I_ind.exists_insert_of_not_isBase I_not_isBase
     (J_isBase_of_notMem_e e_in_J)
    refine' ⟨x, x_mem, _⟩
    dsimp
    rwa [if_neg _]
    rw [mem_insert_iff]; push_neg
    exact ⟨(ne_of_mem_of_notMem x_mem.1 e_in_J).symm, e_in_I⟩

  indep_maximal := by
    intro X X_sub Y Y_ind Y_sub_X
    split_ifs at Y_ind with e_in_Y
  --proof sketch for e ∈ Y case: Find basis Y \ {e} ⊆ B for X, then try to find an element b ∈ B \ Y
  --where cl(B-b) ∉ C. If all are in C, then the closures of B minus all those elements are modular,
  --with their intersection being exactly Y \ {e}, so we may find contradiction of Y \ {e} ∉ C.
  --requires rewriting definition of modular cut to account for infinite intersection
    · have Xdiff_ground : X \ {e} ⊆ M.E
      · rintro x ⟨x_sub_X, (x_ne_e : x ≠ e)⟩
        obtain (rfl | sub_ground) := (X_sub x_sub_X)
        · contradiction
        assumption
      obtain ⟨B, hB⟩ := Y_ind.1.subset_isBasis_of_subset (diff_subset_diff_left Y_sub_X)
      by_cases B_closure_mem : M.closure B ∉ C
      · refine' ⟨insert e B, _⟩
        rw [mem_maximals_iff]
        dsimp
        rw [if_pos (mem_insert _ _), insert_diff_self_of_notMem (notMem_subset
         (hB.1.left_subset_ground) e_nE), and_iff_left B_closure_mem, and_iff_right hB.1.indep,
         ← diff_singleton_subset_iff, insert_subset_iff, and_iff_right hB.2, and_iff_right
          (Y_sub_X e_in_Y), and_iff_right ((hB.1.subset).trans diff_subset)]
        rintro I ⟨I_ind, Y_sub_I, I_sub_X⟩ eb_sub_I
        rw [if_pos (Y_sub_I e_in_Y)] at I_ind
        have B_sub : B ⊆ I \ {e}
        · rw [subset_diff, disjoint_singleton_right]
          exact ⟨(subset_insert _ _).trans eb_sub_I, notMem_subset (hB.1.left_subset_ground) e_nE⟩
        obtain (rfl):= hB.1.eq_of_subset_indep I_ind.1 B_sub (diff_subset_diff_left I_sub_X)
        simp [Y_sub_I e_in_Y]
      push_neg at B_closure_mem
      by_cases remove_cycle : ∀ b ∈ B \ (Y \ {e}), M.closure (B \ {b}) ∈ C
      · apply absurd (Modular_cut_remove hC hB.1.indep hB.2 remove_cycle B_closure_mem) Y_ind.2
      push_neg at remove_cycle
      obtain ⟨b, b_mem, hb⟩ := remove_cycle
      refine' ⟨insert e (B \ {b}), _⟩
      rw [mem_maximals_iff]; dsimp
      rw [if_pos (mem_insert e _), insert_diff_self_of_notMem (notMem_subset _ e_nE),
       and_iff_left hb]
      · refine' ⟨⟨hB.1.indep.subset diff_subset, _, insert_subset (Y_sub_X e_in_Y)
        ((diff_subset.trans hB.1.subset).trans diff_subset)⟩, _⟩
        · rw [insert_eq, ← diff_subset_iff, subset_diff, disjoint_singleton_right,
           and_iff_left b_mem.2]
          exact hB.2
        rintro I ⟨I_ind, Y_sub_I, I_sub_X⟩ eB_sub_I
        rw [if_pos (Y_sub_I e_in_Y)] at I_ind
        obtain (rfl | ssub) := eq_or_ssubset_of_subset eB_sub_I
        · rfl
        obtain ⟨i, hi⟩ := exists_of_ssubset ssub
        exfalso
        apply I_ind.2
        have bsub : insert i (B \ {b}) ⊆ I \ {e}:= (insert_subset ⟨hi.1, (ne_of_mem_of_notMem
         (mem_insert _ _) hi.2).symm⟩
        (subset_diff_singleton ((subset_insert _ _).trans eB_sub_I) (notMem_subset
        (diff_subset.trans hB.1.left_subset_ground) e_nE)))
        apply hC.2.1 (M.closure (insert i (B \ {b})))
        · obtain (rfl | i_ne_b) := eq_or_ne i b
          · simp only [b_mem.1, not_true_eq_false, mem_diff, mem_singleton_iff, and_false,
            insert_diff_singleton, insert_eq_of_mem, B_closure_mem]
          rwa [@Basis.closure_eq_closure _ M _ (X \ {e}) _, ← hB.1.closure_eq_closure]
          apply hB.1.exchange_isBase_of_indep
          · rw [mem_diff, mem_diff, mem_singleton_iff, and_iff_right (I_sub_X hi.1)]
            refine' ⟨fun (rfl) ↦ hi.2 (mem_insert _ _), fun i_mem_B ↦ hi.2 (mem_insert_of_mem _
             ⟨i_mem_B, i_ne_b⟩)⟩
          apply I_ind.1.subset bsub
        · exact M.closure_subset_closure bsub
        exact M.closure_isFlat _
      apply diff_subset.trans hB.1.left_subset_ground
    --easy case: e not in y, e in x. extend y to a basis of x-e, then split on whether it spans e
    have Y_sub_Xdiff : Y ⊆ X \ {e} := subset_diff.2 ⟨Y_sub_X, disjoint_singleton_right.2 e_in_Y⟩
    obtain ⟨B, B_Basis, Y_sub_B⟩ := Y_ind.subset_isBasis_of_subset Y_sub_Xdiff
    have e_nB := notMem_subset B_Basis.left_subset_ground e_nE
    by_cases B_closure_mem : M.closure B ∉ C ∧ e ∈ X
    · refine' ⟨insert e B, _⟩
      rw [mem_maximals_iff]
      dsimp
      rw [if_pos (mem_insert _ _), insert_diff_self_of_notMem e_nB]
      refine' ⟨⟨⟨B_Basis.indep, B_closure_mem.1⟩, Y_sub_B.trans (subset_insert _ _), _⟩,
       fun I I_ind B_sub_I ↦ _⟩
      · exact insert_subset B_closure_mem.2 (B_Basis.subset.trans diff_subset)
      obtain (rfl | ssub) := eq_or_ssubset_of_subset B_sub_I
      · rfl
      obtain ⟨i, hi⟩ := exists_of_ssubset ssub
      exfalso
      rw [if_pos (B_sub_I (mem_insert _ _))] at I_ind
      apply I_ind.1.1.not_dep (B_Basis.dep_of_ssubset _ (diff_subset_diff_left I_ind.2.2))
      rw [ssubset_iff_insert]
      refine' ⟨i, (notMem_subset (subset_insert _ _) hi.2), insert_subset ⟨hi.1,
        (ne_of_mem_of_notMem (mem_insert _ _) hi.2).symm⟩ _⟩
      exact subset_diff.2 ⟨(subset_insert _ _).trans B_sub_I, disjoint_singleton_right.2 e_nB⟩
    refine' ⟨B, _⟩
    rw [mem_maximals_iff]
    dsimp
    rw [if_neg e_nB]
    refine' ⟨⟨B_Basis.indep, Y_sub_B, B_Basis.subset.trans diff_subset⟩,
     fun I I_ind B_sub_I ↦ _⟩
    rw [not_and_or, not_notMem] at B_closure_mem
    split_ifs at I_ind with e_in_I
    · obtain (closure_mem | e_notin_X) := B_closure_mem
      exact absurd (hC.2.1 _ _ closure_mem (M.closure_subset_closure (subset_diff.2 ⟨B_sub_I,
        disjoint_singleton_right.2 e_nB⟩)) (M.closure_isFlat _)) I_ind.1.2
      exact absurd (I_ind.2.2 e_in_I) e_notin_X
    exact B_Basis.eq_of_subset_indep I_ind.1 B_sub_I (subset_diff.2 ⟨I_ind.2.2,
      disjoint_singleton_right.2 e_in_I⟩)
  subset_ground := by
    intro I I_ind
    split_ifs at I_ind with e_in_I
    · intro i i_mem
      obtain (rfl | ne) := eq_or_ne i e
      · exact mem_insert _ _
      exact (subset_insert _ _) (I_ind.1.subset_ground ⟨i_mem, ne⟩)
    exact I_ind.subset_ground.trans (subset_insert _ _)

def matroid_of_cut (M : Matroid α) {C : Set (Set α)} (hC : M.Modular_cut C) {e : α}
    (e_nE : e ∉ M.E) : Matroid α := (M.indepmatroid_of_cut C hC e_nE).matroid


#check restrict_closure_eq

theorem isFlat_of_deleteElem_isFlat {M : Matroid α} (e_nF : e ∉ F) (hF : M.IsFlat (insert e F)) :
    (M ＼ e).IsFlat F := by
  rw [isFlat_iff_closure_self, deleteElem, delete_closure_eq, diff_singleton_eq_self e_nF]
  apply subset_antisymm _ (subset_diff_singleton (M.subset_closure _ ((subset_insert _ _).trans
   hF.subset_ground)) e_nF)
  · rw [diff_singleton_subset_iff]
    apply (hF.closure_subset_of_subset (subset_insert _ _))



#check closure_insert_eq_of_mem_closure

#check iInter_closure_eq_closure_sInter_of_modular --completes modularity part of proof

lemma sInter_insert_each {X : Set (Set α)} {a : α} :
    insert a (sInter X) = sInter {insert a x | x ∈ X} := by
  ext x
  simp
  refine' ⟨fun h y y_mem ↦ _, fun h ↦ _⟩
  · obtain (rfl | h) := h
    · exact Or.inl rfl
    exact Or.inr (h y y_mem)
  obtain (rfl | ne) := eq_or_ne x a
  · exact Or.inl rfl
  exact Or.inr (fun t t_mem ↦ (or_iff_right ne).1 (h t t_mem))


lemma modular_of_modular_restrict (M : Matroid α) (X : Set (Set α)) (hX : sUnion X ⊆ M.E)
    {R : Set α} (hR : ∃ B, (M ↾ R).Modular X B) : ∃ B, M.Modular X B := by
  obtain ⟨B, ⟨B_isBase, B_mod⟩⟩ := hR
  obtain ⟨B', B'_isBase, B_sub_B'⟩ := B_isBase.indep.of_isRestriction
  refine' ⟨B', B'_isBase, fun Ys Ys_sub Ys_none ↦ _⟩
  have:= B_mod Ys_sub Ys_none
  have Ys_inter_sub_R:= this.subset_ground
  rw [restrict_ground_eq] at Ys_inter_sub_R
  have R_inter_B'_eq : R ∩ B' = B := subset_antisymm ?_ (subset_inter B_isBase.subset_ground B_sub_B')
  · rw [← inter_eq_left.2 Ys_inter_sub_R, inter_assoc, R_inter_B'_eq, inter_eq_left.2 Ys_inter_sub_R]
    rw [isBasis_restrict_iff', inter_eq_left.2 (((sInter_subset_sUnion Ys_none).trans
     (sUnion_subset_sUnion Ys_sub)).trans hX)] at this
    exact this.1
  · rintro x ⟨xR, xB'⟩
    by_contra x_nB
    apply (restrict_indep_iff.2 ⟨(B'_isBase.indep.subset (insert_subset xB' B_sub_B')),
     insert_subset xR B_isBase.subset_ground⟩).not_dep
    apply B_isBase.insert_dep ⟨xR, x_nB⟩


@[simp] theorem modular_cut_of_isFlats_remove {M : Matroid α} :
    Modular_cut (M ＼ e) ({F | e ∉ F ∧ M.IsFlat (insert e F) ∧ e ∈ M.closure F}) := by
  refine' ⟨fun F F_isFlat ↦ isFlat_of_deleteElem_isFlat F_isFlat.1 F_isFlat.2.1,
   fun F F' F_IsFlat F_sub_F' F'_IsFlat ↦ _, fun X X_sub X_none X_modular ↦ _⟩
  · have F'_ground : F' ⊆ M.E
    · apply F'_IsFlat.subset_ground.trans
      rw [deleteElem, delete_ground]
      exact diff_subset _ _
    have e_nE : e ∉ (M ＼ e).E
    · rw [deleteElem, delete_ground]
      exact fun e_mem ↦ absurd (rfl) e_mem.2
    have e_in_closure_F' : e ∈ M.closure F' \ F' := ⟨(M.closure_subset_closure F_sub_F' F_IsFlat.2.2),
     notMem_subset F'_IsFlat.subset_ground e_nE⟩
    refine' ⟨e_in_closure_F'.2, _⟩
    rw [isFlat_iff_closure_self, closure_insert_eq_of_mem_closure e_in_closure_F'.1]
    refine' ⟨subset_antisymm _ (insert_subset e_in_closure_F'.1 (M.subset_closure _)), e_in_closure_F'.1⟩
    · rw [isFlat_iff_closure_self, deleteElem, delete_closure_eq,
       diff_singleton_eq_self e_in_closure_F'.2] at F'_IsFlat
      nth_rw 2 [← F'_IsFlat]
      simp only [mem_diff, mem_singleton_iff, not_true_eq_false, and_false, insert_diff_singleton,
        subset_insert]
  obtain ⟨x, hx⟩ := X_none
  have inter_isFlat : M.IsFlat (insert e (sInter X))
  · rw [sInter_insert_each]
    apply IsFlat.sInter
    · refine' ⟨insert e x, ⟨x, hx, rfl⟩⟩
    rintro F ⟨x', x'_mem, rfl⟩
    exact (X_sub x'_mem).2.1
  refine' ⟨_, inter_isFlat, _⟩
  · rw [mem_sInter]; push_neg
    refine' ⟨x, hx, (X_sub hx).1⟩
  · rw [← iInter_closure_eq_closure_sInter_of_modular (M.modular_of_modular_restrict X
     (sUnion_subset _) X_modular) ⟨x, hx⟩]
    · simp only [mem_iInter]
      intro i i_mem
      exact (X_sub i_mem).2.2
    intro t' t'_mem
    exact (subset_insert _ _).trans (X_sub t'_mem).2.1.subset_ground

@[simp] theorem matroid_of_cut_indep_iff (M : Matroid α) (C : Set (Set α)) (hC : M.Modular_cut C)
    {e : α} (e_nE : e ∉ M.E) :
    (M.matroid_of_cut hC e_nE).Indep I ↔ if (e ∈ I) then (M.Indep (I \ {e}) ∧ M.closure (I \ {e}) ∉ C)
    else M.Indep I := by
  simp [matroid_of_cut]; rfl

@[simp] theorem matroid_of_cut_ground_eq (M : Matroid α) (C : Set (Set α)) (hC : M.Modular_cut C)
    {e : α} (e_nE : e ∉ M.E) : (M.matroid_of_cut hC e_nE).E = insert e M.E := by
  simp [matroid_of_cut]; rfl

def Modular_cut_equiv (M : Matroid α) (e_nE : e ∉ M.E) :
    {C | M.Modular_cut C} ≃ {N | (N ＼ e) = M} where
  toFun := fun C ↦ ⟨M.matroid_of_cut C.2 e_nE, by
    apply ext_iff_indep.2
    refine' ⟨by simp [e_nE], _⟩
    simp [e_nE]
    intro I I_sub
    rw [if_neg (notMem_subset I_sub e_nE), and_iff_left (notMem_subset I_sub e_nE)]
  ⟩
  invFun := fun N ↦ ⟨{F | e ∉ F ∧ N.1.IsFlat (insert e F) ∧ e ∈ N.1.closure F}, by
    have M_eq := N.2
    dsimp at M_eq ⊢
    simp_rw [← M_eq]
    exact modular_cut_of_isFlats_remove
  ⟩
  left_inv := by
    intro x
    simp [e_nE, matroid_of_cut];
    dsimp
    sorry
  right_inv := sorry
