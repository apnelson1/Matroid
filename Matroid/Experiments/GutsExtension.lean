import Matroid.Modular.Flat
import Matroid.Connectivity.Separation


open Set BigOperators Set.Notation Function

namespace Matroid

variable {α : Type*} {ι : Type*} {η : Type*} {A : Set η} {M : Matroid α} {B I J X X' Y Y' F : Set α}
    {e : α} {i j : ι} {Xs Ys Is Js : ι → Set α}

-- lemma gcAux (M : Matroid α)
-- (S : M.Partition) (hF : M.IsFlat F) (hB : M.IsBase B)
--     (hBF : M.IsBasis (F ∩ B) F) (hsk : (M ／ F).Skew (S.left \ F) (S.right \ F)) :
--     S.left ⊆ M.closure (B ∩ S.left ∪ (F ∩ B ∩ S.right)) := by
--   suffices aux : S.left ⊆ M.closure (B ∩ S.left ∪ F) by
--     rw [← closure_union_congr_right hBF.closure_eq_closure] at aux
--     convert aux using 2
--     have := hB.subset_ground
--     have := S.union_eq
--     tauto_set
--   have hcl := hsk.closure_union_right_inter_left (S := (B ∩ S.left) \ F)
--     (diff_subset_diff_left inter_subset_right)
--   simp [← union_diff_distrib, contract_closure_eq, diff_union_self,
--     contract_closure_eq] at hcl



def gutsCut (M : Matroid α) (X : ι → Set α) (dj : Pairwise (Disjoint on X))
  (Xu : ⋃ i, X i = M.E) : M.ModularCut where
  carrier := {F | M.IsFlat F ∧ (M.project F).IsSkewFamily X}
  forall_isFlat _ h := h.1
  forall_superset := sorry
  forall_inter := by
    refine fun Gs hGs hne ⟨B, hB⟩ ↦ ⟨IsFlat.sInter hne fun F hF ↦ (hGs hF).1, ?_⟩
    have h₁ (F) (hF : F ∈ Gs) (i) : X i  ⊆ M.closure (B ∩ (X i ∪ F))
    · obtain ⟨hF_flat, hFsk⟩ := hGs hF
      rw [inter_union_distrib_left, inter_comm _ F, closure_union_congr_right
        (show M.closure (F ∩ B) = M.closure F from hB.closure_inter_eq ⟨F, hF⟩),
        ← project_closure, ← inter_eq_right,
        ← (hFsk.skew_compl_singleton i).closure_union_right_inter_left inter_subset_right,
        inter_eq_right]
      have h' : X i ⊆ (M.project F).closure B := by
        rw [project_closure, hB.isBase.spanning.closure_eq_of_superset subset_union_left, ← Xu]
        apply subset_iUnion
      refine h'.trans <| closure_subset_closure _ ?_

      nth_rw 1 [← inter_eq_left.2 (hB.isBase.subset_ground.trans_eq Xu.symm), inter_iUnion]








    -- rintro Q hQ hQne ⟨B, hB⟩
    -- have foo : ∀ F ∈ Q, S.left ⊆ M.closure (B ∩ S.left ∪ (F ∩ B ∩ S.right)) := by
    --   intro F hF
    --   suffices S.left ⊆ M.closure (B ∩ S.left ∪ (F ∩ B)) by
    --     convert this using 2
    --     have := hB.indep.subset_ground
    --     have := S.union_eq
    --     tauto_set
    --   have hFB : M.IsBasis (F ∩ B) F := hB.isBasis_inter ⟨F, hF⟩
    --   rw [closure_union_congr_right hFB.closure_eq_closure]
    --   suffices aux : S.left \ F ⊆ (M ／ F).closure (B ∩ S.left) by
    --     rw [contract_closure_eq] at aux
    --     refine subset_trans (by simp) ((union_subset_union_left F aux).trans ?_)
    --     sorry
    --   -- need API for separators, but this is true because `B \ F` spans `M ／ F`
    --   sorry
