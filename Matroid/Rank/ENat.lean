import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Combinatorics.Matroid.Rank.Finite
import Matroid.Loop
import Matroid.OnUniv
import Matroid.ForMathlib.Other
import Matroid.ForMathlib.Matroid.Sum
import Mathlib.Tactic.TautoSet

/- The rank `M.eRk X` of a set `X` in a matroid `M` is the size of one of its bases,
as a term in `ℕ∞`.
When such bases are infinite, this quantity is too coarse to be useful for building API,
even though it is often the easiest way to do things for finite matroids. -/

open Set ENat

namespace Matroid

universe u v

variable {α ι : Type*} {M N : Matroid α} {I B X X' Y Y' Z R : Set α} {n : ℕ∞} {e f : α}

section Basic

-- lemma IsRkFinite.eRk_ne_top (h : M.IsRkFinite X) : M.eRk X ≠ ⊤ :=
--   h.eRk_lt_top.ne

lemma spanning_iff_eRk' [RankFinite M] : M.Spanning X ↔ M.eRank ≤ M.eRk X ∧ X ⊆ M.E := by
  refine ⟨fun h ↦ ⟨h.eRk_eq.symm.le, h.subset_ground⟩, fun ⟨h, hX⟩ ↦ ?_⟩
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  exact (hI.indep.isBase_of_eRk_ge
    hI.indep.finite (h.trans hI.eRk_eq_eRk.symm.le)).spanning_of_superset hI.subset

lemma spanning_iff_eRk [RankFinite M] (hX : X ⊆ M.E := by aesop_mat) :
    M.Spanning X ↔ M.eRank ≤ M.eRk X := by
  rw [spanning_iff_eRk', and_iff_left hX]

lemma IsLoopEquiv.eRk_eq_eRk (h : M.IsLoopEquiv X Y) : M.eRk X = M.eRk Y := by
  rw [← M.eRk_closure_eq, h.closure_eq_closure, M.eRk_closure_eq]

@[simp]
lemma eRank_lt_top [M.RankFinite] : M.eRank < ⊤ := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← hB.encard_eq_eRank, encard_lt_top_iff]
  exact hB.finite


-- lemma dual_eRk_add_eRank (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
  --   M✶.eRk X + M.eRank = M.eRk (M.E \ X) + X.encard := by
  -- obtain ⟨I, hI⟩ := M✶.exists_isBasis X
  -- obtain ⟨B, hB, rfl⟩ := hI.exists_isBasis_inter_eq_of_superset hX
  -- have hB' : M✶.IsBase B := isBasis_ground_iff.1 hB
  -- have hd : M.IsBasis (M.E \ B ∩ (M.E \ X)) (M.E \ X) := by
  --   simpa using hB'.inter_isBasis_iff_compl_inter_isBasis_dual.1 hI
  -- rw [← hB'.compl_isBase_of_dual.encard_eq_eRank, hI.eRk_eq_encard, hd.eRk_eq_encard,
  --   ← encard_union_eq (by tauto_set), ← encard_union_eq (by tauto_set)]
  -- exact congr_arg _ (by tauto_set)

-- lemma dual_eRk_add_eRank' (M : Matroid α) (X : Set α) :
--     M✶.eRk X + M.eRank = M.eRk (M.E \ X) + (X ∩ M.E).encard := by
--   rw [← diff_inter_self_eq_diff, ← dual_eRk_add_eRank .., ← dual_ground, eRk_inter_ground]

-- lemma eRank_add_dual_eRank (M : Matroid α) : M.eRank + M✶.eRank = M.E.encard := by
--   obtain ⟨B, hB⟩ := M.exists_isBase
--   rw [← hB.encard_eq_eRank, ← hB.compl_isBase_dual.encard_eq_eRank,
--     ← encard_union_eq disjoint_sdiff_right, union_diff_cancel hB.subset_ground]

end Basic

section Constructions


variable {E : Set α}


@[simp] lemma disjointSum_eRk_eq (M N : Matroid α) (hMN : Disjoint M.E N.E) (X : Set α) :
    (M.disjointSum N hMN).eRk X = M.eRk (X ∩ M.E) + N.eRk (X ∩ N.E) := by
  obtain ⟨B₁, hB₁⟩ := M.exists_isBasis (X ∩ M.E)
  obtain ⟨B₂, hB₂⟩ := N.exists_isBasis (X ∩ N.E)
  rw [← eRk_inter_ground, disjointSum_ground_eq, inter_union_distrib_left,
    (hB₁.disjointSum_isBasis_union hB₂ hMN).eRk_eq_encard, hB₁.eRk_eq_encard, hB₂.eRk_eq_encard,
    encard_union_eq (hMN.mono hB₁.indep.subset_ground hB₂.indep.subset_ground)]

@[simp] lemma disjointSum_eRank_eq (M N : Matroid α) (hMN : Disjoint M.E N.E) :
    (M.disjointSum N hMN).eRank = M.eRank + N.eRank := by
  rw [eRank_def, eRank_def, eRank_def, disjointSum_eRk_eq, disjointSum_ground_eq,
    inter_eq_self_of_subset_right subset_union_left,
    inter_eq_self_of_subset_right subset_union_right]

end Constructions


lemma eRk_eq_iSup_finset_eRk (M : Matroid α) (X : Set α) :
    M.eRk X = ⨆ Y ∈ {S : Finset α | (S : Set α) ⊆ X}, M.eRk Y := by
  simp only [mem_setOf_eq, le_antisymm_iff, iSup_le_iff]
  refine ⟨?_, fun S hSX ↦ M.eRk_mono hSX⟩

  by_cases hX : M.IsRkFinite X
  · obtain ⟨I, hI⟩ := hX.exists_finset_isBasis'
    exact le_iSup₂_of_le (i := I) hI.subset <| by rw [hI.eRk_eq_eRk]

  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [← eRk_eq_top_iff] at hX
  rw [hX, top_le_iff, WithTop.eq_top_iff_forall_le]
  intro n
  rw [hI.eRk_eq_encard, encard_eq_top_iff] at hX
  obtain ⟨J, hJI, rfl⟩ := hX.exists_subset_card_eq n
  apply le_iSup₂_of_le J (hJI.trans hI.subset)
  rw [(hI.indep.subset hJI).eRk_eq_encard, encard_coe_eq_coe_finsetCard]
  rfl

lemma eRk_union_eq_of_subset_of_eRk_le_eRk (Z : Set α) (hXY : X ⊆ Y) (hr : M.eRk Y ≤ M.eRk X) :
    M.eRk (X ∪ Z) = M.eRk (Y ∪ Z) := by
  obtain hX' | hX' := em (M.IsRkFinite X)
  · rw [← eRk_union_closure_left_eq, hX'.closure_eq_closure_of_subset_of_eRk_ge_eRk hXY hr,
      eRk_union_closure_left_eq]
  rw [eRk_eq_top_iff.2, eRk_eq_top_iff.2]
  · contrapose! hX'
    exact hX'.subset (hXY.trans subset_union_left)
  contrapose! hX'
  exact hX'.subset subset_union_left

lemma eRk_union_eq_of_subsets_of_eRks_le (hX : X ⊆ X') (hY : Y ⊆ Y') (hXX' : M.eRk X' ≤ M.eRk X)
    (hYY' : M.eRk Y' ≤ M.eRk Y) : M.eRk (X ∪ Y) = M.eRk (X' ∪ Y') := by
  rw [eRk_union_eq_of_subset_of_eRk_le_eRk _ hX hXX', union_comm,
    eRk_union_eq_of_subset_of_eRk_le_eRk _ hY hYY', union_comm]

lemma not_isRkFinite_of_eRk_ge (h : ¬M.IsRkFinite X) (hXY : M.eRk X ≤ M.eRk Y) :
    ¬M.IsRkFinite Y := by
  contrapose! h
  exact eRk_lt_top_iff.1 <| hXY.trans_lt h.eRk_lt_top

lemma eRk_restrict (M : Matroid α) (R X : Set α) : (M ↾ R).eRk X = M.eRk (X ∩ R) := by
  rw [← eRk_inter_ground, restrict_ground_eq, inter_comm, ← eRank_restrict,
    restrict_restrict_eq _ inter_subset_left, eRank_restrict]

@[simp]
lemma eRk_restrict_univ (M : Matroid α) (X : Set α) : (M ↾ univ).eRk X = M.eRk (X) := by
  rw [eRk_restrict, inter_univ]
