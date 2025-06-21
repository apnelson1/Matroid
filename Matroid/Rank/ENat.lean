import Mathlib.Data.Matroid.Rank.ENat
import Mathlib.Data.Matroid.Rank.Finite
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

section Nullity
/-- The rank-deficiency of a set, as a term in `ℕ∞`. Cannot be defined with subtraction.
For the `ℕ` version, the simpler expression `X.ncard - M.r X` is preferable.

To reduce the number of `X ⊆ M.E` assumptions needed for lemmas,
this is defined so that junk elements in `X \ M.E` contribute to the nullity of `X` in `M`,
so `M.nullity X = M.nullity (X ∩ M.E) + (X \ M.E).encard`.
(see `Matroid.nullity_eq_nullity_inter_ground_add_encard_diff` )-/
noncomputable def nullity (M : Matroid α) (X : Set α) : ℕ∞ := (M ↾ X)✶.eRank

lemma nullity_eq_eRank_restrict_dual (M : Matroid α) (X : Set α) :
    M.nullity X = (M ↾ X)✶.eRank := rfl

lemma nullity_restrict_of_subset (M : Matroid α) (hXY : X ⊆ Y) :
    (M ↾ Y).nullity X = M.nullity X := by
  rw [nullity, restrict_restrict_eq _ hXY, nullity]

lemma nullity_restrict_self (M : Matroid α) (X : Set α) : (M ↾ X).nullity X = M.nullity X :=
  M.nullity_restrict_of_subset rfl.subset

lemma IsBasis'.nullity_eq (hIX : M.IsBasis' I X) : M.nullity X = (X \ I).encard := by
  rw [M.nullity_eq_eRank_restrict_dual,
    ← hIX.isBase_restrict.compl_isBase_dual.encard_eq_eRank, restrict_ground_eq]

lemma IsBasis.nullity_eq (hIX : M.IsBasis I X) : M.nullity X = (X \ I).encard :=
  hIX.isBasis'.nullity_eq

lemma eRk_add_nullity_eq_encard (M : Matroid α) (X : Set α) :
    M.eRk X + M.nullity X = X.encard := by
  have h := (M ↾ X)✶.eRank_add_eRank_dual
  simp only [dual_dual, eRank_restrict, dual_ground, restrict_ground_eq] at h
  rw [← h, add_comm, nullity_eq_eRank_restrict_dual]

lemma Indep.nullity_eq (hI : M.Indep I) : M.nullity I = 0 := by
  rw [hI.isBasis_self.nullity_eq, diff_self, encard_empty]

@[simp] lemma nullity_eq_zero : M.nullity I = 0 ↔ M.Indep I := by
  rw [iff_def, and_iff_left Indep.nullity_eq]
  obtain ⟨J, hJI⟩ := M.exists_isBasis' I
  rw [hJI.nullity_eq, encard_eq_zero, diff_eq_empty]
  exact hJI.indep.subset

lemma IsCircuit.nullity_eq {C : Set α} (hC : M.IsCircuit C) : M.nullity C = 1 := by
  rw [(hC.diff_singleton_isBasis hC.nonempty.some_mem).nullity_eq, diff_diff_cancel_left
     (by simpa using hC.nonempty.some_mem)]
  simp

lemma nullity_le_of_subset (M : Matroid α) (hXY : X ⊆ Y) : M.nullity X ≤ M.nullity Y := by
  rw [← M.nullity_restrict_of_subset hXY, ← M.nullity_restrict_self Y]
  obtain ⟨I, hI⟩ := (M ↾ Y).exists_isBasis X
  obtain ⟨B, hB, rfl⟩ := hI.exists_isBase
  rw [← isBasis_ground_iff, restrict_ground_eq] at hB
  rw [hI.nullity_eq, hB.nullity_eq, diff_inter_self_eq_diff]
  exact encard_le_encard (diff_subset_diff_left hXY)

lemma nullity_supermodular (M : Matroid α) (X Y : Set α) :
    M.nullity X + M.nullity Y ≤ M.nullity (X ∪ Y) + M.nullity (X ∩ Y) := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' (X ∩ Y)
  obtain ⟨Ix, hIx, hIIx⟩ := hI.exists_isBasis'_inter_eq_of_superset inter_subset_left
  obtain ⟨Iy, hIy, hIIy⟩ := hI.exists_isBasis'_inter_eq_of_superset inter_subset_right
  obtain ⟨Iu, hIu, hIxIu⟩ := hIx.exists_isBasis'_inter_eq_of_superset (Y := X ∪ Iy)
    subset_union_left
  have hIu' : M.IsBasis' Iu (X ∪ Y) := by
    rw [isBasis'_iff_isBasis_closure, ← closure_union_congr_right hIy.closure_eq_closure,
      and_iff_left (hIu.subset.trans (union_subset_union_right X hIy.subset))]
    exact hIu.isBasis_closure_right
  rw [hIx.nullity_eq, hIy.nullity_eq, hI.nullity_eq, hIu'.nullity_eq,
    ← encard_union_add_encard_inter]
  refine add_le_add (encard_le_encard ?_) (encard_le_encard ?_)
  · suffices Disjoint (X \ Ix) Iu ∧ Disjoint (Y \ Iy) Iu by
      simpa [subset_diff, diff_subset.trans subset_union_left, diff_subset.trans subset_union_right]
    rw [← hIxIu, diff_inter_self_eq_diff, and_iff_right disjoint_sdiff_left, disjoint_iff_forall_ne]
    rintro e ⟨heY, heIy⟩ _ heIu rfl
    have heX : e ∈ X := by simpa [heIy] using hIu.subset heIu
    exact heIy <| (hIIy.symm.subset <| hIIx.subset ⟨hIxIu.subset ⟨heIu, heX⟩, ⟨heX, heY⟩⟩).1
  rw [← hIIx, diff_inter_self_eq_diff, ← inter_diff_assoc, diff_eq, diff_eq, diff_eq,
    inter_assoc (a := X), inter_assoc X Y, inter_comm _ Y]
  exact inter_subset_left

lemma nullity_insert_eq_add_one (hecl : e ∈ M.closure X) (heX : e ∉ X) :
    M.nullity (insert e X) = M.nullity X + 1 := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  have hI' : M.IsBasis' I (insert e X) := by
    rw [isBasis'_iff_isBasis_closure, closure_insert_eq_of_mem_closure hecl]
    exact ⟨hI.isBasis_closure_right, hI.subset.trans <| subset_insert ..⟩
  rw [hI.nullity_eq, hI'.nullity_eq, insert_diff_of_notMem _ (notMem_subset hI.subset heX),
    encard_insert_of_notMem (notMem_subset diff_subset heX)]

lemma nullity_eq_nullity_inter_ground_add_encard_diff (M : Matroid α) (X : Set α) :
    M.nullity X = M.nullity (X ∩ M.E) + (X \ M.E).encard := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [hI.nullity_eq, hI.isBasis_inter_ground.nullity_eq, ← encard_union_eq]
  · nth_rw 1 [← inter_union_diff X M.E, union_diff_distrib, diff_diff,
      union_eq_self_of_subset_right hI.indep.subset_ground]
  exact disjoint_sdiff_right.mono_left (diff_subset.trans inter_subset_right)

lemma nullity_corestrict_univ_eq (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    (M✶ ↾ univ)✶.nullity X = M.nullity X := by
  nth_rw 2 [← M.corestrict_univ_restrict_ground]
  rw [nullity_restrict_of_subset _ hX]

lemma nullity_corestrict_univ_eq_nullity_inter (M : Matroid α) (X : Set α) :
    (M✶ ↾ univ)✶.nullity X = M.nullity (X ∩ M.E) := by
  obtain ⟨B, hB⟩ := M.exists_isBasis' X
  rw [hB.corestrict_univ_isBasis.nullity_eq, union_comm, ← diff_diff, sdiff_sdiff_right_self,
    hB.isBasis_inter_ground.nullity_eq]
  rfl

lemma nullity_insert (heX : e ∉ M.closure X) (heE : e ∈ M.E := by aesop_mat) :
    M.nullity (insert e X) = M.nullity X := by
  wlog hXE : X ⊆ M.E generalizing X with aux
  · rw [nullity_eq_nullity_inter_ground_add_encard_diff,
      insert_inter_of_mem heE, insert_diff_of_mem _ heE, aux (by simpa) (by simp),
      ← nullity_eq_nullity_inter_ground_add_encard_diff]
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  rw [(hI.insert_isBasis_insert_of_notMem_closure (by rwa [hI.closure_eq_closure])).nullity_eq,
    hI.nullity_eq]
  simp only [mem_insert_iff, true_or, insert_diff_of_mem]
  rw [diff_insert_of_notMem (notMem_subset (subset_closure ..) heX)]

lemma nullity_union_eq_nullity_add_encard_diff (hYX : Y ⊆ M.closure X) :
    M.nullity (X ∪ Y) = M.nullity X + (Y \ X).encard := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  have hI' : M.IsBasis' I (X ∪ Y) := by
    rw [isBasis'_iff_isBasis_closure, and_iff_left (hI.subset.trans subset_union_left),
      ← closure_union_closure_left_eq, union_eq_self_of_subset_right hYX, closure_closure]
    exact hI.isBasis_closure_right
  rw [hI.nullity_eq, hI'.nullity_eq, ← encard_union_eq (disjoint_sdiff_right.mono_left diff_subset)]
  congr
  have := hI.subset
  tauto_set

lemma nullity_eq_nullity_add_encard_diff (hXY : X ⊆ Y) (hYX : Y ⊆ M.closure X) :
    M.nullity Y = M.nullity X + (Y \ X).encard := by
  nth_rw 1 [← union_eq_self_of_subset_left hXY]
  exact nullity_union_eq_nullity_add_encard_diff hYX

lemma Disjoint.nullity_union_eq_of_subset_closure (hXY : Disjoint X Y) (hYX : Y ⊆ M.closure X) :
    M.nullity (X ∪ Y) = M.nullity X + Y.encard := by
  rw [nullity_union_eq_nullity_add_encard_diff hYX, hXY.sdiff_eq_right]

end Nullity

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
