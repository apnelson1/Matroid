import Matroid.Rank.ENat
import Matroid.Constructions.Project

open Set ENat

namespace Matroid

universe u v

variable {α ι : Type*} {M N : Matroid α} {I B X X' Y Y' Z R : Set α} {n : ℕ∞} {e f : α}

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

@[simp]
lemma nullity_restrict_univ (M : Matroid α) : (M ↾ univ).nullity = M.nullity := by
  ext X
  rw [nullity_restrict_of_subset _ (subset_univ X)]

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

@[simp]
lemma nullity_empty (M : Matroid α) : M.nullity ∅ = 0 :=
  M.empty_indep.nullity_eq

@[simp]
lemma nullity_eq_zero : M.nullity I = 0 ↔ M.Indep I := by
  rw [iff_def, and_iff_left Indep.nullity_eq]
  obtain ⟨J, hJI⟩ := M.exists_isBasis' I
  rw [hJI.nullity_eq, encard_eq_zero, diff_eq_empty]
  exact hJI.indep.subset

lemma nullity_eq_encard (hX : X ⊆ M.loops) : M.nullity X = X.encard := by
  rw [(empty_isBasis_iff.mpr hX).nullity_eq, diff_empty]

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

lemma Indep.nullity_le_encard_diff_of_subset (hI : M.Indep I) (hIX : I ⊆ X) :
    M.nullity X ≤ (X \ I).encard := by
  wlog hX : X ⊆ M.E generalizing X with aux
  · have hIE := hI.subset_ground
    grw [nullity_eq_nullity_inter_ground_add_encard_diff, aux (subset_inter hIX hIE)
      inter_subset_right, ← encard_union_eq (by tauto_set)]
    exact encard_le_encard <| by tauto_set
  obtain ⟨J, hJ, hIJ⟩ := hI.subset_isBasis_of_subset hIX
  rw [hJ.nullity_eq]
  exact encard_le_encard <| by tauto_set

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

lemma nullity_union_eq_nullity_contract_add_nullity (M : Matroid α) (X Y : Set α) :
    M.nullity (X ∪ Y) = (M ／ X).nullity (Y \ X) + M.nullity X := by
  wlog h : X ⊆ M.E ∧ Y ⊆ M.E generalizing X Y with aux
  · have hrw : ((X ∪ Y) \ M.E).encard = ((Y \ X) \ (M ／ X).E).encard + (X \ M.E).encard := by
      rw [← encard_union_eq (disjoint_sdiff_left.mono diff_subset diff_subset), contract_ground]
      congr
      tauto_set
    rw [nullity_eq_nullity_inter_ground_add_encard_diff, union_inter_distrib_right,
      aux _ _ (by simp), M.nullity_eq_nullity_inter_ground_add_encard_diff X,
      (M ／ X).nullity_eq_nullity_inter_ground_add_encard_diff, contract_inter_ground_eq, hrw,
      ← show (Y \ X) ∩ (M.E \ X) = (Y ∩ M.E) \ (X ∩ M.E) by tauto_set, contract_ground]
    ring
  obtain ⟨J, hJu, hJi⟩ := M.exists_isBasis_union_inter_isBasis Y X
  have hb : (M ／ X).IsBasis (J \ X) (Y \ X) := by
    simpa using hJu.contract_isBasis hJi (by simpa [diff_union_inter] using hJu.indep)
  rw [union_comm, hJu.nullity_eq, hb.nullity_eq, hJi.nullity_eq, ← encard_union_eq (by tauto_set)]
  congr
  tauto_set

lemma nullity_union_eq_nullity_add_encard_diff (hYX : Y ⊆ M.closure X) :
    M.nullity (X ∪ Y) = M.nullity X + (Y \ X).encard := by
  rw [nullity_union_eq_nullity_contract_add_nullity, add_comm, nullity_eq_encard (X := Y \ X)]
  simpa using diff_subset_diff_left hYX

lemma nullity_eq_nullity_add_encard_diff (hXY : X ⊆ Y) (hYX : Y ⊆ M.closure X) :
    M.nullity Y = M.nullity X + (Y \ X).encard := by
  nth_rw 1 [← union_eq_self_of_subset_left hXY]
  exact nullity_union_eq_nullity_add_encard_diff hYX

lemma nullity_eq_nullity_diff_loops_add_encard (M : Matroid α) (X : Set α) :
    M.nullity X = M.nullity (X \ M.loops) + (X ∩ M.loops).encard := by
  nth_rw 1 [← diff_union_inter X M.loops, nullity_union_eq_nullity_add_encard_diff,
    sdiff_eq_left.2 disjoint_sdiff_inter.symm]
  exact inter_subset_right.trans <| M.closure_subset_closure <| empty_subset _

lemma Disjoint.nullity_union_eq_of_subset_closure (hXY : Disjoint X Y) (hYX : Y ⊆ M.closure X) :
    M.nullity (X ∪ Y) = M.nullity X + Y.encard := by
  rw [nullity_union_eq_nullity_add_encard_diff hYX, hXY.sdiff_eq_right]

-- Todo : golf this proof using `nullity_union_eq_nullity_contract_add_nullity`
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

lemma nullity_add_nullity_le_nullity_union (M : Matroid α) (hdj : Disjoint X Y) :
    M.nullity X + M.nullity Y ≤ M.nullity (X ∪ Y) := by
  grw [M.nullity_supermodular, hdj.inter_eq, nullity_empty, add_zero]

lemma nullity_delete_of_disjoint (M : Matroid α) (hXY : Disjoint X Y) :
    (M ＼ Y).nullity X = M.nullity X := by
  wlog hX : X ⊆ M.E generalizing X with aux
  · rw [nullity_eq_nullity_inter_ground_add_encard_diff,
      aux (hXY.mono_left inter_subset_left), delete_ground, diff_diff_right, hXY.inter_eq,
      union_empty, M.nullity_eq_nullity_inter_ground_add_encard_diff X,
      ← inter_diff_assoc, sdiff_eq_left.2 (hXY.mono_left inter_subset_left)]
    exact inter_subset_right.trans diff_subset
  rw [← restrict_compl, nullity_restrict_of_subset _ (subset_diff.2 ⟨hX, hXY⟩)]

lemma nullity_project_ge (M : Matroid α) (C X : Set α) : M.nullity X ≤ (M.project C).nullity X := by
  wlog hX : X ⊆ M.E generalizing X with aux
  · grw [nullity_eq_nullity_inter_ground_add_encard_diff,
      (M.project C).nullity_eq_nullity_inter_ground_add_encard_diff, project_ground,
      aux _ inter_subset_right]
  obtain ⟨I, hI⟩ := (M.project C).exists_isBasis X
  grw [hI.indep.of_project.nullity_le_encard_diff_of_subset hI.subset, hI.nullity_eq]

lemma nullity_project_mono {C C' : Set α} (M : Matroid α) (hCC' : C ⊆ C') (X : Set α) :
    (M.project C).nullity X ≤ (M.project C').nullity X := by
  rw [← union_eq_self_of_subset_left hCC', ← project_project]
  apply nullity_project_ge

lemma nullity_project_add_nullity_eq (M : Matroid α) (C X : Set α) :
    (M.project C).nullity X + M.nullity C = M.nullity (X ∪ C) + (X ∩ C).encard := by
  wlog hX : X ⊆ M.E generalizing M with aux
  · rw [← nullity_restrict_univ, ← project_restrict_univ, ← M.nullity_restrict_univ,
      aux _ (by simp)]
  rw [(M.project C).nullity_eq_nullity_add_encard_diff (X := X \ C) diff_subset,
    diff_diff_right_self, add_right_comm, union_comm, nullity_union_eq_nullity_contract_add_nullity,
    ← project_delete_self, nullity_delete_of_disjoint _ disjoint_sdiff_left]
  simp only [project_closure, diff_union_self]
  refine M.subset_closure_of_subset' subset_union_left hX

lemma nullity_project_add_nullity_comm (M : Matroid α) (X Y : Set α) :
    (M.project X).nullity Y + M.nullity X = (M.project Y).nullity X + M.nullity Y := by
  rw [nullity_project_add_nullity_eq, nullity_project_add_nullity_eq, union_comm, inter_comm]

lemma nullity_project_eq_nullity_contract (M : Matroid α) {C : Set α} :
    (M.project C).nullity X = (M ／ C).nullity X := by
  rw [← nullity_restrict_univ, ← contract_restrict_univ, nullity_restrict_univ]

lemma nullity_project_le_of_le {C : Set α} (hn : M.nullity X ≤ M.nullity Y)
    (hcl : M.closure X ⊆ M.closure Y) : (M.project C).nullity X ≤ (M.project C).nullity Y := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' C
  grw [hI.project_eq_project, ← add_zero (a := nullity ..), ← add_zero (a := nullity _ Y),
    ← hI.indep.nullity_eq, nullity_project_add_nullity_comm,
    nullity_project_add_nullity_comm (Y := Y), nullity_project_ge (C := Y), project_project,
    ← project_closure_eq, ← closure_closure_union_closure_eq_closure_union,
    union_eq_self_of_subset_left hcl, closure_closure, project_closure_eq, hn]

lemma nullity_project_congr {C : Set α} (hn : M.nullity X = M.nullity Y)
    (hcl : M.closure X = M.closure Y) : (M.project C).nullity X = (M.project C).nullity Y :=
  (nullity_project_le_of_le hn.le hcl.subset).antisymm <|
    nullity_project_le_of_le hn.symm.le hcl.symm.subset



-- lemma nullity_contract_le_of_le {C : Set α} (hn : M.nullity X ≤ M.nullity Y)
--     (hcl : M.closure X ≤ M.closure Y) : (M ／ C).nullity X ≤ (M ／ C).nullity Y := by
--   grw [← nullity_restrict_univ, contract_restrict_univ, nullity_restrict_univ,
--     nullity_project_le_of_le hn hcl]

-- lemma nullity_contract_congr {C : Set α} (hn : M.nullity X = M.nullity Y)
--     (hcl : M.closure X = M.closure Y) : (M ／ C).nullity X = (M ／ C).nullity Y := by
--   rw [← nullity_restrict_univ, contract_restrict_univ, nullity_restrict_univ,
--     nullity_project_congr hn hcl]

lemma IsBasis'.nullity_project {C J : Set α} (hI : M.IsBasis' I X) (hJ : M.IsBasis' J X) :
    (M.project C).nullity I = (M.project C).nullity J := by
  apply nullity_project_congr
  · rw [hI.indep.nullity_eq, hJ.indep.nullity_eq]
  rw [hI.closure_eq_closure, hJ.closure_eq_closure]

lemma IsBasis.nullity_project {C J : Set α} (hI : M.IsBasis I X) (hJ : M.IsBasis J X) :
    (M.project C).nullity I = (M.project C).nullity J :=
  hI.isBasis'.nullity_project hJ.isBasis'

end Matroid
