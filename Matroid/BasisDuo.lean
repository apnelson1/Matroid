import Mathlib.Data.Matroid.Closure
import Matroid.Constructions.Project

open Set

namespace Matroid

variable {α : Type*} {M : Matroid α} {I J K X Y Z : Set α}

/-- `M.IsBasisDuo I J X Y` means that `I` and `J` are bases for `X` and `Y` respectively
that intersect in a basis for `X ∩ Y`. -/
structure IsBasisDuo (M : Matroid α) (I J X Y : Set α) : Prop where
  isBasis'_left : M.IsBasis' I X
  isBasis'_right : M.IsBasis' J Y
  isBasis'_inter : M.IsBasis' (I ∩ J) (X ∩ Y)

lemma Indep.exists_isBasisDuo (hK : M.Indep K) (hKX : K ⊆ X) (hKY : K ⊆ Y) :
    ∃ I J, M.IsBasisDuo I J X Y ∧ K ⊆ I ∧ K ⊆ J := by
  obtain ⟨K', hK', hss⟩ := hK.subset_isBasis'_of_subset (subset_inter hKX hKY)
  obtain ⟨I, hI, hIss⟩ := hK'.indep.subset_isBasis'_of_subset (hK'.subset.trans inter_subset_left)
  obtain ⟨J, hJ, hJss⟩ := hK'.indep.subset_isBasis'_of_subset (hK'.subset.trans inter_subset_right)
  refine ⟨I, J, ⟨hI, hJ, ?_⟩, hss.trans hIss, hss.trans hJss⟩
  rwa [← hK'.eq_of_subset_indep (hI.indep.inter_right J) (subset_inter hIss hJss)
    (by grw [hI.subset, hJ.subset])]

lemma exists_isBasisDuo (M : Matroid α) (X Y : Set α) :
    ∃ I J, M.IsBasisDuo I J X Y := by
  obtain ⟨I, J, h, -⟩ := M.empty_indep.exists_isBasisDuo (empty_subset X) (empty_subset Y)
  exact ⟨I, J, h⟩

namespace IsBasisDuo

protected lemma symm (h : M.IsBasisDuo I J X Y) : M.IsBasisDuo J I Y X where
  isBasis'_left := h.isBasis'_right
  isBasis'_right := h.isBasis'_left
  isBasis'_inter := by
    rw [inter_comm, inter_comm Y]
    exact h.isBasis'_inter

lemma isBasis_left (h : M.IsBasisDuo I J X Y) (hX : X ⊆ M.E := by aesop_mat) : M.IsBasis I X := by
  rw [← isBasis'_iff_isBasis]
  exact h.isBasis'_left

lemma isBasis_right (h : M.IsBasisDuo I J X Y) (hX : Y ⊆ M.E := by aesop_mat) : M.IsBasis J Y := by
  rw [← isBasis'_iff_isBasis]
  exact h.isBasis'_right

protected lemma subset_left (h : M.IsBasisDuo I J X Y) : I ⊆ X :=
  h.isBasis'_left.subset

protected lemma subset_right (h : M.IsBasisDuo I J X Y) : J ⊆ Y :=
  h.isBasis'_right.subset

protected lemma indep_left (h : M.IsBasisDuo I J X Y) : M.Indep I :=
  h.isBasis'_left.indep

protected lemma indep_right (h : M.IsBasisDuo I J X Y) : M.Indep J :=
  h.isBasis'_right.indep

protected lemma indep_inter (h : M.IsBasisDuo I J X Y) : M.Indep (I ∩ J) :=
  h.indep_left.inter_right J

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma subset_ground_left (h : M.IsBasisDuo I J X Y) : I ⊆ M.E :=
  h.indep_left.subset_ground

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma subset_ground_right (h : M.IsBasisDuo I J X Y) : J ⊆ M.E :=
  h.indep_right.subset_ground

protected lemma inter_right (h : M.IsBasisDuo I J X Y) : I ∩ Y = I ∩ J :=
  Eq.symm <| h.isBasis'_inter.eq_of_subset_indep (h.indep_left.inter_right Y)
    (by grw [h.subset_right]) (by grw [h.subset_left])

protected lemma inter_left (h : M.IsBasisDuo I J X Y) : X ∩ J = I ∩ J :=
  Eq.symm <| h.isBasis'_inter.eq_of_subset_indep (h.indep_right.inter_left X)
    (by grw [h.subset_left]) (by grw [h.subset_right])

protected lemma subset_of_subset_right (h : M.IsBasisDuo I J X Y) (hIY : I ⊆ Y) : I ⊆ J := by
  rw [← inter_eq_left] at hIY ⊢
  rwa [← h.inter_right]

protected lemma subset_of_subset_left (h : M.IsBasisDuo I J X Y) (hJX : J ⊆ X) : J ⊆ I :=
  h.symm.subset_of_subset_right hJX

protected lemma subset_of_subset (h : M.IsBasisDuo I J X Y) (hXY : X ⊆ Y) : I ⊆ J :=
  h.subset_of_subset_right <| h.subset_left.trans hXY

protected lemma inter_right_of_subset (h : M.IsBasisDuo I J X Y) (hXY : X ⊆ Y) :
    X ∩ J = I := by
  grw [h.inter_left, inter_eq_left, h.subset_of_subset hXY]

protected lemma diff_disjoint_right (h : M.IsBasisDuo I J X Y) : Disjoint (I \ J) Y := by
  grw [disjoint_iff_inter_eq_empty, diff_inter_right_comm, h.inter_right, diff_eq_empty,
    inter_subset_right]

protected lemma diff_disjoint_left (h : M.IsBasisDuo I J X Y) : Disjoint (J \ I) X :=
  h.symm.diff_disjoint_right

lemma isBasis'_diff_project_left (h : M.IsBasisDuo I J X Y) :
    (M.project (X ∩ Y)).IsBasis' (I \ J) X := by
  rw [h.isBasis'_inter.project_eq_project, h.indep_inter.project_isBasis'_iff, union_comm,
    diff_union_inter, and_iff_left disjoint_sdiff_inter.symm,
    union_eq_self_of_subset_left (by grw [inter_subset_left, h.subset_left])]
  exact h.isBasis'_left

lemma isBasis'_diff_project_right (h : M.IsBasisDuo I J X Y) :
    (M.project (X ∩ Y)).IsBasis' (J \ I) Y :=
  inter_comm .. ▸ h.symm.isBasis'_diff_project_left

lemma isBasis_diff_project_left (h : M.IsBasisDuo I J X Y) (hX : X ⊆ M.E := by aesop_mat) :
    (M.project (X ∩ Y)).IsBasis (I \ J) X :=
  h.isBasis'_diff_project_left.isBasis

lemma isBasis_diff_project_right (h : M.IsBasisDuo I J X Y) (hY : Y ⊆ M.E := by aesop_mat) :
    (M.project (X ∩ Y)).IsBasis (J \ I) Y :=
  h.isBasis'_diff_project_right.isBasis

lemma isBasis'_diff_contract_left (h : M.IsBasisDuo I J X Y) :
    (M ／ (X ∩ Y)).IsBasis' (I \ J) (X \ Y) := by
  have h' := h.isBasis'_diff_project_left
  rwa [project_isBasis'_iff_contract_isBasis', diff_self_inter] at h'

lemma isBasis'_diff_contract_right (h : M.IsBasisDuo I J X Y) :
    (M ／ (X ∩ Y)).IsBasis' (J \ I) (Y \ X) :=
  inter_comm .. ▸ h.symm.isBasis'_diff_contract_left


  -- have := h.subset_left.trans hXY
  -- have := h.isBasis'_inter.eq_of_subset_indep h.indep_left inter_subset_left
  --   (subset_inter h.subset_left (h.subset_right.trans hXY))
  -- rw [← inter_eq_left, ← h.inter_left]
