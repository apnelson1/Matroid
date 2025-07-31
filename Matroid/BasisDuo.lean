import Mathlib.Data.Matroid.Closure
import Matroid.Constructions.Project

open Set

namespace Matroid

variable {α : Type*} {M : Matroid α} {I J K X Y Z : Set α}

lemma closure_subset_closure_iff_inter_ground_subset_closure (M : Matroid α) (X Y : Set α) :
    M.closure X ⊆ M.closure Y ↔ X ∩ M.E ⊆ M.closure Y := by
  rw [← closure_inter_ground, closure_subset_closure_iff_subset_closure]

lemma Indep.isBasis'_of_subset_of_subset_closure (hI : M.Indep I) (hIX : I ⊆ X)
    (hXI : X ∩ M.E ⊆ M.closure I) : M.IsBasis' I X := by
  rw [isBasis'_iff_isBasis_closure, and_iff_left hIX]
  exact hI.isBasis_of_subset_of_subset_closure (M.subset_closure_of_subset' hIX) <|
    by simpa using M.closure_subset_closure_of_subset_closure hXI

lemma Indep.isBasis'_of_subset_of_closure_subset_closure (hI : M.Indep I) (hIX : I ⊆ X)
    (hXI : M.closure X ⊆ M.closure I) : M.IsBasis' I X :=
  hI.isBasis'_of_subset_of_subset_closure hIX <| (M.inter_ground_subset_closure ..).trans hXI

lemma IsBasis'.isBasis'_superset (hI : M.IsBasis' I X) (hXY : X ⊆ Y)
    (hYX : Y ∩ M.E ⊆ M.closure X) : M.IsBasis' I Y :=
  hI.indep.isBasis'_of_subset_of_subset_closure (hI.subset.trans hXY) <|
    by rwa [hI.closure_eq_closure]

lemma IsBasis'.isBasis_superset_of_closure (hI : M.IsBasis' I X) (hXY : X ⊆ Y)
    (hYX : M.closure Y ⊆ M.closure X) : M.IsBasis' I Y := by
  rw [closure_subset_closure_iff_inter_ground_subset_closure] at hYX
  exact hI.isBasis'_superset hXY hYX

lemma IsBasis'.isBasis'_subset (hI : M.IsBasis' I X) (hIY : I ⊆ Y) (hYX : Y ⊆ X) :
    M.IsBasis' I Y := by
  rw [isBasis'_iff_isBasis_inter_ground] at hI ⊢
  exact hI.isBasis_subset (subset_inter hIY hI.indep.subset_ground) <| by grw [hYX]

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

-- lemma isBasis'_inter_of_subset (h : M.IsBasisDuo I J X Y) (hIJ : I ⊆ J) :

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

lemma _root_.Matroid.IsBasis'.exists_isBasisDuo (hI : M.IsBasis' I X) (hIY : I ⊆ Y) :
    ∃ J, M.IsBasisDuo I J X Y ∧ I ⊆ J := by
  obtain ⟨I', J, h, hI', hJ⟩ := hI.indep.exists_isBasisDuo hI.subset hIY
  obtain rfl : I = I' := hI.eq_of_subset_indep h.isBasis'_left.indep hI' h.isBasis'_left.subset
  exact ⟨J, h, hJ⟩

lemma isBasisDuo_inter_left (h : M.IsBasisDuo I J X Y) : M.IsBasisDuo (I ∩ J) I (X ∩ Y) X where
  isBasis'_left := h.isBasis'_inter
  isBasis'_right := h.isBasis'_left
  isBasis'_inter := by simpa [inter_right_comm] using h.isBasis'_inter

lemma isBasisDuo_inter_right (h : M.IsBasisDuo I J X Y) : M.IsBasisDuo (I ∩ J) J (X ∩ Y) Y := by
  rw [inter_comm, inter_comm X]
  exact h.symm.isBasisDuo_inter_left

protected lemma mono_left (h : M.IsBasisDuo I J X Y) (hIZ : I ⊆ Z) (hZX : Z ⊆ X) :
    M.IsBasisDuo I J Z Y where
  isBasis'_left := h.isBasis'_left.isBasis'_subset hIZ hZX
  isBasis'_right := h.isBasis'_right
  isBasis'_inter := h.isBasis'_inter.isBasis'_subset (by grw [hIZ, h.subset_right]) <| by grw [hZX]

protected lemma mono_right (h : M.IsBasisDuo I J X Y) (hJZ : J ⊆ Z) (hZX : Z ⊆ Y) :
    M.IsBasisDuo I J X Z :=
  (h.symm.mono_left hJZ hZX).symm

protected lemma trans_of_subset_subset (h : M.IsBasisDuo I J X Y) (h' : M.IsBasisDuo J K Y Z)
    (hXZY : X ∩ Z ⊆ Y) (hYZ : Y ⊆ Z) : M.IsBasisDuo I K X Z where
  isBasis'_left := h.isBasis'_left
  isBasis'_right := h'.isBasis'_right
  isBasis'_inter := by
    rw [show X ∩ Z = X ∩ Y by simpa [subset_antisymm_iff, inter_subset_right.trans hYZ],
      ← h.isBasis'_inter.eq_of_subset_indep (h.indep_left.inter_right K)
        (by grw [h'.subset_of_subset hYZ])
        (subset_inter (by grw [h.subset_left, inter_subset_left])
          (by grw [← hXZY, h.subset_left, h'.subset_right]))]
    exact h.isBasis'_inter

-- Lemmas like this should be derived as special cases of the case where `X,Y` is a modular pair.
protected lemma superset_right' (h : M.IsBasisDuo I J X Y) (hIJ : I ⊆ J) (hJZ : J ⊆ Z)
    (hZY : Z ∩ M.E ⊆ M.closure Y) : M.IsBasisDuo I J X Z where
  isBasis'_left := h.isBasis'_left
  isBasis'_right := h.indep_right.isBasis'_of_subset_of_subset_closure hJZ <|
    by grw [hZY, h.isBasis'_right.closure_eq_closure]
  isBasis'_inter := by
    refine h.indep_inter.isBasis'_of_subset_of_subset_closure (by grw [h.subset_left, hJZ]) ?_
    grw [inter_eq_self_of_subset_left hIJ, h.isBasis'_left.closure_eq_closure,
      inter_subset_left (s := X), inter_ground_subset_closure]

protected lemma superset_left' (h : M.IsBasisDuo I J X Y) (hIJ : I ⊆ J) (hIZ : I ⊆ Z)
    (hZX : Z ∩ M.E ⊆ M.closure X) : M.IsBasisDuo I J Z Y where
  isBasis'_left := h.indep_left.isBasis'_of_subset_of_subset_closure hIZ <|
    by rwa [h.isBasis'_left.closure_eq_closure]
  isBasis'_right := h.isBasis'_right
  isBasis'_inter := by
    refine h.indep_inter.isBasis'_of_subset_of_subset_closure (by grw [h.subset_right, hIZ]) ?_
    grw [inter_inter_distrib_right, hZX, inter_eq_self_of_subset_left hIJ,
    ← h.isBasis'_left.closure_eq_closure, inter_subset_left]

protected lemma exists_extend_right (h : M.IsBasisDuo I J X Y) (hXY : X ∩ Z ⊆ Y) (hYZ : Y ⊆ Z) :
    ∃ K, M.IsBasisDuo I K X Z ∧ M.IsBasisDuo J K Y Z := by
  obtain ⟨K, hK⟩ := h.isBasis'_right.exists_isBasisDuo (h.subset_right.trans hYZ)
  exact ⟨K, h.trans_of_subset_subset hK.1 hXY hYZ, hK.1⟩

protected lemma exists_extend_left (h : M.IsBasisDuo I J X Y) (hYX : Y ∩ Z ⊆ X) (hXZ : X ⊆ Z) :
    ∃ K, M.IsBasisDuo K J Z Y ∧ M.IsBasisDuo K I Z X := by
  obtain ⟨K, hK⟩ := h.symm.exists_extend_right hYX hXZ
  exact ⟨K, hK.1.symm, hK.2.symm⟩

protected lemma closure_union (h : M.IsBasisDuo I J X Y) :
    M.closure (I ∪ J) = M.closure (X ∪ Y) := by
  rw [closure_union_congr_left h.isBasis'_left.closure_eq_closure,
    closure_union_congr_right h.isBasis'_right.closure_eq_closure]

lemma _root_.Matroid.exists_isBasisDuo_union (M : Matroid α) (X Y : Set α) :
    ∃ I J K, M.IsBasisDuo I J X Y ∧ M.IsBasisDuo I K X (X ∪ Y) ∧ I ⊆ K ∧ M.IsBasis K (I ∪ J) := by
  obtain ⟨I, J, h⟩ := M.exists_isBasisDuo X Y
  obtain ⟨K, hK, hIK⟩ := h.isBasis'_left.exists_isBasisDuo (Y := I ∪ J) subset_union_left
  refine ⟨I, J, K, h, hK.superset_right' hIK ?_ ?_, hIK, hK.isBasis_right⟩
  · grw [hK.subset_right, h.subset_left, h.subset_right]
  grw [inter_ground_subset_closure, h.closure_union]

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
