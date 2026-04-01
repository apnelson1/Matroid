import Matroid.Modular.Flat
import Matroid.Connectivity.Minor

open Set Function

variable {ι α : Type*} {M : Matroid α} {B I J T T X X' Y Y' F F' F₀ F₁ F₂ : Set α} {e : α}

namespace Matroid

structure FE (M : Matroid α) (T : Set α) where
  subset_ground : T ⊆ M.E
  closure_inter_subset : ∀ X Y C, X ⊆ T → Y ⊆ T → C ⊆ M.E → Disjoint C T →
    M.closure (X ∪ C) ∩ M.closure (Y ∪ C) ⊆ M.closure (X ∩ Y ∪ C)

private lemma FE.defect_inter_le_aux (h : M.FE T) (hX : X ⊆ M.E) (hY : Y ⊆ M.E) (hXY : X ⊆ Y ∪ T)
    (hYX : Y ⊆ (X ∪ T)) :
    (M.project ((X ∩ Y ∩ T))).eLocalConn (X ∩ T) (Y ∩ T) ≤ (M.project (X ∩ Y)).eLocalConn X Y := by
  set N := M.project (X ∩ Y ∩ T) with hN
  rw [← diff_union_inter (X ∩ Y) T,
    union_comm, ← project_project, ← hN, N.eLocalConn_project_eq_eLocalConn_contract_diff,
    show X \ ((X ∩ Y) \ T) = X ∩ T by grind, show Y \ ((X ∩ Y) \ T) = Y ∩ T by grind,
    ← eLocalConn_project_eq_eLocalConn_contract]
  set U := (X ∩ Y) \ T with hU
  obtain ⟨I₁, hI₁⟩ := (N.project (X ∩ T)).exists_isBasis U (by grind)
  obtain ⟨I₂, hI₂⟩ := ((N.project I₁).project (Y ∩ T)).exists_isBasis U (by grind)
  have hclX : U ⊆ M.closure (X ∩ T ∪ (I₁ ∪ I₂)) := by
    grw [← union_comm, ← project_closure, ← subset_union_left, hI₁.subset_closure, hN,
      project_project, union_eq_self_of_subset_left (by grind)]
  have hclY : U ⊆ M.closure (Y ∩ T ∪ (I₁ ∪ I₂)) := by
    grw [union_comm I₁, ← union_assoc, ← project_closure, ← union_comm, ← project_closure,
      hI₂.subset_closure, N.project_project, M.project_project I₁, project_project,
      union_eq_self_of_subset_left (by grind)]
  have hT := h.closure_inter_subset (X ∩ T) (Y ∩ T) (I₁ ∪ I₂) inter_subset_right inter_subset_right
    (by grind) (by grind)
  have hwin := (subset_inter hclX hclY).trans hT
  rw [← inter_inter_distrib_right, union_comm, ← project_closure, ← hN] at hwin
  replace hwin : N.closure U = N.closure (I₁ ∪ I₂) :=
    (N.closure_subset_closure_of_subset_closure hwin).antisymm <|
      by grw [hI₁.subset, hI₂.subset, union_self]
  grw [eLocalConn_le_eLocalConn_project_add_left (C := I₁),
    (hI₁.indep.skew_of_project (by grind)).symm.eLocalConn,
    eLocalConn_le_eLocalConn_project_add_right (C := I₂),
    (hI₂.indep.skew_of_project (by grind)).symm.eLocalConn, add_zero, add_zero, project_project,
    ← project_closure_eq, ← hwin, project_closure_eq]

lemma FE.defect_inter_le (hT : M.FE T) (X Y : Set α) :
    (M.project ((X ∩ T) ∩ (Y ∩ T))).eLocalConn (X ∩ T) (Y ∩ T) ≤
    (M.project (X ∩ Y)).eLocalConn X Y := by
  let X' := X ∩ (Y ∪ T) ∩ M.E
  let Y' := Y ∩ (X ∪ T) ∩ M.E
  have hi : X' ∩ Y' = (X ∩ Y) ∩ M.E := by grind
  have hXT : X' ∩ T = (X ∩ T) ∩ M.E := by grind
  have hYT : Y' ∩ T = (Y ∩ T) ∩ M.E := by grind
  grw [← project_inter_ground, inter_inter_distrib_right, ← eLocalConn_inter_ground, project_ground,
    ← hXT, ← hYT, ← inter_inter_distrib_right, hT.defect_inter_le_aux (by grind) (by grind)
    (by grind) (by grind), hi, project_inter_ground, ← eLocalConn_inter_ground, project_ground,
     eLocalConn_mono _ (X := X) (Y := Y) (by grind) (by grind)]

lemma FE.foo [M.RankFinite] (hTE : T ⊆ M.E)
    (hdef : ∀ X Y,
      (M.project (X ∩ Y ∩ T)).eLocalConn (X ∩ T) (Y ∩ T) ≤ (M.project (X ∩ Y)).eLocalConn X Y) :
    M.FE T := by
  refine ⟨hTE, fun X Y C hX hY hCE hCT e ⟨heX, heY⟩ ↦ ?_⟩

  by_cases! heT : e ∉ T
  · specialize hdef (insert e (X ∪ C)) (insert e (Y ∪ C))
    rw [inter_assoc, insert_inter_of_notMem heT, insert_inter_of_notMem (by grind),
      insert_inter_of_notMem heT, ← insert_inter_distrib, ← inter_union_distrib_right,
      ← inter_assoc, ← inter_union_distrib_right] at hdef
    simp_rw [union_inter_distrib_right, hCT.inter_eq, union_empty] at hdef



  -- wlog hCT : Disjoint C T generalizing X Y C with aux
  -- · specialize aux (X ∪ (C ∩ T)) (Y ∪ (C ∩ T)) (C \ T) (union_subset hX inter_subset_right)
  --     (union_subset hY inter_subset_right) (by grind) disjoint_sdiff_left
  --   rw [union_assoc, inter_union_diff, union_assoc, inter_union_diff,
  --     ← inter_union_distrib_right, union_assoc, inter_union_diff] at aux



    -- have := aux (X ∪ (C ∩ T)) (Y ∪ (C ∩ T)) (C \ T) (by grind) (by grind)
  sorry

#exit
/-- What is the actual geometric condition that works for infinite matroids? -/
structure FullyEmbedded (M : Matroid α) (T : Set α) where
  subset_ground : T ⊆ M.E
  defect_inter_le' : ∀ X Y, X ⊆ M.E → Y ⊆ M.E → X ⊆ Y ∪ T → Y ⊆ X ∪ T →
    (M.project ((X ∩ T) ∩ (Y ∩ T))).eLocalConn (X ∩ T) (Y ∩ T) ≤
    (M.project (X ∩ Y)).eLocalConn X Y

lemma FullyEmbedded.defect_inter_le (hT : M.FullyEmbedded T) (X Y : Set α) :
    (M.project ((X ∩ T) ∩ (Y ∩ T))).eLocalConn (X ∩ T) (Y ∩ T) ≤
    (M.project (X ∩ Y)).eLocalConn X Y := by
  let X' := X ∩ (Y ∪ T) ∩ M.E
  let Y' := Y ∩ (X ∪ T) ∩ M.E
  have hi : X' ∩ Y' = (X ∩ Y) ∩ M.E := by grind
  have hXT : X' ∩ T = (X ∩ T) ∩ M.E := by grind
  have hYT : Y' ∩ T = (Y ∩ T) ∩ M.E := by grind
  grw [← project_inter_ground, inter_inter_distrib_right, ← eLocalConn_inter_ground, project_ground,
    ← hXT, ← hYT, hT.defect_inter_le' X' Y' inter_subset_right (by grind) (by grind) (by grind),
    hi, project_inter_ground, ← eLocalConn_inter_ground, project_ground,
    eLocalConn_mono _ (X := X) (Y := Y) (by grind) (by grind)]



-- set_option trace.profiler true in
lemma foo (hTE : T ⊆ M.E)
    (hT : ∀ X Y C, X ⊆ T → Y ⊆ T → M.closure (X ∪ C) ∩ M.closure (Y ∪ C) ⊆ M.closure (X ∩ Y ∪ C)) :
    M.FullyEmbedded T := by
  refine ⟨hTE, fun X Y hXE hYE hXYT hYXT ↦ ?_⟩
  set N := M.project (X ∩ Y ∩ T) with hN
  rw [← inter_inter_distrib_right, inter_assoc, ← diff_union_inter (X ∩ Y) T, ← inter_assoc,
    union_comm, ← project_project, ← hN, N.eLocalConn_project_eq_eLocalConn_contract_diff,
    show X \ ((X ∩ Y) \ T) = X ∩ T by grind, show Y \ ((X ∩ Y) \ T) = Y ∩ T by grind,
    ← eLocalConn_project_eq_eLocalConn_contract]
  set U := (X ∩ Y) \ T with hU
  obtain ⟨I₁, hI₁⟩ := (N.project (X ∩ T)).exists_isBasis U (by grind)

  obtain ⟨I₂, hI₂⟩ := ((N.project I₁).project (Y ∩ T)).exists_isBasis U (by grind)
  have hclX : U ⊆ M.closure (X ∩ T ∪ (I₁ ∪ I₂)) := by
    grw [← union_comm, ← project_closure, ← subset_union_left, hI₁.subset_closure, hN,
      project_project, union_eq_self_of_subset_left (by grind)]
  have hclY : U ⊆ M.closure (Y ∩ T ∪ (I₁ ∪ I₂)) := by
    grw [union_comm I₁, ← union_assoc, ← project_closure, ← union_comm, ← project_closure,
      hI₂.subset_closure, N.project_project, M.project_project I₁, project_project,
      union_eq_self_of_subset_left (by grind)]

  specialize hT (X ∩ T) (Y ∩ T) (I₁ ∪ I₂) inter_subset_right inter_subset_right
  have hwin := (subset_inter hclX hclY).trans hT
  rw [← inter_inter_distrib_right, union_comm, ← project_closure, ← hN] at hwin
  replace hwin : N.closure U = N.closure (I₁ ∪ I₂) :=
    (N.closure_subset_closure_of_subset_closure hwin).antisymm <|
      by grw [hI₁.subset, hI₂.subset, union_self]
  grw [eLocalConn_le_eLocalConn_project_add_left (C := I₁),
    (hI₁.indep.skew_of_project (by grind)).symm.eLocalConn,
    eLocalConn_le_eLocalConn_project_add_right (C := I₂),
    (hI₂.indep.skew_of_project (by grind)).symm.eLocalConn, add_zero, add_zero, project_project,
    ← project_closure_eq, ← hwin, project_closure_eq]
