import Matroid.Modular.Flat
import Matroid.Connectivity.Minor

open Set Function

variable {ι α : Type*} {M : Matroid α} {B I J T K X X' Y Y' F F' F₀ F₁ F₂ : Set α} {e : α}

namespace Matroid

/-- What is the actual geometric condition that works for infinite matroids? -/
structure FullyEmbedded (M : Matroid α) (K : Set α) where
  subset_ground : K ⊆ M.E
  defect_inter_le' : ∀ X Y, X ⊆ M.E → Y ⊆ M.E → X ⊆ Y ∪ K → Y ⊆ X ∪ K →
    (M.project ((X ∩ K) ∩ (Y ∩ K))).eLocalConn (X ∩ K) (Y ∩ K) ≤
    (M.project (X ∩ Y)).eLocalConn X Y

lemma FullyEmbedded.defect_inter_le (hK : M.FullyEmbedded K) (X Y : Set α) :
    (M.project ((X ∩ K) ∩ (Y ∩ K))).eLocalConn (X ∩ K) (Y ∩ K) ≤
    (M.project (X ∩ Y)).eLocalConn X Y := by
  let X' := X ∩ (Y ∪ K) ∩ M.E
  let Y' := Y ∩ (X ∪ K) ∩ M.E
  have hi : X' ∩ Y' = (X ∩ Y) ∩ M.E := by grind
  have hXK : X' ∩ K = (X ∩ K) ∩ M.E := by grind
  have hYK : Y' ∩ K = (Y ∩ K) ∩ M.E := by grind
  grw [← project_inter_ground, inter_inter_distrib_right, ← eLocalConn_inter_ground, project_ground,
    ← hXK, ← hYK, hK.defect_inter_le' X' Y' inter_subset_right (by grind) (by grind) (by grind),
    hi, project_inter_ground, ← eLocalConn_inter_ground, project_ground,
    eLocalConn_mono _ (X := X) (Y := Y) (by grind) (by grind)]


lemma foo (hTE : T ⊆ M.E) (hT : ∀ X Y D, X ⊆ T → Y ⊆ T → Disjoint D T →
    M.closure (X ∪ D) ∩ M.closure (Y ∪ D) ∩ M.closure (X ∪ Y) ⊆ M.closure (X ∩ Y)) :
    M.FullyEmbedded T := by
  refine ⟨hTE, fun X Y hXE hYE hXYT hYXT ↦ ?_⟩
  specialize hT (X ∩ T) (Y ∩ T) ((X ∩ Y) \ T) inter_subset_right inter_subset_right
    disjoint_sdiff_left
  rw [← inter_inter_distrib_right] at ⊢ hT

  rw [show X ∩ T ∪ (X ∩ Y) \ T = X ∩ (T \ Y) ∪ (X ∩ Y) by grind] at hT
  nth_rw 1 [← diff_union_inter T Y, inter_union_distrib_left] at hT


-- lemma foo (hKE : K ⊆ M.E)
--     (hK : ∀ ⦃X Y⦄, X ⊆ K → Y ⊆ K → M.closure X ∩ M.closure Y ⊆ M.closure (X ∩ Y)) :
--     M.FullyEmbedded K := by
--   refine ⟨hKE, fun X Y hXE hYE hXYK hYXK ↦ ?_⟩
--   specialize hK (X := X ∩ K) (Y := Y ∩ K) inter_subset_right inter_subset_right
--   rw [← inter_inter_distrib_right] at ⊢ hK

--   obtain ⟨I, hI⟩ := M.exists_isBasis (X ∩ Y ∩ K)
--   obtain ⟨J, hJ, hJI⟩ := hI.exists_isBasis_inter_eq_of_superset (Y := X ∩ Y) inter_subset_left
--   obtain ⟨IX, hIX, hIIX⟩ := hI.exists_isBasis_inter_eq_of_superset (Y := X ∩ K) (by grind)
--   obtain ⟨IY, hIY, hIIY⟩ := hI.exists_isBasis_inter_eq_of_superset (Y := Y ∩ K) (by grind)
--   have hXcl : (M.project I).IsBasis (IX \ I) (X ∩ K) := by
--     rwa [hI.indep.project_isBasis_iff, union_diff_cancel (by grind),
--       and_iff_left disjoint_sdiff_right, union_eq_self_of_subset_left (by grind)]
--   have hYcl : (M.project I).IsBasis (IY \ I) (Y ∩ K) := by
--     rwa [hI.indep.project_isBasis_iff, union_diff_cancel (by grind),
--       and_iff_left disjoint_sdiff_right, union_eq_self_of_subset_left (by grind)]
--   have hXcl' : (M.project J).closure (IX \ I) ⊆ (M.project J).closure X := by
--     grw [diff_subset, ← hJ.project_eq_project, project_closure, project_closure,
--       closure_union_congr_left hIX.closure_eq_closure, inter_subset_left]
--   have hYcl' : (M.project J).closure (IY \ I) ⊆ (M.project J).closure Y := by
--     grw [diff_subset, ← hJ.project_eq_project, project_closure, project_closure,
--       closure_union_congr_left hIY.closure_eq_closure, inter_subset_left]
--   grw [hI.project_eq_project, hXcl.eLocalConn_eq_of_disjoint' hYcl (by grind),
--     ← union_diff_distrib, hI.indep.nullity_project_of_disjoint disjoint_sdiff_right,
--     union_diff_cancel (by grind), hJ.project_eq_project, ← eLocalConn_closure_closure,
--     ← eLocalConn_mono _ hXcl' hYcl', eLocalConn_closure_closure]

  --  ← eLocalConn_closure_closure, project_closure, project_closure,

  --   union_eq_self_of_subset_right (by grind), union_eq_self_of_subset_right (by grind),
  --   ← hIX.closure_eq_closure, ← hIY.closure_eq_closure]
