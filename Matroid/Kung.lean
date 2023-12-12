import Matroid.Simple
import Matroid.ForMathlib.ENatTopology

open Set

variable {α : Type*} {M : Matroid α}
namespace Matroid

noncomputable def numPoints (M : Matroid α) : ℕ∞ := {P | M.Point P}.encard

theorem numPoints_eq_encard_parallelClasses (M : Matroid α) :
    M.numPoints = (M.parallelClasses : Set (Set α)).encard := by
  rw [numPoints, ← encard_univ_coe, M.parallelPointEquiv.symm.encard_univ_eq, encard_univ_coe]

theorem numPoints_eq_encard_ground_simplification (M : Matroid α) :
    M.numPoints = M.simplification.E.encard := by
  rw [numPoints_eq_encard_parallelClasses, M.simplification_equiv.encard_eq]



-- Define relative rank.

-- def foo (M : Matroid α) {F₀ : Set α} (hF₀ : M.Flat F₀) :
--     { F // F₀ ⋖[M] F } ≃ { P // (M ⧸ F₀).Point P } where
--   toFun F := ⟨F \ F₀, by
--     obtain ⟨F, hF⟩ := F

--     rw [Point, flat_contract_iff]
--     simp only [diff_union_self, union_eq_self_of_subset_right hF.subset]
--     rw [and_iff_left (disjoint_sdiff_left), and_iff_right hF.flat_right]

--     have hr := M.contract_er_diff_add_contract_er_diff (empty_subset F₀) hF.subset
--     simp only [contract_empty, diff_empty, hF.er_eq] at hr
--     rw [diff_union_self, union_eq_self_of_subset_right hF.subset, hF.er_eq, add_comm] at hr

--     --hF.er_eq

--     ⟩
--   invFun P := ⟨P ∪ F₀, sorry⟩
--   left_inv := by
--     rintro ⟨F, hF⟩
--     simp only [diff_union_self, Subtype.mk.injEq, union_eq_left]
--     exact hF.subset
--   right_inv := by
--     rintro ⟨P, hP⟩
--     simp only [union_diff_right, Subtype.mk.injEq, sdiff_eq_left]
--     exact (subset_diff.1 hP.subset_ground).2

-- theorem foo {F F' : Set α} (hF : M.Flat F) (hF' : M.Flat F') :
--   M.Parallel

-- theorem point_contract_iff {C P : Set α} (hC : C ⊆ M.E) :
--     (M ⧸ C).Point P ↔ M.cl C ⋖[M] C ∪ P := by
--   rw [Point, flat_contract_iff]
--   rw [← loops_covby_iff, contract_loops_eq]
