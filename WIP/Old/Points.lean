import Matroid.Simple
import Matroid.ForMathlib.Card

open Set
open PSetoid

namespace Matroid

variable {α : Type*} {M : Matroid α}

/-- The number of parallel classes (or equivalently, points) of a matroid. -/
@[pp_dot] noncomputable def point_count (M : Matroid α) :=
  (classes M.Parallel).encard

theorem point_count_eq_num_points (M : Matroid α) :
    M.point_count = {P | M.Point P}.encard := by
  rw [point_count, encard_congr]; exact M.parallel_point_equiv

theorem point_count_eq_card_iff_simple [Finite M] :
    M.point_count = M.E.encard ↔ M.Simple := by
  rw [point_count, ← ENat.finsum_mem_one_eq]

/-- rank-`k` isFlats of `M ／ e` correspond to rank-`(k+1)` isFlats of `M` containing `e`. -/
def Nonloop.contract_isFlat_equiv (he : M.Nonloop e) (k : ℕ) :
  {F // (M ／ e).IsFlat F ∧ (M ／ e).eRk F = k} ≃ {F // M.IsFlat F ∧ M.eRk F = k + 1 ∧ e ∈ F} where
    toFun := fun F ↦ ⟨insert e F, by
      obtain ⟨F, hF⟩ := F
      rw [he.contract_isFlat_iff, ← WithTop.add_right_cancel_iff WithTop.one_ne_top,
        he.contract_eRk_add_one_eq] at hF
      simp [hF.1.1, hF.2] ⟩
    invFun := fun F ↦ ⟨F \ {e}, by
      obtain ⟨F, hF⟩ := F
      rw [he.contract_isFlat_iff, insert_diff_singleton, insert_eq_of_mem hF.2.2,
        ← WithTop.add_right_cancel_iff WithTop.one_ne_top, and_iff_right hF.1,
        he.contract_eRk_add_one_eq, and_iff_right (fun h ↦ h.2 rfl)]
      simp only [mem_diff, mem_singleton_iff, not_true, and_false,
        insert_diff_singleton, insert_eq_of_mem hF.2.2]
      exact hF.2.1 ⟩
    left_inv := fun ⟨F, hF⟩ ↦ by simp [show e ∉ F from fun heF ↦ (hF.1.subset_ground heF).2 rfl]
    right_inv := fun ⟨F, hF⟩ ↦ by simp [hF.2.2]

theorem Nonloop.point_count_contract_eq (he : M.Nonloop e) :
    (M ／ e).point_count = {L | M.IsLine L ∧ e ∈ L}.encard := by
  rw [point_count_eq_num_points]
  apply encard_congr
  simp only [coe_setOf]
  convert he.contract_isFlat_equiv 1 using 2
  ext L
  simp [IsLine, and_assoc, one_add_one_eq_two]

-- theorem foo (hM : M.simple) (he : e ∈ M.E) : M.E
