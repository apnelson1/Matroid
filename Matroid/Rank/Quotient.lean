
import Matroid.Order.Discrepancy

open Set
namespace Matroid

variable {α : Type*} {M N M₁ M₂ : Matroid α} {X Y F : Set α} {e f : α}

lemma ModularCut.extendBy_eRk_eq_eRk (U : M.ModularCut) (heX : e ∉ X) :
    (M.extendBy e U).eRk X = M.eRk X := by
  simp [show (M.extendBy e U).eRk X = (M.extendBy e U ＼ {e}).eRk X by simp [heX],
    extendBy_deleteElem', heX]

lemma ModularCut.extendBy_eRk_insert_eq (U : M.ModularCut) (he : e ∉ M.E) (heX : e ∉ X)
    (hXSU : M.closure X ∈ U) : (M.extendBy e U).eRk (insert e X) = M.eRk X := by
  rw [← eRk_closure_eq, closure_insert_eq_of_mem_closure, eRk_closure_eq,
    U.extendBy_eRk_eq_eRk heX]
  simp [extendBy_closure_eq_insert _ he heX hXSU]

lemma ModularCut.extendBy_rk_insert_eq (U : M.ModularCut) (he : e ∉ M.E) (heX : e ∉ X)
    (hXSU : M.closure X ∈ U) : (M.extendBy e U).rk (insert e X) = M.rk X := by
  rw [rk, U.extendBy_eRk_insert_eq he heX hXSU, rk]

/-- This might be true without the `e ∈ M.E` and `e ∉ X` assumptions -/
lemma ModularCut.extendBy_eRk_insert_eq_of_notMem (U : M.ModularCut) (he : e ∉ M.E) (heX : e ∉ X)
    (hXSU : M.closure X ∉ U) (hecl : e ∉ M.closure X) :
    (M.extendBy e U).eRk (insert e X) = M.eRk X + 1 := by
  rw [eRk_insert_eq_add_one, U.extendBy_eRk_eq_eRk heX]
  simp only [extendBy_E, mem_diff, mem_insert_iff, true_or, true_and]
  rwa [extendBy_closure_eq_self _ he heX hXSU]

/-- This might be true without the `e ∈ M.E` and `e ∉ X` assumptions -/
lemma ModularCut.extendBy_rk_insert_eq_of_notMem [RankFinite M] (U : M.ModularCut) (he : e ∉ M.E)
    (heX : e ∉ X) (hXSU : M.closure X ∉ U) (hecl : e ∉ M.closure X) :
    (M.extendBy e U).rk (insert e X) = M.rk X + 1 := by
  rw [rk, U.extendBy_eRk_insert_eq_of_notMem he heX hXSU hecl]
  simp

lemma ModularCut.eRk_insert_le_eRk_add_one (U : M.ModularCut) :
    (M.extendBy e U).eRk (insert e X) ≤ M.eRk X + 1 := by
  rw [← insert_diff_singleton]
  refine (eRk_insert_le_add_one _ e (X \ {e})).trans ?_
  rw [U.extendBy_eRk_eq_eRk (by simp)]
  exact add_le_add_right (M.eRk_mono (by simp)) _

lemma ModularCut.rk_insert_le_rk_add_one [RankFinite M] {e : α} (U : M.ModularCut) :
    (M.extendBy e U).rk (insert e X) ≤ M.rk X + 1 := by
  rw [← Nat.cast_le (α := ℕ∞), cast_rk_eq, Nat.cast_add, cast_rk_eq, Nat.cast_one]
  exact U.eRk_insert_le_eRk_add_one

lemma ModularCut.eRk_le_extendBy_eRk_insert {e : α} (U : M.ModularCut) :
    M.eRk X ≤ (M.extendBy e U).eRk X  := by
  by_cases heX : e ∈ X
  · sorry
  sorry

lemma ModularCut.rank_ge [RankFinite M] {e : α} (U : M.ModularCut) :
    M.rk X ≤ (M.extendBy e U).rk (insert e X)  := by
  sorry
  -- by_cases hXin : M.closure X ∈ U
  -- · exact Nat.le.intro (congrFun (congrArg HAdd.hAdd (U.extendBy_rk_eq he heX hXin )) 1)
  -- · exact Nat.le_of_eq (U.extendBy_rk_notin he heX hXin hecl )

--lemma foo {a : α} (h : a < a) : False := by exact
