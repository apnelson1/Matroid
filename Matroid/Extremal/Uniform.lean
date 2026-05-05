import Matroid.Extremal.Covers_
import Matroid.Uniform.Minor
import Matroid.ForMathlib.Data.ENat.Powerset

variable {α : Type*} {M N M' : Matroid α} {I F X Y F' F₀ F₁ F₂ P L H H₁ H₂ H' B C D K : Set α}
  {e f : α} {l r : ℕ} {a k : ℕ∞} {T : Set (Set α)} {ι : Type*} {i j : ι}
  {P P' Q : Set α → Prop}

open Set

namespace Matroid

lemma coverNumber_le_choose_of_eRank_le {a b : ℕ} (ha : a ≠ 0)
    (hM : NoUniformMinor M (a + 1) (b + 1)) (hr : M.eRank = a + 1) :
    M.E.coverNumber (M.RkLE a) ≤ Nat.choose b a := by
  set U := {X ⊆ M.E | (M ↾ X).IsFiniteRankUniform (a + 1)}
  obtain ⟨B, hB⟩ := M.exists_isBase
  have hBU : B ∈ U := ⟨hB.subset_ground, by
    rwa [hB.indep.restrict_eq_freeOn, isFiniteRankUniform_iff, eRank_freeOn, hB.encard_eq_eRank,
      and_iff_left (freeOn_uniform ..)]⟩
  have hforall (X) (hX : X ∈ U) : X.encard ≤ b := by
    simpa [ENat.lt_coe_add_one_iff] using hM.lt_of_isoMinor (restrict_isMinor _ hX.1).isoMinor hX.2
  have hfin : (encard '' U).Finite := by
    refine ENat.finite_of_sSup_lt_top (lt_of_le_of_lt ?_ (ENat.coe_lt_top b))
    grw [sSup_image, iSup₂_le_iff.2 hforall]
  obtain ⟨X, hX⟩ := Finite.exists_maximalFor' encard U hfin ⟨B, hBU⟩
  have hcov : (X.powersetENcard a).IsCover X (M.RkLE a) := by
    refine ⟨sUnion_powersetENcard_eq _ (by simpa) ?_, ?_⟩
    · grw [← hX.le hBU, hB.encard_eq_eRank, hr, ← le_self_add]
    exact fun F ⟨_, hF⟩ ↦ (M.eRk_le_encard F).trans hF.le
  have hfin : X.Finite := by
    grw [← encard_lt_top_iff, hforall _ hX.prop]
    simp
  have hss : M.E ⊆ ⋃ Y ∈ X.powersetENcard a, M.closure Y := by
    rw [← diff_union_of_subset hX.prop.1, union_subset_iff, and_comm]
    refine ⟨?_, ?_⟩
    · grw [← iUnion₂_mono (s := fun Y _ ↦ Y), ← sUnion_eq_biUnion,
      sUnion_powersetENcard_eq _ (by simpa)]
      · grw [← hX.le hBU, hB.encard_eq_eRank, hr, ← le_self_add]
      exact fun Y ⟨hY, _⟩ ↦ M.subset_closure _ (hY.trans hX.prop.1)
    simp only [mem_powersetENcard_iff, subset_def (s := M.E \ X), mem_diff, mem_iUnion, exists_prop,
      and_imp]
    by_contra! hcon
    obtain ⟨e, heE, heX, he⟩ := hcon
    have hins : insert e X ∈ U := by
      refine ⟨insert_subset heE hX.prop.1, ?_⟩
      rw [IsFiniteRankUniform.restrict_insert_iff hX.prop.2 heX]
      · grind
      grw [(M.isRkFinite_of_finite hfin).mem_closure_iff_le, ← M.eRank_restrict X,
        hX.prop.2.eRank_eq, Nat.cast_add_one, ← hr, ← eRk_le_eRank]
    exact (hX.le_of_le hins (by grw [← subset_insert])).not_gt <|
      by simpa [encard_insert_of_notMem heX]
  have := hcov.image M.closure (Q := M.RkLE a) (by simp)
  have hle := (hcov.image M.closure (Q := M.RkLE a) (by simp)).coverNumber_le
  grw [encard_image_le, encard_powersetENcard_eq, hforall X hX.prop, ENat.choose_coe_coe] at hle
  grw [← hle, ← coverNumber_rkLE_subset _ hss]
