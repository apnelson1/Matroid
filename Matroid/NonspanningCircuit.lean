import Matroid.Circuit
import Matroid.Closure
import Matroid.Rank.ENat
import Matroid.ForMathlib.Tactic.ENatToNat


namespace Matroid

variable {α : Type*} {M : Matroid α} {X Y C K T : Set α} {e f g x y : α}

@[mk_iff]
structure IsNonspanningCircuit (M : Matroid α) (C : Set α) : Prop where
  nonspanning : M.Nonspanning C
  isCircuit : M.IsCircuit C

@[grind →, aesop unsafe 10% (rule_sets := [Matroid])]
lemma IsNonspanningCircuit.subset_ground (h : M.IsNonspanningCircuit C) : C ⊆ M.E :=
  h.1.subset_ground

lemma isBase_iff_forall_not_isNonspanningCircuit_subset [M.RankFinite] {B : Set α} (hBE : B ⊆ M.E) :
    M.IsBase B ↔ B.encard = M.eRank ∧ ∀ C ⊆ B, ¬ M.IsNonspanningCircuit C := by
  refine ⟨fun h ↦ ⟨h.encard_eq_eRank, fun C hCB hC ↦ ?_⟩, fun ⟨hBr, hB⟩ ↦ ?_⟩
  · exact False.elim <| (h.indep.subset hCB).not_dep hC.isCircuit.dep
  have hBi : M.Indep B := by
    rw [indep_iff_forall_subset_not_isCircuit]
    contrapose! hB
    obtain ⟨C, hCB, hC⟩ := hB
    refine ⟨C, hCB, ?_, hC⟩
    grw [nonspanning_iff_eRk_lt, ← hBr, ← ENat.add_one_lt_add_one_iff, hC.eRk_add_one_eq,
      ENat.lt_add_one_iff, hCB]
    rwa [hBr, ← lt_top_iff_ne_top, eRank_lt_top_iff]
  exact hBi.isBase_of_eRk_ge hBi.finite <| by grw [← hBr, hBi.eRk_eq_encard]

/-- Two matroids with the same finite rank, the same ground set,
and the same nonspanning circuits are equal. -/
lemma ext_isNonspanningCircuit {M N : Matroid α} (hE : M.E = N.E) (hr : M.eRank = N.eRank)
    [M.RankFinite] (hMN : ∀ C ⊆ M.E, M.IsNonspanningCircuit C ↔ N.IsNonspanningCircuit C) :
    M = N := by
  have hN : N.RankFinite := by rwa [← eRank_lt_top_iff, ← hr, eRank_lt_top_iff]
  refine ext_isBase hE fun B hBE ↦ ?_
  rw [isBase_iff_forall_not_isNonspanningCircuit_subset hBE,
    isBase_iff_forall_not_isNonspanningCircuit_subset (hBE.trans_eq hE), hr, and_congr_right_iff]
  refine fun hr' ↦ ⟨fun h C hCB hC ↦ h C hCB ?_, fun h C hCB hC ↦ h C hCB ?_⟩
  · rwa [hMN _ (hCB.trans hBE)]
  rwa [← hMN _ (hCB.trans hBE)]

lemma isNonspanningCircuit_iff_isCircuit_encard_le [M.RankFinite] :
    M.IsNonspanningCircuit C ↔ M.IsCircuit C ∧ C.encard ≤ M.eRank := by
  rw [isNonspanningCircuit_iff, and_comm, and_congr_right_iff]
  intro hC
  rw [nonspanning_iff_eRk_lt, ← ENat.add_one_lt_add_one_iff, hC.eRk_add_one_eq]
  have := M.eRank_lt_top
  enat_to_nat!; lia

lemma ext_isCircuit_encard_le {M N : Matroid α} (hE : M.E = N.E) (hr : M.eRank = N.eRank)
    [M.RankFinite] (hMN : ∀ C ⊆ M.E, C.encard ≤ M.eRank → (M.IsCircuit C ↔ N.IsCircuit C)) :
    M = N := by
  have hN : N.RankFinite := by rwa [← eRank_lt_top_iff, ← hr, eRank_lt_top_iff]
  refine ext_isNonspanningCircuit hE hr fun C hCE ↦ ?_
  rw [isNonspanningCircuit_iff_isCircuit_encard_le, isNonspanningCircuit_iff_isCircuit_encard_le,
    ← hr, and_congr_left_iff]
  exact hMN C hCE
