import Matroid.Uniform
import Matroid.Connectivity.Skew

namespace Matroid

open Set

variable {α : Type*} {M : Matroid α} {C K X Y B I J : Set α}

def Binary (M : Matroid α) := ∀ C K, M.Circuit C → M.Cocircuit K → ∀ (h : (C ∩ K).Finite),
  Even h.toFinset.card

theorem odd_circuit_cocircuit_foo {C : Finset α} (hCc : M.Circuit C) (hCk : M.Cocircuit C)
    (hsp : M.Spanning C) (h_odd : Odd C.card) (h_minor : IsEmpty (unif 2 4 ≤i M)) :
    ∃ (e : α) (C₀ : Finset α), (e ∈ M.E \ C) ∧ C₀ ⊆ C ∧ (M ／ e).Circuit C₀ := by

  classical

  have hfin : FiniteRk M
  · rw [finiteRk_iff, ← hsp.er_eq, Ne, ← WithTop.add_right_cancel_iff (a := 1) (by simp),
      hCc.er_add_one_eq, top_add, encard_eq_top_iff, not_infinite]
    exact C.finite_toSet

  have hcard : 3 ≤ C.card
  · obtain ⟨(rfl | k), hk⟩ := h_odd
    · obtain ⟨a, rfl⟩ : ∃ a, C = {a} := by simpa [Finset.card_eq_one, mul_zero, zero_add] using hk
      simpa using hCc.inter_cocircuit_ne_singleton hCk (e := a)
    linarith

  have hr : 2 ≤ M.r C
  · rw [← hCc.r_add_one_eq] at hcard
    linarith

  obtain ⟨e, he, heC⟩ : ∃ e, M.Nonloop e ∧ e ∉ C := by
    by_contra! hcon'
    have hr' : M.r (M.E \ C) = 0 := by
      rw [r_eq_zero_iff diff_subset]
      intro e he
      rw [← loop_iff_mem_closure_empty, ← not_nonloop_iff]
      exact fun hne ↦ he.2 (by simpa using hcon' e hne)
    have hr0 := hCk.compl_hyperplane.covBy.er_eq
    rw [← cast_r_eq, ← cast_r_eq] at hr0
    norm_cast at hr0
    rw [hr', zero_add] at hr0
    simpa using hr.trans <| (M.r_mono hCc.subset_ground).trans_eq hr0

  have heE := he.mem_ground
  set N := M ↾ (insert e C) with hN_def

  have hNdel : N ＼ e = circuitOn C
  · rw [hN_def, deleteElem, delete_eq_restrict, restrict_ground_eq,
      restrict_restrict_eq _ diff_subset, insert_diff_of_mem _ (mem_singleton e),
      diff_singleton_eq_self (by simpa), hCc.restrict_eq_circuitOn]

  have hNcon : N✶ ／ e = unifOn C 1
  · rw [contract_elem, ← delete_dual_eq_dual_contract, ← deleteElem, hNdel, circuitOn_dual]

  have heN : N✶.Nonloop e
  · rw [← not_loop_iff (mem_insert _ _), dual_loop_iff_coloop, coloop_iff_not_mem_closure_compl]
    suffices e ∈ M.closure (↑C \ {e} ∩ insert e ↑C) by simpa [hN_def, heE]
    rwa [inter_eq_self_of_subset_left (diff_subset.trans (subset_insert _ _)),
      hCc.closure_diff_singleton_eq_closure, hsp.closure_eq]

  have heNcl : N✶.closure {e} = {e}
  · rw [subset_antisymm_iff, subset_def,
      and_iff_left (N✶.subset_closure (X := {e}) (by simpa using heN.mem_ground))]
    refine fun x hx ↦ by_contra fun (hne : x ≠ e) ↦ ?_
    have hloop : (N✶ ／ e).Loop x
    · rw [loop_iff_mem_closure_empty, contract_elem, contract_closure_eq]
      simpa [hne]
    have hxC : x ∈ C := by simpa [hN_def, hne] using hloop.mem_ground
    exact hloop.not_nonloop <| by simpa [hNcon, ← indep_singleton, unifOn_indep_iff]

  have hNer : N✶.erk = 2
  · rw [← heN.erk_contract_add_one, hNcon, unifOn_erk_eq,
      min_eq_right (by simpa using hCc.nonempty), show (1 : ℕ∞) + 1 = 2 from rfl]

  have hNr : N✶.rk = 2
  · rw [rk, hNer, ENat.toNat_ofNat]

  have hfin' : FiniteRk N✶ := by simp [finiteRk_iff, hNer]

  obtain ⟨_, hI⟩ := (N✶ ＼ e).exists_base
  obtain ⟨I, rfl⟩ := hI.indep.finite.exists_finset_coe



  have hIcard : I.card = 1 ∨ I.card = 2
  · suffices 1 ≤ I.card ∧ I.card ≤ 2 by omega
    rw [← ncard_coe_Finset, hI.ncard, deleteElem]
    refine ⟨?_, (N✶.delete_rk_le {e}).trans_eq hNr⟩
    linarith [N✶.delete_rk_add_r_ge_rk {e}, (N✶.r_le_finset_card {e}), Finset.card_singleton e]

  rw [Finset.card_eq_one, Finset.card_eq_two] at hIcard
  sorry
  -- obtain ⟨a, rfl⟩ | ⟨a,b, hne, rfl⟩ := hIcard
  -- · refine ⟨e, C, ⟨heE, heC⟩, rfl.subset, ?_⟩
  --   have h' : (N ／ e).Circuit C
  --   · rw [← dual_dual (N ／ e), ← cocircuit_def, contract_elem, contract_dual_eq_dual_delete]


  --   -- have := Finite.r_le_card N✶ {e}

    -- refine ⟨?_, ?_⟩
    -- · have := relRank_delete_eq
    -- sorry
  --   have := hI.ncard
  --   simp only [ncard_coe_Finset, deleteElem] at this
  -- -- · rw [hI.encard, deleteElem, ← contract_dual_eq_dual_delete]






theorem odd_circuit_cocircuit {C : Finset α} (hCc : M.Circuit C) (hCk : M.Cocircuit C)
    (hsp : M.Spanning C) (h_odd : Odd C.card) : Nonempty (unif 2 4 ≤i M) := by
  by_contra hcon

  have hcard : 3 ≤ C.card
  · obtain ⟨(rfl | k), hk⟩ := h_odd
    · obtain ⟨a, rfl⟩ : ∃ a, C = {a} := by simpa [Finset.card_eq_one, mul_zero, zero_add] using hk
      simpa using hCc.inter_cocircuit_ne_singleton hCk (e := a)
    linarith

  have hr : 2 ≤ M.er C := by
    rwa [← Nat.cast_le (α := ℕ∞), ← encard_coe_eq_coe_finsetCard, ← hCc.er_add_one_eq,
      Nat.cast_ofNat, show (3 : ℕ∞) = 2 + 1 from rfl, WithTop.add_le_add_iff_right (by simp)]
        at hcard

  obtain ⟨e, he, heC⟩ : ∃ e, M.Nonloop e ∧ e ∉ C := by
    by_contra! hcon'
    have hr' : M.er (M.E \ C) = 0 := by
      rw [er_eq_zero_iff]
      intro e he
      rw [← loop_iff_mem_closure_empty, ← not_nonloop_iff]
      exact fun hne ↦ he.2 (by simpa using hcon' e hne)
    have hr0 := hCk.compl_hyperplane.covBy.er_eq
    rw [hr', zero_add] at hr0
    simpa using hr.trans <| (M.er_mono hCc.subset_ground).trans_eq hr0


  -- obtain ⟨e, heE, heC⟩ : (M.E \ C).Nonempty := by
  --   rw [nonempty_iff_ne_empty]
  --   intro h_empty
  --   have hr' := hCk.compl_hyperplane.covBy.er_eq
  --   rw [h_empty, er_empty, zero_add] at hr'


  set N := M ↾ (insert e C) with hN_def

  have hNr : N✶.erk = 2
  · obtain ⟨f, hf⟩ := hCc.nonempty
    have hB : N.Base (C \ {f})
    · rw [base_restrict_iff]
      refine (hCc.diff_singleton_indep hf).basis_of_subset_of_subset_closure
        (diff_subset.trans (subset_insert _ _)) ?_
      rw [hCc.closure_diff_singleton_eq_closure, hsp.closure_eq, insert_subset_iff,
        and_iff_left hCc.subset_ground]
      exact he.mem_ground
    rw [← hB.compl_base_dual.encard, hN_def, restrict_ground_eq,
      insert_diff_of_not_mem _ (by simp [heC]), diff_diff_cancel_left (by simpa),
      encard_pair (by rintro rfl; contradiction)]

  have hNr' : (N✶ ＼ e).erk = 2
  · rwa [deleteElem, Coindep.delete_erk_eq]
    simp only [dual_coindep_iff, indep_singleton]
    simpa [hN_def]



  _



  have := hCc.inter_cocircuit_ne_singleton hCk

theorem foo [M.Finite] (hM : ¬ M.Binary) : Nonempty (unif 2 4 ≤i M) := by

  simp only [Binary, not_forall, Classical.not_imp, Nat.not_even_iff_odd, exists_and_left] at hM
  obtain ⟨C, K, hC, hK, hfin, h_odd : Odd hfin.toFinset.card⟩ := hM
  have nonempty : (C ∩ K).Nonempty := by
    rw [← encard_ne_zero, hfin.encard_eq_coe_toFinset_card, ← ENat.coe_zero, Ne, ENat.coe_inj]
    exact Nat.ne_of_odd_add h_odd
  have hssu1 : C \ K ⊂ C := by
    refine diff_subset.ssubset_of_ne fun h_eq ↦ ?_
    rw [sdiff_eq_left] at h_eq
    simp [h_eq.inter_eq] at nonempty
  have hssu2 : K \ C ⊂ K := by
    refine diff_subset.ssubset_of_ne fun h_eq ↦ ?_
    rw [sdiff_eq_left] at h_eq
    simp [h_eq.symm.inter_eq] at nonempty
  have hdj1 : Disjoint (C ∩ K) (K \ C) := disjoint_sdiff_right.mono_left inter_subset_left
  have hdj2 : Disjoint (C ∩ K) (C \ K) := disjoint_sdiff_right.mono_left inter_subset_right

  set N₁ := M ／ (C \ K) ＼ (K \ C) with hN₁_def

  have hCN : N₁.Circuit (C ∩ K) := by
    rw [← circuit_iff_delete_of_disjoint hdj1]
    simpa using hC.contract_circuit hssu1

  have hE := hCN.subset_ground
  obtain ⟨I, hI⟩ := N₁.exists_basis (C ∩ K) hCN.subset_ground
  obtain ⟨B, hB, rfl⟩ := hI.exists_base

  set N₂ := N₁ ／ (B \ (C ∩ K)) with hN₂_def

  have hsk : N₁.Skew (C ∩ K) (B \ (C ∩ K))
  · rw [skew_iff_closure_skew_left hCN.subset_ground, ← hI.closure_eq_closure,
      ← skew_iff_closure_skew_left (inter_subset_right.trans hE)]
    simpa using hB.indep.subset_skew_diff (inter_subset_left (t := C ∩ K))

  have hN₂c : N₂.Circuit (C ∩ K)
  · rwa [hN₂_def, circuit_iff_restr_eq_circuitOn hCN.nonempty _, hsk.symm.contract_restrict_eq,
      ← circuit_iff_restr_eq_circuitOn hCN.nonempty]
    rwa [contract_ground, subset_diff, and_iff_left disjoint_sdiff_right]

  have hN₂k : N₂.Cocircuit (C ∩ K)
  · rw [hN₂_def, hN₁_def, cocircuit_def]
    simp only [contract_dual_eq_dual_delete, delete_dual_eq_dual_contract, delete_circuit_iff]
    rw [← contract_delete_comm _ disjoint_sdiff_sdiff, delete_circuit_iff,
      and_iff_left disjoint_sdiff_right, and_iff_left hdj2, inter_comm]
    simpa using hK.circuit.contract_circuit hssu2

  have hN₂sp : N₂.Spanning (C ∩ K)
  · rw [hN₂_def, contract_spanning_iff', and_iff_left disjoint_sdiff_right,
      inter_eq_self_of_subset_left (diff_subset.trans hB.subset_ground), union_diff_self]
    exact hB.spanning.superset subset_union_right (union_subset hE hB.subset_ground)

  obtain ⟨e⟩ := odd_circuit_cocircuit (M := N₂) (C := hfin.toFinset) (by simpa) (by simpa)
    (by simpa) h_odd

  exact ⟨e.trans_minor ((contract_minor _ _).trans (contract_delete_minor _ _ _))⟩
