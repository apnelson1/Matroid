import Matroid.Uniform
import Matroid.Connectivity.Skew



open Set

@[simp] lemma Set.diff_ssubset_left_iff {α : Type*} {s t : Set α} :
    s \ t ⊂ s ↔ (s ∩ t).Nonempty := by
  rw [ssubset_iff_subset_ne, and_iff_right diff_subset, Ne, sdiff_eq_left,
    disjoint_iff_inter_eq_empty, nonempty_iff_ne_empty]

@[simp] lemma Set.inter_ssubset_right_iff {α : Type*} {s t : Set α} :
    s ∩ t ⊂ t ↔ ¬ (t ⊆ s) := by
  rw [ssubset_iff_subset_ne, and_iff_right inter_subset_right, Ne, inter_eq_right]

@[simp] lemma Set.inter_ssubset_left_iff {α : Type*} {s t : Set α} :
    s ∩ t ⊂ s ↔ ¬ (s ⊆ t) := by
  rw [ssubset_iff_subset_ne, and_iff_right inter_subset_left, Ne, inter_eq_left]

@[simp] lemma Set.ssubset_union_left_iff {α : Type*} {s t : Set α} :
    s ⊂ s ∪ t ↔ ¬ (t ⊆ s) := by
  rw [ssubset_iff_subset_ne, and_iff_right subset_union_left, Ne, eq_comm, union_eq_left]

@[simp] lemma Set.ssubset_union_right_iff {α : Type*} {s t : Set α} :
    t ⊂ s ∪ t ↔ ¬ (s ⊆ t) := by
  rw [ssubset_iff_subset_ne, and_iff_right subset_union_right, Ne, eq_comm, union_eq_right]

lemma Set.Finite.encard_lt_encard' {α : Type*} {s t : Set α} (hs : s.Finite) (hst : s ⊂ t) :
    s.encard < t.encard := by
  obtain hfin | hinf := t.finite_or_infinite
  · exact hfin.encard_lt_encard hst
  rwa [hinf.encard_eq, encard_lt_top_iff]


@[simp] lemma ENat.natCast_odd_iff (n : ℕ) : Odd (n : ℕ∞) ↔ Odd n := by
  refine ⟨fun ⟨k, h⟩ ↦ ?_, fun ⟨k, h⟩ ↦ ⟨k, by simp [h]⟩⟩
  lift k to ℕ using (by rintro rfl; simp at h)
  exact ⟨k, by norm_cast at h⟩

@[simp] lemma ENat.natCast_even_iff (n : ℕ) : Even (n : ℕ∞) ↔ Even n := by
  refine ⟨fun ⟨k, h⟩ ↦ ?_, fun ⟨k, h⟩ ↦ ⟨k, by simp [h]⟩⟩
  lift k to ℕ using (by rintro rfl; simp at h)
  exact ⟨k, by norm_cast at h⟩


namespace Matroid



variable {α : Type*} {M : Matroid α} {C K X Y B I J : Set α} {e f : α}

def Binary (M : Matroid α) := ∀ C K, M.Circuit C → M.Cocircuit K → ∀ (h : (C ∩ K).Finite),
  Even h.toFinset.card

lemma Binary.dual (hM : M.Binary) : M✶.Binary := by
  intro C K hC hK h
  rw [inter_comm] at h
  convert hM K C (by simpa using hK.circuit) (by simpa using hC.cocircuit) h using 3
  rw [inter_comm]

lemma Binary.minor {N M : Matroid α} (hM : M.Binary) (hNM : N ≤m M) : N.Binary := by
  suffices aux : ∀ ⦃M : Matroid α⦄ ⦃S : Set α⦄, M.Spanning S → M.Binary → (M ↾ S).Binary
  · obtain ⟨I, R, hI, hIR, hR, rfl⟩ := hNM.exists_eq_contract_spanning_restrict
    apply aux hR
    rw [← dual_delete_dual_eq_contract]
    apply (aux _ hM.dual).dual
    rwa [← coindep_iff_compl_spanning, dual_coindep_iff]

  clear! N M
  intro M S hS hM C D hC hD h
  rw [restrict_circuit_iff] at hC
  have hh := hD.compl_hyperplane
  rw [restrict_ground_eq, hS.hyperplane_restrict_iff] at hh

  suffices h_eq : C ∩ D = C ∩ (M.E \ M.closure (S \ D))
  · convert hM C _ hC.1 hh.1.compl_cocircuit (by rwa [← h_eq]) using 3

  rw [diff_eq, ← inter_assoc, inter_eq_self_of_subset_left hC.1.subset_ground,
    ← inter_eq_self_of_subset_left hC.2, inter_assoc, inter_assoc, ← diff_eq,
    ← diff_self_inter, inter_comm S (M.closure _), ← hh.2]
  simp


lemma exist_cocircuits_of_rank_two (hr : M.erk = 2) (hel : ¬ M.Coloop e) (he : M.Point {e})
    (hU : M.NoUniformMinor 2 4) : ∃ C₁ C₂, (M ＼ e).Cocircuit C₁ ∧ (M ＼ e).Cocircuit C₂ ∧
    Disjoint C₁ C₂ ∧ C₁ ∪ C₂ = M.E \ {e} := by

  have hl := he.loopless_of_singleton.delete {e}
  have heE : e ∈ M.E := by simpa using he.subset_ground

  -- Take a simplification `N` of `M`. Since `e` isn't parallel to anything else,
  -- we also have that `N ＼ e` is a simplification of `M ＼ e`.
  obtain ⟨N, hN⟩ := M.exists_isSimplification
  have heN : e ∈ N.E := he.mem_simplification hN
  have hNe : (N ＼ e).IsSimplification (M ＼ e)
  · convert hN.delete (D := {e}) (by simpa)
    simp only [deleteElem, mem_singleton_iff, iUnion_iUnion_eq_left]
    rw [setOf_parallel_eq_closure_diff_loops, he.loopless_of_singleton.closure_empty,
      he.flat.closure, diff_empty]

  -- Since `M` has no `U_{2,4}`-minor, we have `|N| ≤ 3` and so `|N \ e| ≤ 2`.
  replace hU := hU.minor hN.restriction.minor
  rw [no_line_minor_iff_of_erk_le_two (hN.restriction.minor.erk_le.trans_eq hr),
    hN.simple.simplification_eq_self, show ((4 : ℕ) : ℕ∞) = (2 : ℕ∞) + 1 + 1 by norm_num,
    ENat.lt_add_one_iff (by norm_num),
    ← encard_diff_singleton_add_one (he.mem_simplification hN),
    WithTop.add_le_add_iff_right (by simp), ← delete_ground, ← deleteElem] at hU

  -- Since `N ＼ e` has rank two and at most two elements,
  -- it must have a two-element ground set `{a,b}`.
  obtain ⟨I, hI⟩ := (N ＼ e).exists_base
  have hIM : (M ＼ e).Base I := hNe.base_of_base hI

  have hIcard : I.encard = 2
  · rwa [hI.encard, hNe.erk_eq, deleteElem_erk_eq hel]

  obtain ⟨a,b, hab, rfl⟩ := encard_eq_two.1 hIcard

  have hIe : {a,b} = (N ＼ e).E
  · apply Finite.eq_of_subset_of_encard_le ?_ hI.subset_ground (hU.trans_eq hIcard.symm)
    rw [← encard_lt_top_iff]
    exact hU.trans_lt (by exact Batteries.compareOfLessAndEq_eq_lt.mp rfl)

  -- `N \ e` is a simplification of `M ＼ e`, so the closures of `{a}` and `{b}`
  -- form a partition of `M ＼ e`.
  have hdj : Disjoint ((M ＼ e).closure {a}) ((M ＼ e).closure {b})
  · have h := hNe.closure_pairwiseDisjoint
    rw [← hIe, pair_comm, ← union_singleton, pairwiseDisjoint_union] at h
    simpa only [pairwiseDisjoint_singleton, mem_singleton_iff, ne_eq, hab,
      forall_eq, hab.symm, not_false_eq_true, forall_const, true_and] using h

  have hpos : (M ＼ e).RkPos := hIM.rkPos_of_nonempty (by simp)

  have hucl : (M ＼ e).closure {a} ∪ (M ＼ e).closure {b} = (M ＼ e).E
  · rw [hNe.ground_eq_biUnion_closure, ← hIe]
    simp

  -- Each such closure is the complement of a hyperplane, so is a cocircuit. We're done.
  refine ⟨_, _, ?_, ?_, hdj, hucl⟩
  · rw [← compl_hyperplane_iff_cocircuit, ← hucl, union_diff_left, hdj.sdiff_eq_right,
      ← pair_diff_left hab]
    exact hIM.hyperplane_of_closure_diff_singleton (by simp)
  rw [← compl_hyperplane_iff_cocircuit, ← hucl, union_diff_right, hdj.sdiff_eq_left,
    ← pair_diff_right hab]
  exact hIM.hyperplane_of_closure_diff_singleton (by simp)


lemma exists_smaller_of_odd_circuit_cocircuit {C : Set α} (hCc : M.Circuit C) (hfin : C.Finite)
    (h_odd : Odd hfin.toFinset.card) (hCs : M.Spanning C) (hCh : M.Hyperplane (M.E \ C))
    (hCi : M.Indep (M.E \ C)) (hcard : 3 ≤ C.encard) (h_bin : M.NoUniformMinor 2 4) :
  ∃ (N : Matroid α) (K : Finset α),
    N ≤m M ∧ N.Circuit C ∧ N.Cocircuit K ∧ (K : Set α) ⊂ C ∧ Odd K.card := by

  classical
  obtain ⟨f, hf⟩ : (M.E \ C).Nonempty
  · rw [nonempty_iff_ne_empty]
    intro hss
    have hle := (M.er_le_erk C).trans_eq hCh.er_add_one_eq.symm
    rw [hss, er_empty, zero_add, ← WithTop.add_le_add_iff_right (show 1 ≠ ⊤ by simp),
      hCc.er_add_one_eq] at hle
    have hcon := hcard.trans hle
    norm_num at hcon

  set N := M ／ ((M.E \ ↑C) \ {f}) with hN
  have hNM : N ≤m M := contract_minor _ _

  have hfl : ¬ N.Coloop f
  · simpa [hN, ← dual_loop_iff_coloop] using (hCs.compl_coindep.indep.nonloop_of_mem hf).not_loop

  have hNr : N.erk = 2
  · obtain ⟨e, he, hbas⟩ := hCh.exists_insert_base_of_basis (hCi.basis_self)
    simp only [sdiff_sdiff_right_self, inf_eq_inter, mem_inter_iff, Finset.mem_coe] at he
    have hb' : N.Base {e, f}
    · rw [hN, (hCi.diff _).contract_base_iff, ← singleton_union, union_assoc, disjoint_union_left]
      simpa [hf, he.1, he.2]
    rw [← hb'.encard, encard_pair (by rintro rfl; exact hf.2 he.2)]

  have hfP : N.Point {f}
  · rw [Point, flat_iff_closure_self, hN, contract_closure_eq, union_diff_cancel (by simpa)]
    simp [hCh.flat.closure, hf.1, hf.2, hCi.not_mem_closure_diff_of_mem hf]


  obtain ⟨C₁, C₂, hC₁, hC₂, hdj, hu⟩ := exist_cocircuits_of_rank_two hNr hfl hfP (h_bin.minor hNM)

  obtain rfl : C₁ ∪ C₂ = C
  · simpa [hu, hN, diff_diff_right, inter_eq_self_of_subset_right hCc.subset_ground,
      show M.E ∩ {f} = {f} by simpa using hf.1] using hf.2

  have hnss1 : ¬ C₁ ⊆ C₂
  · simpa [← diff_eq_empty, hdj.sdiff_eq_left, ← nonempty_iff_ne_empty] using hC₁.nonempty

  have hnss2 : ¬ C₂ ⊆ C₁
  · simpa [← diff_eq_empty, hdj.sdiff_eq_right, ← nonempty_iff_ne_empty] using hC₂.nonempty

  contrapose! h_odd

  rw [hN, deleteElem, contract_delete_comm _ (by simp)] at hC₁ hC₂

  have hfin' := hfin
  rw [finite_union] at hfin'

  obtain ⟨C₁, rfl⟩ := hfin'.1.exists_finset_coe
  obtain ⟨C₂, rfl⟩ := hfin'.2.exists_finset_coe

  have hC₁_even : ¬ Odd C₁.card :=
    h_odd (M ＼ f) C₁ (delete_minor _ _) (by simpa [hf.2]) hC₁.of_contract (by simpa)

  have hC₂_even : ¬ Odd C₂.card :=
    h_odd (M ＼ f) C₂ (delete_minor _ _) (by simpa [hf.2]) hC₂.of_contract (by simpa)

  rw [Nat.not_odd_iff_even] at hC₁_even hC₂_even ⊢
  rw [toFinite_toFinset, toFinset_union, Finset.toFinset_coe, Finset.toFinset_coe,
    Finset.card_union_eq_card_add_card.2 (by simpa using hdj)]
  exact hC₁_even.add hC₂_even


lemma Circuit.exists_minor_inter_circuit_cocircuit_of_cocircuit (hC : M.Circuit C)
    (hK : M.Cocircuit K) (h_inter : (C ∩ K).Nonempty) :
    ∃ N, N ≤m M ∧ N.Circuit (C ∩ K) ∧ N.Cocircuit (C ∩ K) := by
  refine ⟨M ／ (C \ K) ＼ (K \ C), contract_delete_minor _ _ _, ?_, ?_⟩
  · simpa [delete_circuit_iff, disjoint_sdiff_right.mono_left inter_subset_left]
      using hC.contract_circuit (C := C \ K) (by simpa)
  simp only [contract_delete_comm _ disjoint_sdiff_sdiff, contract_cocircuit_iff,
    disjoint_sdiff_right.mono_left inter_subset_right, and_true]
  rw [cocircuit_def, delete_dual_eq_dual_contract]
  simpa [inter_comm C K] using hK.circuit.contract_circuit (C := K \ C) (by simpa [inter_comm])

lemma Circuit.exists_minor_spanning_cospanning_of_cocircuit (hC : M.Circuit C)
    (hK : M.Cocircuit C) :
    ∃ N, N ≤m M ∧ N.Circuit C ∧ N.Cocircuit C ∧ N.Spanning C ∧ N✶.Spanning C := by
  obtain ⟨I, hI, hIC, hI_eq, hIsp⟩ := M.exists_contract_indep_to_spanning C hC.subset_ground
  obtain ⟨J, hJ, hJC, hJ_eq, hJsp⟩ := (M ／ I)✶.exists_contract_indep_to_spanning C
    hIsp.subset_ground

  have hJI : Disjoint J I := (subset_diff.1 hJ.subset_ground).2
  have hCI : Disjoint C I := (subset_diff.1 hIsp.subset_ground).2

  refine ⟨M ／ I ＼ J, contract_delete_minor _ _ _, ?_, ?_, ?_, ?_⟩
  · rw [← circuit_iff_delete_of_disjoint hJC.symm,
      circuit_iff_restr_eq_circuitOn hC.nonempty hIsp.subset_ground, hI_eq]
    exact hC.restrict_eq_circuitOn
  · rw [cocircuit_def, delete_dual_eq_dual_contract,
      circuit_iff_restr_eq_circuitOn hC.nonempty hJsp.subset_ground, hJ_eq]
    exact Circuit.restrict_eq_circuitOn <| by simp [hCI, hK.circuit]
  · rwa [Coindep.delete_spanning_iff hJ, and_iff_left hJC.symm]
  have hJ' : J ⊆ (M✶ ＼ I).E := hJ.subset_ground
  rw [contract_dual_eq_dual_delete, contract_spanning_iff hJ',
    Coindep.delete_spanning_iff hI.coindep] at hJsp
  rwa [delete_dual_eq_dual_contract, contract_dual_eq_dual_delete, contract_spanning_iff hJ',
    and_iff_left hJC.symm, Coindep.delete_spanning_iff hI.coindep, disjoint_union_left,
    and_iff_left hJI, and_iff_right hJsp.1.1]



lemma exists_uniformMinor_of_odd_circuit_cocircuit {M : Matroid α} {C K : Set α} (hC : M.Circuit C)
    (hK : M.Cocircuit K) (h_odd : ∃ (hfin : (C ∩ K).Finite), Odd hfin.toFinset.card) :
  ¬ M.NoUniformMinor 2 4  := by

  obtain ⟨hfin, k, hk⟩ := h_odd

  have hcard : 3 ≤ (C ∩ K).encard
  · cases k
    · exfalso
      simp only [mul_zero, zero_add, Finset.card_eq_one] at hk
      obtain ⟨e, he⟩ := hk

      obtain h : C ∩ K = {e} := by simpa [← Finset.coe_inj] using he
      exact hC.inter_cocircuit_ne_singleton hK h
    simp [hfin.encard_eq_coe_toFinset_card, hk, mul_add, add_assoc]

  have hne : (C ∩ K).Nonempty
  · rw [← encard_ne_zero, ← ENat.one_le_iff_ne_zero]
    exact le_trans (by norm_num) hcard

  by_contra hcon
  obtain ⟨N₁, hN₁M, hCN₁, hKN₁⟩ := hC.exists_minor_inter_circuit_cocircuit_of_cocircuit hK hne

  obtain ⟨N₂, hN₂N₁, hCN₂, hKN₂, hSN₂, hSdN₂⟩ :=
    hCN₁.exists_minor_spanning_cospanning_of_cocircuit hKN₁

  have hN₂m := hcon.minor (hN₂N₁.trans hN₁M)

  obtain ⟨N₃, C₀, hN₃, hN₃C, hN₃K, hssu, h_odd'⟩ :=
    exists_smaller_of_odd_circuit_cocircuit hCN₂ hfin ⟨k, hk⟩ hSN₂ hKN₂.compl_hyperplane
    (by simpa using hSdN₂.compl_coindep) hcard (hcon.minor (hN₂N₁.trans hN₁M))

  have decreasing : ((C ∩ K) ∩ (C₀ : Set α)).encard < (C ∩ K).encard := by
    rw [inter_eq_self_of_subset_right hssu.subset]
    exact Finite.encard_lt_encard' (by simp) hssu

  exact exists_uniformMinor_of_odd_circuit_cocircuit hN₃C hN₃K
    (by simpa [inter_eq_self_of_subset_right hssu.subset]) <| hN₂m.minor hN₃

termination_by (C ∩ K).encard

theorem binary_iff_no_uniformMinor (M : Matroid α) : M.Binary ↔ M.NoUniformMinor 2 4 := by
  rw [← not_iff_not]

  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp only [Binary, not_forall, Classical.not_imp, Nat.not_even_iff_odd, exists_and_left] at h
    obtain ⟨C, K, hC, hK, hfin, hodd⟩ := h
    exact exists_uniformMinor_of_odd_circuit_cocircuit hC hK ⟨hfin, hodd⟩

  simp only [not_noUniformMinor_iff] at h
  sorry
  -- Need to show that being binary is closed under isomorphism, and U24 isn't binary.
