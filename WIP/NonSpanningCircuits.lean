import Mathlib.Data.Matroid.Basic
import Mathlib.Data.Matroid.IndepAxioms
import Matroid.Constructions.CircuitAxioms
import Matroid.Rank
import Matroid.Circuit
import Mathlib.Tactic.Linarith


open Set Matroid

variable {α k V P ι : Type*} {I B X : Set α}


namespace Matroid

-- NonspanningCircuit for Matroid
@[mk_iff]
  structure NonspanningCircuit (M : Matroid α) (C : Finset α) : Prop where
    circuit : M.Circuit C
    nonspanning : ¬ M.Spanning C


end Matroid

-- Non-spanning circuits
structure FinsetNonspanningCircuitMatroid (α : Type*) [DecidableEq α] where
  (E : Set α)
  (rk : ℕ)
  (NonspanningCircuit : Finset α → Prop)
  (empty_not_NonspanningCircuit : ¬NonspanningCircuit ∅)
  (NonspanningCircuit_antichain : IsAntichain (· ⊆ ·) {C | NonspanningCircuit C})
  (NonspanningCircuit_elimination : ∀ ⦃C₁ C₂ e⦄, NonspanningCircuit C₁ → NonspanningCircuit C₂ → C₁ ≠ C₂ →
  e ∈ C₁ ∩ C₂ → ((C₁ ∪ C₂).erase e).card ≤ rk → ∃ C, NonspanningCircuit C ∧ C ⊆ (C₁ ∪ C₂).erase e)
  (non_spanning : ∀ ⦃C⦄, NonspanningCircuit C → C.card ≤ rk)
  (exists_NonspanningCircuitless_rk_set : ∃ S : Finset α, S.card = rk ∧ ↑S ⊆ E ∧ ∀ ⦃C⦄, NonspanningCircuit C → ¬↑C ⊆ S)
  (NonspanningCircuit_subset_ground : ∀ ⦃C⦄, NonspanningCircuit C → ↑C ⊆ E)

  (Circuit : Finset α → Prop)
  (circuit_iff : ∀ ⦃C : Finset α⦄, Circuit C ↔ NonspanningCircuit C ∨ C.card = rk + 1
    ∧ (∀ ⦃C' : Finset α⦄, NonspanningCircuit C' → ¬C' ⊆ C) ∧ ↑C ⊆ E)

  (Indep : Finset α → Prop)
  (indep_iff : ∀ ⦃I⦄, Indep I ↔ ↑I ⊆ E ∧ ∀ ⦃C⦄, C ⊆ I → ¬Circuit C)


namespace FinsetNonspanningCircuitMatroid

variable {α : Type*} [DecidableEq α] {I J C : Finset α} {M : FinsetNonspanningCircuitMatroid α}

@[simps!] protected def matroid (M : FinsetNonspanningCircuitMatroid α) : Matroid α := by
  set Circuit := fun I ↦ (M.NonspanningCircuit I ∨ (I.card = M.rk + 1 ∧ (∀ C, M.NonspanningCircuit C → ¬C ⊆ I)
    ∧ ↑I ⊆ M.E))
  have h_antichain : IsAntichain (fun x x_1 ↦ x ⊆ x_1) {C | (fun I ↦ M.NonspanningCircuit I ∨
    I.card = M.rk + 1 ∧ (∀ (C : Finset α), M.NonspanningCircuit C → ¬C ⊆ I) ∧ ↑I ⊆ M.E) C} := by
    simp only [IsAntichain]
    refine fun C hC D hD hne ↦ ?_
    simp only [mem_setOf_eq] at hC hD
    obtain Cns | hC := hC
    obtain Dns | hD := hD
    · exact M.NonspanningCircuit_antichain Cns Dns hne
    · exact hD.2.1 C Cns
    obtain Dns | hD := hD
    · have hcard : C.card > D.card := by linarith [M.non_spanning Dns]
      contrapose! hcard
      exact Finset.card_le_card (by simpa using hcard)
    · contrapose! hne
      simp only [Pi.compl_apply, compl_iff_not, Decidable.not_not] at hne
      exact Finset.eq_of_subset_of_card_le hne <| le_trans hD.1.le hC.1.symm.le

  have h_subset_ground : ∀ ⦃C : Finset α⦄,
    (fun I ↦ M.NonspanningCircuit I ∨ I.card = M.rk + 1 ∧ (∀ (C : Finset α), M.NonspanningCircuit C → ¬C ⊆ I) ∧
    ↑I ⊆ M.E) C → ↑C ⊆ M.E := by
    intro C hC
    obtain hC | hC := hC
    exact M.NonspanningCircuit_subset_ground hC
    exact hC.2.2

  exact FinsetCircuitMatroid.matroid <| FinsetCircuitMatroid.mk
    (E := M.E)
    (Circuit := fun I ↦ (M.NonspanningCircuit I ∨
      (I.card = M.rk + 1 ∧ (∀ C, M.NonspanningCircuit C → ¬C ⊆ I) ∧ ↑I ⊆ M.E)))
    (empty_not_circuit := by
      simp only [M.empty_not_NonspanningCircuit, Finset.card_empty,
      self_eq_add_left, add_eq_zero, one_ne_zero, and_false, false_and, or_false, not_false_eq_true]
      )
    (circuit_antichain := h_antichain)
    (circuit_elimination := by
      refine fun C D e hC hD hne he ↦ ?_
      simp only [mem_setOf_eq] at hC hD
      have large_set : ∀ S : Finset α, ↑S ⊆ M.E → S.card > M.rk → ∃ C : Finset α, Circuit C ∧ C ⊆ S
        := by
        intro S hsub hcard
        obtain hcard :=  Nat.succ_eq_one_add _ ▸ Nat.succ_le_of_lt hcard
        obtain ⟨D, hDsub, hDcard⟩ := Finset.exists_subset_card_eq hcard
        by_cases hcon : ∀ C, M.NonspanningCircuit C → ¬C ⊆ D
        · refine ⟨D, ?_, hDsub⟩
          right
          exact ⟨add_comm 1 _ ▸ hDcard, hcon, subset_trans hDsub hsub⟩
        · simp only [not_forall, Classical.not_imp, Decidable.not_not] at hcon
          obtain ⟨C, hC, hCsub⟩ := hcon
          exact ⟨C, by simp only [hC, true_or, Circuit], subset_trans hCsub hDsub⟩

      have card_up : ∀ C₁ C₂, (C₁.card = M.rk + 1 ∧ (∀ (C : Finset α), M.NonspanningCircuit C →
        ¬C ⊆ C₁) ∧ ↑C₁ ⊆ M.E) → Circuit C₂ → C₁ ≠ C₂ → (C₁ ∪ C₂).card > M.rk + 1 := by
        intro C₁ C₂ hC1 hC2 hne
        simp only [← hC1.1, gt_iff_lt]
        apply Finset.card_strictMono
        obtain notsub := h_antichain hC2 (show Circuit C₁ by right; exact hC1) hne.symm
        simp only [Pi.compl_apply, compl_iff_not] at notsub
        refine ssubset_of_subset_not_subset Finset.subset_union_left ?_
        contrapose! notsub
        exact (Finset.union_subset_iff.mp notsub).2

      obtain hle | hgt := le_or_gt ((C ∪ D).erase e).card M.rk
      obtain Cns | hC := hC
      obtain Dns | hD := hD
      obtain ⟨C', hC', hsub⟩ := M.NonspanningCircuit_elimination Cns Dns hne he hle
      exact ⟨C', by simp only [hC', true_or], hsub⟩
      obtain hcard := card_up D C hD (by simp only [Circuit, Cns, true_or]) hne.symm
      obtain _ := not_le_of_lt <| Finset.union_comm C _ ▸
        (LE.le.trans_lt' Finset.pred_card_le_card_erase
        (show M.rk + 1 - 1  < (D ∪ C).card - 1 by exact Nat.sub_lt_sub_right (show 1 ≤ M.rk + 1 by
        simp only [le_add_iff_nonneg_left, zero_le]) hcard))
      contradiction
      obtain hcard := card_up C D hC hD hne
      obtain _ := not_le_of_lt <| (LE.le.trans_lt' Finset.pred_card_le_card_erase
        (show M.rk + 1 - 1  < (C ∪ D).card - 1 by exact Nat.sub_lt_sub_right (show 1 ≤ M.rk + 1 by
        simp only [le_add_iff_nonneg_left, zero_le]) hcard))
      contradiction
      obtain ⟨C', hC', hC'ss⟩ := large_set _ sorry hgt
      refine ⟨C', ?_, hC'ss⟩

      sorry
      -- simp_rw [nonspanningCircuit_iff]
      -- refine large_set ((C ∪ D).erase e) (le_trans (Finset.erase_subset _ _) (fun a ha ↦ ?_))
      --   hgt

      -- simp only [Finset.union_val, Multiset.mem_union, Finset.mem_val] at ha

      -- obtain ha | ha := ha
      -- exact (h_subset_ground hC) ha
      -- exact (h_subset_ground hD) ha
      )
      (circuit_subset_ground := h_subset_ground)
      (Indep := fun I : Finset α ↦ ↑I ⊆ M.E ∧ ∀ ⦃C⦄, C ⊆ I → ¬Circuit C)
      (indep_iff := by refine fun I ↦ by simp only [not_or, not_and, Circuit])


lemma circuit_not_indep : M.Circuit C → ¬M.Indep C := by
  simp only [circuit_iff, indep_iff, not_or, not_and, not_forall, Classical.not_imp, not_not]
  intro h _
  by_cases h' : M.NonspanningCircuit C
  contrapose! h'
  exact (h' C subset_rfl).1
  simp only [h', false_or] at h
  exact ⟨C, subset_rfl, fun _ ↦ ⟨h.1, h.2.1, h.2.2⟩⟩

lemma indep_not_circuit : M.Indep I → ¬M.Circuit I := imp_not_comm.mp circuit_not_indep

@[simp] lemma matroid_circuit_iff : M.matroid.Circuit C ↔ M.Circuit C := by
  simp only [FinsetNonspanningCircuitMatroid.matroid, not_or, not_and,
    FinsetCircuitMatroid.matroid_circuit_iff, circuit_iff]

@[simp] lemma matroid_indep_iff : M.matroid.Indep I ↔ M.Indep I := by
  simp only [matroid_Indep, IndepMatroid.ofFinset_indep, indep_iff, circuit_iff, not_or, not_and]

@[simp] lemma matroid_rk_eq [Fintype α]: M.matroid.rk = M.rk := by
  obtain ⟨I, hcard, h⟩ := M.exists_NonspanningCircuitless_rk_set
  simp_rw [imp_not_comm] at h
  have hC: ∀ ⦃C : Finset α⦄, C ⊆ I → ¬M.Circuit C := by
    intro C hsub
    simp only [circuit_iff, not_or, not_and]
    refine ⟨h.2 hsub, fun hCcard _ ↦ ?_⟩
    obtain h := hcard ▸ hCcard ▸ (Finset.card_mono hsub)
    linarith
  obtain hI := matroid_indep_iff.mpr <| M.indep_iff.mpr ⟨h.1, hC⟩

  have hB: ∀ ⦃C : Finset α⦄, M.rk + 1 ≤ C.card ∧ ↑C ⊆ M.E → ¬M.Indep C := by
    intro C hC
    obtain ⟨D, hDsub, hDcard⟩ := Finset.exists_subset_card_eq hC.1
    by_cases hD : M.Circuit D
    obtain hD := circuit_not_indep hD
    contrapose! hD
    exact matroid_indep_iff.mp <| Matroid.Indep.subset (matroid_indep_iff.mpr hD) hDsub
    simp only [circuit_iff, not_or, not_and, imp_not_comm, not_forall, Classical.not_imp, not_not]
      at hD
    simp only [indep_iff, not_and, not_forall, Classical.not_imp, not_not]
    intro hsub
    obtain ⟨S, hSsub, hS⟩ := hD.2 hDcard <| subset_trans hDsub hsub
    exact ⟨S, subset_trans hSsub hDsub, by simp only [circuit_iff, hS, true_or]⟩

  have hBase : M.matroid.Base I := by
    classical
    simp only [base_iff_maximal_indep, Maximal]
    refine ⟨hI, fun I'  hI' hsub ↦ ?_⟩
    set J := I'.toFinset with hJ
    have : I' = ↑J := hJ ▸ (coe_toFinset _).symm
    obtain hsub' := hcard ▸ (Finset.card_mono <| this ▸ hsub)
    obtain hlt | heq := lt_or_eq_of_le hsub'
    obtain hcard :=  Nat.succ_eq_one_add _ ▸ Nat.succ_le_of_lt hlt
    obtain hJ := this ▸ (not_iff_not.mpr matroid_indep_iff).mpr <|
      hB ⟨add_comm 1 _ ▸ hcard, Indep.subset_ground (this ▸  hI')⟩
    contradiction
    simp only [le_eq_subset] at hsub
    exact subset_of_eq (this ▸ (Finset.coe_inj.mpr <| Finset.eq_of_subset_of_card_le  (this ▸ hsub)
      (le_of_eq <| hcard ▸ heq.symm))).symm
  exact  (Base.ncard hBase) ▸ ncard_coe_Finset _ ▸ hcard


@[simp] lemma matroid_NonspanningCircuit_iff [Fintype α] : M.matroid.NonspanningCircuit C ↔ M.NonspanningCircuit C := by
  sorry
  -- simp only [Matroid.NonspanningCircuit, matroid_circuit_iff, circuit_iff, or_and_right]
  -- refine Iff.intro (fun hC ↦ ?_) (fun hC ↦ ?_)
  -- obtain hC | hC := hC
  -- exact hC.1
  -- linarith [M.matroid_rk_eq ▸ hC.1.1 ▸ hC.2]
  -- left
  -- exact ⟨hC, M.matroid_rk_eq ▸ M.non_spanning hC⟩

end FinsetNonspanningCircuitMatroid


abbrev CoNonspanningCircuit (M : Matroid α) (K : Finset α) : Prop := M✶.NonspanningCircuit K

lemma circuit_of_NonspanningCircuit_rk {M :Matroid α} [FiniteRk M] : ∀ C : Finset α, ↑C ⊆ M.E →
  (M.Circuit C ↔ M.NonspanningCircuit C ∨ (C.card = M.rk + 1 ∧ (∀ D, M.NonspanningCircuit D → ¬D ⊆ C))) := by
    sorry
    -- refine fun C hsub ↦ (Iff.intro (fun hC ↦ ?_) (fun hC ↦ ?_))
    -- simp only [NonspanningCircuit, and_imp]
    -- by_cases h : C.card ≤ M.rk
    -- · left
    --   exact ⟨hC, h⟩
    -- · right
    --   by_contra! h'
    --   obtain _ :=  Nat.succ_eq_one_add _ ▸ Nat.succ_le_of_lt (not_le.mp h)
    --   obtain ⟨I, hI⟩ := M.exists_basis C
    --   obtain hI' := Indep.card_le_rk (Basis.indep hI)
    --   obtain ⟨e, he, hin⟩ := (Circuit.basis_iff_insert_eq hC).mp hI
    --   obtain _ := ncard_coe_Finset _ ▸ ((ncard_eq_succ (Finset.finite_toSet _)).mpr
    --     ⟨e, I, he.2, hin.symm, rfl⟩)
    --   have : C.card = M.rk + 1 := by linarith
    --   obtain ⟨D, hCD, hDcard, hDsub⟩ := h' this
    --   obtain heq := Finset.coe_inj.mp <| Circuit.eq_of_subset_circuit hCD hC hDsub
    --   rw [heq] at hDcard
    --   contradiction
    -- simp only [NonspanningCircuit, and_imp] at hC
    -- obtain hC | ⟨hcard, hC⟩ := hC
    -- exact hC.1
    -- contrapose! hC
    -- simp only [Circuit, Minimal, le_eq_subset, not_and, not_forall, Classical.not_imp] at hC
    -- have : M.Dep ↑C := by
    --   by_contra!
    --   obtain a := ncard_coe_Finset _ ▸ Indep.card_le_rk <| (not_dep_iff hsub).mp this
    --   linarith
    -- obtain ⟨D, hD, hDsub, hnsub⟩ := hC this
    -- obtain ⟨E, hEsub, hCE⟩ := Dep.exists_circuit_subset hD
    -- have EFin: E.Finite := Circuit.finite hCE
    -- have CFin: (C.toSet).Finite := Finset.finite_toSet _
    -- refine ⟨(Finite.toFinset EFin), Finite.coe_toFinset _ ▸ hCE, ncard_eq_toFinset_card _ EFin ▸ ?_,
    --   Finset.coe_subset.mp <| Finite.coe_toFinset _ ▸ (subset_trans hEsub hDsub)⟩
    -- obtain hDlt := hcard ▸ ncard_coe_Finset C ▸ ncard_lt_ncard
    --   (ssubset_of_subset_not_subset hDsub hnsub) CFin
    -- obtain hEle := ncard_le_ncard hEsub <| Finite.subset CFin hDsub
    -- exact Nat.lt_succ.mp (lt_of_le_of_lt hEle hDlt)





lemma eq_of_NonspanningCircuit_iff_NonspanningCircuit_forall {M₁ M₂ : Matroid α} [FiniteRk M₁] [FiniteRk M₂]
  (hE : M₁.E = M₂.E)  (hCiff : ∀ C : Finset α , ↑C ⊆ M₁.E → (M₁.NonspanningCircuit C ↔ M₂.NonspanningCircuit C))
  (hrk : M₁.rk = M₂.rk ) : M₁ = M₂ := by
  refine ext_circuit hE (fun C hsub ↦ Iff.intro (fun hC ↦ ?_) (fun hC ↦ ?_))
  obtain CFin := Circuit.finite hC
  obtain hC | hC := (circuit_of_NonspanningCircuit_rk (Finite.toFinset CFin)
    (Finite.coe_toFinset CFin ▸ hsub)).mp (Finite.coe_toFinset _ ▸ hC)
  obtain hC := (hCiff (Finite.toFinset CFin) (Finite.coe_toFinset _ ▸ hsub)).mp hC
  refine Finite.coe_toFinset CFin ▸ ((circuit_of_NonspanningCircuit_rk (Finite.toFinset CFin)
    (hE ▸ Finite.coe_toFinset _ ▸ hsub)).mpr ?_)
  left
  exact hC
  refine Finite.coe_toFinset CFin ▸ ((circuit_of_NonspanningCircuit_rk (Finite.toFinset CFin)
    (hE ▸ Finite.coe_toFinset _ ▸ hsub)).mpr ?_)
  right
  refine ⟨hrk ▸ hC.1, fun D hCD ↦ ?_⟩
  obtain hDE := hE ▸ Circuit.subset_ground hCD.1
  exact hC.2 D <| (hCiff D hDE).mpr hCD
  obtain CFin := Circuit.finite hC
  obtain hC | hC := (circuit_of_NonspanningCircuit_rk (Finite.toFinset CFin)
    (hE ▸ Finite.coe_toFinset CFin ▸ hsub)).mp (Finite.coe_toFinset _ ▸ hC)
  obtain hC := (hCiff (Finite.toFinset CFin) (Finite.coe_toFinset _ ▸ hsub)).mpr hC
  refine Finite.coe_toFinset CFin ▸ ((circuit_of_NonspanningCircuit_rk (Finite.toFinset CFin)
    (Finite.coe_toFinset _ ▸ hsub)).mpr ?_)
  left
  exact hC
  refine Finite.coe_toFinset CFin ▸ ((circuit_of_NonspanningCircuit_rk (Finite.toFinset CFin)
    (Finite.coe_toFinset _ ▸ hsub)).mpr ?_)
  right
  refine ⟨hrk ▸ hC.1, fun D hCD ↦ ?_⟩
  obtain hDE := Circuit.subset_ground hCD.1
  exact hC.2 D <| (hCiff D hDE).mp hCD



theorem rk_add_dual_rk (M : Matroid α) [M.Finite] : M.rk + M✶.rk = M.E.ncard := by
  obtain h := M.eRank_add_dual_eRank
  rwa [← coe_rk_eq, ← coe_rk_eq, ← ENat.coe_add, ← Finite.cast_ncard_eq, Nat.cast_inj] at h
  exact M.ground_finite
