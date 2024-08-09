import Mathlib.Data.Matroid.Basic
import Mathlib.Data.Matroid.IndepAxioms
import Matroid.Constructions.CircuitAxioms


open Set Matroid

variable {α k V P ι : Type*} {I B X : Set α}

-- Non-spanning circuits
structure FinsetCircuit'Matroid (α : Type*) [DecidableEq α] where
  (E : Set α)
  (rk : ℕ)
  (Circuit' : Finset α → Prop)
  (empty_not_circuit' : ¬Circuit' ∅)
  (circuit'_antichain : IsAntichain (· ⊆ ·) {C | Circuit' C})
  (circuit'_elimination : ∀ ⦃C₁ C₂ e⦄, Circuit' C₁ → Circuit' C₂ → C₁ ≠ C₂ →
  e ∈ C₁ ∩ C₂ → ((C₁ ∪ C₂).erase e).card ≤ rk → ∃ C, Circuit' C ∧ C ⊆ (C₁ ∪ C₂).erase e)
  (non_spanning : ∀ ⦃C⦄, Circuit' C → C.card ≤ rk)
  (exists_circuit'less_rk_set : ∃ S , S.card = rk ∧ ∀ ⦃C⦄, Circuit' C → ¬↑C ⊆ S)
  (circuit'_subset_ground : ∀ ⦃C⦄, Circuit' C → ↑C ⊆ E)

  (Circuit : Finset α → Prop)
  (circuit_iff : ∀ ⦃C : Finset α⦄, Circuit C ↔ Circuit' C ∨ C.card = rk + 1
    ∧ (∀ ⦃C' : Finset α⦄, Circuit' C' → ¬C' ⊆ C) ∧ ↑C ⊆ E)

  (Indep : Finset α → Prop)
  (indep_iff : ∀ ⦃I⦄, Indep I ↔ ↑I ⊆ E ∧ ∀ ⦃C⦄, C ⊆ I → ¬Circuit C)


namespace FinsetCircuit'Matroid

variable {α : Type*} [DecidableEq α] {I J C : Finset α} {M : FinsetCircuit'Matroid α}

@[simps!] protected def matroid (M : FinsetCircuit'Matroid α) : Matroid α := by
  set Circuit := fun I ↦ (M.Circuit' I ∨ (I.card = M.rk + 1 ∧ (∀ C, M.Circuit' C → ¬C ⊆ I)
    ∧ ↑I ⊆ M.E))
  have h_antichain : IsAntichain (fun x x_1 ↦ x ⊆ x_1) {C | (fun I ↦ M.Circuit' I ∨
    I.card = M.rk + 1 ∧ (∀ (C : Finset α), M.Circuit' C → ¬C ⊆ I) ∧ ↑I ⊆ M.E) C} := by
    simp only [IsAntichain]
    refine fun C hC D hD hne ↦ ?_
    simp only [mem_setOf_eq] at hC hD
    obtain Cns | hC := hC
    obtain Dns | hD := hD
    · exact M.circuit'_antichain Cns Dns hne
    · exact hD.2.1 C Cns
    obtain Dns | hD := hD
    · have hcard : C.card > D.card := by linarith [M.non_spanning Dns]
      contrapose! hcard
      exact Finset.card_le_card (by simpa using hcard)
    · contrapose! hne
      simp only [Pi.compl_apply, compl_iff_not, Decidable.not_not] at hne
      exact Finset.eq_of_subset_of_card_le hne <| le_trans hD.1.le hC.1.symm.le

  have h_subset_ground : ∀ ⦃C : Finset α⦄,
    (fun I ↦ M.Circuit' I ∨ I.card = M.rk + 1 ∧ (∀ (C : Finset α), M.Circuit' C → ¬C ⊆ I) ∧
    ↑I ⊆ M.E) C → ↑C ⊆ M.E := by
    intro C hC
    obtain hC | hC := hC
    exact M.circuit'_subset_ground hC
    exact hC.2.2

  exact FinsetCircuitMatroid.matroid <| FinsetCircuitMatroid.mk
    (E := M.E)
    (Circuit := fun I ↦ (M.Circuit' I ∨
      (I.card = M.rk + 1 ∧ (∀ C, M.Circuit' C → ¬C ⊆ I) ∧ ↑I ⊆ M.E)))
    (empty_not_circuit := by
      simp only [M.empty_not_circuit', Finset.card_empty,
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
        by_cases hcon : ∀ C, M.Circuit' C → ¬C ⊆ D
        · refine ⟨D, ?_, hDsub⟩
          right
          exact ⟨add_comm 1 _ ▸ hDcard, hcon, subset_trans hDsub hsub⟩
        · simp only [not_forall, Classical.not_imp, Decidable.not_not] at hcon
          obtain ⟨C, hC, hCsub⟩ := hcon
          exact ⟨C, by simp only [hC, true_or, Circuit], subset_trans hCsub hDsub⟩

      have card_up : ∀ C₁ C₂, (C₁.card = M.rk + 1 ∧ (∀ (C : Finset α), M.Circuit' C →
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
      obtain ⟨C', hC', hsub⟩ := M.circuit'_elimination Cns Dns hne he hle
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
      refine large_set ((C ∪ D).erase e) (subset_trans (Finset.erase_subset _ _) (fun a ha ↦ ?_))
        hgt
      simp only [Finset.union_val, Multiset.mem_union, Finset.mem_val] at ha
      obtain ha | ha := ha
      exact (h_subset_ground hC) ha
      exact (h_subset_ground hD) ha
      )
      (circuit_subset_ground := h_subset_ground)
      (Indep := fun I : Finset α ↦ ↑I ⊆ M.E ∧ ∀ ⦃C⦄, C ⊆ I → ¬Circuit C)
      (indep_iff := by refine fun I ↦ by simp only [not_or, not_and, Circuit])

@[simp] lemma matroid_circuit_iff : M.matroid.Circuit C ↔ M.Circuit C := by
  simp only [FinsetCircuit'Matroid.matroid, not_or, not_and,
    FinsetCircuitMatroid.matroid_circuit_iff, circuit_iff]

@[simp] lemma matroid_indep_iff : M.matroid.Indep I ↔ M.Indep I := by
  simp only [matroid_Indep, IndepMatroid.ofFinset_indep, indep_iff, circuit_iff, not_or, not_and]

end FinsetCircuit'Matroid
