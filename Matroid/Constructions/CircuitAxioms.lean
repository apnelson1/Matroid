import Mathlib.Data.Matroid.Basic
import Mathlib.Data.Matroid.IndepAxioms
import Matroid.Circuit

open Finset

structure FinsetCircuitMatroid (α : Type*) [DecidableEq α] where
  (E : Set α)
  (Circuit : Finset α → Prop)

  (empty_not_circuit : ¬Circuit ∅)
  (circuit_antichain : IsAntichain (· ⊆ ·) {C | Circuit C})
  (circuit_exchange : ∀ ⦃C₁ C₂ e⦄, Circuit C₁ → Circuit C₂ → C₁ ≠ C₂ → e ∈ C₁ ∩ C₂ →
    ∃ C, Circuit C ∧ C ⊆ (C₁ ∪ C₂) \ {e})
  (circuit_subset_ground : ∀ ⦃C⦄, Circuit C → ↑C ⊆ E)

  (Indep : Finset α → Prop)
  (indep_iff : ∀ ⦃I⦄, Indep I ↔ ↑I ⊆ E ∧ ∀ ⦃C⦄, C ⊆ I → ¬Circuit C)

namespace FinsetCircuitMatroid

variable {α : Type*} [DecidableEq α] {I J C : Finset α}

lemma indep_empty {M : FinsetCircuitMatroid α} : M.Indep ∅ := by
  simp [indep_iff]
  intro C hC
  rw [subset_empty] at hC
  rw [hC]
  exact M.empty_not_circuit

lemma Indep.subset {M : FinsetCircuitMatroid α} (hJ : M.Indep J) (hI : I ⊆ J) : M.Indep I := by
  simp [indep_iff] at hJ ⊢
  obtain ⟨hJ_subset, hJ⟩ := hJ
  refine ⟨(coe_subset.mpr hI).trans hJ_subset, ?_⟩
  intro C hC
  exact hJ <| hC.trans hI

lemma Finset.ssubset_of_subset_of_card_lt_card {s t : Finset α} (h : s.card < t.card) (hs : s ⊆ t) :
    s ⊂ t := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨hs, ?_⟩
  contrapose! h; rw [h]

lemma Finset.diff_nonempty_of_card_lt_card {s t : Finset α} (h : s.card < t.card) :
    (t \ s).Nonempty := by
  suffices h : 0 < (t \ s).card by exact card_pos.mp h
  calc
    0 < t.card - s.card := Nat.zero_lt_sub_of_lt h
    _ ≤ (t \ s).card := le_card_sdiff s t

lemma Finset.sdiff_erase_not_mem {s t : Finset α} {a : α} (h : a ∉ s) : s \ t.erase a = s \ t := by
  rw [sdiff_eq_sdiff_iff_inter_eq_inter, inter_erase, erase_eq_of_not_mem]
  contrapose! h; exact mem_of_mem_inter_left h

lemma Indep.aug {M : FinsetCircuitMatroid α} (hI : M.Indep I) (hJ : M.Indep J)
    (hIJ : I.card < J.card) : ∃ e ∈ J, e ∉ I ∧ M.Indep (insert e I) := by
  let T := {S | S ⊆ I ∪ J ∧ M.Indep S ∧ I.card < S.card}
  have hfin : T.Finite :=
    (finite_toSet <| (I ∪ J).powerset).subset fun S hS ↦ by simp only [hS.1, mem_coe, mem_powerset]
  have hne : T.Nonempty := ⟨J, subset_union_right, hJ, hIJ⟩
  obtain ⟨K, ⟨hK_subset, hK_indep, hK_card⟩, hK_min⟩ :=
    Set.Finite.exists_minimal_wrt (card <| I \ ·) _ hfin hne

  obtain (h_empty | ⟨e, he⟩) := (I \ K).eq_empty_or_nonempty
  · have hssu : I ⊂ K := (sdiff_eq_empty_iff_subset.1 h_empty).ssubset_of_ne
      (by rintro rfl; simp at hK_card)
    obtain ⟨e, heK, heI⟩ := exists_of_ssubset hssu
    have heJ := (mem_union.1 (hK_subset heK)).elim (False.elim ∘ heI) id
    refine ⟨e, heJ, heI, hK_indep.subset <| insert_subset heK hssu.subset⟩

  obtain ⟨heI, heK⟩ := Finset.mem_sdiff.mp he
  have hKfe : ∀ f ∈ K \ I, ∃ C ⊆ ((insert e K).erase f), M.Circuit C := by
    intro f hf
    obtain ⟨hfK, hfI⟩ := Finset.mem_sdiff.mp hf
    contrapose! hK_min with hK_indep'
    have hKfe_subset : ((insert e K).erase f) ⊆ I ∪ J := (erase_subset f (insert e K)).trans <|
      insert_subset (mem_union_left J heI) hK_subset
    have hKfe_card : ((insert e K).erase f).card = K.card := by
      calc ((insert e K).erase f).card
        _ = (insert e K).card - 1 := card_erase_of_mem <| mem_insert_of_mem hfK
        _ = K.card := by rw [card_insert_of_not_mem heK]; simp only [add_tsub_cancel_right]
    use ((insert e K).erase f)
    refine ⟨⟨hKfe_subset, M.indep_iff.mpr ⟨?_, hK_indep'⟩, (by rwa [hKfe_card])⟩, ?_⟩
    · simp only [coe_erase, coe_insert]
      refine Set.diff_subset.trans ?_
      exact Set.insert_subset ((M.indep_iff.mp hI).1 heI) (M.indep_iff.mp hK_indep).1
    have h_lt : (I \ (insert e K).erase f).card < (I \ K).card := by
      rw [Finset.sdiff_erase_not_mem hfI, sdiff_insert I K, card_erase_of_mem]
      simp [hK_card]; use e; assumption
    refine ⟨h_lt.le, h_lt.ne.symm⟩
  obtain ⟨f, hf⟩ := Finset.diff_nonempty_of_card_lt_card hK_card
  simp only [M.indep_iff, not_forall, Classical.not_imp, not_not, and_imp] at hKfe
  obtain ⟨Cf, hCf_subset, hCf⟩ := hKfe f hf
  exfalso
  by_cases hCfKI : Finset.Nonempty <| Cf ∩ (K \ I); swap
  · simp only [not_nonempty_iff_eq_empty] at hCfKI
    suffices h_bad : Cf ⊆ I by rw [M.indep_iff] at hI; exact hI.2 h_bad hCf
    rw [← inter_sdiff_assoc, sdiff_eq_empty_iff_subset] at hCfKI
    replace hCfKI := insert_subset heI hCfKI
    rw [Finset.insert_inter_distrib, inter_eq_left.mpr <| insert_subset_iff.mpr
      ⟨mem_insert_self e K, (hCf_subset.trans <| erase_subset f <| insert e K)⟩] at hCfKI
    exact (insert_subset_iff.mp hCfKI).right
  obtain ⟨g, hg⟩ := hCfKI
  obtain ⟨Cg, hCg_subset, hCg⟩ := hKfe g <| mem_of_mem_inter_right hg
  have he_mem : ∀ ⦃C x⦄, C ⊆ (insert e K).erase x → M.Circuit C → e ∈ C := by
    intro C x hC_subset hC; by_contra! heC
    replace hC_subset := hC_subset.trans <| erase_subset _ _
    rw [subset_insert_iff_of_not_mem heC] at hC_subset
    rw [M.indep_iff] at hK_indep
    exact hK_indep.2 hC_subset hC
  have h_subset : ∀ ⦃C x⦄, C ⊆ (insert e K).erase x → C \ {e} ⊆ K := by
    intro C x hC_subset
    replace hC_subset := sdiff_subset_sdiff hC_subset <| subset_refl {e}
    rw [erase_sdiff_comm, insert_sdiff_of_mem K <| mem_singleton_self e] at hC_subset
    exact (hC_subset.trans (erase_subset x _)).trans <| sdiff_subset
  have h_ne : Cf ≠ Cg := by
    intro h_bad; rw [← h_bad] at hCg_subset
    exact not_mem_erase _ _ (hCg_subset <| mem_of_mem_inter_left hg)
  obtain ⟨C, hC, hC_subset⟩ := M.circuit_exchange hCf hCg h_ne <|
    mem_inter.mpr ⟨he_mem hCf_subset hCf, he_mem hCg_subset hCg⟩
  rw [union_sdiff_distrib] at hC_subset
  rw [M.indep_iff] at hK_indep
  exact hK_indep.2 (hC_subset.trans <| union_subset (h_subset hCf_subset) (h_subset hCg_subset)) hC

lemma Indep.subset_ground {M : FinsetCircuitMatroid α} (hI : M.Indep I) : ↑I ⊆ M.E :=
  (M.indep_iff.mp hI).1

@[simps!] protected def matroid (M : FinsetCircuitMatroid α) : Matroid α :=
  IndepMatroid.matroid <| IndepMatroid.ofFinset
  (E := M.E)
  (Indep := M.Indep)
  (indep_empty := M.indep_empty)
  (indep_subset := fun _ _ hJ ↦ hJ.subset)
  (indep_aug := fun _ _ hI hJ ↦ hI.aug hJ)
  (subset_ground := fun _ hI ↦ hI.subset_ground)

@[simp] theorem matroid_circuit_iff (M : FinsetCircuitMatroid α)
    {I : Finset α} : M.matroid.Circuit I ↔ M.Circuit I := by
  unfold Matroid.Circuit Matroid.Dep
  simp only [matroid_Indep, matroid_E, IndepMatroid.ofFinset_indep]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨⟨h_indep, h_subset⟩, h_min⟩ := h
    simp only [IndepMatroid.ofFinset_indep, M.indep_iff] at h_indep
    push_neg at h_indep
    specialize h_indep h_subset
    obtain ⟨C, hC_subset, hC⟩ := h_indep
    have h_bad : ¬M.Indep C := by simp
      [M.indep_iff, show ∃ x ⊆ C, M.Circuit x from ⟨C, Subset.rfl, hC⟩]
    rw [← IndepMatroid.ofFinset_indep M.E M.Indep M.indep_empty (fun _ _ hJ ↦ hJ.subset)
      (fun _ _ hI hJ ↦ hI.aug hJ) (fun _ hI ↦ hI.subset_ground)] at h_bad
    specialize h_min ⟨h_bad, (Finset.coe_subset.mpr hC_subset).trans h_subset⟩
      <| Finset.coe_subset.mpr hC_subset
    simp only [coe_subset] at h_min
    rwa [h_min.antisymm hC_subset]
  refine ⟨⟨?_, ?_⟩, fun C ⟨hC, hC'⟩ hC_subset ↦ ?_⟩
  · simp only [IndepMatroid.ofFinset_indep, M.indep_iff]
    push_neg; intro _; use I
  · exact M.circuit_subset_ground h
  obtain (rfl | hssu) := hC_subset.eq_or_ssubset
  · rfl
  obtain ⟨D, hDC, hD⟩ : ∃ x, ↑x ⊆ C ∧ ¬M.Indep x := by simpa [IndepMatroid.ofFinset] using hC
  replace hD := show (D : Set α) ⊆ M.E → ∃ x ⊆ D, M.Circuit x by simpa [indep_iff] using hD
  obtain ⟨C₁, hC₁D, hC₁⟩ := hD (hDC.trans hC')
  have hssu : C₁ ⊂ I := hC₁D.trans_ssubset (Finset.coe_ssubset.1 (hDC.trans_ssubset hssu))
  exact False.elim <| hssu.ne <| M.circuit_antichain.eq hC₁ h hssu.subset

end FinsetCircuitMatroid
