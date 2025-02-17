import Mathlib.Data.Matroid.IndepAxioms
import Matroid.ForMathlib.Finset
import Matroid.Circuit

open Finset

/-- A matroid described using a `IsCircuit` predicate on `Finset`s. Can be converted to a matroid
using `FinsertCircuitMatroid.matroid`. -/
structure FinsetCircuitMatroid (α : Type*) [DecidableEq α] where
  (E : Set α)
  (IsCircuit : Finset α → Prop)

  (empty_not_isCircuit : ¬IsCircuit ∅)
  (circuit_antichain : IsAntichain (· ⊆ ·) {C | IsCircuit C})
  (circuit_elimination : ∀ ⦃C₁ C₂ e⦄, IsCircuit C₁ → IsCircuit C₂ → C₁ ≠ C₂ → e ∈ C₁ ∩ C₂ →
    ∃ C, IsCircuit C ∧ C ⊆ (C₁ ∪ C₂).erase e)
  (circuit_subset_ground : ∀ ⦃C⦄, IsCircuit C → ↑C ⊆ E)

  (Indep : Finset α → Prop)
  (indep_iff : ∀ ⦃I⦄, Indep I ↔ ↑I ⊆ E ∧ ∀ ⦃C⦄, C ⊆ I → ¬IsCircuit C)

namespace FinsetCircuitMatroid


variable {α : Type*} [DecidableEq α] {I J C : Finset α} {M : FinsetCircuitMatroid α}

lemma intro_elimination_nontrivial {IsCircuit : Finset α → Prop}
    (h_antichain : IsAntichain (· ⊆ ·) {C | IsCircuit C}) {C₁ C₂ : Finset α} {e : α}
    (hC₁ : IsCircuit C₁) (hC₂ : IsCircuit C₂) (h_ne : C₁ ≠ C₂) (he : e ∈ C₁ ∩ C₂) :
    C₁.Nontrivial ∧ C₂.Nontrivial := by
  obtain ⟨heC₁, heC₂⟩ := mem_inter.mp he
  refine ⟨?_, ?_⟩
  <;> rw [← one_lt_card_iff_nontrivial]
  <;> by_contra!
  <;> have h_con := singleton_of_mem_card_le_one this (by assumption)
  · exact h_antichain hC₁ hC₂ h_ne (by rwa [← singleton_subset_iff, ← h_con] at heC₂)
  exact h_antichain hC₂ hC₁ h_ne.symm (by rwa [← singleton_subset_iff, ← h_con] at heC₁)

lemma IsCircuit.subset_ground (hC : M.IsCircuit C) : (C : Set α) ⊆ M.E :=
  M.circuit_subset_ground hC

lemma indep_empty : M.Indep ∅ :=
  M.indep_iff.2 <| by simp [subset_empty, empty_not_isCircuit]

lemma Indep.subset_ground (hI : M.Indep I) : (I : Set α) ⊆ M.E :=
  (M.indep_iff.1 hI).1

lemma Indep.not_isCircuit_of_subset (hI : M.Indep I) (hCI : C ⊆ I) : ¬ M.IsCircuit C :=
  (M.indep_iff.1 hI).2 hCI

lemma IsCircuit.not_indep (hC : M.IsCircuit C) : ¬ M.Indep C :=
  fun hI ↦ hI.not_isCircuit_of_subset Subset.rfl hC

lemma exists_isCircuit_subset (h : ¬ M.Indep I) (hIE : (I : Set α) ⊆ M.E) :
    ∃ C ⊆ I, M.IsCircuit C := by
  simpa [M.indep_iff, hIE] using h

lemma Indep.subset {M : FinsetCircuitMatroid α} (hJ : M.Indep J) (hI : I ⊆ J) : M.Indep I :=
  M.indep_iff.2 ⟨(coe_subset.2 hI).trans hJ.subset_ground,
    fun _ hCI hC ↦ hJ.not_isCircuit_of_subset (hCI.trans hI) hC⟩

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
  have hKfe : ∀ f ∈ K \ I, ∃ C ⊆ ((insert e K).erase f), M.IsCircuit C := by
    intro f hf
    obtain ⟨hfK, hfI⟩ := mem_sdiff.mp hf
    contrapose! hK_min with hK_indep'
    have hKfe_subset : ((insert e K).erase f) ⊆ I ∪ J := (erase_subset f (insert e K)).trans <|
      insert_subset (mem_union_left J heI) hK_subset
    have hKfe_card : ((insert e K).erase f).card = K.card := by
      calc ((insert e K).erase f).card
        _ = (insert e K).card - 1 := card_erase_of_mem <| mem_insert_of_mem hfK
        _ = K.card := by rw [card_insert_of_not_mem heK, add_tsub_cancel_right]
    use ((insert e K).erase f)
    refine ⟨⟨hKfe_subset, M.indep_iff.mpr ⟨?_, hK_indep'⟩, (by rwa [hKfe_card])⟩, ?_⟩
    · simp only [coe_erase, coe_insert]
      exact Set.diff_subset.trans <| Set.insert_subset (hI.subset_ground heI) hK_indep.subset_ground
    have hssu : (I \ (insert e K).erase f) ⊂ I \ K := by
      rw [sdiff_erase_not_mem hfI, Finset.ssubset_iff_subset_ne, Ne, Finset.ext_iff, not_forall]
      exact ⟨(sdiff_subset_sdiff Subset.rfl (subset_insert _ _)), ⟨e, by simp [heI, heK]⟩⟩
    exact ⟨card_le_card hssu.subset, (card_lt_card hssu).ne.symm⟩
  obtain ⟨f, hfK, hfI⟩ : ∃ f ∈ K, f ∉ I :=
    not_subset.1 (show ¬ K ⊆ I from fun hss ↦ hK_card.not_le (card_le_card hss))

  obtain ⟨Cf, hCf_subset, hCf⟩ := hKfe f (by simp [hfI, hfK])
  exfalso
  obtain (hCfKI | ⟨g,hg⟩) := (Cf ∩ (K \ I)).eq_empty_or_nonempty
  · suffices h_bad : Cf ⊆ I by rw [M.indep_iff] at hI; exact hI.2 h_bad hCf
    rw [← inter_sdiff_assoc, sdiff_eq_empty_iff_subset] at hCfKI
    replace hCfKI := insert_subset heI hCfKI
    rw [Finset.insert_inter_distrib, inter_eq_left.mpr <| insert_subset_iff.mpr
      ⟨mem_insert_self e K, (hCf_subset.trans <| erase_subset f <| insert e K)⟩] at hCfKI
    exact (insert_subset_iff.mp hCfKI).right

  obtain ⟨Cg, hCg_subset, hCg⟩ := hKfe g <| mem_of_mem_inter_right hg
  have he_mem : ∀ ⦃C x⦄, C ⊆ (insert e K).erase x → M.IsCircuit C → e ∈ C := by
    intro C x hC_subset hC; by_contra! heC
    replace hC_subset := hC_subset.trans <| erase_subset _ _
    rw [subset_insert_iff_of_not_mem heC] at hC_subset
    rw [M.indep_iff] at hK_indep
    exact hK_indep.2 hC_subset hC
  have h_subset : ∀ ⦃C x⦄, C ⊆ (insert e K).erase x → C \ {e} ⊆ K := by
    simp_rw [sdiff_subset_iff, insert_eq]
    exact fun C x hC ↦ hC.trans (erase_subset _ _)
  have h_ne : Cf ≠ Cg := by rintro rfl; simpa using hCg_subset (mem_inter.1 hg).1
  obtain ⟨C, hC, hC_subset⟩ := M.circuit_elimination hCf hCg h_ne <|
    mem_inter.mpr ⟨he_mem hCf_subset hCf, he_mem hCg_subset hCg⟩
  rw [← sdiff_singleton_eq_erase, union_sdiff_distrib] at hC_subset
  exact hK_indep.not_isCircuit_of_subset
    (hC_subset.trans <| union_subset (h_subset hCf_subset) (h_subset hCg_subset)) hC

/-- A `FinsetCircuitMatroid` gives rise to a finitary `Matroid` with the same circuits. -/
@[simps!] protected def matroid (M : FinsetCircuitMatroid α) : Matroid α :=
  IndepMatroid.matroid <| IndepMatroid.ofFinset
  (E := M.E)
  (Indep := M.Indep)
  (indep_empty := M.indep_empty)
  (indep_subset := fun _ _ hJ ↦ hJ.subset)
  (indep_aug := fun _ _ hI hJ ↦ hI.aug hJ)
  (subset_ground := fun _ hI ↦ hI.subset_ground)

instance : Matroid.Finitary (M.matroid) := by
  rw [FinsetCircuitMatroid.matroid, IndepMatroid.ofFinset]
  infer_instance

@[simp] lemma matroid_isCircuit_iff : M.matroid.IsCircuit C ↔ M.IsCircuit C := by
  simp only [Matroid.isCircuit_def, Matroid.Dep, matroid_Indep, IndepMatroid.ofFinset_indep',
    not_forall, Classical.not_imp, minimal_subset_iff, Set.mem_setOf_eq, coe_subset, and_imp,
    forall_exists_index, exists_prop, matroid_E]
  refine ⟨fun ⟨⟨⟨D, hDC, hD⟩, hCE⟩, hmin⟩ ↦ ?_,
    fun h ↦ ⟨⟨⟨C, Subset.rfl,h.not_indep⟩, h.subset_ground⟩, fun X D hDX hD hX hXC ↦ ?_⟩⟩
  · obtain ⟨C', hCD', hC'⟩ := exists_isCircuit_subset hD <| subset_trans (by simpa) hCE
    rwa [coe_inj.1 <| hmin (t := C') C' Subset.rfl hC'.not_indep hC'.subset_ground
      (by simpa using hCD'.trans hDC)]

  obtain ⟨C', hCD', hC'⟩ := exists_isCircuit_subset hD <| subset_trans (by simpa) hX
  have hC'X := (coe_subset.2 hCD').trans hDX
  obtain rfl := M.circuit_antichain.eq hC' h (by simpa using hC'X.trans hXC)
  exact hC'X.antisymm hXC

lemma matroid_isCircuit_iff' {C : Set α} :
    M.matroid.IsCircuit C ↔ ∃ (h : C.Finite), M.IsCircuit h.toFinset := by
  simp only [← matroid_isCircuit_iff, Set.Finite.coe_toFinset, exists_prop, iff_and_self]
  exact fun h ↦ h.finite

@[simp] lemma matroid_indep_iff : M.matroid.Indep I ↔ M.Indep I := by
  rw [M.indep_iff, Matroid.indep_iff_forall_subset_not_isCircuit', and_comm]
  simp only [matroid_E, matroid_isCircuit_iff', not_exists, and_congr_right_iff]
  exact fun _ ↦ ⟨fun h C hCI hC ↦ h C (by simpa) (by simp) (by simpa),
    fun h C hCI hfin hC ↦ h (by simpa) hC⟩

end FinsetCircuitMatroid
