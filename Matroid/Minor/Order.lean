import Matroid.Loop
import Matroid.Minor.Contract
import Mathlib.Combinatorics.Matroid.Minor.Order


open Set

variable {α : Type*} {M M' N : Matroid α} {e f : α} {I C D J R B X Y Z K S : Set α}

namespace Matroid

section IsMinor

variable {M₀ M₁ M₂ : Matroid α}

attribute [grind =] contract_ground delete_ground restrict_ground_eq dual_ground dual_dual

attribute [grind →] IsMinor.subset

lemma contract_delete_ground (M : Matroid α) (C D : Set α) : (M ／ C ＼ D).E = M.E \ (C ∪ D) := by
  simp [diff_diff]

lemma delete_contract_ground (M : Matroid α) (C D : Set α) : (M ＼ D ／ C).E = M.E \ (D ∪ C) := by
  simp [diff_diff]

/-- The scum theorem : we can always realize a minor by contracting an independent set and deleting
a coindependent set/ -/
lemma IsMinor.exists_contract_indep_delete_coindep (h : N ≤m M) :
    ∃ C D, M.Indep C ∧ M.Coindep D ∧ Disjoint C D ∧ N = M ／ C ＼ D := by
  -- Using duality, it is enough to prove this just for contraction-minors.
  suffices aux : ∀ (M' : Matroid α) (C : Set α) (hC : C ⊆ M'.E),
      ∃ I D, Disjoint I D ∧ M'.Indep I ∧ M'.Coindep D ∧ M' ／ I ＼ D = M' ／ C by
    obtain ⟨C', D', hC', hD', hCD', rfl⟩ := h.exists_eq_contract_delete_disjoint
    obtain ⟨I, D, hID, hI, hD, h_eq⟩ := aux (M ／ C')✶ D' (subset_diff.2 ⟨hD', hCD'.symm⟩)
    obtain ⟨J, D₁, hJD₁, hJ, hD₁, h_eq'⟩ := aux M C' hC'
    rw [← h_eq', dual_coindep_iff, delete_indep_iff, hJ.contract_indep_iff, union_comm] at hD
    rw [← h_eq', dual_contract_delete, ← contract_delete_comm _ hJD₁.symm, delete_indep_iff,
      hD₁.indep.contract_indep_iff] at hI
    refine ⟨J ∪ D, I ∪ D₁, hD.1.2, hI.1.2, by tauto_set, ?_⟩
    rw [← dual_inj, dual_contract_delete, eq_comm, dual_contract, dual_dual] at h_eq
    rw [h_eq, ← h_eq', delete_delete, contract_delete_contract _ _ _ _ (by tauto_set), union_comm I]
  intro M' C hC
  obtain ⟨I, hI⟩ := M'.exists_isBasis C
  refine ⟨_, _, disjoint_sdiff_right, hI.indep, ?_, hI.contract_eq_contract_delete.symm⟩
  refine Indep.of_delete (D := I) <| (coloops_indep _).subset ?_
  rw [← dual_contract, dual_coloops, contract_loops_eq, hI.closure_eq_closure]
  exact diff_subset_diff_left <| M'.subset_closure C

lemma IsMinor.exists_delete_coindep_contract_indep (h : N ≤m M) :
    ∃ D C, M.Coindep D ∧ M.Indep C ∧ Disjoint D C ∧ N = M ＼ D ／ C := by
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := h.exists_contract_indep_delete_coindep
  exact ⟨D, C, hD, hC, hCD.symm, M.contract_delete_comm hCD⟩

/-- A version of the scum theorem where the minor is obtained as a spanning restriction
of a contraction rather than a contraction-deletion.  -/
lemma IsMinor.exists_spanning_isRestriction_contract (h : N ≤m M) :
    ∃ C, M.Indep C ∧ (N ≤r M ／ C) ∧ (M ／ C).closure N.E = (M ／ C).E := by
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := h.exists_contract_indep_delete_coindep
  exact ⟨C, hC, delete_isRestriction .., by
    rw [← (hD.coindep_contract_of_disjoint hCD.symm).closure_compl, delete_ground]⟩

/-- A version of the scum theorem where the minor is obtained as a spanning restriction
of a contraction rather than a contraction-deletion.  -/
lemma IsMinor.exists_eq_contract_spanning_restrict (h : N ≤m M) :
    ∃ I R, M.Indep I ∧ Disjoint I R ∧ (M ／ I).Spanning R ∧ N = (M ／ I) ↾ R := by
  obtain ⟨C, hC, hNC, hcl⟩ := h.exists_spanning_isRestriction_contract
  obtain ⟨R, hR, rfl⟩ := hNC.exists_eq_restrict
  exact ⟨C, R, hC, (subset_diff.1 hR).2.symm, ⟨hcl, hR⟩, rfl⟩

lemma IsRestriction.isMinor (h : N ≤r M) : N ≤m M := by
  obtain ⟨R, hR, rfl⟩ := h
  refine ⟨∅, M.E \ R, ?_⟩
  rw [contract_empty, delete_compl hR]

lemma IsMinor.finite (h : N ≤m M) [M.Finite] : N.Finite :=
  ⟨M.ground_finite.subset h.subset⟩

lemma IsMinor.rankFinite (h : N ≤m M) [RankFinite M] : RankFinite N := by
  obtain ⟨C, D, rfl⟩ := h
  infer_instance

lemma IsMinor.finitary (h : N ≤m M) [Finitary M] : Finitary N := by
  obtain ⟨C, D, rfl⟩ := h
  infer_instance

lemma contract_isMinor (M : Matroid α) (C : Set α) : M ／ C ≤m M := by
  rw [← (M ／ C).delete_empty]
  apply contract_delete_isMinor

lemma contract_isMinor_of_subset (M : Matroid α) {C C' : Set α} (hCC' : C ⊆ C') :
    M ／ C' ≤m M ／ C := by
  rw [← diff_union_of_subset hCC', union_comm, ← contract_contract]
  apply contract_isMinor

lemma contract_isMinor_of_mem (M : Matroid α) {C : Set α} (he : e ∈ C) :
    M ／ C ≤m M ／ {e} :=
  M.contract_isMinor_of_subset (singleton_subset_iff.2 he)

lemma delete_isMinor (M : Matroid α) (D : Set α) : M ＼ D ≤m M := by
  nth_rw 1 [← M.contract_empty]; apply contract_delete_isMinor

lemma delete_isRestriction_of_subset (M : Matroid α) {D D' : Set α} (hDD' : D ⊆ D') :
    M ＼ D' ≤r M ＼ D := by
  convert (M ＼ D).delete_isRestriction D' using 1
  rw [delete_delete, union_eq_self_of_subset_left hDD']

lemma delete_contract_diff (M : Matroid α) (C D : Set α) : M ＼ D ／ C = M ＼ D ／ (C \ D) := by
  rw [← dual_inj]
  simp [contract_delete_diff]

lemma IsMinor.delete_isMinor_delete (h : N ≤m M) {D : Set α} (hD : D ⊆ N.E) : N ＼ D ≤m M ＼ D := by
  obtain ⟨C, D', hCE, hDE, hCD, rfl⟩ := h.exists_eq_contract_delete_disjoint
  rw [delete_delete, contract_delete_comm, union_comm, ← delete_delete]
  · exact (contract_isMinor ..).trans <| delete_isMinor ..
  grw [hD, delete_ground, contract_ground, disjoint_union_right, and_iff_right hCD,
    diff_subset]
  exact disjoint_sdiff_right

lemma IsMinor.delete_isMinor_delete' (h : N ≤m M) {D : Set α} (hD : D ∩ M.E ⊆ N.E) :
    N ＼ D ≤m M ＼ D := by
  rw [← delete_inter_ground_eq, ← M.delete_inter_ground_eq, ← inter_eq_self_of_subset_left h.subset,
    ← inter_assoc, inter_right_comm, inter_eq_self_of_subset_left hD]
  exact h.delete_isMinor_delete hD

lemma IsMinor.delete_isMinor_delete_of_subset (h : N ≤m M) {D D' : Set α} (hss : D ⊆ D')
    (hD : D ∩ M.E ⊆ N.E) :
    N ＼ D' ≤m M ＼ D :=
  (delete_isRestriction_of_subset N hss).isMinor.trans (h.delete_isMinor_delete' hD)

lemma delete_isMinor_delete_of_subset {D'} (M : Matroid α) (hDD' : D ⊆ D') : M ＼ D' ≤m M ＼ D :=
  (delete_isRestriction_of_subset _ hDD').isMinor

lemma restrict_isMinor (M : Matroid α) (hR : R ⊆ M.E := by aesop_mat) : (M ↾ R) ≤m M := by
  rw [← delete_compl]
  apply delete_isMinor

lemma Dep.of_isMinor_of_subset (hX : M.Dep X) (hNM : N ≤m M) (hIN : X ⊆ N.E) : N.Dep X := by
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := hNM.exists_contract_indep_delete_coindep
  simp only [delete_ground, contract_ground, subset_diff] at hIN
  rw [delete_dep_iff, hC.contract_dep_iff, and_iff_right hIN.1.2, and_iff_left hIN.2]
  exact hX.superset subset_union_left

/-- The `right` version of this is false; for instance, if `N` is a component of `M`,
and `N' = M ／ C` for some set `C` in another component. -/
lemma IsRestriction.isRestriction_left_of_isMinor_isMinor (hNM : N ≤r M) {N'}
    (hNN' : N ≤m N') (hN'M : N' ≤m M) : N ≤r N' := by
  rw [isRestriction_iff_exists]
  refine ⟨N.E, hNN'.subset, ext_indep rfl fun I hIN ↦ ?_⟩
  rw [restrict_indep_iff, and_iff_left hIN]
  exact ⟨fun h ↦ h.of_isMinor hNN', fun h ↦ (h.of_isMinor hN'M).indep_isRestriction hNM hIN⟩

lemma IsStrictRestriction.isStrictMinor (h : N <r M) : N <m M :=
  ⟨h.isRestriction.isMinor, fun h' ↦ h.ssubset.not_subset h'.subset⟩

lemma restrict_isStrictMinor (hR : R ⊂ M.E) : M ↾ R <m M :=
  (restrict_isStrictRestriction hR).isStrictMinor

@[simp]
lemma delete_contract_isMinor (M : Matroid α) (D C : Set α) : M ＼ D ／ C ≤m M :=
  ((M ＼ D).contract_isMinor C).trans <| M.delete_isMinor D

lemma contract_delete_isMinor_delete {C D : Set α} (M : Matroid α) (hCD : Disjoint C D) :
    M ／ C ＼ D ≤m M ＼ D := by
  rw [contract_delete_comm _ hCD]
  apply contract_isMinor ..

lemma contract_restrict_isMinor (M : Matroid α) (C : Set α) (hR : R ⊆ M.E \ C) :
    (M ／ C) ↾ R ≤m M := by
  rw [← delete_compl]
  apply contract_delete_isMinor

lemma contract_delete_isMinor_contract_delete (M : Matroid α) {C' D'} (hCD : Disjoint C D)
    (hC : C' ⊆ C) (hD : D' ⊆ D) : M ／ C ＼ D ≤m M ／ C' ＼ D' :=
  (contract_isMinor_of_subset _ hC).delete_isMinor_delete_of_subset hD <| by grind

lemma IsMinor.exists_isMinor_of_subset_subset (h : N ≤m M) {X} (hNX : N.E ⊆ X) (hXM : X ⊆ M.E) :
    ∃ N', N ≤m N' ∧ N' ≤m M ∧ N'.E = X := by
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := h.exists_eq_contract_delete_disjoint
  exact ⟨M ／ (C \ X) ＼ (D \ X),
    M.contract_delete_isMinor_contract_delete hCD diff_subset diff_subset,
    contract_delete_isMinor .., by grind⟩

lemma contractElem_isStrictMinor (he : e ∈ M.E) : M ／ {e} <m M :=
  ⟨contract_isMinor M {e}, fun hM ↦ (hM.subset he).2 rfl⟩

lemma deleteElem_isStrictMinor (he : e ∈ M.E) : M ＼ {e} <m M :=
  ⟨delete_isMinor M {e}, fun hM ↦ (hM.subset he).2 rfl⟩

lemma IsStrictMinor.exists_eq_contract_delete_disjoint (hNM : N <m M) :
    ∃ C D, C ⊆ M.E ∧ D ⊆ M.E ∧ Disjoint C D ∧ (C ∪ D).Nonempty ∧ N = M ／ C ＼ D := by
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := hNM.isMinor.exists_eq_contract_delete_disjoint
  refine ⟨C, D, hC, hD, hCD, ?_, rfl⟩
  exact (show (M.E ∩ _).Nonempty by simpa [diff_diff] using hNM.ssubset).mono inter_subset_right

lemma isStrictMinor_iff_exists_eq_contract_delete :
    N <m M ↔ ∃ C D, C ⊆ M.E ∧ D ⊆ M.E ∧ Disjoint C D ∧ (C ∪ D).Nonempty ∧ N = M ／ C ＼ D := by
  refine ⟨IsStrictMinor.exists_eq_contract_delete_disjoint, ?_⟩
  rintro ⟨C, D, hC, hD, hdj, h, rfl⟩
  suffices (M.E ∩ (C ∪ D)).Nonempty by simpa [isStrictMinor_iff_isMinor_ssubset, diff_diff]
  rwa [inter_eq_self_of_subset_right (by simp [hC, hD])]

lemma IsStrictMinor.exists_isMinor_contractElem_or_deleteElem (hNM : N <m M) :
    ∃ e ∈ M.E, N ≤m M ／ {e} ∨ N ≤m M ＼ {e} := by
  obtain ⟨C, D, hC, hD, hCD, hne, rfl⟩ := hNM.exists_eq_contract_delete_disjoint
  obtain ⟨e, he : e ∈ C⟩ | ⟨e, he : e ∈ D⟩ := by simpa using hne
  · refine ⟨e, hC he, .inl ?_⟩
    rw [← insert_eq_of_mem he, ← singleton_union, ← contract_contract]
    apply contract_delete_isMinor
  refine ⟨e, hD he, .inr ?_⟩
  rw [contract_delete_comm _ hCD, ← insert_eq_of_mem he, ← singleton_union, ← delete_delete]
  apply delete_contract_isMinor

lemma IsMinor.isStrictMinor_or_eq (h : N ≤m M) : N <m M ∨ N = M := by
  rw [isStrictMinor_iff_isMinor_ne, and_iff_right h]
  exact ne_or_eq N M

lemma IsMinor.dual (h : N ≤m M) : N✶ ≤m M✶ := by
  obtain ⟨C, D, rfl⟩ := h
  rw [dual_delete, dual_contract]
  apply delete_contract_isMinor

lemma IsMinor.of_dual (h : N✶ ≤m M✶) : N ≤m M := by
  simpa using h.dual

@[simp]
lemma dual_isMinor_iff : N✶ ≤m M✶ ↔ N ≤m M :=
  ⟨IsMinor.of_dual, IsMinor.dual⟩

lemma isMinor_dual_iff_dual_isMinor : N ≤m M✶ ↔ N✶ ≤m M := by
  rw [← dual_isMinor_iff, dual_dual]

lemma IsStrictMinor.dual (h : N <m M) : N✶ <m M✶ := by
  rwa [IsStrictMinor, dual_isMinor_iff, dual_isMinor_iff]

lemma IsStrictMinor.of_dual (h : N✶ <m M✶) : N <m M := by
  simpa using h.dual

lemma dual_isStrictMinor_iff: N✶ <m M✶ ↔ N <m M :=
  ⟨IsStrictMinor.of_dual, IsStrictMinor.dual⟩

lemma isStrictMinor_dual_iff_dual_isStrictMinor : N <m M✶ ↔ N✶ <m M := by
  rw [← dual_isStrictMinor_iff, dual_dual]

lemma IsMinor.contract_isMinor_contract (h : N ≤m M) {C : Set α} (hC : C ⊆ N.E) :
    N ／ C ≤m M ／ C := by
  simpa using (h.dual.delete_isMinor_delete hC).dual

lemma IsMinor.contract_isMinor_contract' (h : N ≤m M) {C : Set α} (hC : C ∩ M.E ⊆ N.E) :
    N ／ C ≤m M ／ C := by
  simpa using (h.dual.delete_isMinor_delete' hC).dual

lemma IsMinor.contract_isMinor_contract_of_subset (h : N ≤m M) {C C' : Set α} (hss : C ⊆ C')
    (hC : C ∩ M.E ⊆ N.E) :
    N ／ C' ≤m M ／ C :=
  (N.contract_isMinor_of_subset hss).trans (h.contract_isMinor_contract' hC)

lemma IsColoop.of_isMinor (he : M.IsColoop e) (heN : e ∈ N.E) (hNM : N ≤m M) : N.IsColoop e := by
  rw [← dual_isLoop_iff_isColoop] at he ⊢
  exact he.of_isMinor heN hNM.dual

lemma IsStrictMinor.encard_ground_lt [N.Finite] (hNM : N <m M) : N.E.encard < M.E.encard :=
  N.ground_finite.encard_lt_encard hNM.ssubset

lemma Nonspanning.of_isMinor (h : N.Nonspanning X) (hN : N ≤m M) : M.Nonspanning X := by
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := hN
  exact h.of_delete.of_contract

lemma IsMinor.closure_inter_subset_closure (hN : N ≤m M) (hX : X ⊆ N.E) :
    M.closure X ∩ N.E ⊆ N.closure X := by
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := hN.exists_contract_indep_delete_coindep
  grw [contract_delete_ground, delete_closure_eq, contract_closure_eq, diff_diff, subset_diff,
    and_iff_left (by grind), (show Disjoint X D by grind).sdiff_eq_left, inter_subset_left,
    ← subset_union_left]

lemma Spanning.of_isMinor (hX : M.Spanning X) (hN : N ≤m M) (hXN : X ⊆ N.E) : N.Spanning X := by
  grw [spanning_iff_ground_subset_closure, ← hN.closure_inter_subset_closure hXN,
    hX.closure_eq, inter_eq_self_of_subset_right hN.subset]

lemma IsSpanningRestriction.isMinor (h : N ≤sr M) : N ≤m M :=
  h.isRestriction.isMinor

/-- If `X` is spanning in `M`, and independent in a minor `N` of `M`, then `N` is a spanning
restriction of `M`. -/
lemma IsMinor.isSpanningRestriction_of_indep_spanning {X : Set α} (hNM : N ≤m M) (hNX : N.Indep X)
    (hMX : M.Spanning X) : N ≤sr M := by
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := hNM.exists_contract_indep_delete_coindep
  rw [delete_indep_iff, hC.contract_indep_iff] at hNX
  have hX : X = X ∪ C := (hMX.isBase_of_indep (hNX.1.2.subset subset_union_left)).eq_of_subset_indep
    hNX.1.2 subset_union_left
  rw [eq_comm, union_eq_left, ← diff_eq_empty, hNX.1.1.sdiff_eq_right] at hX
  rw [hX, contract_empty]
  exact hD.delete_isSpanningRestriction

lemma IsSpanningRestriction.isSpanningRestriction_left_of_isMinor_isMinor {M₁ M₂ M₃ : Matroid α}
    (h : M₁ ≤sr M₃) (h₁₂ : M₁ ≤m M₂) (h₂₃ : M₂ ≤m M₃) : M₁ ≤sr M₂ :=
  ⟨h.isRestriction.isRestriction_left_of_isMinor_isMinor h₁₂ h₂₃,
    h.spanning.of_isMinor h₂₃ h₁₂.subset⟩

lemma IsSpanningRestriction.isSpanningRestriction_right_of_isMinor_isMinor {M₁ M₂ M₃ : Matroid α}
    (h : M₁ ≤sr M₃) (h₁₂ : M₁ ≤m M₂) (h₂₃ : M₂ ≤m M₃) : M₂ ≤sr M₃ := by
  obtain ⟨B, hB⟩ := M₁.exists_isBase
  exact h₂₃.isSpanningRestriction_of_indep_spanning (hB.indep.of_isMinor h₁₂)
    (h.spanning_of_spanning hB.spanning)




  -- have : M₁ ≤r M₂ := by exact IsRestriction.isRestriction_left_of_isMinor_isMinor this h₁₂ h₂₃

-- /-- Classically choose an independent contract-set from a proof that `N` is a minor of `M`. -/
-- def IsMinor.C (h : N ≤m M) : Set α :=
--   h.exists_contract_indep_delete_coindep.choose

-- /-- Classically choose a coindependent delete-set from a proof that `N` is a minor of `M`. -/
-- def IsMinor.D (h : N ≤m M) : Set α :=
--   h.exists_contract_indep_delete_coindep.choose_spec.choose

-- lemma IsMinor.C_indep (h : N ≤m M) : M.Indep h.C :=
--   h.exists_contract_indep_delete_coindep.choose_spec.choose_spec.1

-- lemma IsMinor.D_coindep (h : N ≤m M) : M.Coindep h.D :=
--   h.exists_contract_indep_delete_coindep.choose_spec.choose_spec.2.1

-- lemma IsMinor.disjoint (h : N ≤m M) : Disjoint h.C h.D :=
--   h.exists_contract_indep_delete_coindep.choose_spec.choose_spec.2.2.1

-- lemma IsMinor.eq_con_del (h : N ≤m M) : N = M ／ h.C ＼ h.D :=
--   h.exists_contract_indep_delete_coindep.choose_spec.choose_spec.2.2.2

-- lemma IsMinor.C_union_D_eq (h : N ≤m M) : h.C ∪ h.D = M.E \ N.E := by
--   simp only [h.eq_con_del, delete_ground, contract_ground, diff_diff]
--   rw [Set.diff_diff_cancel_left]
--   exact union_subset h.C_indep.subset_ground h.D_coindep.subset_ground

-- lemma IsMinor.C_disjoint (h : N ≤m M) : Disjoint h.C N.E :=
--   (subset_diff.1 h.C_union_D_eq.subset).2.mono_left subset_union_left

-- lemma IsMinor.D_disjoint (h : N ≤m M) : Disjoint h.D N.E :=
--   (subset_diff.1 h.C_union_D_eq.subset).2.mono_left subset_union_right

-- lemma IsMinor.eq_con_restr (h : N ≤m M) : N = (M ／ h.C) ↾ N.E := by
--   simp [h.eq_con_del, ← restrict_compl]

-- lemma IsStrictMinor.C_union_D_nonempty (h : N < M) : (h.isMinor.C ∪ h.isMinor.D).Nonempty := b
--   rw [h.isMinor.C_union_D_eq]
--   exact nonempty_of_ssubset h.ssubset

lemma finite_setOf_isMinor (M : Matroid α) [M.Finite] : {N | N ≤m M}.Finite :=
  (finite_setOf_matroid M.ground_finite).subset (fun _ hNM ↦ hNM.subset)

end IsMinor

section Constructions

variable {E : Set α}

@[simp] lemma emptyOn_isMinor (M : Matroid α) : emptyOn α ≤m M :=
  M.emptyOn_isRestriction.isMinor

@[simp] lemma isMinor_emptyOn_iff : M ≤m emptyOn α ↔ M = emptyOn α :=
  ⟨fun h ↦ ground_eq_empty_iff.1 (eq_empty_of_subset_empty h.subset),
    by rintro rfl; apply emptyOn_isMinor⟩

lemma isMinor_loopyOn_iff_exists : M ≤m loopyOn E ↔ ∃ F ⊆ E, M = loopyOn F := by
  refine ⟨fun h ↦ ⟨M.E, h.subset, ?_⟩, fun h ↦ ?_⟩
  · obtain ⟨C, D, rfl⟩ := h
    simp
  obtain ⟨F, hF, rfl⟩ := h
  simpa using (loopyOn E).restrict_isMinor hF

lemma isMinor_loopyOn_iff : M ≤m loopyOn E ↔ M = loopyOn M.E ∧ M.E ⊆ E := by
  rw [isMinor_loopyOn_iff_exists]
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨_, h.2, h.1⟩⟩
  obtain ⟨F, h, rfl⟩ := h
  simpa

@[simp]
lemma freeOn_isMinor_iff : freeOn E ≤m M ↔ M.Indep E := by
  refine ⟨fun h ↦ Indep.of_isMinor (by simp) h, fun h ↦ ?_⟩
  rw [← h.restrict_eq_freeOn]
  exact restrict_isMinor _ h.subset_ground

@[simp]
lemma loopyOn_isMinor_iff : loopyOn E ≤m M ↔ M.Coindep E := by
  rw [← dual_isMinor_iff, loopyOn_dual_eq, freeOn_isMinor_iff]

end Constructions

end Matroid
