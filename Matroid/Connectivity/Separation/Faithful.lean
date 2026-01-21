import Matroid.Connectivity.Separation.Minor

set_option linter.style.longLine false

open Set Function

variable {α : Type*} {M N : Matroid α} {j k : ℕ∞} {e f : α} {A B X X' Y Y' : Set α} {i : Bool}
  {P : M.Separation} {C D : Set α} {e f : α}

namespace Matroid.Separation


section Faithful

/-- A separation `P` of `M` is faithful for a minor `N` if, for each `C` such that
`N ≤m M ／ C`, each side of `P` is skew to the intersection of `C` with the other side,
and the same is true in the dual.
If `P` has finite connectivity, this is equivalent to the assertion that `P` induces a separation
of `N` with the same connectivity that `P` has in `M`.

Some API is missing here; it should be the case that if `N = M ／ C ＼ D`, then verifying the
skewness conditions only for `C` and `D` themselves is enough to guarantee faithfulness.
Currently this is only proved when `C` or `D` is empty
(see `faithful_contract_iff` and `faithful_delete_iff`)
and can be derived easily enough via connectivity when `P.eConn < ⊤`.
But it should be true more generally.
Could faithfulness for general partitions shed some light on how to do this? -/
@[mk_iff]
structure Faithful (P : M.Separation) (N : Matroid α) : Prop where
  skew_of_contract : ∀ ⦃C⦄, C ⊆ M.E → N ≤m M ／ C → ∀ i, M.Skew (P i) (C \ P i)
  skew_dual_of_delete : ∀ ⦃D⦄, D ⊆ M.E → N ≤m M ＼ D → ∀ i, M✶.Skew (P i) (D \ P i)

@[simp]
lemma faithful_copy_iff {M' : Matroid α} {hM : M = M'} : (P.copy hM).Faithful N ↔ P.Faithful N := by
  subst hM
  simp [faithful_iff]

lemma Faithful.dual (hP : P.Faithful N) : P.dual.Faithful N✶ := by
  refine ⟨fun C hCE hm i ↦ ?_, fun D hDE hm i ↦ ?_⟩
  · rw [← M.dual_delete, dual_isMinor_iff] at hm
    exact hP.skew_dual_of_delete hCE hm i
  rw [← M.dual_contract, dual_isMinor_iff] at hm
  simpa using hP.skew_of_contract hDE hm i

@[simp] lemma faithful_dual_iff : P.dual.Faithful N ↔ P.Faithful N✶ :=
  ⟨fun h ↦ by simpa [P.dual_dual] using h.dual, fun h ↦ by simpa using h.dual⟩

lemma Faithful.ofDual {P : M✶.Separation} (hP : P.Faithful N) : P.ofDual.Faithful N✶ := by
  rwa [← faithful_dual_iff, ofDual_dual]

@[simp]
lemma faithful_symm_iff : P.symm.Faithful N ↔ P.Faithful N := by
  simp [faithful_iff, and_comm]

-- lemma faithful_iff_forall_skew_forall_skew_contract :
--     P.Faithful N ↔ (∀ ⦃C⦄, C ⊆ M.E → N ≤m M ／ C → ∀ i, M.Skew (P i) (C \ P i)) ∧
--     ∀ ⦃D⦄, D ⊆ M.E → N ≤m M ＼ D → ∀ i, (M.contract (P (!i) \ D)).Skew (P i) (D \ P i) := by
--   rw [faithful_iff, and_congr_right_iff]
--   rintro -
--   convert Iff.rfl using 5 with D hD hm i
--   rw [skew_dual_iff disjoint_sdiff_right, isModularPair_comm,
--       isModularPair_iff_skew_contract_inter (by grind)]
--   convert Iff.rfl using 2
--   · convert rfl using 2
--     grind [P.union_bool_eq i, P.disjoint_bool i]
--   · grind [P.subset (i := i), P.disjoint_bool i]
--   grind

lemma faithful_of_forall_eq (h : ∀ C D, C ⊆ M.E → D ⊆ M.E → N = M ／ C ＼ D →
    ∀ i, (M.Skew (P i) (C \ P i) ∧ M✶.Skew (P i) (D \ P i))) : P.Faithful N := by
  refine ⟨fun C hCE hm i ↦ ?_, fun D hDE hm i ↦ ?_⟩
  · obtain ⟨C', D, hC', hD, hC'D, rfl⟩ := hm.exists_contract_indep_delete_coindep
    exact (h (C ∪ C') D (union_subset hCE hC'.of_contract.subset_ground)
      (hD.of_contract.subset_ground) (by simp) i).1.mono_right <| by grind
  obtain ⟨D', C, hD', hC, hDC, rfl⟩ :=  hm.exists_delete_coindep_contract_indep
  refine (h C (D ∪ D') hC.of_delete.subset_ground
    (union_subset hDE (hD'.subset_ground.trans diff_subset)) ?_ i).2.mono_right <| by grind
   [← Matroid.contract_delete_comm _ (subset_diff.1 hC.subset_ground).2, Matroid.delete_delete]
  rw [M.delete_delete, M.contract_delete_comm
    (disjoint_union_right.2 ⟨(subset_diff.1 hC.subset_ground).2, hDC.symm⟩)]

lemma faithful_of_forall_indep_forall_coindep
    (hC : ∀ C i, M.Indep C → N ≤m M ／ C → M.Skew (P i) (C \ P i))
    (hD : ∀ D i, M.Coindep D → N ≤m M ＼ D → M✶.Skew (P i) (D \ P i)) : P.Faithful N := by
  refine ⟨fun C hCE hm i ↦ ?_, fun D hDE hm i ↦ ?_⟩
  · obtain ⟨I, J, hI, hJ, hIJ⟩ := M.exists_isBasis_subset_isBasis (diff_subset : C \ P i ⊆ C)
    refine (hC J i hJ.indep ?_).closure_skew_right.mono_right ?_
    · exact hm.trans <| contract_isMinor_of_subset _ hJ.subset
    grw [hI.subset_closure, ← hIJ, sdiff_eq_left.2 (subset_diff.1 hI.subset).2]
  obtain ⟨I, J, hI, hJ, hIJ⟩ := M✶.exists_isBasis_subset_isBasis (show D \ P i ⊆ D from diff_subset)
  refine (hD J i hJ.indep ?_).closure_skew_right.mono_right ?_
  · exact hm.trans <| IsRestriction.isMinor <| delete_isRestriction_of_subset _ hJ.subset
  grw [hI.subset_closure, ← hIJ, sdiff_eq_left.2 (subset_diff.1 hI.subset).2]

lemma faithful_contract_iff (hCE : C ⊆ M.E) : P.Faithful (M ／ C) ↔ ∀ i, M.Skew (P i) (C \ P i) := by
  refine ⟨fun h i ↦ h.skew_of_contract hCE IsMinor.refl i,
    fun h ↦ faithful_of_forall_indep_forall_coindep (fun C' i hC' hm ↦ (h i).mono_right ?_)
    (fun D i hD hm ↦ ?_)⟩
  · exact diff_subset_diff_left <| (diff_subset_diff_iff_subset hCE hC'.subset_ground).1 hm.subset
  have hDC : D ⊆ C := (diff_subset_diff_iff_subset hCE hD.subset_ground).1 hm.subset
  obtain ⟨Y, X, hY, hX, hYX, h_eq⟩ := hm.exists_delete_coindep_contract_indep
  rw [hD.delete_coindep_iff, Y.union_comm] at hY
  rw [delete_indep_iff] at hX
  obtain rfl : X ∪ (D ∪ Y) = C := by
    rw [← inter_eq_self_of_subset_left hCE,
      ← inter_eq_self_of_subset_left (union_subset hX.1.subset_ground hY.1.subset_ground),
      ← diff_eq_diff_iff_inter_eq_inter]
    apply_fun Matroid.E at h_eq
    rwa [contract_ground, contract_ground, M.delete_delete, delete_ground, diff_diff_comm,
      diff_diff, eq_comm] at h_eq
  rw [← M.contract_contract, M.delete_delete, ← M.contract_delete_comm (by grind),
    contract_eq_delete_iff_skew_compl (by grind [contract_ground]),
    Coindep.skew_compl_iff_subset_loops (by rw [coindep_contract_iff]; grind),
    contract_loops_eq, subset_diff] at h_eq
  set L := D ∪ Y with hL
  suffices h' : M✶.Skew (P i) (L \ P i) from h'.mono_right <| by grind
  nth_rw 1 [skew_dual_iff disjoint_sdiff_right, P.compl_eq, isModularPair_comm,
    (hY.1.subset diff_subset).compl_spanning.isModularPair_iff, diff_inter_right_comm,
    inter_eq_self_of_subset_right P.subset, P.diff_eq_inter_bool, diff_inter_self_eq_diff]
  suffices aux : P (!i) ∩ L ⊆ (M ↾ P (!i)).closure ((P !i) \ L) by
    nth_grw 1 [← inter_union_diff (P (!i)) L, union_subset_iff, aux,
    (restrict_isRestriction ..).closure_subset_closure, and_iff_right rfl.subset,
      ← M.subset_closure _ (diff_subset.trans P.subset)]
  nth_grw 1 [← (h !i).symm.contract_restrict_eq, restrict_closure_eq _ diff_subset
    (by grind [contract_ground, P.subset (i := !i)]), subset_inter_iff,
    and_iff_left inter_subset_left, contract_closure_eq, subset_diff, and_iff_left (by grind),
    inter_subset_right, h_eq.1, M.closure_subset_closure]
  rw [← P.union_inter_left X hX.1.subset_ground i, Set.union_comm]
  exact union_subset_union (by grind) <| by grind [P.disjoint_bool i]

lemma faithful_contract_iff_of_subset (hC : C ⊆ P i) : P.Faithful (M ／ C) ↔ M.Skew (P (!i)) C := by
  rw [faithful_contract_iff (hC.trans P.subset), Bool.forall_bool' i, diff_eq_empty.2 hC,
    and_iff_right (M.skew_empty P.subset), P.diff_eq_inter_bool, i.not_not,
    inter_eq_self_of_subset_left hC]

lemma faithful_delete_iff (hD : D ⊆ M.E) : P.Faithful (M ＼ D) ↔ ∀ i, M✶.Skew (P i) (D \ P i) := by
  rw [← faithful_contract_iff (show D ⊆ M✶.E from hD), ← M.dual_delete, ← faithful_dual_iff]
  convert Iff.rfl
  simp

lemma faithful_delete_iff_forall_subset_closure (hD : M.Coindep D) :
    P.Faithful (M ＼ D) ↔ ∀ i, P i ∩ D ⊆ M.closure (P i \ D) := by
  rw [← faithful_symm_iff, faithful_delete_iff hD.subset_ground]
  convert Iff.rfl using 2 with i
  rw [P.symm_apply, skew_comm, (hD.subset diff_subset).skew_dual_iff disjoint_sdiff_left,
    P.diff_eq_inter_bool, i.not_not, Set.union_comm, ← diff_diff, P.compl_not_eq,
    diff_inter_self_eq_diff, Set.inter_comm]

lemma faithful_delete_iff_subset_closure_of_subset (hD : M.Coindep D) (hDP : D ⊆ P i) :
    P.Faithful (M ＼ D) ↔ D ⊆ M.closure (P i \ D) := by
  rw [faithful_delete_iff_forall_subset_closure hD, Bool.forall_bool' i,
    inter_eq_self_of_subset_right hDP, ← D.inter_comm, ← P.diff_eq_inter_bool _,
    diff_eq_empty.2 hDP, and_iff_left (empty_subset ..)]

lemma faithful_delete_iff_forall_restrict_coindep (hD : M.Coindep D) :
    P.Faithful (M ＼ D) ↔ ∀ i, (M ↾ P i).Coindep (D ∩ P i) := by
  convert faithful_delete_iff_forall_subset_closure hD using 2 with i
  rw [coindep_iff_subset_closure_compl, restrict_ground_eq, diff_inter_self_eq_diff,
    restrict_closure_eq _ diff_subset, subset_inter_iff, and_iff_left inter_subset_right,
    D.inter_comm]

-- theorem what {D' : Set α} (hCE : C ⊆ M.E) (hDE : D ⊆ M.E) (hCD : Disjoint C D)
--     (h : ∀ (i : Bool), M.Skew (P i) (C \ P i) ∧ M✶.Skew (P i) (D \ P i)) (i : Bool)
--     (hD' : M.Coindep D') (hm : M ／ C ＼ D ≤m M ＼ D') : M✶.Skew (P (!i)) (D' \ P (!i)) := by
--   obtain ⟨X, Y, hX, hY, hXY, h_eq⟩ := hm.exists_delete_coindep_contract_indep

--   -- have := h_faith.skew_dual_of_delete (D := D') ?_ ?_ (!i)
--   -- wlog hD' : X = ∅ generalizing M D' X with aux
--   -- · specialize aux (M := M ＼ D') (D' := D ∪ X) (P := P.delete D') sorry sorry sorry
--   suffices h' : M✶.Skew (P (!i)) ((D' ∪ X) \ (P (!i))) from h'.mono_right <| by grind
--   rw [hD'.delete_coindep_iff, X.union_comm] at hX
--   rw [delete_indep_iff] at hY
--   rw [M.delete_delete] at h_eq
--   set W := D' ∪ X with hW
--   rw [skew_comm, (hX.1.subset diff_subset).skew_dual_iff disjoint_sdiff_left, Set.union_comm,
--     ← diff_diff, P.compl_not_eq, P.diff_eq_inter_bool _ hX.1.subset_ground, i.not_not,
--     diff_inter_self_eq_diff]
--   have h_faith := (faithful_contract_iff hCE).2 (fun i ↦ (h i).1)

--   have := ((P.contract C).faithful_delete_iff (D := D) sorry).2 ?_
--   · have := (M.dual_contract _ ▸ (this.skew_dual_of_delete (D := W \ C) sorry sorry (!i))).of_delete
--     rw [P.contract_apply, skew_comm, Coindep.skew_dual_iff _ _ _, diff_union_self,
--       ← union_diff_distrib, diff_diff_right, disjoint_sdiff_left.inter_eq, union_empty,
--       diff_diff_comm, diff_diff_right, W.union_comm, ← diff_diff, P.diff_eq_inter_bool _ sorry,
--       P.compl_not_eq, i.not_not] at this
--   · simp_rw [P.contract_apply, M.dual_contract, skew_delete_iff, and_iff_right disjoint_sdiff_left,
--       and_iff_left sorry]
--     sorry



--   clear hm hD'
--   suffices h' : W ∩ P i ⊆ M.closure ((P i ∪ C) \ W) by
--     grw [← (restrict_isRestriction (R := P i) ..).closure_subset_closure,
--       ← (h i).1.symm.contract_restrict_eq, restrict_closure_eq _ diff_subset sorry,
--       contract_closure_eq, subset_inter_iff, and_iff_left inter_subset_right, subset_diff,
--       and_iff_left (by grind), h', closure_subset_closure]
--     grind




--   have hYW : Disjoint Y W := by grind
--   have hcl := fun A ↦ congr_arg (fun N ↦ N.closure A) h_eq
--   simp [diff_diff] at hcl

--   rw [diff_diff, diff_diff, union_diff_distrib, diff_eq_empty.2 inter_subset_left, empty_union,
--     hYW.sdiff_eq_left] at hcl
--   -- have hcl : (M ／ C ＼ D).closure (P i \ (W ∪ C)) = (M ＼ W ／ Y).closure (P i \ (W ∪ C)) := sorry

--   rw [contract_closure_eq] at hcl


--   sorry
--   -- rw [skew_dual_iff disjoint_sdiff_right P.subset (diff_subset.trans hX.1.subset_ground),
--   --   isModularPair_comm, ((hX.1).subset diff_subset).compl_spanning.isModularPair_iff]
--     -- refine (aux (X := X ∪ D') ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).mono_right ?_

--   -- rw [skew_dual_iff disjoint_sdiff_right P.subset (diff_subset.trans hD'.subset_ground),
--   --   isModularPair_comm, (hD'.subset diff_subset).compl_spanning.isModularPair_iff, P.compl_not_eq,
--   --   P.diff_eq_inter_bool, i.not_not, diff_inter_right_comm, inter_eq_self_of_subset_right P.subset,
--   --   diff_inter_self_eq_diff]
--   -- nth_rw 1 [← diff_union_inter (P i) D', union_subset_iff, and_iff_right (M.subset_closure ..)]
--   -- rw [coindep_contract_iff] at hX
--   -- rw [hC'.contract_indep_iff] at hY
--   -- rw [M.contract_contract] at h_eq


-- lemma faithful_contract_delete_iff (hCE : C ⊆ M.E) (hDE : D ⊆ M.E) (hCD : Disjoint C D) :
--     P.Faithful (M ／ C ＼ D) ↔ ∀ i, M.Skew (P i) (C \ P i) ∧ M✶.Skew (P i) (D \ P i) := by
--   refine ⟨fun h i ↦ ⟨h.skew_of_contract hCE (delete_isMinor ..) i, ?_⟩,
--     fun h ↦ faithful_of_blah (fun C' i hC' hm ↦ ?_) (fun D' i hD' hm ↦ ?_)⟩
--   · exact h.skew_dual_of_delete hDE (contract_delete_isMinor_delete _ hCD) i
--   · have := what (M := M✶) (P := P.dual) (C := D) (D := C) (D' := C') (i := !i) hDE hCE
--       hCD.symm sorry (by simpa) sorry
--     simpa using this
--   simpa using what (P := P) (C := C) (D := D) (D' := D') hCE hDE hCD h (!i) hD' hm
--     -- have := what hC'.subset_ground hDE (D' := D)
--   -- refine what (M := M✶) (P := P.dual) hDE hCE hCD.symm (fun i ↦ ?_) i hD'.indep ?_
--   -- · simpa [and_comm] using h i
--   -- rw [← dual_isMinor_iff, M✶.contract_delete_comm hCD.symm]
--   -- simpa







lemma Faithful.eConn_induce_eq (hP : P.Faithful N) (hNM : N ≤m M) :
    (P.induce hNM.subset).eConn = P.eConn := by
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := hNM.exists_contract_indep_delete_coindep
  grw [induce_eq_contract_delete, ← eConn_dual, delete_dual, eConn_copy,
    eConn_contract_eq_self_of_forall_skew]
  · rw [eConn_dual, eConn_contract_eq_self_of_forall_skew]
    apply hP.skew_of_contract hC.subset_ground (delete_isMinor ..)
  simp_rw [M.dual_contract, Separation.dual_apply, P.contract_apply, skew_delete_iff]
  refine fun i ↦ ⟨?_, disjoint_sdiff_left, hCD.symm.mono_left diff_subset⟩
  exact (hP.skew_dual_of_delete hD.subset_ground (contract_delete_isMinor_delete _ hCD) i).mono
    diff_subset <| by grind

lemma Faithful.eConn_delete_eq (hP : P.Faithful (M ＼ D)) : (P.delete D).eConn = P.eConn := by
  rw [← hP.eConn_induce_eq (delete_isMinor ..), induce_eq_delete]

lemma Faithful.eConn_contract_eq (hP : P.Faithful (M ／ C)) : (P.contract C).eConn = P.eConn := by
  rw [← hP.eConn_induce_eq (contract_isMinor ..), induce_eq_contract]

lemma faithful_iff_eConn_induce_eq {hNM : N ≤m M} (hConn : (P.induce hNM.subset).eConn ≠ ⊤) :
    P.Faithful N ↔ (P.induce hNM.subset).eConn = P.eConn := by
  refine ⟨fun h ↦ h.eConn_induce_eq hNM, fun h ↦ ?_⟩
  suffices aux (N' M' : Matroid α) (C : Set α) (P' : M'.Separation) (hC : C ⊆ M'.E)
      (hm : N' ≤m M' ／ C) (hP' : P'.eConn < ⊤) (hPconn : P'.eConn ≤ (P'.contract C).eConn)
      (i : Bool) : M'.Skew (P' i) (C \ P' i)
  · have hPtop : P.eConn < ⊤ := by enat_to_nat!
    refine ⟨fun C hC hNC i ↦ ?_, fun D hD hND i ↦ ?_⟩
    · refine aux N M C P hC hNC hPtop ?_ i
      have hrw : (P.induce hNM.subset) = (P.contract C).induce hNC.subset :=
        induce_eq_contract _ _ ▸ (Bipartition.induce_induce ..).symm
      grw [← h, hrw, eConn_induce_le_of_isMinor _ hNC]
    apply aux N✶ M✶ D P.dual hD (by rwa [← M.dual_delete, dual_isMinor_iff]) (by simpa)
    have hrw : (P.induce hNM.subset) = (P.delete D).induce hND.subset :=
      induce_eq_delete _ _ ▸ (Bipartition.induce_induce ..).symm
    grw [dual_contract, eConn_copy, eConn_dual, eConn_dual, ← h, hrw,
      eConn_induce_le_of_isMinor _ hND]
  rw [eConn_le_eConn_contract_iff_forall_skew _] at hPconn
  · apply hPconn
  grw [← lt_top_iff_ne_top, eConn_contract_le]
  assumption

lemma Faithful.isModularPair (h : P.Faithful N) (hND : N ≤m M ＼ D) (i : Bool) :
    M.IsModularPair (P i) (M.E \ (D ∩ P i)) := by
  wlog hD : D ⊆ M.E generalizing D with aux
  · convert aux (D := D ∩ M.E) (by simpa) inter_subset_right using 1
    grind
  have hsk := h.skew_dual_of_delete hD hND !i
  rwa [skew_dual_iff disjoint_sdiff_right, P.compl_not_eq, P.diff_eq_inter_bool,
    Bool.not_not] at hsk

lemma Faithful.isModularPair' (h : P.Faithful N) (hND : N ≤m M ＼ D) (i : Bool) :
    M.IsModularPair (P i) (P (!i) ∪ (P i \ D)) := by
  convert h.isModularPair hND i using 1
  grind [P.disjoint_bool i, P.union_bool_eq i]

lemma Faithful.subset_closure_diff_of_coindep (h : P.Faithful N) (hND : N ≤m M ＼ D)
    (hD : M.Coindep D) (i : Bool) : P i ⊆ M.closure (P i \ D) := by
  have hmod := h.isModularPair hND i
  rw [isModularPair_comm, (hD.subset inter_subset_left).compl_spanning.isModularPair_iff] at hmod
  exact hmod.trans <| M.closure_subset_closure <| by grind

lemma Faithful.nullity_le (h : P.Faithful N) (hNM : N ≤m M) (i : Bool) :
    N.nullity (P i ∩ N.E) ≤ M.nullity (P i) := by
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := hNM.exists_contract_indep_delete_coindep
  rw [delete_ground, contract_ground, nullity_delete _ (by grind), ← inter_diff_assoc,
    ← inter_diff_assoc, inter_eq_self_of_subset_left P.subset, diff_diff_comm]
  have h_eq := M.nullity_union_eq_nullity_contract_add_nullity C (P i \ D)
  rw [hC.nullity_eq, add_zero] at h_eq
  grw [← h_eq, ← diff_union_self, diff_diff_right, hCD.inter_eq, union_empty,
    Skew.nullity_union_eq _ (by grind), (hC.diff _).nullity_eq, zero_add,
    nullity_le_of_subset _ diff_subset]
  exact (h.skew_of_contract hC.subset_ground (delete_isMinor ..) i).symm.mono_right diff_subset

lemma Faithful.indep_of_indep (hPN : P.Faithful N) (hNM : N ≤m M) (h : M.Indep (P i)) :
    N.Indep (P i ∩ N.E) := by
  grw [← nullity_eq_zero, ← nonpos_iff_eq_zero, hPN.nullity_le hNM, h.nullity_eq]

lemma Faithful.coindep_of_coindep (hPN : P.Faithful N) (hNM : N ≤m M) (h : M.Coindep (P i)) :
    N.Coindep (P i ∩ N.E) :=
  hPN.dual.indep_of_indep hNM.dual h

lemma Faithful.spanning_of_spanning (hPN : P.Faithful N) (hNM : N ≤m M) (h : M.Spanning (P i)) :
    N.Spanning (P i ∩ N.E) := by
  rw [spanning_iff_compl_coindep, diff_inter_self_eq_diff, P.diff_eq_inter_bool _ hNM.subset,
    Set.inter_comm]
  exact hPN.coindep_of_coindep hNM <| P.compl_eq _ ▸ h.compl_coindep

end Faithful

end Separation

/-- The sum of the nullity and conullity of a set in `M`. For finite sets, this is the difference
between the cardinality and the connectivity. -/
noncomputable def tutteWeight (M : Matroid α) (X : Set α) : ℕ∞ := M.nullity X + M✶.nullity X

lemma tutteWeight_def : M.tutteWeight X = M.nullity X + M✶.nullity X := rfl

lemma tutteWeight_le_of_subset (M : Matroid α) (hXY : X ⊆ Y) : M.tutteWeight X ≤ M.tutteWeight Y :=
  add_le_add (M.nullity_le_of_subset hXY) (M✶.nullity_le_of_subset hXY)

@[simp]
lemma tutteWeight_dual : M✶.tutteWeight = M.tutteWeight := by
  ext X
  simp [tutteWeight_def, add_comm]

lemma Indep.tutteWeight_eq (h : M.Indep X) : M.tutteWeight X = M✶.nullity X := by
  simp [tutteWeight_def, h]

lemma Coindep.tutteWeight_eq (h : M.Coindep X) : M.tutteWeight X = M.nullity X := by
  simp [tutteWeight_def, h]

-- @[simp]
-- lemma tutteWeight_eq_zero : M.tutteWeight X = 0 ↔ M.TutteDegen X := by
--   simp [tutteWeight_def, tutteDegen_iff]

lemma eConn_add_tutteWeight_eq (M : Matroid α) (hXE : X ⊆ M.E := by aesop_mat) :
    M.eConn X + M.tutteWeight X = X.encard := by
  rw [← M.eConn_add_nullity_add_nullity_dual X, add_assoc, tutteWeight_def]

def IsFaithfulMono (w : Matroid α → Set α → ℕ∞) : Prop := ∀ ⦃M N : Matroid α⦄ ⦃P : M.Separation⦄
    (i : Bool), N ≤m M → P.Faithful N → w N (P i ∩ N.E) ≤ w M (P i)

lemma IsFaithfulMono.add {w w' : Matroid α → Set α → ℕ∞} (hw : IsFaithfulMono w)
    (hw' : IsFaithfulMono w') : IsFaithfulMono (fun M X ↦ w M X + w' M X) :=
  fun _ _ _ i h h' ↦ add_le_add (hw i h h') (hw' i h h')

lemma IsFaithfulMono.dual {w} (hw : IsFaithfulMono (α := α) w) :
    IsFaithfulMono (fun M X ↦ w M✶ X) :=
  fun M N P i h h' ↦ by simpa using hw i h.dual h'.dual

lemma IsFaithfulMono.le_of_delete {w} (h : IsFaithfulMono w) (hP : P.Faithful (M ＼ D))
    (i : Bool) : w (M ＼ D) (P i \ D) ≤ w M (P i) := by
  grw [← h i (M.delete_isMinor D) hP, delete_ground, ← inter_diff_assoc, P.inter_ground_eq]

lemma IsFaithfulMono.le_of_contract {w} (h : IsFaithfulMono w) (hP : P.Faithful (M ／ C))
    (i : Bool) : w (M ／ C) (P i \ C) ≤ w M (P i) := by
  grw [← h i (M.contract_isMinor C) hP, contract_ground, ← inter_diff_assoc, P.inter_ground_eq]

lemma isFaithfulMono_nullity : IsFaithfulMono (α := α) Matroid.nullity :=
  fun _ _ _ i hNM h ↦ h.nullity_le hNM i

lemma isFaithfulMono_tutteWeight : IsFaithfulMono (α := α) Matroid.tutteWeight :=
  isFaithfulMono_nullity.add isFaithfulMono_nullity.dual

end Matroid





  -- rw [M.delete_delete] at h_eq


  -- refine ⟨fun h i ↦ ?_, fun h ↦ (faithful_iff _ _).2
  --   ⟨fun C' hC'E hm i ↦ (h i).mono_right (diff_subset_diff_left ?_), fun D hDE hm i ↦ ?_⟩⟩
  -- · apply h.skew_of_contract hCE <| IsMinor.refl
  -- · exact (diff_subset_diff_iff_subset hCE hC'E).1 hm.subset
  -- have hDC : D ⊆ C := (diff_subset_diff_iff_subset hCE hDE).1 hm.subset
  -- obtain ⟨X, Y, hX, hY, hXY, h_eq⟩ := hm.exists_contract_indep_delete_coindep
  -- obtain ⟨hXE, hXD⟩ := by simpa [subset_diff] using hX.subset_ground
  -- obtain ⟨hYE, hYD⟩ := by simpa [subset_diff] using hY.subset_ground
  -- rw [← M.contract_delete_comm hXD] at h_eq



  -- rw [faithful_iff_forall_skew_forall_skew_contract]



-- lemma contract_faithful_of_forall_skew (hP : ∀ i, M.Skew (P i) (C \ P i)) : P.Faithful (M ／ C) := by
--   refine ⟨fun C₀ hC₀ hC₀M i ↦ (hP i).mono_right (diff_subset_diff_left ?_), ?_⟩
--   · have hss := hC₀M.subset
--     rw [contract_ground, contract_ground, subset_diff] at hss
--     grind

--   wlog hCE : C ⊆ M.E generalizing C with aux
--   · simpa using aux (C := C ∩ M.E) (fun i ↦ (hP i).mono_right (by grind)) inter_subset_right

--   intro D hDE hm i
--   have hDC : D ⊆ C := by simpa [diff_subset_diff_iff_subset hCE hDE] using hm.subset

--   obtain ⟨C', D', hC', hD', hdj, h_eq⟩ := hm.exists_contract_indep_delete_coindep
--   obtain ⟨hD'E : D' ⊆ M.E, hD'D : Disjoint D' D⟩ := subset_diff.1 hD'.subset_ground
--   obtain ⟨hC'E : C' ⊆ M.E, hC'D : Disjoint C' D⟩ := subset_diff.1 hC'.subset_ground
--   rw [← contract_delete_comm _ hC'D] at h_eq
--   obtain rfl : C  = C' ∪ (D ∪ D') := by
--     apply_fun Matroid.E at h_eq
--     simp only [contract_ground, delete_ground, diff_diff] at h_eq
--     rw [diff_eq_diff_iff_inter_eq_inter, inter_eq_self_of_subset_left hCE] at h_eq
--     grind
--   suffices h' : M✶.Skew (P i) ((D ∪ D') \ P i) from h'.mono_right (by grind)
--   wlog hD'e : D' = ∅ generalizing D D' with aux
--   · rw [← union_empty (D ∪ D')]
--     refine aux (union_subset hDE hD'E) ∅ (by simp [hC'.of_delete, hdj, hC'D]) (by simp) (by simp)
--       (by simp) (by simp) (by simp [hC'D, hdj]) (by simpa using hP) (by aesop_mat) ?_ (by simp)
--       ?_ rfl
--     · rw [Set.union_empty, h_eq, (M ／ C').delete_delete, contract_delete_comm _ (by grind)]
--       exact contract_isMinor ..
--     rwa [union_empty, delete_empty, ← (M ／ C').delete_delete]
--   simp only [delete_indep_iff, hD'e, empty_indep, disjoint_empty, empty_subset, empty_disjoint,
--     union_empty, union_subset_iff, subset_union_right, delete_empty, and_iff_left hC'D] at *

--   rw [skew_dual_iff disjoint_sdiff_right, P.compl_eq]
  -- wlog hCe : C' = ∅ generalizing M C' P with aux
  -- ·
  --   specialize aux (M := M ／ C') (P := P.contract C') ∅ (by simp) (by grind [contract_ground])
  --     (by simp) (by simp) sorry sorry sorry sorry rfl
  --   simp at aux






      -- ·
          -- specialize aux (union_subset hDE hD'E) ∅

          -- simp [hC'D, hC'.of_delete, hdj, -Bool.forall_bool, hC'E, hDE, hD'E, hP] at aux
          -- specialize aux (union_subset hDE hD'E) ?_ (by grind) ∅
          -- · rw [h_eq, contract_delete_comm _ (by grind)]
          --   apply contract_isMinor
          -- have h' : M✶.Skew (P i) ((D ∪ D') \ P i) := by simpa [hC'.of_delete, hC'D, hdj, h_eq] using aux
          -- exact h'.mono_right (by grind)






    -- ·
    -- specialize aux (union_subset hDE hD'E) ∅

    -- simp [hC'D, hC'.of_delete, hdj, -Bool.forall_bool, hC'E, hDE, hD'E, hP] at aux
    -- specialize aux (union_subset hDE hD'E) ?_ (by grind) ∅
    -- · rw [h_eq, contract_delete_comm _ (by grind)]
    --   apply contract_isMinor
    -- have h' : M✶.Skew (P i) ((D ∪ D') \ P i) := by simpa [hC'.of_delete, hC'D, hdj, h_eq] using aux
    -- exact h'.mono_right (by grind)
  -- simp only [delete_indep_iff, hD'e, empty_indep, disjoint_empty, union_empty,
  --   empty_subset, empty_disjoint, and_iff_left hC'D] at *
  -- have hC : C = C' ∪ D := by
  --   _

    -- ?_ (by simp) (by simp) (by simpa)
    --   (by simp) (by simp)
    -- · sorry
    -- · rwa [← M.delete_delete, delete_indep_iff, and_iff_left hdj]

    -- simp at aux

    --  sorry (by grind) ?_ ?_
    -- · rwa [← M.delete_delete, delete_indep_iff, and_iff_left hdj]
    -- · rw [← M.delete_delete, Coindep.delete_coindep_iff]










  -- wlog hC : M.Skew C (M.E \ C) generalizing M C with aux
  -- · intro D hDE hmin i
  --   obtain ⟨C', D', hC', hD', hdj, hM⟩ := hmin.exists_eq_contract_delete_disjoint
  --   rw [delete_ground, subset_diff] at hC' hD'
  --   rw [← contract_delete_comm _ (by grind), (M ／ C').delete_delete,
  --     show C = C' ∪ (D ∪ D') from sorry, ← M.contract_contract] at hM
  --   have hM' := (contract_eq_delete_iff_skew_compl ?_).1 hM
  --   specialize aux (M := M ／ C') (P := P.contract C') (C := D ∪ D') sorry hM'
  --     (show D ∪ D' ⊆ (M ／ C').E by sorry) hM.le i
  --   · simp only [Matroid.dual_contract, ↓contract_apply] at aux
  --     refine aux.of_delete.mono ?_
  --   sorry
  -- sorry



--   obtain ⟨C', D', hC', hD', hdj, hM⟩ := hm.exists_eq_contract_delete_disjoint
--   have hDC : D ⊆ C := sorry
--   rw [delete_ground, subset_diff] at hC' hD'
--   have hss : D ∪ D' ⊆ (M ／ C').E := by grind [contract_ground]
--   rw [contract_delete_comm _ hdj, M.delete_delete, ← contract_delete_comm _ (by grind),
--     show C = C' ∪ (D ∪ D') by sorry, ← M.contract_contract,
--     contract_eq_delete_iff_skew_compl, contract_ground,
--     skew_iff_restrict_union_eq hss (by simp [diff_subset]) disjoint_sdiff_right,
--     union_diff_cancel (by simpa using hss), ← contract_ground, restrict_ground_eq_self] at hM
--   simp_rw [← delete_eq_restrict] at hM
--   set D₀ := D ∪ D' with hD₀
--   suffices h : M✶.Skew (P i) (D₀ \ P i) from h.mono_right (diff_subset_diff_left
-- subset_union_left)

--   rw [skew_dual_iff disjoint_sdiff_right P.subset (diff_subset.trans (hss.trans diff_subset))]

  -- replace hP := (hP !i).mono_right (diff_subset_diff_left hDC)
  -- have := hP.isModularPair_union_right_of_subset_left (Z := P (!i) \ D)
  -- have := (hP !i).isModularPair_union_right_of_subset_left (Z := P !i) rfl.subset
  -- rw [skew_iff_contract_restrict_eq_restrict, ← delete_compl _, contract_ground, dual_ground,
  --   P.compl_eq, P.diff_eq_inter_bool, diff_inter_self_eq_diff, ← delete_compl _, dual_ground,
  --   ← P.diff_eq_inter_bool, ← dual_inj, dual_contract_delete, dual_dual, dual_delete_dual]
  -- · have hDC : D ⊆ C := sorry
  --   replace hP := (hP i).mono_right (diff_subset_diff_left hDC)
  --   have := hP.contract_restrict_eq
  -- rw [skew_dual_iff disjoint_sdiff_right]
