import Matroid.Connectivity.Separation.Minor

open Set Function Bool

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
  isMinor : N ≤m M
  skew_of_contract : ∀ ⦃C⦄, C ⊆ M.E → N ≤m M ／ C → ∀ i, M.Skew (P i) (C \ P i)
  skew_dual_of_delete : ∀ ⦃D⦄, D ⊆ M.E → N ≤m M ＼ D → ∀ i, M✶.Skew (P i) (D \ P i)

@[simp]
lemma faithful_copy_iff {M' : Matroid α} {hM : M = M'} : (P.copy hM).Faithful N ↔ P.Faithful N := by
  subst hM
  simp [faithful_iff]

lemma Faithful.dual (hP : P.Faithful N) : (P.induce M✶).Faithful N✶ := by
  refine ⟨hP.isMinor.dual, fun C hCE hm i ↦ ?_, fun D hDE hm i ↦ ?_⟩
  · rw [← M.dual_delete, dual_isMinor_iff] at hm
    simpa using hP.skew_dual_of_delete hCE hm i
  rw [← M.dual_contract, dual_isMinor_iff] at hm
  simpa using hP.skew_of_contract hDE hm i

lemma Faithful.of_dual {P : M✶.Separation} (hP : P.Faithful N) : (P.induce M).Faithful N✶ := by
  convert hP.dual
  simp

@[simp]
lemma faithful_dual_iff : (P.induce M✶).Faithful N ↔ P.Faithful N✶ :=
  ⟨fun h ↦ by simpa [induce_copy] using faithful_copy_iff (hM := M.dual_dual).2 h.dual,
    fun h ↦ by simpa using h.dual⟩

lemma faithful_dual_iff' : (P.induce M✶).Faithful N✶ ↔ P.Faithful N := by
  simp

@[simp]
lemma faithful_of_dual_iff {P : M✶.Separation} : (P.induce M).Faithful N ↔ P.Faithful N✶ :=
  ⟨fun h ↦ by simpa using h.dual, fun h ↦ by simpa using h.of_dual⟩

-- @[simp]
-- lemma faithful_bDual_iff {P : M.Separation} {b : Bool} :
--     (P.bDual b).Faithful N ↔ P.Faithful (N.bDual b) := by
--   cases b <;> simp

-- @[simp]
-- lemma faithful_ofbDual_iff {b} {P : (M.bDual b).Separation} :
--     P.ofbDual.Faithful N ↔ P.Faithful (N.bDual b) := by
--   rw [← faithful_bDual_iff, ← N.bDual_bDual_self b, ← faithful_bDual_iff, ofbDual_bDual,
--     N.bDual_bDual_self, faithful_bDual_iff]

@[simp]
lemma faithful_symm_iff : P.symm.Faithful N ↔ P.Faithful N := by
  simp [faithful_iff, _root_.and_comm]

lemma Faithful.faithful_of_isMinor_isMinor (h : P.Faithful N) {N'} (hNN' : N ≤m N')
    (hN' : N' ≤m M) : P.Faithful N' :=
  ⟨hN', fun _ hC hN'C ↦ h.skew_of_contract hC (hNN'.trans hN'C),
    fun _ hD hN'D ↦ h.skew_dual_of_delete hD (hNN'.trans hN'D)⟩

alias ⟨_, Faithful.symm⟩ := faithful_symm_iff

lemma faithful_of_forall_eq (hN : N ≤m M) (h : ∀ C D, C ⊆ M.E → D ⊆ M.E → Disjoint C D →
    N = M ／ C ＼ D → ∀ i, (M.Skew (P i) (C \ P i) ∧ M✶.Skew (P i) (D \ P i))) : P.Faithful N := by
  refine ⟨hN, fun C hCE hm i ↦ ?_, fun D hDE hm i ↦ ?_⟩
  · obtain ⟨C', D, hC', hD, hC'D, rfl⟩ := hm.exists_contract_indep_delete_coindep
    exact (h (C ∪ C') D (union_subset hCE hC'.of_contract.subset_ground)
      (hD.of_contract.subset_ground) (by grind [hD.subset_ground]) (by simp) i).1.mono_right <|
      by grind
  obtain ⟨D', C, hD', hC, hDC, rfl⟩ :=  hm.exists_delete_coindep_contract_indep
  refine (h C (D ∪ D') hC.of_delete.subset_ground
    (union_subset hDE (hD'.subset_ground.trans diff_subset)) ?_ ?_ i).2.mono_right <| by grind
   [← Matroid.contract_delete_comm _ (subset_diff.1 hC.subset_ground).2, Matroid.delete_delete]
  · grind [hC.subset_ground]
  rw [M.delete_delete, M.contract_delete_comm
    (disjoint_union_right.2 ⟨(subset_diff.1 hC.subset_ground).2, hDC.symm⟩)]

lemma Faithful.faithful_induce_of_isMinor (h : P.Faithful N) {N'} (hNN' : N ≤m N') (hN' : N' ≤m M) :
    (P.induce N').Faithful N := by
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := hN'.exists_contract_indep_delete_coindep
  refine ⟨hNN', fun X hX hNX i ↦ ?_, fun X hX hNX i ↦ ?_⟩
  · have hs := h.skew_of_contract (C := X ∪ C) (by grind [hC.subset_ground]) ?_ i
    refine ((hs.contract_subset_union (C := C) (by grind)).delete D).mono ?_ ?_
    · rw [induce_apply_contract_delete, diff_diff]
    · grind [induce_apply_contract_delete]
    rw [← contract_delete_comm _ (by grind), contract_contract, union_comm] at hNX
    exact hNX.trans <| delete_isMinor ..
  rw [dual_contract_delete, ← contract_delete_comm _ hCD.symm]
  have hs := (h.skew_dual_of_delete (D := X ∪ D) (by grind [hD.subset_ground]) ?_ i)
  · refine ((hs.contract_subset_union (C := D) (by grind)).delete C).mono ?_ ?_
    · simp [diff_diff, union_comm]
    grind [induce_apply_contract_delete]
  refine hNX.trans ?_
  rw [delete_delete, union_comm]
  apply M.contract_delete_isMinor_delete (by grind)

lemma Faithful.faithful_induce_of_isMinor_isMinor {N₁ N₂ : Matroid α} (h : P.Faithful N)
    (hN₁ : N ≤m N₁) (hN₁N₂ : N₁ ≤m N₂) (hN₂ : N₂ ≤m M) : (P.induce N₂).Faithful N₁ :=
  (h.faithful_induce_of_isMinor (hN₁.trans hN₁N₂) hN₂).faithful_of_isMinor_isMinor hN₁ hN₁N₂

lemma faithful_of_forall_indep_forall_coindep (hN : N ≤m M)
    (hC : ∀ C i, M.Indep C → N ≤m M ／ C → M.Skew (P i) (C \ P i))
    (hD : ∀ D i, M.Coindep D → N ≤m M ＼ D → M✶.Skew (P i) (D \ P i)) : P.Faithful N := by
  refine ⟨hN, fun C hCE hm i ↦ ?_, fun D hDE hm i ↦ ?_⟩
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
    fun h ↦ faithful_of_forall_indep_forall_coindep (contract_isMinor ..)
      (fun C' i hC' hm ↦ (h i).mono_right ?_) (fun D i hD hm ↦ ?_)⟩
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
  convert faithful_contract_iff (P := P.induce M✶) hD using 1
  · rw [faithful_dual_iff, dual_contract_dual]
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

lemma faithful_delete_of_subset_closure (hD : D ⊆ P i) (hDcl : D ⊆ M.closure (P i \ D)) :
    P.Faithful (M ＼ D) := by
  have hDE : D ⊆ M.E := hD.trans P.subset
  have hDi : M.Coindep D := by
    grw [coindep_iff_subset_closure_compl, ← diff_subset_diff_left (P.subset (i := i)), ← hDcl]
  rwa [faithful_delete_iff_subset_closure_of_subset hDi hD]

set_option backward.isDefEq.respectTransparency false in
lemma faithful_delete_of_forall_subset_closure (hDcl : ∀ i, P i ∩ D ⊆ M.closure (P i \ D)) :
    P.Faithful (M ＼ D) := by
  wlog hD : D ⊆ M.E generalizing D with aux
  · rw [← delete_inter_ground_eq]
    refine aux (fun i ↦ ?_) inter_subset_right
    grw [← inter_assoc, inter_right_comm, P.inter_ground_left, hDcl, diff_inter,
      diff_eq_empty.2 P.subset, union_empty]
  have hD : M.Coindep D := by
    grw [coindep_iff_subset_closure_compl, ← P.union_eq, union_diff_distrib,
      ← closure_closure_union_closure_eq_closure_union, ← hDcl, ← hDcl, ← union_inter_distrib_right,
      P.union_eq, inter_eq_self_of_subset_right hD, ← M.subset_closure D hD]
  rwa [faithful_delete_iff_forall_subset_closure hD]

lemma faithful_remove_iff (hX : X ⊆ M.E) {b : Bool} :
    P.Faithful (M.remove b X) ↔ ∀ i, (M.bDual (!b)).Skew (P i) (X \ P i) := by
  cases b
  · simp [faithful_delete_iff hX]
  simp [faithful_contract_iff hX]

lemma faithful_remove_iff_of_subset {b : Bool} (hX : X ⊆ P i) :
    P.Faithful (M.remove b X) ↔ (M.bDual (!b)).Skew (P (!i)) X := by
  rw [faithful_remove_iff (hX.trans P.subset), forall_bool' i, diff_eq_empty.2 hX,
    and_iff_right ((M.bDual _).skew_empty (by simp)), P.diff_eq_inter_bool, i.not_not,
    inter_eq_self_of_subset_left hX]

lemma faithful_remove_of_subset_closure {b : Bool} (hX : X ⊆ P i)
    (hXcl : X ⊆ (M.bDual b).closure (P i \ X)) : P.Faithful (M.remove b X) := by
  cases b
  · exact faithful_delete_of_subset_closure hX hXcl
  simpa using
    ((P.induce M✶).faithful_delete_of_subset_closure (by simpa) (by simpa using hXcl)).of_dual

lemma faithful_delete_iff_forall_restrict_coindep (hD : M.Coindep D) :
    P.Faithful (M ＼ D) ↔ ∀ i, (M ↾ P i).Coindep (D ∩ P i) := by
  convert faithful_delete_iff_forall_subset_closure hD using 2 with i
  rw [coindep_iff_subset_closure_compl, restrict_ground_eq, diff_inter_self_eq_diff,
    restrict_closure_eq _ diff_subset, subset_inter_iff, and_iff_left inter_subset_right,
    D.inter_comm]

lemma Faithful.eConn_induce_eq (hP : P.Faithful N) : (P.induce N).eConn = P.eConn := by
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := hP.isMinor.exists_eq_contract_delete_disjoint
  wlog hD0 : D = ∅ generalizing M C D with aux
  · rw [← aux C ∅ hC (by simp) (by simp) ?_ rfl, delete_empty, ← P.induce_dual_eConn (M ／ C),
      ← aux (M := (M ／ C)✶) D ∅ _ (by simp) (by simp) ?_ rfl,
      delete_empty, induce_induce_contract, ← (M ／ C).dual_delete,
      induce_dual_eConn, induce_contract_delete]
    · simp only [dual_contract, delete_ground, dual_ground]
      grind
    · rw [dual_contract, delete_empty, ← induce_dual_induce]
      exact hP.dual.faithful_induce_of_isMinor (by simp [contract_isMinor]) (delete_isMinor ..)
    exact hP.faithful_of_isMinor_isMinor (by simp [delete_isMinor]) (contract_delete_isMinor ..)
  subst hD0
  rw [delete_empty, faithful_contract_iff hC] at hP
  rw [delete_empty, ← contract_inter_ground_eq, ← P.union_eq, inter_union_distrib_left,
    ← contract_contract, P.eConn_eq_eConn_induce_contract_add (C := C ∩ P true) inter_subset_right,
    (P.induce (M ／ (C ∩ P true))).eConn_eq_eConn_induce_contract_add
      (C := C ∩ P false) (i := false), induce_union_contract, eConn_copy, contract_contract,
      Skew.eLocalConn, Skew.eLocalConn, add_zero, add_zero]
  · exact (hP false).mono_right <| by rw [P.diff_eq_inter_bool, Bool.not_false]
  · refine ((hP true).contract_subset_left inter_subset_right).mono ?_ ?_
    · grind [induce_false_true]
    grind [P.disjoint_true_false]
  grind [P.disjoint_false_true, induce_apply_contract]

lemma faithful_iff_eConn_induce_eq (hNM : N ≤m M) (hConn : (P.induce N).eConn ≠ ⊤) :
    P.Faithful N ↔ (P.induce N).eConn = P.eConn := by
  refine ⟨Faithful.eConn_induce_eq, fun h ↦ faithful_of_forall_eq hNM ?_⟩
  rintro C D hC hD hCD rfl i
  have hrw : (M ／ C).eConn (P i \ C) = M.eConn (P i) := by
    nth_grw 1 [le_antisymm_iff, eConn_contract_diff_le, and_iff_right rfl.le, P.eConn_eq, ← h,
      ← Separation.eConn_eq _ i, induce_apply_contract_delete, ← diff_diff, eConn_delete_diff_le]
  have hrw' : (M✶ ／ D).eConn (P i \ D) = M.eConn (P i) := by
    nth_grw 1 [← eConn_dual, dual_contract_dual, le_antisymm_iff,
      and_iff_right (eConn_delete_diff_le ..), P.eConn_eq, ← h,
      ← Separation.eConn_eq _ i, induce_apply_contract_delete, contract_delete_comm _ hCD,
      union_comm, ← diff_diff, eConn_contract_diff_le]
  refine ⟨((M.eConn_contract_diff_eq_self_iff_skew_skew ?_).1 hrw).1, ?_⟩
  · rwa [hrw, P.eConn_eq, ← h]
  refine ((M✶.eConn_contract_diff_eq_self_iff_skew_skew ?_).1 (by simpa using hrw')).1
  rwa [hrw', P.eConn_eq, ← h]

lemma faithful_of_eConn_induce_ge (hP : P.eConn ≠ ⊤) (hNM : N ≤m M)
    (hconn : P.eConn ≤ (P.induce N).eConn) : P.Faithful N := by
  grw [faithful_iff_eConn_induce_eq hNM, le_antisymm_iff, and_iff_left hconn,
    eConn_induce_le_of_isMinor _ hNM]
  grw [← lt_top_iff_ne_top, eConn_induce_le_of_isMinor _ hNM, lt_top_iff_ne_top]
  assumption

/-- This should be true without the `⊤` assumption. -/
lemma Faithful.trans {N₀ : Matroid α} (hP : P.Faithful N)
    (hP' : (P.induce N).Faithful N₀) (hconn : P.eConn ≠ ⊤) : P.Faithful N₀ := by
  refine faithful_of_eConn_induce_ge hconn (hP'.isMinor.trans hP.isMinor) ?_
  grw [← hP.eConn_induce_eq, ← hP'.eConn_induce_eq, induce_induce _ hP'.isMinor.subset]

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

lemma Faithful.mem_closure_of_delete {e} (hP : P.Faithful (M ＼ D)) (hD : M.Coindep D)
    (hei : e ∈ P i) : e ∈ M.closure (P i \ D) :=
  mem_of_mem_of_subset hei <| hP.subset_closure_diff_of_coindep IsMinor.refl hD _

lemma Faithful.mem_closure_delete_of_delete {e D'} {P : (M ＼ D).Separation}
    (hP : P.Faithful (M ＼ D')) (hDD' : D ⊆ D') (hei : e ∈ P i) (hD : M.Coindep D') :
    e ∈ M.closure (P i \ D') := by
  have h := hP.subset_closure_diff_of_coindep (D := (D' \ D)) ?_ ?_ i hei
  · rw [delete_closure_eq_of_disjoint _ ((P.disjoint_delete _).mono_left diff_subset),
      diff_diff_right, (P.disjoint_delete _).inter_eq, union_empty, mem_diff] at h
    exact h.1
  · rw [delete_delete, union_diff_cancel hDD']
    exact IsMinor.refl
  rwa [(hD.subset hDD').delete_coindep_iff, and_iff_left disjoint_sdiff_left,
    diff_union_of_subset hDD']

lemma Faithful.mem_closure_of_deleteElem {e} (hP : P.Faithful (M ＼ {e})) (hei : e ∈ P i)
    (he : ¬ M.IsColoop e) : e ∈ M.closure (P i \ {e}) :=
  hP.mem_closure_of_delete (by rwa [coindep_def, indep_singleton, ← not_isLoop_iff]) hei

lemma Faithful.notMem_closure_of_contractElem {e} (hP : P.Faithful (M ／ {e})) (hei : e ∈ P i)
    (he : M.IsNonloop e) : e ∉ M.closure (P !i) := by
  rwa [faithful_contract_iff_of_subset (by rwa [singleton_subset_iff]), he.skew_right_iff] at hP

lemma Faithful.nullity_le (h : P.Faithful N) (i : Bool) :
    N.nullity (P i ∩ N.E) ≤ M.nullity (P i) := by
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := h.isMinor.exists_contract_indep_delete_coindep
  rw [delete_ground, contract_ground, nullity_delete _ (by grind), ← inter_diff_assoc,
    ← inter_diff_assoc, inter_eq_self_of_subset_left P.subset, diff_diff_comm]
  have h_eq := M.nullity_union_eq_nullity_contract_add_nullity C (P i \ D)
  rw [hC.nullity_eq, add_zero] at h_eq
  grw [← h_eq, ← diff_union_self, diff_diff_right, hCD.inter_eq, union_empty,
    Skew.nullity_union_eq _ (by grind), (hC.diff _).nullity_eq, zero_add,
    nullity_le_of_subset _ diff_subset]
  exact (h.skew_of_contract hC.subset_ground (delete_isMinor ..) i).symm.mono_right diff_subset

lemma Faithful.indep_of_indep (hPN : P.Faithful N) (h : M.Indep (P i)) :
    N.Indep (P i ∩ N.E) := by
  grw [← nullity_eq_zero, ← nonpos_iff_eq_zero, hPN.nullity_le, h.nullity_eq]

lemma Faithful.coindep_of_coindep (hPN : P.Faithful N) (h : M.Coindep (P i)) :
    N.Coindep (P i ∩ N.E) := by
  simpa using hPN.dual.indep_of_indep (i := i) (by simpa)

lemma Faithful.spanning_of_spanning (hPN : P.Faithful N) (h : M.Spanning (P i)) :
    N.Spanning (P i ∩ N.E) := by
  rw [spanning_iff_compl_coindep, diff_inter_self_eq_diff,
    P.diff_eq_inter_bool _ hPN.isMinor.subset, Set.inter_comm]
  exact hPN.coindep_of_coindep <| P.compl_eq _ ▸ h.compl_coindep

lemma faithful_iff_of_delete (P : (M ＼ D).Separation) (hD : D ⊆ M.E) (i : Bool) :
    (P.induce M i).Faithful (M ＼ D) ↔ M✶.Skew (P !i) (D \ P !i) := by
  rw [faithful_delete_iff hD]
  have hss {j} : P j ∪ D ⊆ M✶.E := union_subset (P.subset.trans diff_subset) hD
  cases i <;> simp [P.induce_apply_of_delete_eq_cond, ← diff_diff, skew_empty hss]


  -- cases i <;> simp [ofDelete, inter_eq_self_of_subset_right hD, ← diff_diff, skew_empty hss]
set_option backward.isDefEq.respectTransparency false in
lemma faithful_iff_of_contract (P : (M ／ C).Separation) (hC : C ⊆ M.E) (i : Bool) :
    (P.induce M i).Faithful (M ／ C) ↔ M.Skew (P !i) (C \ P !i) := by
  convert (P.induce (M✶ ＼ C) i).faithful_iff_of_delete hC i using 1
  · rw [← faithful_dual_iff', dual_contract, induce_induce_dual,
      induce_induce_of_subset _ (by simp)]
  rw [dual_dual, induce_apply_not, show (M✶ ＼ C).E = (M ／ C).E by simp, P.inter_ground_left]

set_option backward.isDefEq.respectTransparency false in
lemma faithful_iff_of_remove {b} (P : (M.remove b X).Separation) (hX : X ⊆ M.E) (i : Bool) :
    (P.induce M i).Faithful (M.remove b X) ↔ (M.bDual (!b)).Skew (P !i) (X \ P !i) := by
  cases b
  · simp [P.faithful_iff_of_delete hX]
  simp [P.faithful_iff_of_contract hX]

lemma faithful_of_subset_closure_of_remove {b} (P : (M.remove b X).Separation)
    (hX : X ⊆ (M.bDual b).closure (P i)) : (P.induce M i).Faithful (M.remove b X) := by
  have hXE : X ⊆ M.E := by simpa using hX.trans ((M.bDual b).closure_subset_ground (P i))
  refine faithful_remove_of_subset_closure (X := X) (i := i) ?_ ?_
  · grw [induce_apply_of_remove_self, ← subset_union_right]
  rwa [induce_apply_of_remove_self, union_diff_cancel_right]
  grw [P.subset]
  simp

lemma faithful_of_subset_closure_of_delete (P : (M ＼ D).Separation) (hD : D ⊆ M.closure (P i)) :
    (P.induce M i).Faithful (M ＼ D) :=
  faithful_of_subset_closure_of_remove (b := false) P hD

lemma faithful_of_subset_closure_dual_of_contract (P : (M ／ C).Separation)
    (hC : C ⊆ M✶.closure (P i)) : (P.induce M i).Faithful (M ／ C) :=
  faithful_of_subset_closure_of_remove (b := true) P hC

lemma faithful_iff_of_coindep_of_delete (P : (M ＼ D).Separation) (hD : M.Coindep D) (i : Bool) :
    (P.induce M i).Faithful (M ＼ D) ↔ D ⊆ M.closure (P i) := by
  rw [faithful_delete_iff_forall_subset_closure hD, Bool.forall_bool' i,
    induce_apply_of_delete_self, union_diff_cancel_right (P.disjoint_delete _).inter_eq.subset,
    inter_eq_self_of_subset_right subset_union_right, induce_apply_not,
    P.apply_inter_ground_of_delete, (P.disjoint_delete _).inter_eq, and_iff_left (empty_subset ..)]

lemma Faithful.eConn_eq_of_remove {b} {P : (M.remove b X).Separation}
    (h : (P.induce M i).Faithful (M.remove b X)) : (P.induce M i).eConn = P.eConn := by
  simpa using h.eConn_induce_eq.symm

lemma Faithful.eConn_eq_of_delete {P : (M ＼ D).Separation}
    (h : (P.induce M i).Faithful (M ＼ D)) : (P.induce M i).eConn = P.eConn :=
  h.eConn_eq_of_remove (b := false)

lemma Faithful.eConn_eq_of_contract {P : (M ／ C).Separation}
    (h : (P.induce M i).Faithful (M ／ C)) : (P.induce M i).eConn = P.eConn :=
  h.eConn_eq_of_remove (b := true)

end Faithful

end Separation


@[mk_iff]
structure TutteDegen (M : Matroid α) (X : Set α) : Prop where
  indep : M.Indep X
  coindep : M.Coindep X

lemma tutteDegen_eq : TutteDegen (α := α) = fun M X ↦ M.Indep X ∧ M.Coindep X := by
  ext M X
  rw [M.tutteDegen_iff]

@[simp]
lemma tutteDegen_dual : M✶.TutteDegen X ↔ M.TutteDegen X := by
  simp [tutteDegen_iff,_root_.and_comm]

@[simp]
lemma tutteDegen_empty (M : Matroid α) : M.TutteDegen ∅ := by
  simp [tutteDegen_iff]

lemma TutteDegen.antitone : Antitone M.TutteDegen :=
  fun _ _ hYX h ↦ ⟨h.indep.subset hYX, h.coindep.subset hYX⟩

lemma TutteDegen.subset (h : M.TutteDegen X) (hYX : Y ⊆ X) : M.TutteDegen Y :=
  h.antitone hYX

alias ⟨_, TutteDegen.dual⟩ := tutteDegen_dual

/-- The sum of the nullity and conullity of a set in `M`.
Also the difference between the cardinality and the connectivity; see `eConn_add_tutteWeight_eq`. -/
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

@[simp]
lemma tutteWeight_eq_zero : M.tutteWeight X = 0 ↔ M.TutteDegen X := by
  simp [tutteWeight_def, tutteDegen_iff]

/-- A notion of degeneracy `IsLawfulDG` if, for each separation `P` of a matroid `M`,
and each minor `N` of `M` that is faithful to `P`,
Each degenerate side of `P` induces a degenerate side of the corresponding separation of `N`.
Examples include being spanning and being independent, or having bounded tutte-weight. -/
def IsLawfulDG (dg : Matroid α → Set α → Prop) : Prop := ∀ ⦃N M : Matroid α⦄
    ⦃P : M.Separation⦄, P.Faithful N → ∀ i, dg M (P i) → dg N (P i ∩ N.E)

@[simp]
lemma isLawfulDG_indep : IsLawfulDG (α := α) Matroid.Indep :=
  fun _ _ _ hPN _ ↦ hPN.indep_of_indep

@[simp]
lemma isLawfulDG_spanning : IsLawfulDG (α := α) Matroid.Spanning :=
  fun _ _ _ hPN _ ↦ hPN.spanning_of_spanning

@[simp]
lemma isLawfulDG_tutteDegen : IsLawfulDG (α := α) Matroid.TutteDegen :=
  fun _ _ _ hPN _ h ↦ ⟨hPN.indep_of_indep h.1, hPN.coindep_of_coindep h.2⟩

lemma IsLawfulDG.dual {dg} (h : IsLawfulDG (α := α) dg) : IsLawfulDG fun M X ↦ dg M✶ X :=
  fun M N P hP i hdg ↦ by simpa using h hP.dual i (by simpa)

lemma IsLawfulDG.compl {dg} (h : IsLawfulDG (α := α) dg) : IsLawfulDG fun M X ↦ dg M (M.E \ X) := by
  refine fun N M P hP i hi ↦ ?_
  simp only [Separation.compl_eq] at hi
  have hwin := h hP.symm i (by simpa using hi)
  rwa [diff_inter_self_eq_diff, P.diff_eq_inter_bool _ hP.isMinor.subset, inter_comm]

lemma Separation.Faithful.remove_of_isLawfulDG {dg b} (h : P.Faithful (M.remove b X))
    (hdg : IsLawfulDG dg) (hi : dg M (P i)) : dg (M.remove b X) (P i \ X) := by
  convert hdg h i hi using 1
  rw [remove_ground, ← inter_diff_assoc, P.inter_ground_eq]

lemma Separation.Faithful.delete_of_isLawfulDG {dg} (h : P.Faithful (M ＼ D)) (hdg : IsLawfulDG dg)
    (hi : dg M (P i)) : dg (M ＼ D) (P i \ D) :=
  h.remove_of_isLawfulDG (b := false) hdg hi

lemma Separation.Faithful.contract_of_isLawfulDG {dg} (h : P.Faithful (M ／ C)) (hdg : IsLawfulDG dg)
    (hi : dg M (P i)) : dg (M ／ C) (P i \ C) :=
  h.remove_of_isLawfulDG (b := true) hdg hi

/-- An `ℕ∞`-valued matroid parameter on sets `IsFaithfulMono` if, when applied to one side of a
separation `P`, its value does not increase when taking a minor that is faithful to `P`.
This is the numerical version of `IsLawfulDG`;
examples include rank, corank, nullity and tutte weight.  -/
def IsFaithfulMono (w : Matroid α → Set α → ℕ∞) : Prop := ∀ ⦃M N : Matroid α⦄ ⦃P : M.Separation⦄
    (i : Bool), P.Faithful N → w N (P i ∩ N.E) ≤ w M (P i)

lemma IsFaithfulMono.add {w w' : Matroid α → Set α → ℕ∞} (hw : IsFaithfulMono w)
    (hw' : IsFaithfulMono w') : IsFaithfulMono (fun M X ↦ w M X + w' M X) :=
  fun _ _ _ i h ↦ add_le_add (hw i h) (hw' i h)

lemma IsFaithfulMono.dual {w} (hw : IsFaithfulMono (α := α) w) :
    IsFaithfulMono (fun M X ↦ w M✶ X) :=
  fun M N P i h ↦ by simpa using hw i h.dual

lemma IsFaithfulMono.le_of_delete {w} (h : IsFaithfulMono w) (hP : P.Faithful (M ＼ D))
    (i : Bool) : w (M ＼ D) (P i \ D) ≤ w M (P i) := by
  grw [← h i hP, delete_ground, ← inter_diff_assoc, P.inter_ground_eq]

lemma IsFaithfulMono.le_of_contract {w} (h : IsFaithfulMono w) (hP : P.Faithful (M ／ C))
    (i : Bool) : w (M ／ C) (P i \ C) ≤ w M (P i) := by
  grw [← h i hP, contract_ground, ← inter_diff_assoc, P.inter_ground_eq]

lemma isFaithfulMono_nullity : IsFaithfulMono (α := α) Matroid.nullity :=
  fun _ _ _ i h ↦ h.nullity_le i

lemma isFaithfulMono_tutteWeight : IsFaithfulMono (α := α) Matroid.tutteWeight :=
  isFaithfulMono_nullity.add isFaithfulMono_nullity.dual

lemma IsFaithfulMono.isLawfulDG {w} (h : IsFaithfulMono (α := α) w) {t : ℕ∞ → ℕ∞} :
    IsLawfulDG fun M X ↦ w M X ≤ t (M.eConn X) := by
  intro N M P hP i hle
  grw [h i hP, hle, P.eConn_eq, ← hP.eConn_induce_eq, ← Separation.eConn_eq _ i,
    Separation.induce_apply_subset _ hP.isMinor.subset]

end Matroid
