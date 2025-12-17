import Matroid.Connectivity.Vertical

variable {α : Type*} {M : Matroid α} {j k : ℕ∞} {d k : ℕ∞} {A X Y : Set α} {P : M.Separation}
  {b : Bool}

open Set Matroid Matroid.Separation Function

namespace Matroid.Separation

/-- An internal separation is the type of separation required by internal connectivity.
For finite connectivity, is it equivalent to both sides of the separation having cardinality
exceeding the connectivity by at least two. -/
def IsInternalSeparation (P : M.Separation) :=
    P.IsPredSeparation (fun _ M X ↦ M.nullity X + M✶.nullity X ≤ 1)

lemma isInternalSeparation_iff : P.IsInternalSeparation ↔
    ∀ b, 1 < M.nullity (P b) + M✶.nullity (P b) := by
  simp [IsInternalSeparation, IsPredSeparation]

lemma IsStrongSeparation.isInternalSeparation (h : P.IsStrongSeparation) :
    P.IsInternalSeparation := by
  refine IsPredSeparation.mono (fun N X hX hle ↦ ?_) h
  rw [← nullity_eq_zero, coindep_def, ← nullity_eq_zero]
  enat_to_nat!; omega

lemma isInternalSeparation_iff_encard (hP : P.eConn ≠ ⊤) :
    P.IsInternalSeparation ↔ ∀ b, P.eConn + 1 < (P b).encard := by
  convert isInternalSeparation_iff using 2 with b
  rw [← M.eConn_add_nullity_add_nullity_dual (P b), P.eConn_eq, add_assoc,
    ENat.add_lt_add_iff_left hP]

lemma IsInternalSeparation.isTutteSeparation (h : P.IsInternalSeparation) :
    P.IsTutteSeparation := by
  rw [isTutteSeparation_iff_nullity]
  rw [isInternalSeparation_iff] at h
  exact fun b ↦ (h b).le

lemma IsInternalSeparation.exists_encard_eq_of_not_isTutteSeparation (h : P.IsInternalSeparation)
    (h_not : ¬ P.IsTutteSeparation) : ∃ b, (P b).encard = P.eConn + 1 := by
  obtain htop | hne := eq_or_ne P.eConn ⊤
  · refine ⟨true, ?_⟩
    rw [← M.eConn_add_nullity_add_nullity_dual (P true), P.eConn_eq]
    simp [htop]
  simp [isTutteSeparation_iff_lt_encard hne] at h_not
  rw [isInternalSeparation_iff_encard hne] at h
  grw [← h_not (le_self_add.trans_lt (h _))] at h
  exact ((h _).not_ge le_self_add).elim

lemma IsInternalSeparation.encard_ge (hP : P.IsInternalSeparation) (b : Bool) :
    P.eConn + 1 + 1 ≤ (P b).encard := by
  grw [← M.eConn_add_nullity_add_nullity_dual (P b), P.eConn_eq]
  rw [isInternalSeparation_iff] at hP
  grw [add_assoc _ (nullity ..), ← Order.add_one_le_of_lt (hP b), add_assoc]

lemma IsInternalSeparation.symm (hP : P.IsInternalSeparation) : P.symm.IsInternalSeparation :=
  IsPredSeparation.symm hP

lemma IsInternalSeparation.of_symm (hP : P.symm.IsInternalSeparation) : P.IsInternalSeparation :=
  IsPredSeparation.of_symm hP

lemma IsInternalSeparation.dual (hP : P.IsInternalSeparation) : P.dual.IsInternalSeparation :=
  IsPredSeparation.dual (by simp +contextual [add_comm]) hP

lemma IsInternalSeparation.of_dual (hP : P.dual.IsInternalSeparation) : P.IsInternalSeparation :=
  IsPredSeparation.of_dual (by simp +contextual [add_comm]) hP

@[simp]
lemma isInternalSeparation_dual_iff : P.dual.IsInternalSeparation ↔ P.IsInternalSeparation :=
  ⟨IsInternalSeparation.of_dual, IsInternalSeparation.dual⟩

@[simp]
lemma isInternalSeparation_symm_iff : P.symm.IsInternalSeparation ↔ P.IsInternalSeparation :=
  ⟨IsInternalSeparation.of_symm, IsInternalSeparation.symm⟩

end Separation

/-! ### Internal and Weak Connectivity -/

/-- A weakly `(k+1)`-connected matroid is one with no strong separation of order less than `k`.
Weak `3`-connectedness is `3`-connectedness up to series/parallel pairs (TODO).  -/
def WeaklyConnected (M : Matroid α) := M.NumConnected (fun M X ↦ M.Indep X ∨ M.Coindep X)

lemma weaklyConnected_iff_forall : M.WeaklyConnected (k + 1) ↔
    ∀ (P : M.Separation), P.eConn + 1 ≤ k → ¬ P.IsStrongSeparation := by
  simp [WeaklyConnected, numConnected_iff_forall]

@[simp]
lemma weaklyConnected_zero (M : Matroid α) : M.WeaklyConnected 0 := by
  simp [WeaklyConnected]

@[simp]
lemma weaklyConnected_one (M : Matroid α) : M.WeaklyConnected 1 := by
  simp [WeaklyConnected]

lemma WeaklyConnected.mono (h : M.WeaklyConnected k) (hjk : j ≤ k) : M.WeaklyConnected j :=
  NumConnected.mono h hjk

lemma weaklyConnected_dual_iff : M✶.WeaklyConnected k ↔ M.WeaklyConnected k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  simp only [weaklyConnected_iff_forall]
  exact ⟨fun h P hP hP' ↦ h P.dual (by simpa) (by simpa),
    fun h P hP hP' ↦ h P.ofDual (by simpa) (by simpa)⟩

alias ⟨WeaklyConnected.of_dual, WeaklyConnected.dual⟩ := weaklyConnected_dual_iff

lemma CyclicallyConnected.weaklyConnected (h : M.CyclicallyConnected k) : M.WeaklyConnected k :=
  NumConnected.mono_degen h fun _ _ ↦ Or.inl

lemma VerticallyConnected.weaklyConnected (h : M.VerticallyConnected k) : M.WeaklyConnected k :=
  NumConnected.mono_degen h fun _ _ ↦ Or.inr

lemma TutteConnected.weaklyConnected (h : M.TutteConnected k) : M.WeaklyConnected k :=
  h.verticallyConnected.weaklyConnected

lemma WeaklyConnected.not_isStrongSeparation (h : M.WeaklyConnected (k + 1))
    (hPconn : P.eConn + 1 ≤ k) : ¬ P.IsStrongSeparation :=
  h.not_isPredSeparation hPconn

/-- A weakly 2-connected matroid having both a loop and a coloop is structurally trivial. -/
lemma WeaklyConnected.eq_uniqueBaseOn_of_isLoop_isColoop {e f : α} (hM : M.WeaklyConnected 2)
    (he : M.IsLoop e) (hf : M.IsColoop f) :
    ∃ E, e ∈ E ∧ f ∈ E ∧ (M = uniqueBaseOn {f} E ∨ M = uniqueBaseOn (E \ {e}) E) := by
  rw [← one_add_one_eq_two] at hM
  replace hM := hM.not_isStrongSeparation (P := M.ofSetSep {e,f} true)
  have heE := he.mem_ground
  have hfE := hf.mem_ground
  have hefD : M.Dep {e, f} := he.dep_of_mem (by simp)
  have hefcD : M.Codep {e, f} := hf.dep_of_mem (by simp)
  have hefconn : M.eConn {e,f} = 0 := eConn_of_subset_loops_union_coloops
    (by simp [pair_subset_iff, show e ∈ M.loops from he, show f ∈ M.coloops from hf])
  replace hM : M.Dep (M.E \ {e, f}) → M.Coindep (M.E \ {e, f}) := by
    simpa [isStrongSeparation_iff, hefD, hefcD, hefconn] using hM
  obtain h1 | h2 := M.indep_or_dep (X := M.E \ {e,f})
  · refine ⟨M.E, heE, hfE, .inr <| ext_indep rfl fun I hIE ↦ ?_⟩
    simp +contextual only [uniqueBaseOn_indep_iff', subset_inter_iff, subset_diff_singleton_iff,
      and_right_comm, and_self, iff_def, Indep.subset_ground, true_and, and_imp]
    refine ⟨fun hI heI ↦ (he.not_indep_of_mem heI) hI, fun hIE heI ↦ ?_⟩
    rw [← diff_indep_iff_indep_of_subset_coloops (K := {f}) (by simpa)]
    exact h1.subset <| by simp [subset_diff, heI, hIE.trans <| subset_insert ..]
  refine ⟨M.E, heE, hfE, .inl <| ext_indep rfl fun I hI ↦ ?_⟩
  rw [uniqueBaseOn_indep_iff (by simpa)]
  specialize hM h2
  refine ⟨fun h x hxI ↦ ?_, fun h ↦ hf.isNonloop.indep.subset h⟩
  rw [← spanning_iff_compl_coindep, spanning_iff, pair_comm,
    closure_insert_congr_right he.closure, insert_empty_eq, closure_eq_of_subset_coloops
    (by simpa), singleton_union] at hM
  have hx := hM.1 ▸ (h.subset_ground hxI)
  rwa [mem_insert_iff, ← isLoop_iff, or_iff_left (h.isNonloop_of_mem hxI).not_isLoop] at hx

lemma WeaklyConnected.subsingleton_loops_or_coloops (h : M.WeaklyConnected 2) :
    M.loops.Subsingleton ∨ M.coloops.Subsingleton := by
  by_contra! hcon
  obtain ⟨e, he⟩ := hcon.1.nonempty
  obtain ⟨f, hf⟩ := hcon.2.nonempty
  obtain ⟨E, heE, hfE, rfl | rfl⟩ := h.eq_uniqueBaseOn_of_isLoop_isColoop he hf
  · simp [uniqueBaseOn_coloops_eq', ← not_subsingleton_iff,
      subsingleton_singleton.anti inter_subset_left] at hcon
  simp [uniqueBaseOn_loops_eq, ← not_subsingleton_iff,
      subsingleton_singleton.anti inter_subset_right] at hcon

lemma weaklyConnected_uniqueBaseOn_iff {B E : Set α} (hBE : B ⊆ E) (hk : k ≠ 0) :
    (uniqueBaseOn B E).WeaklyConnected (k + 1) ↔ B.Subsingleton ∨ (E \ B).Subsingleton := by
  wlog hwlog : (E \ B).Subsingleton → B.Subsingleton generalizing B with aux
  · simp only [Classical.not_imp, not_subsingleton_iff] at hwlog
    specialize aux (B := E \ B) diff_subset
    rw [diff_diff_cancel_left hBE, ← uniqueBaseOn_dual_eq, weaklyConnected_dual_iff, or_comm] at aux
    exact aux fun _ ↦ hwlog.1
  refine ⟨fun h ↦ ?_, ?_⟩
  · simpa [inter_eq_self_of_subset_left hBE, uniqueBaseOn_loops_eq] using
      (h.mono (show 2 ≤ k + 1 by eomega)).subsingleton_loops_or_coloops.symm
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp at hk
  have aux (P : (uniqueBaseOn B E).Separation) (b : Bool) : P b ⊆ E := P.subset_ground
  simp +contextual only [weaklyConnected_iff_forall, ENat.add_le_add_right_iff, ENat.one_ne_top,
    or_false, isStrongSeparation_iff, uniqueBaseOn_dep_iff, ← dep_dual_iff, uniqueBaseOn_dual_eq,
    not_and, Bool.forall_bool, and_imp, not_true_eq_false, imp_false, not_not, forall_const, aux]
  rw [or_iff_left_of_imp hwlog]
  rintro hB P hPconn hPne h1 h2 h3 h4
  rw [subset_diff, hB.disjoint_iff_right, and_iff_right (aux ..)] at ⊢ h4
  simp only [Classical.not_imp] at h4
  intro h5
  grw [← subset_empty_iff, subset_inter h4.1 h5, P.disjoint_false_true.inter_eq]

lemma TutteConnected.weaklyConnected_add_one_iff (h : M.TutteConnected (k + 1)) :
    M.WeaklyConnected (k + 1 + 1) ↔ ∀ (P : M.Separation), P.eConn = k → ¬ P.IsStrongSeparation := by
  simp only [weaklyConnected_iff_forall, ENat.add_le_add_right_iff, ENat.one_ne_top, or_false]
  refine ⟨fun h' P hPconn ↦ h' P hPconn.le, fun h' P hPconn hP ↦ h' P ?_ hP⟩
  obtain rfl | hlt := hPconn.eq_or_lt
  · rfl
  exact False.elim <| h.not_isTutteSeparation (Order.add_one_le_of_lt hlt) hP.isTutteSeparation

lemma TutteConnected.weaklyConnected_of_delete_of_subset_loops {D : Set α}
    (h : (M ＼ D).TutteConnected 2) (hD : D ⊆ M.loops) : M.WeaklyConnected 2 := by
  rw [show (2 : ℕ∞) = 1 + 1 from rfl] at *
  simp only [weaklyConnected_iff_forall, ENat.add_le_right_iff, ENat.one_ne_top, or_false]
  intro P hP0 hP
  refine h.not_isTutteSeparation (P := P.delete D) (by grw [P.eConn_delete_le, hP0, zero_add]) ?_
  simp only [isTutteSeparation_iff_forall, delete_apply, delete_dep_iff, disjoint_sdiff_left,
    and_true, ← dep_dual_iff, dual_delete]
  rw [isStrongSeparation_iff] at hP
  refine fun b ↦ .inr <| (hP.2 b).contract_of_indep (I := D)
    (M✶.coloops_indep.subset (by grw [dual_coloops, inter_subset_right, hD]))

/-- A matroid is weakly 2-connected if and only if it is 2-connected after removing the
loops or coloops. -/
lemma weaklyConnected_two_iff :
    M.WeaklyConnected 2 ↔ M.removeLoops.TutteConnected 2 ∨ M.removeColoops.TutteConnected 2 := by
  rw [← one_add_one_eq_two, iff_comm]
  refine ⟨fun h ↦ h.elim (fun h' ↦ ?_) (fun h' ↦ ?_), fun h ↦ ?_⟩
  · rw [removeLoops_eq_delete] at h'
    exact TutteConnected.weaklyConnected_of_delete_of_subset_loops h' rfl.subset
  · rw [← tutteConnected_dual_iff, removeColoops_dual, removeLoops_eq_delete] at h'
    exact (h'.weaklyConnected_of_delete_of_subset_loops rfl.subset).of_dual
  wlog hlps : M.loops.Nonempty → M.coloops.Nonempty generalizing M with aux
  · rw [← tutteConnected_dual_iff, removeLoops_dual, or_comm, ← tutteConnected_dual_iff,
      removeColoops_dual]
    exact aux h.dual (by simp [Classical.not_imp.1 hlps])
  obtain hLe | hLne := M.loops.eq_empty_or_nonempty
  · right
    simp only [removeColoops_eq_delete, tutteConnected_iff_forall, ENat.add_le_right_iff,
      ENat.one_ne_top, or_false]
    rintro P hP0 hP
    refine h.not_isStrongSeparation (P := P.ofDelete true) ?_ ?_
    · simpa [eConn_ofDelete, ← dual_loops, loops]
    simp only [isStrongSeparation_iff, ofDelete_apply _ M.coloops_subset_ground, beq_true,
      Bool.forall_bool, cond_false, cond_true, union_coloops_dep_iff]
    obtain hs | h0 := (isTutteSeparation_iff_isStrongSeparation_of_zero hP0).1 hP
    · refine ⟨⟨(hs.dep false).of_delete, (hs.dep true).of_delete⟩, ?_, (hs.codep true).of_delete⟩
      have h' := hs.codep false
      simp_rw [← removeColoops_eq_delete, removeColoops_eq_contract] at h'
      exact h'.of_contract
    simp only [nonempty_iff_ne_empty, ne_eq, ← removeColoops_eq_delete, removeColoops_loops_eq, hLe,
      subset_empty_iff, removeColoops_coloops, or_self] at h0
    tauto
  obtain ⟨f, hf : M.IsColoop f⟩ := hlps hLne
  obtain ⟨e, he : M.IsLoop e⟩ := hLne
  obtain ⟨E, heE, hfE, rfl | rfl⟩ := h.eq_uniqueBaseOn_of_isLoop_isColoop he hf
  · refine .inl <| tutteConnected_of_subsingleton ?_ _
    simp [removeLoops_eq_delete, uniqueBaseOn_loops_eq,
      subsingleton_singleton.anti inter_subset_right]
  refine .inr <| tutteConnected_of_subsingleton ?_ _
  simp [removeColoops_eq_delete, subsingleton_singleton.anti inter_subset_right]


-- /-- This lemma is most relevant when `k = 1`; it means that a connected matroid is weakly
-- three-connected if and only if it is three-connected up to simplification and cosimplification.
-- lemma TutteConnected.weaklyConnected_add_one_iff (h : M.TutteConnected (k + 1)) :
--     M.WeaklyConnected (k + 1 + 1) ↔ ∀ (P : M.Separation), P.eConn = k → M.eRk P.left = k ∨
--         M.eRk P.right = k ∨ M✶.eRk P.left = k ∨ M✶.eRk P.right = k := by
--   obtain rfl | hne := eq_or_ne k ⊤
--   · simp_rw [top_add, ← top_le_iff]
--     refine iff_of_true h.weaklyConnected fun P hP ↦ ?_
--     by_contra! hcon
--     grw [← eConn_le_eRk, P.eConn_left] at hcon
--     exact hP.not_gt hcon.1
--   simp only [weaklyConnected_iff_forall, ENat.add_le_add_right_iff, ENat.one_ne_top, or_false]
--   refine ⟨fun h' ↦ ?_, fun h' P hPconn hP ↦ ?_⟩
--   · rintro P rfl
--     specialize h' P rfl.le
--     simp only [isStrongSeparation_iff_eRk hne, not_and, not_lt] at h'
--     nth_rw 1 [← P.eConn_left, ← P.eConn_right, ← P.eConn_left, ← P.eConn_right]
--     simp only [le_antisymm_iff, eConn_le_eRk .., eConn_le_eRk_dual, and_true]
--     simp only [eConn_left, eConn_right]
--     grind
--   obtain hlt | rfl := hPconn.lt_or_eq
--   · exact h.not_isTutteSeparation (P := P) (Order.add_one_le_of_lt hlt) hP.isTutteSeparation
--   rw [isStrongSeparation_iff_eRk (by eomega)] at hP
--   grind

-- lemma TutteConnected.exists_of_not_weaklyConnected_add_one (h : M.TutteConnected (k + 1))
--     (h' : ¬ M.WeaklyConnected (k + 1 + 1)) :
--     ∃ (P : M.Separation), P.eConn = k ∧ k < M.eRk P.left ∧ k < M.eRk P.right ∧
--       k < M✶.eRk P.left ∧ k < M✶.eRk P.right := by
--   simp only [h.weaklyConnected_add_one_iff, not_forall, exists_prop, not_or] at h'
--   obtain ⟨P, rfl, h1, h2, h3, h4⟩ := h'
--   refine ⟨P, rfl, lt_of_le_of_ne' ?_ h1, lt_of_le_of_ne' ?_ h2, lt_of_le_of_ne' ?_ h3,
--   lt_of_le_of_ne' ?_ h4⟩
--   · grw [← P.eConn_left, eConn_le_eRk]
--   · grw [← P.eConn_right, eConn_le_eRk]
--   · grw [← P.eConn_left, eConn_le_eRk_dual]
--   grw [← P.eConn_right, eConn_le_eRk_dual]

/-- A matroid is weakly internally `(k+1)` connected if all separations of order at most `k-1`
are degenerate in the sense that one side is 'nearly' independent and coindependent.
Internal `(k+1)`-connectivity is the conjunction of weak internal `(k+1)`-connectivity and
Tutte `k`-connectivity. -/
def WeaklyInternallyConnected (M : Matroid α) :=
    M.NumConnected (fun M X ↦ M.nullity X + M✶.nullity X ≤ 1)

lemma weaklyInternallyConnected_iff_forall : M.WeaklyInternallyConnected (k + 1) ↔
    ∀ P : M.Separation, P.eConn + 1 ≤ k → ¬ P.IsInternalSeparation :=
  numConnected_iff_forall

lemma TutteConnected.weaklyInternallyConnected (h : M.TutteConnected k) :
    M.WeaklyInternallyConnected k :=
  NumConnected.mono_degen h <| by simp +contextual [← nullity_eq_zero]

lemma weaklyInternallyConnected_iff_numConnected_encard (hk : k ≠ ⊤) :
    M.WeaklyInternallyConnected k ↔ M.NumConnected (fun M X ↦ X.encard ≤ M.eConn X + 1) k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp [WeaklyInternallyConnected]
  simp only [weaklyInternallyConnected_iff_forall, numConnected_iff_forall, isPredSeparation_iff,
    eConn_eq, not_le]
  refine ⟨fun h P hPk hP ↦ h P hPk ?_, fun h P hPk hP ↦ h P hPk ?_⟩
  · rwa [isInternalSeparation_iff_encard (by enat_to_nat!)]
  rwa [← isInternalSeparation_iff_encard (by enat_to_nat!)]

/-- `M` is internally `(k+1)`-connected if it is weakly `(k+1)`-connected and `k`-Tutte-connected.-/
structure InternallyConnected (M : Matroid α) (k : ℕ∞) : Prop where
    weaklyInternallyConnected : M.WeaklyInternallyConnected k
    tutteConnected' : M.TutteConnected (k-1)

lemma InternallyConnected.tutteConnected (h : M.InternallyConnected (k+1)) :
    M.TutteConnected k := by
  have h' := h.2
  enat_to_nat <;> simpa using h'

lemma internallyConnected_iff' :
    M.InternallyConnected k ↔ M.NumConnected (fun M X ↦ M.nullity X + M✶.nullity X ≤ 1) k ∧
      M.TutteConnected (k-1) :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

lemma internallyConnected_iff :
    M.InternallyConnected (k + 1) ↔ M.WeaklyInternallyConnected (k + 1) ∧ M.TutteConnected k := by
  rw [internallyConnected_iff', ENat.add_sub_cancel_right _ (by simp)]
  rfl

@[simp]
lemma internallyConnected_zero (M : Matroid α) : M.InternallyConnected 0 := by
  simp [internallyConnected_iff']

@[simp]
lemma internallyConnected_one (M : Matroid α) : M.InternallyConnected 1 := by
  simp [internallyConnected_iff']

lemma internallyConnected_iff_forall : M.InternallyConnected (k + 1) ↔
    ∀ (P : M.Separation), (P.eConn + 1 + 1 ≤ k → ¬ P.IsTutteSeparation) ∧
      (P.eConn + 1 = k → ¬ P.IsInternalSeparation) := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  simp only [ENat.add_one_le_add_one_iff, ENat.add_one_inj, internallyConnected_iff,
    tutteConnected_iff_forall, weaklyInternallyConnected_iff_forall]
  refine ⟨fun h P ↦ ⟨fun hPc ↦ h.2 P hPc, fun hPc ↦ h.1 P hPc.le⟩,
    fun h ↦ ⟨fun P hP hPi ↦ ?_, fun P hP ↦ (h P).1 hP⟩⟩
  obtain rfl | hlt := hP.eq_or_lt
  · simpa [hPi] using h P
  exact (h P).1 (Order.add_one_le_of_lt hlt) hPi.isTutteSeparation

lemma InternallyConnected.not_isTutteSeparation (h : M.InternallyConnected (k + 1))
    (hP : P.eConn + 1 + 1 ≤ k) : ¬ P.IsTutteSeparation :=
  ((internallyConnected_iff_forall.1 h) P).1 hP

lemma InternallyConnected.not_isInternalSeparation (h : M.InternallyConnected (k + 1))
    (hP : P.eConn + 1 ≤ k) : ¬ P.IsInternalSeparation := by
  obtain hlt | rfl := hP.lt_or_eq
  · exact fun h' ↦ h.not_isTutteSeparation (Order.add_one_le_of_lt hlt) h'.isTutteSeparation
  rw [internallyConnected_iff_forall] at h
  exact (h P).2 rfl

lemma TutteConnected.internallyConnected (h : M.TutteConnected k) : M.InternallyConnected k :=
  ⟨h.weaklyInternallyConnected, h.mono tsub_le_self⟩

lemma TutteConnected.internallyConnected_iff_forall (h : M.TutteConnected k) :
    M.InternallyConnected (k + 1) ↔
    ∀ P : M.Separation, P.eConn + 1 = k → ¬ P.IsInternalSeparation := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  rw [tutteConnected_iff_forall] at h
  simp only [internallyConnected_iff_forall, ENat.add_one_le_add_one_iff, ENat.add_one_inj,
    forall_and, and_iff_right_iff_imp]
  exact fun _ ↦ h

lemma WeaklyConnected.weaklyConnected_of_isRestriction {N : Matroid α} (h : M.WeaklyConnected k)
    (hN : N ≤r M) (hNM : ∀ e, M.IsNonloop e → e ∉ N.E → ∃ f ∈ N.E, e ∈ M.closure {f}) :
    N.WeaklyConnected k := by
  obtain rfl | ⟨k,rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  obtain hNe | ⟨f₀, hf₀⟩ := N.E.eq_empty_or_nonempty
  · exact numConnected_of_subsingleton (by simp [hNe]) _ (by simp)
  replace hNM : ∀ e ∈ M.E, ∃ f ∈ N.E, e ∈ M.closure {f} ∧ (e ∈ N.E → e = f) := by
    intro e he
    by_cases heN : e ∈ N.E
    · exact ⟨e, heN, M.mem_closure_of_mem rfl, by simp⟩
    obtain he' | he' := M.isLoop_or_isNonloop e
    · exact ⟨f₀, hf₀, he'.mem_closure {f₀}, by simp [heN]⟩
    obtain ⟨f, hf, hef⟩ := hNM e he' heN
    exact ⟨f, hf, hef, by simp [heN]⟩
  choose! φ hφ using hNM
  rw [weaklyConnected_iff_forall] at *
  intro P hPk hP
  have hdj' : Pairwise (Disjoint on fun i ↦ φ ⁻¹' P i ∩ M.E) :=
    P.pairwise_disjoint.mono fun _ _ h ↦ (h.preimage _).mono inter_subset_left inter_subset_left
  have hu' : ⋃ i, φ ⁻¹' (P i) ∩ M.E = M.E := by
    rw [← iUnion_inter, ← preimage_iUnion, P.iUnion_eq, inter_eq_right]
    exact fun e he ↦ (hφ e he).1
  let Q := Matroid.Separation.mk (M := M) _ hdj' hu'
  have hPE {b} : P b ⊆ M.E := P.subset_ground.trans hN.subset
  have hssQ {b} : Q b ⊆ φ ⁻¹' (P b) := by simp [Q]
  have hclQ {b} : (Q b) ⊆ M.closure (P b) :=
    fun e ⟨he, heE⟩ ↦ M.closure_subset_closure (by simpa using he) (hφ e heE).2.1
  have hPS {b} : P b ⊆ Q b := by
    simp only [Separation.mk_apply, subset_inter_iff, Q]
    refine ⟨fun e he ↦ ?_, hPE⟩
    rwa [mem_preimage, ← (hφ e (hPE he)).2.2 (P.subset_ground he)]
  refine h Q ?_ ?_
  · grw [← hPk, Separation.eConn_eq_eLocalConn, eLocalConn_mono _ hclQ hclQ,
      eLocalConn_closure_closure, P.eConn_eq_eLocalConn, hN.eLocalConn_eq_of_subset]
  refine isStrongSeparation_iff'.2 ⟨fun b ↦ ?_, fun b ↦ ?_⟩
  · exact ((hP.dep b).of_isRestriction hN).superset hPS
  exact ((hP.isVerticalSeparation.nonspanning b).of_isRestriction hN).closure_nonspanning.subset
    hclQ

lemma WeaklyConnected.delete_of_forall_exists_parallel (h : M.WeaklyConnected k)
    {D : Set α} (hD : ∀ e ∈ D, M.IsNonloop e → ∃ f ∉ D, M.Parallel e f) :
    (M ＼ D).WeaklyConnected k := by
  by_cases hDE : M.E ⊆ D
  · exact numConnected_of_subsingleton (by simp [diff_eq_empty.2 hDE]) _ (by simp)
  obtain ⟨f', hf'⟩ := not_subset.1 hDE
  refine h.weaklyConnected_of_isRestriction (delete_isRestriction ..) fun e henl heD ↦ ?_
  replace heD := show e ∈ D by simpa [henl.mem_ground] using heD
  obtain ⟨f, hf⟩ := hD e heD henl
  exact ⟨f, ⟨hf.2.mem_ground_right, hf.1⟩, hf.2.mem_closure⟩

lemma WeaklyConnected.delete_weaklyConnected_of_parallel {e f : α} (h : M.WeaklyConnected k)
    (hef : M.Parallel e f) (hne : e ≠ f) : (M ＼ {e}).WeaklyConnected k :=
  h.delete_of_forall_exists_parallel <| by grind

lemma WeaklyConnected.weaklyConnected_of_isSimplification {N : Matroid α} (h : M.WeaklyConnected k)
    (hN : N.IsSimplification M) : N.WeaklyConnected k := by
  refine h.weaklyConnected_of_isRestriction hN.isRestriction fun e henl _ ↦ ?_
  obtain ⟨f, hf, -⟩ := hN.exists_unique henl
  exact ⟨f, hf.1, hf.2.mem_closure⟩

end Matroid
