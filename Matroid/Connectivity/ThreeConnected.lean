import Matroid.Connectivity.Infinite
import Matroid.ForMathlib.Data.Set.Subsingleton
import Matroid.ForMathlib.GCongr

open Set Matroid.Partition

namespace Matroid

section separation

variable {α : Type*} {N M : Matroid α} {j k : ℕ∞} {a b e f : α} {A B X Y : Set α}

-- abbrev ThreeConnected (M : Matroid α) := M.IsTutteConnected 3

-- abbrev InternallyThreeConnected (M : Matroid α) := M.IsInternallyConnected 3


section Minor

lemma VerticallyConnected.contract {C : Set α} (h : M.VerticallyConnected (k + M.eRk C)) :
    (M ／ C).VerticallyConnected k := by
  wlog hCE : C ⊆ M.E generalizing C with aux
  · rw [← M.contract_inter_ground_eq]
    exact aux (h.mono (by grw [eRk_mono _ inter_subset_left])) inter_subset_right
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  rw [add_right_comm] at h
  refine verticallyConnected_iff_forall.2 fun P hPconn hP ↦ ?_
  have hl := h.not_isVerticalSeparation (P := P.ofContractLeft)
    (by grw [ENat.add_one_le_add_one_iff, eConn_ofContractLeft, eLocalConn_le_eRk_right,
    add_right_comm, hPconn])
  rw [isVerticalSeparation_iff_nonspanning, ofContractLeft_left, ofContractLeft_right] at hl
  rw [isVerticalSeparation_iff_nonspanning, contract_nonspanning_iff,
    contract_nonspanning_iff] at hP
  simp [hP.1.1, hP.2.1.subset subset_union_left] at hl

lemma VerticallyConnected.contract_of_top (h : M.VerticallyConnected ⊤) (C : Set α) :
    (M ／ C).VerticallyConnected ⊤ :=
  (h.mono le_top).contract

lemma TutteConnected.contract {C : Set α} (h : M.TutteConnected (k + M.eRk C + 1))
    (hnt : 2 * (k + M.eRk C) < M.E.encard + 1) : (M ／ C).TutteConnected (k + 1) := by
  obtain rfl | hne := eq_or_ne k 0; simp
  wlog hCE : C ⊆ M.E generalizing C with aux
  · specialize aux (C := C ∩ M.E)
    grw [M.eRk_mono inter_subset_left, imp_iff_right inter_subset_right,
      contract_inter_ground_eq] at aux
    exact aux h hnt
  have hnt' := Order.le_of_lt_add_one hnt
  have hgirth := h.le_girth hnt'
  have hC : M.Indep C := indep_of_eRk_add_one_lt_girth (by enat_to_nat! <;> omega) hCE
  have hfin : C.Finite := not_infinite.1 fun hinf ↦ by
    simp [hC.eRk_eq_encard, hinf.encard_eq] at hnt
  rw [tutteConnected_iff_verticallyConnected_girth]
  refine ⟨(h.verticallyConnected.mono ?_).contract, ?_⟩
  · grw [add_right_comm]
  · have hle := hgirth.trans (M.girth_le_girth_contract_add C)
    · rwa [add_right_comm, WithTop.add_le_add_iff_right
        (M.isRkFinite_of_finite hfin).eRk_lt_top.ne] at hle
  grw [hC.eRk_eq_encard, ← encard_diff_add_encard_of_subset hCE, ← contract_ground] at hnt
  enat_to_nat! <;> omega

lemma TutteConnected.delete {D : Set α} (h : M.TutteConnected (k + M✶.eRk D + 1))
    (hnt : 2 * (k + M✶.eRk D) < M.E.encard + 1) : (M ＼ D).TutteConnected (k + 1) :=
  dual_contract_dual .. ▸ (h.dual.contract (by simpa)).dual

lemma TutteConnected.contractElem (h : M.TutteConnected (k+1)) (hnt : 2 * k < M.E.encard + 1)
    (e : α) : (M ／ {e}).TutteConnected k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  refine TutteConnected.contract (h.mono (by grw [eRk_singleton_le])) ?_
  grw [eRk_singleton_le]
  assumption

/-- I believe that this is false if the assumption is relaxed to `2 * k ≤ M.E.encard`
in the case where `k = ⊤` and `M` is a free extension of a nontrivial sparse paving matroid by `e`-/
lemma TutteConnected.deleteElem (h : M.TutteConnected (k + 1)) (hnt : 2 * k < M.E.encard + 1)
    (e : α) : (M ＼ {e}).TutteConnected k := by
  simpa using (h.dual.contractElem (by simpa) e).dual

end Minor

/-- Any element can be deleted or contracted from a `k`-connected tame uniform matroid to preserve
`k`-connectedness. The proof is mostly the discharging of trivialities. -/
lemma IsUniform.contract_or_delete_tutteConnected_of_tutteConnected [M.Tame] (hM : M.IsUniform)
    (hconn : M.TutteConnected k) (e : α) :
    (M ／ {e}).TutteConnected k ∨ (M ＼ {e}).TutteConnected k := by
  wlog hfin : M.RankFinite generalizing M with aux
  · have := M.tame_dual
    rw [← tutteConnected_dual_iff, or_comm, ← tutteConnected_dual_iff, dual_contract, dual_delete]
    exact aux hM.dual (by simpa) <|
      (or_iff_right hfin).1 hM.sparsePaving.rankFinite_or_rankFinite_dual
  wlog he : e ∈ M.E generalizing with aux
  · rw [← contract_inter_ground_eq, singleton_inter_eq_empty.2 he, contract_empty]
    exact .inl hconn
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one
  · simp
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one
  · simp
  obtain ⟨E, r, hle, rfl⟩ := hM.exists_eq_unifOn
  simp only [unifOn_ground_eq] at he
  obtain hE | hE := E.subsingleton_or_nontrivial
  · exact .inl <| tutteConnected_of_subsingleton (hE.anti diff_subset) _
  obtain rfl | r := r
  · simp [hE.not_subsingleton] at hconn
  obtain ⟨F, heF, hFne, rfl⟩ : ∃ F, e ∉ F ∧ F.Nonempty ∧ insert e F = E :=
    ⟨E \ {e}, by simp, hE.diff_singleton_nonempty .., insert_diff_self_of_mem he⟩
  rw [unifOn_insert_contractElem heF, unifOn_delete_eq, insert_diff_self_of_notMem heF]
  simp only [unifOn_tutteConnected_iff hle, Nat.cast_add, Nat.cast_one, ENat.add_one_le_add_one_iff,
    ← add_assoc, encard_insert_of_notMem heF, two_mul, add_right_comm (r : ℕ∞) 1 r,
    ENat.add_one_inj] at hconn
  simp only [Nat.cast_add, Nat.cast_one, encard_insert_of_notMem heF,
    ENat.add_one_le_add_one_iff] at hle
  rw [unifOn_tutteConnected_iff hle]
  obtain h_eq | hlt := hle.eq_or_lt
  · eomega
  rw [unifOn_tutteConnected_iff (by simpa using Order.add_one_le_of_lt hlt)]
  eomega

/-- If `(P₁, P₂)` and `(Q₁, Q₂)` are partitions of matroids with the same ground set and both
with sides of size at least `k`, then either `P₁ ∩ Q₁` and `P₂ ∩ Q₂` both have size at least `k/2`,
or `P₁ ∩ Q₂` and `P₂ ∩ Q₁` both have size at least `k/2`. -/
lemma Partition.exists_large_diagonal {M N : Matroid α} (hNM : M.E = N.E) {P : M.Partition}
    {Q : N.Partition} (hP1 : 2 * k + 1 ≤ P.1.encard) (hP2 : 2 * k + 1 ≤ P.2.encard)
    (hQ1 : 2 * k + 1 ≤ Q.1.encard) (hQ2 : 2 * k + 1 ≤ Q.2.encard) :
      (k + 1 ≤ (P.1 ∩ Q.1).encard ∧ k + 1 ≤ (P.2 ∩ Q.2).encard)
    ∨ (k + 1 ≤ (P.1 ∩ Q.2).encard ∧ k + 1 ≤ (P.2 ∩ Q.1).encard) := by
  rw [← Q.union_inter_left P.left (P.left_subset_ground.trans_eq hNM)] at hP1
  rw [← Q.union_inter_left P.right (P.right_subset_ground.trans_eq hNM)] at hP2
  rw [← P.union_inter_right Q.left (Q.left_subset_ground.trans_eq hNM.symm)] at hQ1
  rw [← P.union_inter_right Q.right (Q.right_subset_ground.trans_eq hNM.symm)] at hQ2
  rw [encard_union_eq (by simp)] at hP1 hP2 hQ1 hQ2
  eomega

-- Bixby's lemma.
set_option maxHeartbeats 1000000 in
theorem TutteConnected.internallyConnected_three_contractElem_or_deleteElem
    (hM : M.TutteConnected 3) (e : α) :
    (M ／ {e}).InternallyConnected 3 ∨ (M ＼ {e}).InternallyConnected 3 := by
  obtain heE | heE := em' <| e ∈ M.E
  · simp [contractElem_of_notMem_ground heE, hM.internallyConnected]
  rw [show (3 : ℕ∞) = 1 + 1 + 1 from rfl] at *
  obtain hle | hgt := le_or_gt M.E.encard 4
  · have hfin : M.Finite := by
      rw [finite_iff, ← encard_lt_top_iff]
      enat_to_nat!
    have hU := hM.isUniform_of_encard_le (by eomega)
    obtain (h | h) := hU.contract_or_delete_tutteConnected_of_tutteConnected hM e
    · exact .inl h.internallyConnected
    exact .inr h.internallyConnected
  have hc := hM.contractElem (by eomega) e
  have hd := hM.deleteElem (by eomega) e
  -- Choose bad partitions `P` and `Q` of `M ／ e` and `M ＼ e` respectively.
  simp_rw [hc.internallyConnected_iff_forall, hd.internallyConnected_iff_forall, ENat.add_one_inj]
  by_contra! hcon
  obtain ⟨⟨P, hPconn, hP⟩, ⟨Q, hQconn, hQ⟩⟩ := hcon
  wlog hle : 2 ≤ (P.1 ∩ Q.1).encard ∧ 2 ≤ (P.2 ∩ Q.2).encard generalizing Q with aux
  · obtain (⟨h1, h2⟩ | ⟨h1,h2⟩) := exists_large_diagonal (P := P) (Q := Q) (k := 1) (by simp)
      (by simpa [hPconn] using hP.encard_left_ge)
      (by simpa [hPconn] using hP.encard_right_ge)
      (by simpa [hQconn] using hQ.encard_left_ge)
      (by simpa [hQconn] using hQ.encard_right_ge)
    · eomega
    exact aux Q.symm (by simpa) (by simpa) ⟨h1, h2⟩
  -- Since both sides of `P` and `Q` have size at least three,
  -- we can assume wlog that `P₁ ∩ Q₁` and `P₂ ∩ Q₂` are nontrivial.
  have heP : e ∉ P.left := by simpa using P.disjoint_left_contract
  have heQ : e ∉ Q.left := by simpa using Q.disjoint_left_delete
  have hle' := M.eConn_inter_add_eConn_insert_union_le (C := P.left) (D := Q.left) heP heQ
  simp [hPconn, hQconn] at hle'
  obtain h1 | h1 : M.eConn (P.1 ∩ Q.1) ≤ 1 ∨ M.eConn (insert e (P.1 ∪ Q.1)) ≤ 1 := by eomega
  · let P' := P.ofContractRight.inter Q.ofDeleteRight
    have hleft : P'.left = P.1 ∩ Q.1 := by simp [P']
    have hright : P'.right = insert e (P.2 ∪ Q.2) := by simp [P', insert_union]
    have hP'conn : P'.eConn ≤ 1 := by simpa [P', ← Partition.eConn_left]
    refine hM.not_isTutteSeparation (P := P') (by simpa) ?_
    grw [P'.isTutteSeparation_iff_add_one_le_encard (by generalize P'.eConn = a at *; enat_to_nat),
      hP'conn, hleft, one_add_one_eq_two, and_iff_right hle.1, hright,
      ← encard_le_encard (subset_insert ..),
      ← encard_le_encard subset_union_left, ← hP.encard_right_ge, add_assoc, one_add_one_eq_two]
    simp
  let P' := P.ofContractLeft.union Q.ofDeleteLeft
  have hPl : P.left ∩ Q.left ⊆ P'.left := by
    simp only [union_left, ofContractLeft_left, union_singleton, ofDeleteLeft_left, union_insert,
      mem_union, mem_insert_iff, true_or, insert_eq_of_mem, P']
    grind
  have hPr : P'.right = P.right ∩ Q.right := by simp [P']
  have hP'conn : P'.eConn ≤ 1 := by simpa [P', ← P'.eConn_left, insert_union]
  refine hM.not_isTutteSeparation (P := P') (by simpa) ?_
  grw [Partition.isTutteSeparation_iff_add_one_le_encard
    (by generalize P'.eConn = a at *; enat_to_nat), hP'conn, hPr,
    one_add_one_eq_two, and_iff_left hle.2, ← encard_le_encard hPl, hle.1]

-- lemma IsSimplification.foo (hN : N.IsSimplification M) (P : M.Partition) :
--     P.1 ⊆ M.closure (P.induce hN.isRestriction.subset).1 := by
--   intro e heP

-- lemma NumConnected.numConnected_of_isSimplification [M.Loopless]
--     {dg : Matroid α → Set α → Prop} (hdg : ∀ ⦃X Y⦄, Y ⊆ M.E → dg M Y → dg N X)
--     (h : M.NumConnected dg k) (hNM : N.IsSimplification M) : N.NumConnected dg k := by
--   obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
--   simp only [numConnected_iff_forall] at h ⊢
--   intro P hPle hPsep
--   set X := ⋃ e ∈ P.left, {f | M.Parallel f e} with hX
--   have hXE : X ⊆ M.E := iUnion₂_subset fun _ _ _ ↦ Parallel.mem_ground_left
--   set Q := M.partition (X \ P.right) with hQ
--   have hPQ1 : P.1 ⊆ Q.1 := by
--     simp only [partition_left, subset_diff, disjoint, and_true, Q, X]
--     refine fun e he ↦ mem_biUnion (x := e) he <| ?_
--     simpa using hNM.isNonloop_of_mem (P.left_subset_ground he)
--   have hPQ2 : P.2 ⊆ Q.2 := by
--     simp [Q, X, diff_diff_right,
--       inter_eq_self_of_subset_right (P.right_subset_ground.trans hNM.isRestriction.subset)]
--   have hQconn : Q.eConn = P.eConn := by
--     apply Partition.eConn_eq_of_subset_closure_of_isRestriction hNM.isRestriction hPQ1 hPQ2
--     · refine diff_subset.trans ?_
--       simp only [hX, iUnion_subset_iff]
--       refine fun e he f hf ↦ ?_
--       grw [← singleton_subset_iff.2 he]
--       exact Parallel.mem_closure hf
--     simp only [hX, partition_right, diff_diff_right, inter_comm M.E, union_subset_iff,
--       diff_subset_iff, inter_ground_subset_closure, and_true, hQ]
--     simp only [subset_def, mem_union, mem_iUnion, mem_setOf_eq, exists_prop]
--     intro e heE
--     obtain ⟨f, ⟨hfE, hef⟩, -⟩ := hNM.exists_unique (isNonloop_of_loopless heE)
--     obtain (hfP | hfP) := P.union_eq ▸ hfE
--     · exact .inl ⟨f, hfP, hef⟩
--     refine .inr ?_
--     grw [← singleton_subset_iff.2 hfP]
--     exact hef.mem_closure
--   exact h Q (by rwa [hQconn]) ⟨fun h' ↦ hPsep.1 (hdg hPQ1 Q.left_subset_ground h'),
--     fun h' ↦ hPsep.2 (hdg hPQ2 Q.right_subset_ground h')⟩




/- This is presumably true for infinite `k` as well. -/
-- lemma InternallyConnected.internallyConnected_of_isSimplification [M.Loopless]
--     (h : M.InternallyConnected k) (hN : N.IsSimplification M) (hk : k ≠ ⊤) :
--     N.InternallyConnected k := by
--   obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
--   rw [internallyConnected_iff, tutteConnected_iff_numConnected_encard (by simpa using hk),
--     weaklyInternallyConnected_iff_numConnected_encard (by simpa using hk)] at h ⊢
--   refine ⟨h.1.numConnected_of_isSimplification (fun X Y hXY hYE hY) hN,
--     h.2.numConnected_of_isSimplification ?_ hN⟩
  -- obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  -- simp only [internallyConnected_iff_forall] at h ⊢
  -- intro P
  -- set X := ⋃ e ∈ P.left, {f | M.Parallel f e} with hX
  -- have hXE : X ⊆ M.E := iUnion₂_subset fun _ _ _ ↦ Parallel.mem_ground_left
  -- set Q := M.partition (X \ P.right) with hQ
  -- have hPQ1 : P.1 ⊆ Q.1 := by
  --   simp only [partition_left, subset_diff, disjoint, and_true, Q, X]
  --   refine fun e he ↦ mem_biUnion (x := e) he <| ?_
  --   simpa using hN.isNonloop_of_mem (P.left_subset_ground he)
  -- have hPQ2 : P.2 ⊆ Q.2 := by
  --   simp [Q, X, diff_diff_right,
  --     inter_eq_self_of_subset_right (P.right_subset_ground.trans hN.isRestriction.subset)]
  -- have hQconn : Q.eConn = P.eConn := by
  --   apply Partition.eConn_eq_of_subset_closure_of_isRestriction hN.isRestriction hPQ1 hPQ2
  --   · refine diff_subset.trans ?_
  --     simp only [hX, iUnion_subset_iff]
  --     refine fun e he f hf ↦ ?_
  --     grw [← singleton_subset_iff.2 he]
  --     exact Parallel.mem_closure hf
  --   simp only [hX, partition_right, diff_diff_right, inter_comm M.E, union_subset_iff,
  --     diff_subset_iff, inter_ground_subset_closure, and_true, hQ]
  --   simp only [subset_def, mem_union, mem_iUnion, mem_setOf_eq, exists_prop]
  --   intro e heE
  --   obtain ⟨f, ⟨hfE, hef⟩, -⟩ := hN.exists_unique (isNonloop_of_loopless heE)
  --   obtain (hfP | hfP) := P.union_eq ▸ hfE
  --   · exact .inl ⟨f, hfP, hef⟩
  --   refine .inr ?_
  --   grw [← singleton_subset_iff.2 hfP]
  --   exact hef.mem_closure
  -- refine ⟨fun h0 hP ↦ (h Q).1 (by rwa [hQconn]) ?_,
  --   fun h1 hP ↦ (h Q).2 (by rwa [hQconn]) ?_⟩
  -- · rw [isTutteSeparation_iff_add_one_le_encard (by eomega)] at hP ⊢
  --   nth_grw 1 [hQconn, hQconn, hP.1, hP.2, hPQ1, hPQ2]
  --   simp
  -- rw [isInternalSeparation_iff_encard (by eomega)] at hP ⊢
  -- grw [← hPQ1, ← hPQ2, hQconn]
  -- assumption

-- lemma IsSimplification.internallyConnected_three_iff (hM : M.Loopless)
--     (hN : N.IsSimplification M) : M.InternallyConnected 3 ↔ N.InternallyConnected 3 := by
--   rw [show (3 : ℕ∞) = 1 + 1 + 1 from rfl] at *
--   refine ⟨fun h ↦ h.internallyConnected_of_isSimplification hN (by simp), fun h ↦ ?_⟩
--   simp only [internallyConnected_iff_forall, ENat.add_one_le_add_one_iff, ENat.add_le_right_iff,
--     ENat.one_ne_top, or_false, ENat.add_one_inj] at h ⊢
--   intro P





                  -- simp only [hX]



                -- rw [← P.eConn_left, ← Q.eConn_left, eConn_eq_eLocalConn, eConn_eq_eLocalConn]
                -- simp only [hQ, hX, partition_left, compl_left, diff_diff_right,
          --   inter_eq_self_of_subset_right (P.right_subset_ground.trans hN.isRestriction.subset)]
                -- refine le_antisymm ?_ ?_
                -- · sorry







      -- · rw [isTutteSeparation_iff_add_one_le_encard]
        -- grw [← closure_subset_closure (s := {f})]




          -- simp only [hX]



        -- rw [← P.eConn_left, ← Q.eConn_left, eConn_eq_eLocalConn, eConn_eq_eLocalConn]
        -- simp only [hQ, hX, partition_left, compl_left, diff_diff_right,
        --   inter_eq_self_of_subset_right (P.right_subset_ground.trans hN.isRestriction.subset)]
        -- refine le_antisymm ?_ ?_
        -- · sorry
