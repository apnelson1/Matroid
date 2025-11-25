import Matroid.Connectivity.Infinite

open Set Matroid.Partition

namespace Matroid

section separation

variable {α : Type*} {M : Matroid α} {j k : ℕ∞} {a b e f : α} {A B X Y : Set α}

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
lemma TutteConnected.deleteElem (h : M.TutteConnected (k+1)) (hnt : 2 * k < M.E.encard + 1)
    (e : α) : (M ＼ {e}).TutteConnected k := by
  simpa using (h.dual.contractElem (by simpa) e).dual


end Minor

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



  -- rw [show E = insert e (E \ {e})] at *

  obtain hE | hE := E.subsingleton_or_nontrivial
  · exact .inl <| tutteConnected_of_subsingleton (hE.anti diff_subset) _
  obtain rfl | r := r
  · simp [hE.not_subsingleton] at hconn
  obtain ⟨F, heF, hFne, rfl⟩ : ∃ F, e ∉ F ∧ F.Nonempty ∧ E = insert e F := sorry
  rw [unifOn_insert_contractElem heF, unifOn_delete_eq, insert_diff_self_of_notMem heF]

  -- rw [unifOn_ground_eq] at he
  simp only [unifOn_tutteConnected_iff hle, Nat.cast_add, Nat.cast_one, ENat.add_one_le_add_one_iff,
    ← add_assoc, encard_insert_of_notMem heF, two_mul, add_right_comm (r : ℕ∞) 1 r,
    ENat.add_one_inj] at hconn
  simp only [Nat.cast_add, Nat.cast_one, encard_insert_of_notMem heF,
    ENat.add_one_le_add_one_iff] at hle
  obtain h1 | h2 := hconn
  · rw [unifOn_tutteConnected_iff hle]




  rw [Nat.cast_add, Nat.cast_one, ← encard_diff_singleton_add_one he,
    ENat.add_one_le_add_one_iff] at hle

  rw [unifOn_contractElem (by simpa using he), unifOn_delete_eq, unifOn_tutteConnected_iff hle]





  -- obtain hl | hn := M.isLoop_or_isNonloop e
  -- · exact False.elim <| hl.not_tutteConnected hE (by simp) hconn
  -- obtain hl' | hn' := M✶.isLoop_or_isNonloop e
  -- · exact False.elim <| hl'.not_tutteConnected (by simpa) (by simp) hconn.dual




  -- rw [hM.tutteConnected_iff] at hconn
  -- obtain ⟨hk, hk'⟩ | htop := hconn
  -- ·

  -- rw [(hM.contract _).tutteConnected_iff, (hM.delete _).tutteConnected_iff,
  --   tutteConnected_top_iff_of_tame, tutteConnected_top_iff_of_tame, and_iff_right (hM.contract _),
  --   and_iff_right (hM.delete _)]
  -- simp only [dual_contract, contract_ground, dual_delete, delete_ground, finite_iff]




-- Cardinality hypothesis shouldn't be needed.
-- Bixby's lemma.
theorem TutteConnected.internallyConnected_three_contract_or_delete (hM : M.TutteConnected 3)
    (hnt : 4 ≤ M.E.encard) (e : α) :
    (M ／ {e}).InternallyConnected 3 ∨ (M ＼ {e}).InternallyConnected 3 := by
  wlog he : e ∈ M.E generalizing with aux
  · rw [← contract_inter_ground_eq, singleton_inter_eq_empty.2 he, contract_empty]
    exact .inl hM.internallyConnected
  rw [show (3 : ℕ∞) = 1 + 1 + 1 from rfl] at *

  obtain hle | hgt := le_or_gt M.E.encard 3
  · have hfin : M.Finite := by
      rw [finite_iff, ← encard_lt_top_iff]
      enat_to_nat!

    have hU := hM.isUniform_of_encard_le (by enat_to_nat!; omega)

    have := (hU.contract {e}).tutteConnected_iff

    -- have := (hU.contract {e}).tutteConnected_iff (k := 1 + 1)

  have hc := hM.contractElem (by enat_to_nat!; omega) e
  have hd := hM.deleteElem (by enat_to_nat!; omega) e
  -- Choose bad partitions `P` and `Q` of `M ／ e` and `M ＼ e` respectively.
  simp_rw [hc.internallyConnected_iff_forall, hd.internallyConnected_iff_forall, ENat.add_one_inj]
  by_contra! hcon
  obtain ⟨⟨P, hPconn, hP⟩, ⟨Q, hQconn, hQ⟩⟩ := hcon
  -- Since both sides of `P` and `Q` have size at least three,
  -- we can assume wlog that `P₁ ∩ Q₁` and `P₂ ∩ Q₂` are nontrivial.
  wlog h00 : (P.1 ∩ Q.1).Nontrivial generalizing Q with aux
  · replace aux := imp_false.1 <| aux Q.symm (by simpa) (by simpa)
    rw [← one_lt_encard_iff_nontrivial, not_lt] at aux h00
    refine hP.encard_left_ge.not_gt ?_
    grw [← inter_eq_self_of_subset_left P.left_subset_ground, contract_ground, ← delete_ground,
      ← Q.union_eq, inter_union_distrib_left, encard_union_le, h00, ← Q.symm_left, aux, hPconn]
    simp
  wlog hPQ : (P.1 ∩ Q.1).Nontrivial ∧ (P.2 ∩ Q.2).Nontrivial generalizing Q with aux
  · rw [and_iff_right h00, ← one_lt_encard_iff_nontrivial, not_lt] at hPQ
    have h1 : (P.left ∩ Q.right).Nontrivial := by
      nth_grw 1 [← one_lt_encard_iff_nontrivial, ← not_le, ← ENat.add_one_le_add_one_iff, ← hPQ,
        ← encard_union_le, ← encard_le_encard (s := Q.right), ← hQ.encard_right_ge, hQconn]
      · simp
      rw [← union_inter_distrib_right, P.union_eq,
        inter_eq_self_of_subset_right (by simpa using Q.right_subset_ground)]
    have h2 : (P.2 ∩ Q.1).Nontrivial := by
      nth_grw 1 [← one_lt_encard_iff_nontrivial, ← not_le, ← ENat.add_one_le_add_one_iff, ← hPQ,
        ← encard_union_le, ← encard_le_encard (s := P.right), ← hP.encard_right_ge, hPconn]
      · simp
      rw [← inter_union_distrib_left, Q.union_eq, inter_eq_self_of_subset_left
        (by simpa using P.right_subset_ground)]
    simpa [h1, h2] using aux Q.symm (by simpa) (by simpa)
  have heP : e ∉ P.left := by simpa using P.disjoint_left_contract
  have heQ : e ∉ Q.left := by simpa using Q.disjoint_left_delete
  have hle := M.eConn_inter_add_eConn_insert_union_le (C := P.left) (D := Q.left) heP heQ
  simp [hPconn, hQconn] at hle
  obtain h1 | h1 : M.eConn (P.1 ∩ Q.1) ≤ 1 ∨ M.eConn (insert e (P.1 ∪ Q.1)) ≤ 1 := by
    enat_to_nat! <;> omega
  · let P' := P.ofContractRight.inter Q.ofDeleteRight
    have hleft : P'.left = P.1 ∩ Q.1 := by simp [P']
    have hright : P'.right = insert e (P.2 ∪ Q.2) := by simp [P', insert_union]
    have hP'conn : P'.eConn ≤ 1 := by simpa [P', ← Partition.eConn_left]
    refine hM.not_isTutteSeparation (P := P') (by simpa) ?_
    grw [P'.isTutteSeparation_iff_add_one_le_encard (by enat_to_nat!), hP'conn, hleft,
      one_add_one_eq_two, two_le_encard_iff_nontrivial, and_iff_right hPQ.1,
      hright, ← encard_le_encard (subset_insert ..), ← encard_le_encard subset_union_left,
      ← hP.encard_right_ge, add_assoc, one_add_one_eq_two]
    simp
  let P' := P.ofContractLeft.union Q.ofDeleteLeft
  have hPl : P.left ∩ Q.left ⊆ P'.left := by
    simp only [union_left, ofContractLeft_left, union_singleton, ofDeleteLeft_left, union_insert,
      mem_union, mem_insert_iff, true_or, insert_eq_of_mem, P']
    grind
  have hPr : P'.right = P.right ∩ Q.right := by simp [P']
  have hP'conn : P'.eConn ≤ 1 := by simpa [P', ← P'.eConn_left, insert_union]
  refine hM.not_isTutteSeparation (P := P') (by simpa) ?_
  grw [Partition.isTutteSeparation_iff_add_one_le_encard (by enat_to_nat!), hP'conn, hPr,
    one_add_one_eq_two, two_le_encard_iff_nontrivial, two_le_encard_iff_nontrivial,
    and_iff_left hPQ.2]
  exact hPQ.1.mono hPl
