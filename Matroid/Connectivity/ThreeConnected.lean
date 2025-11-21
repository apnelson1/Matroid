import Matroid.Connectivity.Uniform

open Set Matroid.Partition

namespace Matroid

section separation

variable {α : Type*} {M : Matroid α} {j k : ℕ∞} {a b e f : α} {A B X Y : Set α}

-- abbrev ThreeConnected (M : Matroid α) := M.IsTutteConnected 3

-- abbrev InternallyThreeConnected (M : Matroid α) := M.IsInternallyConnected 3

-- Cardinality hypothesis shouldn't be needed.
theorem bixby (hM : M.TutteConnected 3) (hnt : 4 ≤ M.E.encard) (e : α) :
    (M ／ {e}).InternallyConnected 3 ∨ (M ＼ {e}).InternallyConnected 3 := by
  wlog he : e ∈ M.E generalizing with aux
  · rw [← contract_inter_ground_eq, singleton_inter_eq_empty.2 he, contract_empty]
    exact .inl hM.internallyConnected
  rw [show (3 : ℕ∞) = 1 + 1 + 1 from rfl] at *
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
