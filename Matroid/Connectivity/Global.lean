import Matroid.Connectivity.Finitize

variable {α ι : Type*} {M : Matroid α} {A B C X Y I J : Set α} {e f : α} {k : ℕ∞}

set_option linter.style.longLine false

open Set Function

namespace Matroid

-- /-- Connectivity is submodular. -/
-- lemma eConn_submod (M : Matroid α) (X Y : Set α) :
--     M.eConn (X ∪ Y) + M.eConn (X ∩ Y) ≤ M.eConn X + M.eConn Y := by
--   by_contra! hcon
--   obtain ⟨N, hNM, hNfin, hsum⟩ :=
--     M.exists_finite_counterexample_of_lt_eConn
--     (fun b ↦ bif b then X else Y) (fun b ↦ bif b then X ∪ Y else X ∩ Y) (by simpa)
--   have hbad : N.eConn X + N.eConn Y < N.eConn (X ∪ Y) + N.eConn (X ∩ Y) :=
--     by simpa using hsum
--   simp_rw [← cast_conn_eq, ← Nat.cast_add, Nat.cast_lt, add_comm (a := N.conn (X ∪ Y))] at hbad
--   exact (N.conn_submod X Y).not_gt hbad


-- theorem bixbyCoullard_elem' {e : α} (C D : Set α) (heC : e ∉ C) (heD : e ∉ D) :
--     M.eConn (C ∩ D) + M.eConn (insert e (C ∪ D)) ≤ (M ／ {e}).eConn C + (M ＼ {e}).eConn D + 1 := by
--   have hCe := M.eConn_eq_eConn_contract_subset_add (show {e} ⊆ insert e C by simp)
--   rw [insert_diff_self_of_notMem heC] at hCe
--   have hDe := M✶.eConn_eq_eConn_contract_disjoint_add (show Disjoint D {e} by simpa)
--   rw [eConn_dual, ← dual_delete, eConn_dual] at hDe


lemma monotone_rhs_aux {P Q X : Set α} :
    Monotone (fun N : Matroid α ↦ (N ／ X).eConn P + (N ＼ X).eConn Q + N.eConn X) := by
  rintro N M (hNM : N ≤m M)
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := hNM.exists_eq_contract_delete_disjoint
  simp only
  have hmin1 : M ／ C ＼ D ／ X ≤m M ／ (X \ D) ＼ (X ∩ D) := by
    rw [contract_delete_contract']
    refine IsMinor.delete_isMinor_delete_of_subset ?_ inter_subset_right ?_
    · exact contract_isMinor_of_subset _ subset_union_right
    simp_rw [contract_ground]
    tauto_set
  have hmin2 : M ／ C ＼ D ＼ X ≤m M ＼ (X \ C) ／ (X ∩ C) := by
    rw [delete_delete, contract_delete_comm']
    refine IsMinor.contract_isMinor_contract_of_subset ?_ inter_subset_right ?_
    · exact (delete_isRestriction_of_subset _ (by tauto_set)).isMinor
    simp_rw [delete_ground]
    tauto_set
  have hmin3 : M ／ C ＼ D ≤m M ／ (X ∩ C) ＼ (X ∩ D) :=
    (contract_isMinor_of_subset _ inter_subset_right).delete_isMinor_delete_of_subset
       inter_subset_right (by simp_rw [contract_ground]; tauto_set)
  grw [hmin1.eConn_le, hmin2.eConn_le, eConn_delete_le_eConn_contract_add,
    contract_contract, diff_union_inter, eConn_contract_le_eConn_delete_add _ _ (X ∩ C),
      delete_delete, diff_union_inter, hmin3.eConn_le, ← add_assoc,
      add_right_comm (c := (M ＼ X).eConn Q), add_assoc, add_assoc]
  convert rfl.le
  nth_rw 1 [← diff_union_inter X D, M.eConn_union_eq_eConn_contract_add_eConn_delete
    disjoint_sdiff_inter]
  convert rfl
  rw [← diff_union_inter (X \ D) C, union_comm,
    eConn_union_eq_eConn_contract_add_eConn_delete _ disjoint_sdiff_inter.symm,
    delete_delete, show (X \ D) ∩ C = X ∩ C by tauto_set,
    show X ∩ D ∪ (X \ D) \ C = X \ C by tauto_set, add_comm, contract_delete_comm _ (by tauto_set),
    ← eConn_inter_ground, eq_comm, ← eConn_inter_ground, contract_ground,
    delete_ground]
  convert rfl using 3
  tauto_set

theorem eConn_inter_add_eConn_union_le_conn_contract_add_eConn_delete_add_econn
    (M : Matroid α) {C D X : Set α} (hC : Disjoint C X) (hD : Disjoint D X) :
    M.eConn (C ∩ D) + M.eConn (X ∪ C ∪ D) ≤ (M ／ X).eConn C + (M ＼ X).eConn D + M.eConn X := by
  by_contra! hlt
  set g := fun (N : Matroid α) ↦ (N ／ X).eConn C + (N ＼ X).eConn D + N.eConn X with hg
  set A := fun b ↦ bif b then C ∩ D else X ∪ C ∪ D
  obtain ⟨N, hNM, hNfin, hN⟩ := M.exists_finite_counterexample_of_lt_sum_eConn g
    (monotone_rhs_aux ..) A (by simpa)
  simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
    Finset.sum_insert, cond_true, Finset.sum_singleton, cond_false, g, A,
    ← cast_conn_eq, ← Nat.cast_add, Nat.cast_lt] at hN
  exact (N.conn_inter_add_conn_union_le_conn_contract_add_conn_delete_add_conn hC hD).not_gt hN



end Matroid
