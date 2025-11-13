import Matroid.Connectivity.Finitize

variable {α ι : Type*} {M : Matroid α} {A B C X Y I J : Set α} {e f : α} {k : ℕ∞}

set_option linter.style.longLine false

open Set Function

namespace Matroid

/-- Connectivity is submodular. -/
lemma eConn_submod (M : Matroid α) (X Y : Set α) :
    M.eConn (X ∪ Y) + M.eConn (X ∩ Y) ≤ M.eConn X + M.eConn Y := by
  by_contra! hcon
  obtain ⟨N, hNM, hNfin, hsum⟩ :=
    M.exists_finite_counterexample_of_lt_eConn
    (fun b ↦ bif b then X else Y) (fun b ↦ bif b then X ∪ Y else X ∩ Y) (by simpa)
  have hbad : N.eConn X + N.eConn Y < N.eConn (X ∪ Y) + N.eConn (X ∩ Y) :=
    by simpa using hsum
  simp_rw [← cast_conn_eq, ← Nat.cast_add, Nat.cast_lt, add_comm (a := N.conn (X ∪ Y))] at hbad
  exact (N.conn_submod X Y).not_gt hbad


-- theorem bixbyCoullard_elem' {e : α} (C D : Set α) (heC : e ∉ C) (heD : e ∉ D) :
--     M.eConn (C ∩ D) + M.eConn (insert e (C ∪ D)) ≤ (M ／ {e}).eConn C + (M ＼ {e}).eConn D + 1 := by
--   have hCe := M.eConn_eq_eConn_contract_subset_add (show {e} ⊆ insert e C by simp)
--   rw [insert_diff_self_of_notMem heC] at hCe
--   have hDe := M✶.eConn_eq_eConn_contract_disjoint_add (show Disjoint D {e} by simpa)
--   rw [eConn_dual, ← dual_delete, eConn_dual] at hDe


-- theorem eConn_inter_add_eConn_union_le_conn_contract_add_eConn_delete_add_econn
--     (M : Matroid α) {C D X : Set α} (hC : Disjoint C X) (hXD : Disjoint D X) :
--     M.eConn (C ∩ D) + M.eConn (X ∪ C ∪ D) ≤ (M ／ X).eConn C + (M ＼ X).eConn D + X.encard := by
--   obtain hX | hX := X.infinite_or_finite
--   · simp [hX.encard_eq]
--   rw [← WithTop.add_le_add_iff_left (x := M.eLocalConn C X) sorry]
--   simp_rw [← add_assoc]
--   rw [add_comm _ ((M ／ X).eConn ..), ← M.eConn_eq_eConn_contract_disjoint_add hC]
--   rw [← WithTop.add_le_add_iff_right (z := M✶.eLocalConn D X) sorry,
--     add_right_comm (c := encard ..), ← (M ＼ X).eConn_dual, dual_delete,
--     add_assoc, add_assoc, add_assoc, ← M✶.eConn_eq_eConn_contract_disjoint_add hXD]
    -- ← WithTop.add_le_add_iff_right (z := M✶.eLocalConn X D) sorry]


end Matroid
