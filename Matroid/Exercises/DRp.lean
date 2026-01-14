import Matroid.Connectivity.Local
import Matroid.Connectivity.Separation.Minor


open Set Set.Notation

namespace Matroid

variable {α : Type*} {M : Matroid α} {B B' I I' J K X Y : Set α}

/- Put the `1` on the RHS! Your version below is stated in terms of `Nat` subtraction,
so will be harder to apply. -/
lemma Exercise_for_DRP' (M : Matroid α) [RankFinite M] (X Y : Set α) (e : α) (heX : e ∉ X)
    (heY : e ∉ Y) :
    M.conn (X ∩ Y) + M.conn (insert e (X ∪ Y)) ≤  1 + (M ＼ {e}).conn X + (M ／ {e}).conn Y := by
  -- Apply submodularity fo the pairs `(X, insert e Y)` and `(M.E \ insert e X, Y)`, and simplify.
  have hsm := M.rk_submod X (insert e Y)
  rw [union_insert, inter_insert_of_notMem heX] at hsm
  have hsm' := M.rk_submod_compl (insert e X) Y
  rw [insert_union, insert_inter_of_notMem heY] at hsm'
  -- Now `zify` and simplify.
  zify
  --deleteElem,contractElem,
  simp only [intCast_conn_eq, delete_ground, diff_singleton_diff_eq,
    contract_rk_cast_int_eq, union_singleton, contract_ground, insert_diff_insert,
    contract_rank_cast_int_eq]
  -- Rewrite this particular annoying term. If `e ∈ M.E` is assumed, this can be taken
  -- care of more easily .
  have hrw : M.rk (insert e (M.E \ Y)) = M.rk (M.E \ Y) := by
    by_cases he : e ∈ M.E
    · rw [insert_eq_of_mem (by simp [he, heY])]
    rw [rk_insert_of_notMem_ground _ he]

  have hle : (M ＼ ({e} : Set α)).rank ≤ M.rank := delete_rank_le M {e}
  have hle' : M.rk {e} ≤ 1 := rk_singleton_le M e

  rw [delete_rk_eq_of_disjoint _ (by simpa), delete_rk_eq_of_disjoint _ (by simp), hrw]

  linarith



lemma Exercise_for_DRP (M : Matroid α) [RankFinite M] (X Y : Set α) (e : α) (he : e ∈ M.E)
    (heX : e ∉ X) (heY : e ∉ Y) : M.conn (X ∩ Y) + M.conn (X ∪ Y ∪ {e})
    ≤  (M ＼ {e}).conn X + (M ／ {e}).conn Y + 1 := by
  --The proof starts with getting all the equations for the contractions, there is 3 of them
  have : M.rk {e} ≤ 1 := by sorry
  have hconY : M.rk (insert e Y) - 1 = ((M ／ {e}).rk Y : ℤ ) := by sorry
    -- You can rewrite what it means to contract an element with set notation using contractElem
    -- You can then use the definition of contracting for integers
    -- union_singleton opens insert e X to e ∪ X
    --linarith
  have hconEY : M.rk (M.E \ Y) - 1 = ((M ／ {e}).rk (M.E \ (insert e Y)) : ℤ ) := by
    --similar to hconY but with an extra step since we need the following observation
    have hins : insert e (M.E \ insert e Y) =  M.E \ Y := by
      sorry
    sorry
  have hconE : M.rank - 1 = ((M ／ {e}).rk (M.E \ {e}) : ℤ ) := by
    sorry
    -- This may be useful to finsih: rw [insert_diff_self_of_mem he, ←rank_def M]
  --End of the contractions. We are now going to get the equations of submodularity,
  --there is two of them
  have hsub1 : (M.rk ( X ∪ Y ∪ {e}) : ℤ ) + (M.rk ( X ∩ Y) : ℤ)
      ≤ M.rk X + M.rk (insert e Y) := by sorry
  have hsub2 : (M.rk (M.E \ (X ∩ Y)) : ℤ) + (M.rk (M.E \ ( X ∪ Y ∪ {e})) : ℤ)
      ≤ M.rk (M.E \ (insert e X)) + M.rk (M.E \ Y) := by sorry
  --This equation is the last one we need as aid.
  have hneed : ( (M ＼ {e}).rank : ℤ)  ≤ (M.rank : ℤ) := by sorry
  --We now want to subsitute the definition of connectivity with the following
  have hf : M.conn (X ∩ Y) + M.conn (X ∪ Y ∪ {e}) =
      ((M.rk ( X ∪ Y ∪ {e}) : ℤ ) + ( M.rk ( X ∩ Y)) : ℤ ) +
      ((M.rk (M.E \ (X ∩ Y)) + M.rk (M.E \ ( X ∪ Y ∪ {e}))) : ℤ ) - (2 * M.rank : ℤ ) := by
    --The proof is easy if we use int_cast_conn_eq and linarith
    sorry
  -- To not get annoyed with Lean we use zify. This let's us subtract without getting annoyed
  zify
  -- We use the following 3 to change the rank function of a deletion
  --to the rank function of the matroid
  have hdelx : (M ＼ {e}).E \ X = M.E \ insert e X := by sorry
  have hconYh : (M ／ {e}).E \ Y = M.E \ insert e Y :=  by sorry
  have hrkcon : (M ／ {e}).rk (M.E \ {e}) = (M ／ {e}).rank := rk_eq_rank fun ⦃a⦄ a ↦ a
  --Here I used a lot of rw
  --rw [intCast_conn_eq (M ＼ e) X, intCast_conn_eq (M ／ e) Y, hf ]
  --rw[delete_elem_rk_eq, delete_elem_rk_eq, hdelx, hconYh, ←hrkcon]
  sorry
  --· --linarith
    --sorry
 -- · sorry
  --sorry
-- gh repo clone apnelson1/Matroid

--lemma Check {a : ℕ} (h : a < a) : False := by exact (lt_self_iff_false a).mp h

theorem TLT (M : Matroid α) [M.Finite] (hXY : Disjoint X Y) (hXE : X ⊆ M.E) (hYE : Y ⊆ M.E) :
    ∃ N, N ≤m M ∧ N.E = X ∪ Y ∧ N.conn X = M.connBetween X Y := by
  by_cases hE : X ∪ Y = M.E
  · refine ⟨M, IsMinor.refl, hE.symm, ?_⟩
    have hY : Y = M.E \ X := Eq.symm (Disjoint.sdiff_eq_of_sup_eq hXY hE)
    subst hY
    rw [conn, connBetween, eConnBetween_self_compl]
  have he : ∃ e ∈ M.E, e ∉ X ∪ Y
  · rw [← not_subset]
    contrapose! hE
    exact (union_subset hXE hYE).antisymm hE
  obtain ⟨e, heE, heXY⟩ := he
  have hdel : (M ＼ {e}).E.encard < M.E.encard := by
    refine IsStrictMinor.encard_ground_lt ?_
    exact deleteElem_isStrictMinor heE
  have hcon : (M ／ {e}).E.encard < M.E.encard := by
    exact hdel
  have t1 := TLT (M ／ {e}) hXY
  have t2 := TLT (M ＼ {e}) hXY
  -- connectivity of M / e and M \ e is less or equal than in M so we can say in the
  -- 2 inductive step cases that they are equal

  have minor_delConnBetween: (M ＼ {e}).connBetween X Y ≤ M.connBetween X Y := by
    rw [← Nat.cast_le (α := ℕ∞), M.coe_connBetween X Y hXY, (M ＼ {e}).coe_connBetween X Y hXY]
    --simp only [deleteElem]
    apply M.eConnBetween_delete_le X Y {e}

  have minor_contrConnBetween: (M ／ {e}).connBetween X Y ≤ M.connBetween X Y := by
    rw [← Nat.cast_le (α := ℕ∞), M.coe_connBetween X Y hXY, (M ／ {e}).coe_connBetween X Y hXY]
    --simp only [contractElem]
    apply M.eConnBetween_contract_le X Y {e}

  have e_not_in_x: e ∉ X := by
      rw [mem_union, not_or] at heXY
      exact heXY.left
  have e_not_in_y: e ∉ Y := by
      rw [mem_union, not_or] at heXY
      exact heXY.right

  -- M / e and M \ e are minors of M
  have del_minor_strict: (M ＼ {e}) <m M := deleteElem_isStrictMinor heE
  have del_minor: (M ＼ {e}) ≤m M := IsStrictMinor.isMinor del_minor_strict
  have contract_minor_strict:  (M ／ {e}) <m M := contractElem_isStrictMinor heE
  have contract_minor: (M ／ {e}) ≤m M := IsStrictMinor.isMinor contract_minor_strict

  -- N from t2 is a minor of M
  have n_del_minor {N: Matroid α} (minor_m_del_e: N ≤m (M ＼ {e})) : (N ≤m M) := by
    apply IsMinor.trans minor_m_del_e del_minor
  -- N from t1 is a minor of M
  have n_contract_minor {N: Matroid α} (minor_m_cont_e: N ≤m (M ／ {e})) : (N ≤m M) := by
    apply IsMinor.trans minor_m_cont_e contract_minor

  -- this can probably be avoided - it just made it easier to write the next part, but should change
  have use_t2: ∃ N, (N ≤m (M ＼ {e}) ∧ N.E = X ∪ Y ∧ N.conn X = (M ＼ {e}).connBetween X Y) := by
    apply t2
    --simp only [deleteElem, delete_ground]
    exact subset_diff_singleton hXE e_not_in_x
    --simp only [deleteElem, delete_ground]
    exact subset_diff_singleton hYE e_not_in_y

  have use_t1: ∃ N, (N ≤m (M ／ {e}) ∧ N.E = X ∪ Y ∧ N.conn X = (M ／ {e}).connBetween X Y) := by
    apply t1
    --simp only [contractElem, delete_ground]
    exact subset_diff_singleton hXE e_not_in_x
    --simp only [contractElem, delete_ground]
    exact subset_diff_singleton hYE e_not_in_y

  --The following two sorrys are the easy case by induction I recommend one of you does this 5 sorry
  by_cases hde : M.connBetween X Y ≤ (M ＼ {e}).connBetween X Y

  obtain ⟨n, hN⟩ := use_t2 -- minor N
  obtain ⟨minor, groundset, connectivity⟩ := hN
  have replace_minor_t2 : (n ≤m M ∧ n.E = X ∪ Y ∧ n.conn X = (M ＼ {e}).connBetween X Y) := by
    apply n_del_minor at minor
    exact ⟨minor, ⟨groundset, connectivity⟩⟩

  have equal_connBetween: (M ＼ {e}).connBetween X Y = M.connBetween X Y := by
    exact Nat.le_antisymm minor_delConnBetween hde

  rw [← equal_connBetween]
  · use n -- give minor n as minor of M satisfying conditions

  by_cases hco : M.connBetween X Y ≤ (M ／ {e}).connBetween X Y
  obtain ⟨n, hN⟩ := use_t1 -- minor N
  obtain ⟨minor, groundset, connectivity⟩ := hN
  have replace_minor_t1 : (n ≤m M ∧ n.E = X ∪ Y ∧ n.conn X = (M ／ {e}).connBetween X Y) := by
    apply n_contract_minor at minor
    exact ⟨minor, ⟨groundset, connectivity⟩⟩

  have equal_connBetween: (M ／ {e}).connBetween X Y = M.connBetween X Y := by
    exact Nat.le_antisymm minor_contrConnBetween hco

  rw [← equal_connBetween]
  · use n

  --I recommend someone else does the proof from here until **
  --Here you need to rewrite hde and hco so that you get
  --(M ＼ e).connBetween X Y < M.connBetween X Y  and
  --(M ／ e).connBetween X Y < M.connBetween X Y

  push_neg at hde
  push_neg at hco

  have he_not_in_X : e ∉ X := by
    contrapose! heXY
    exact mem_union_left Y heXY

  have he_not_in_Y : e ∉ Y := by
    contrapose! heXY
    exact mem_union_right X heXY

  --Then you use the partition lemmas to get
  have hpardel : ∃ P : (M ＼ {e}).Partition, P.SepOf X Y ∧
  P.conn = (M ＼ {e}).connBetween X Y := by

    have X_sub_mdel : X ⊆ (M ＼ {e}).E := by
      --rw [@deleteElem, @delete_ground]
      refine subset_diff_singleton hXE ?_
      exact he_not_in_X

    have Y_sub_mdel : Y ⊆ (M ＼ {e}).E := by
      --rw [@deleteElem, @delete_ground]
      refine subset_diff_singleton hYE ?_
      exact he_not_in_Y

    obtain ⟨Q, hQ, hQconn⟩ := exists_partition_conn_eq_connBetween hXY X_sub_mdel Y_sub_mdel
    exact ⟨Q, hQ, hQconn⟩

--  contraction
-- have hparcon : ∃ P : M.Partition, P.SepOf X (insert e Y) ∧ P.conn = (M ／ e).connBetween X Y := by
  have hparcon : ∃ P : (M ／ {e}).Partition, P.SepOf X Y ∧
  P.conn = (M ／ {e}).connBetween X Y := by

    have X_sub_mdel : X ⊆ (M ／ {e}).E := by
     -- rw [@contractElem, @contract_ground]
      refine subset_diff_singleton hXE ?_
      exact he_not_in_X

    have Y_sub_mdel : Y ⊆ (M ／ {e}).E := by
      --rw [@contractElem, @contract_ground]
      refine subset_diff_singleton hYE ?_
      exact he_not_in_Y

    obtain ⟨R, hR, hRconn⟩ := exists_partition_conn_eq_connBetween hXY X_sub_mdel Y_sub_mdel

    exact ⟨R, hR, hRconn⟩

  --Use the tactic obtain and the previous two haves to obtain the sets S and T

  obtain ⟨Pdel, hPdel, hPdel_conn⟩ := hpardel       -- S = Pdel.1
  obtain ⟨Pcon, hPcon, hPcon_conn⟩ := hparcon       -- T = Pcon.2

  -- S = Pdel.1
  -- T = Pcon.2

--Use the tactic obtain and the previous two haves to obtain the sets S and T

  have hS : ∃ S ⊆ M.E \ (insert e Y), X ⊆ S ∧ (M ＼ {e}).conn S ≤ M.connBetween X Y - 1 := by
    have hSY : Pdel.1 ⊆ M.E \ (insert e Y) := by
      rw [@subset_diff]
      apply And.intro
      have hPdel_sub : Pdel.left ⊆ (M ＼ {e}).E := Partition.left_subset_ground Pdel
      have hMeSub : (M ＼ {e}).E ⊆ M.E := by
        --rw [@deleteElem, @delete_ground]
        exact diff_subset
      exact fun ⦃a⦄ a_1 ↦ hMeSub (hPdel_sub a_1)
      refine disjoint_insert_right.mpr ?_
      apply And.intro
      have h_ePdel : Pdel.left ⊆ M.E \ {e} := Partition.left_subset_ground Pdel
      contrapose! h_ePdel
      refine not_subset.mpr ?_
      have h_e : e ∉ M.E \ {e} := notMem_diff_of_mem rfl

      exact ⟨e, h_ePdel , h_e⟩
      exact Partition.SepOf.disjoint_left hPdel

    have hSX : X ⊆ Pdel.left := hPdel.subset_left

    have h_Pdel_left_conn : Pdel.conn = (M ＼ {e}).conn Pdel.1 := by
      have h_Pdel_left_eConn : Pdel.eConn = (M ＼ {e}).eConn Pdel.1 := Partition.eConn_eq_left Pdel
      rw [Partition.conn, conn]
      exact congrArg ENat.toNat h_Pdel_left_eConn

    have hSconn : (M ＼ {e}).conn Pdel.left ≤ M.connBetween X Y - 1 := by
      refine Nat.le_sub_one_of_lt ?_
      rw [← h_Pdel_left_conn, hPdel_conn]
      exact hde
    exact ⟨Pdel.left, hSY, hSX, hSconn⟩

  have hT : ∃ T ⊆ M.E \ (insert e Y), X ⊆ T ∧ (M ／ {e}).conn T ≤ M.connBetween X Y - 1 := by
    have hTY : Pcon.left ⊆ M.E \ (insert e Y) := by
      rw [@subset_diff]
      apply And.intro
      have hPcon_sub : Pcon.left ⊆ (M ／ {e}).E := Partition.left_subset_ground Pcon
      have hMeSub : (M ／ {e}).E ⊆ M.E := by
        --rw [@contractElem, @contract_ground]
        exact diff_subset
      exact fun ⦃a⦄ a_1 ↦ hMeSub (hPcon_sub a_1)
      refine disjoint_insert_right.mpr ?_
      apply And.intro
      have h_ePcon : Pcon.left ⊆ M.E \ {e} := Partition.left_subset_ground Pcon
      contrapose! h_ePcon
      refine not_subset.mpr ?_
      have h_e : e ∉ M.E \ {e} := notMem_diff_of_mem rfl
      exact ⟨e, h_ePcon , h_e⟩
      exact Partition.SepOf.disjoint_left hPcon

    have hTX : X ⊆ Pcon.left := hPcon.subset_left

    have h_Pcon_left_conn : Pcon.conn = (M ／ {e}).conn Pcon.1 := by
      have h_Pcon_left_eConn : Pcon.eConn = (M ／ {e}).eConn Pcon.1 := by
        exact Partition.eConn_eq_left Pcon
      rw [Partition.conn, conn]
      exact congrArg ENat.toNat h_Pcon_left_eConn

    have hTconn : (M ／ {e}).conn Pcon.left ≤ M.connBetween X Y - 1 := by
      refine Nat.le_sub_one_of_lt ?_
      rw [← h_Pcon_left_conn, hPcon_conn]
      exact hco

    exact ⟨Pcon.left, hTY, hTX, hTconn⟩


  --obtain S, T and the corresponding hypotheses
  obtain ⟨S, hSY, hSX, hSconn⟩ := hS
  obtain ⟨T, hTY, hTX, hTconn⟩ := hT


  --obtain S, T and the corresponding hypothesis

  --The last person should finish the proof using lemma Exercise_for_DRP' and linarith to conclude

  --Add a have that uses lemma Exercise_for_DRP' on S and T

  --have heither : M.conn (S ∩ T) ≤ M.connBetween X Y - 1 ∨
  --M.conn (insert e(S ∪ T)) ≤ M.connBetween X Y - 1 := by

  --Use Partition.SepOf.connBetween_le_conn and the case from either to conclude
  --have : M.connBetween X Y ≤ Somthing := by

  --have hend : M.connBetween X Y ≤ M.connBetween X Y - 1 := by sorry

  --sorry
  have h_ST : M.conn (S ∩ T) + M.conn (insert e (S ∪ T))
      ≤ 1 + (M ＼ {e}).conn S + (M ／ {e}).conn T := by
    have he_not_in_S : e ∉ S := by
      contrapose! hSY
      refine not_subset.mpr ?_
      have h_e : e ∉ M.E \ (insert e Y) := by
        simp only [mem_diff, mem_insert_iff, true_or, not_true_eq_false, and_false,
          not_false_eq_true]
     -- sorry
      exact ⟨e, hSY , h_e⟩

    have he_not_in_T : e ∉ T := by
      contrapose! hTY
      refine not_subset.mpr ?_
      have h_e : e ∉ M.E \ (insert e Y) := by
        simp only [mem_diff, mem_insert_iff, true_or, not_true_eq_false, and_false,
          not_false_eq_true]
      exact ⟨e, hTY , h_e⟩

    apply Exercise_for_DRP' M S T e
    exact he_not_in_S
    exact he_not_in_T


  have heither : M.conn (S ∩ T) ≤ M.connBetween X Y - 1 ∨
  M.conn (insert e (S ∪ T)) ≤ M.connBetween X Y - 1 := by
    contrapose! h_ST
    linarith

  have h_ST_subset : (S ∩ T) ⊆ M.E := by
    intro x hx
    have : x ∈ S := hx.1
    have : x ∈ T := hx.2
    -- S is contained in M.E \ Y, which is a subset of M.E
    have hS : S ⊆ M.E := subset_trans hSY (diff_subset)
    -- T is contained in M.E \ Y, which is a subset of M.E
    have hT : T ⊆ M.E := subset_trans hTY (diff_subset)
    exact hS ‹x ∈ S›

  have h_Union_subset : (insert e (S ∪ T)) ⊆ M.E := by
    rw [insert_subset_iff]
    apply And.intro
    · exact heE  -- e ∈ M.E from context
    · apply union_subset
      · exact subset_trans hSY (diff_subset)  -- S ⊆ M.E
      · exact subset_trans hTY (diff_subset)  -- T ⊆ M.E

  set P1 := M.partition (S ∩ T) h_ST_subset
  set P2 := M.partition (insert e (S ∪ T)) h_Union_subset

  have hdisj : Disjoint ((M.E \ {e}) \ Y) Y := disjoint_sdiff_left
  rw [← union_singleton, @union_comm, ← @diff_diff] at hSY
  rw [← union_singleton, @union_comm, ← @diff_diff] at hTY

  have hdisj_YS : Disjoint S Y := disjoint_of_subset hSY (fun ⦃a⦄ a ↦ a) hdisj
  have hdisj_YT : Disjoint T Y := disjoint_of_subset hTY (fun ⦃a⦄ a ↦ a) hdisj


  have hP1 : P1.SepOf X Y := by
    -- First show X is contained in S ∩ T (the left part of partition)
    have hX_subset : X ⊆ S ∩ T := by
      intro x hx
      exact ⟨hSX hx, hTX hx⟩  -- x is in both S and T because X ⊆ S and X ⊆ T
  -- Then show Y is disjoint from S ∩ T
    have hY_disjoint : Disjoint P1.left Y  := by
      rw [@partition_left]
      exact Disjoint.inter_left' S hdisj_YT
-- Combine these using the partition lemma
    rw [Partition.sepOf_iff_left]
    exact ⟨hX_subset, hY_disjoint⟩
    exact hYE

  have hP2 : P2.SepOf X Y := by
  -- P2 is the partition where P2.left = insert e (S ∪ T)
  -- We need to show:
  -- 1. X ⊆ insert e (S ∪ T)
  -- 2. Y ⊆ M.E \ insert e (S ∪ T)

  -- First part: X is in the left side
    have X_in_left : X ⊆ insert e (S ∪ T) := by
      intro x hx
      apply Or.inr         -- Not the 'e' case
      apply Or.inl         -- In the S branch
      exact hSX hx         -- Since X ⊆ S

  -- Second part: Y is in the right side (complement)
    have Y_in_right : Y ⊆ M.E \ insert e (S ∪ T) := by
      intro y hy
      have hym: y ∈ M.E := hYE hy
      have hy_not_in_S: y ∉ S := Disjoint.notMem_of_mem_left (id (Disjoint.symm hdisj_YS)) hy
      have hy_not_in_T: y ∉ T := Disjoint.notMem_of_mem_left (id (Disjoint.symm hdisj_YT)) hy
      have hy_not_in_union: y ∉ insert e (S ∪ T) := by
        simp only [mem_insert_iff, mem_union, not_or]
        apply And.intro
        exact ne_of_mem_of_notMem hy he_not_in_Y
        exact Classical.not_imp.mp fun a ↦ hy_not_in_T (a hy_not_in_S)
      exact mem_diff_of_mem (hYE hy) hy_not_in_union

    exact ⟨X_in_left, Y_in_right⟩

  have h_conn_le_P1 : M.connBetween X Y ≤ P1.conn := Partition.SepOf.connBetween_le_conn hP1
  have h_conn_le_P2 : M.connBetween X Y ≤ P2.conn := Partition.SepOf.connBetween_le_conn hP2


  have hP1_conn : P1.conn = M.conn (S ∩ T) := rfl

  have hP2_conn : P2.conn = M.conn (insert e (S ∪ T)) := rfl

  have h_final : M.connBetween X Y ≤ M.connBetween X Y - 1 := by linarith
  -- have h_final : M.connBetween X Y ≤ M.connBetween X Y - 1 := by linarith


  have hend : M.connBetween X Y < M.connBetween X Y := by
    rw [@Nat.le_iff_lt_add_one] at h_final
    rw [@Nat.sub_add_cancel] at h_final
    exact h_final
    exact Nat.one_le_of_lt hde
  by_contra! hcontradiction
  exact (lt_self_iff_false (M.connBetween X Y)).mp hend
  --exact
  --linarith
termination_by M.E.encard
