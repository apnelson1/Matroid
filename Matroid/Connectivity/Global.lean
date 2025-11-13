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


lemma aux {P Q X : Set α} :
    Monotone (fun N : Matroid α ↦ (N ／ X).eConn P + (N ＼ X).eConn Q + N.eConn X) := by
  rintro N M (hNM : N ≤m M)
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := hNM.exists_eq_contract_delete_disjoint

  simp only
  have hrw1 : M ／ C ＼ D ／ X = M ／ (X \ D) ＼ (X ∩ D) ／ (C \ X) ＼ (D \ X) := by
    rw [eq_comm, ← contract_delete_comm _ (by tauto_set), delete_delete, inter_comm X,
      inter_union_diff, contract_contract, delete_contract_comm', contract_contract,
      show X \ D ∪ C \ X = C ∪ X \ D by tauto_set]
  have hrw2 : M ／ C ＼ D ＼ X = M ＼ (X \ C) ／ (X ∩ C) ／ (C \ X) ＼ (D \ X) := by
    rw [eq_comm, contract_contract, inter_comm, inter_union_diff,
      ← contract_delete_comm _ disjoint_sdiff_right, delete_delete, delete_delete,
      contract_delete_comm' (D := D ∪ X), ← contract_delete_comm _ disjoint_sdiff_right,
      show X \ C ∪ D \ X = (D ∪ X) \ C by tauto_set]
  grw [hrw1, (contract_delete_isMinor ..).eConn_le,
    hrw2, (contract_delete_isMinor _ (C \ X) _).eConn_le,
    eConn_delete_le_eConn_contract_add, contract_contract, diff_union_inter,
    (M ＼ _).eConn_contract_le_eConn_delete_add, delete_delete, diff_union_inter,
    add_right_comm (a := (M ／ X).eConn P), add_assoc, add_assoc, add_assoc, add_assoc,
    add_le_add_left, add_le_add_left]
  · rfl
  grw [add_le_add_left]

  convert rfl.le

  -- nth_rw 1 [← diff_union_inter X C, union_comm,
  --   eConn_union_eq_eConn_contract_add_eConn_delete _ disjoint_sdiff_inter.symm, add_comm]
  -- nth_rw 2 [show X \ C = (X \ C) ]

  -- rw [show M.eConn X = M.eConn ((X ∩ C) ∪ (X \ C)) from sorry,
  --   eConn_union_eq_eConn_contract_add_eConn_delete _ sorry, add_comm]

  -- set g := (fun (X : Set α) (N : Matroid α) ↦ (N ／ X).eConn P + (N ＼ X).eConn Q + N.eConn X)
  -- have hg (X : Set α) (N : Matroid α) : g X N = (N ／ X).eConn P + (N ＼ X).eConn Q + N.eConn X :=
  --   rfl
  -- suffices hXE {N M : Matroid α} (hNM : N ≤m M) {X : Set α} : X ⊆ M.E → g X N ≤ g X M
  -- · refine fun N M (hNM : N ≤m M) ↦ ?_
  --   simp only [← contract_inter_ground_eq _ (C := X), ← delete_inter_ground_eq _ (D := X),
  --     ← eConn_inter_ground (X := X)]
  --   simp only [hg] at hXE
  --   grw [← hXE hNM inter_subset_right, ← N.eConn_inter_ground (X ∩ M.E),
  --     ← N.contract_inter_ground_eq (X ∩ M.E), ← N.delete_inter_ground_eq (X ∩ M.E),
  --     inter_assoc, inter_eq_self_of_subset_right hNM.subset]
  -- intro hXE
  -- suffices h {C D : Set α} {N : Matroid α} (hXN : X ⊆ N.E) (hCX : C ⊆ X) (hDX : D ⊆ X)
  --     (hdj : Disjoint C D) : g X (N ／ C ＼ D) ≤ g X N
  -- ·
  --   -- intro N M (hNM : N ≤m M)
  --   obtain ⟨C', D', hC', hD', hC'D, rfl⟩ := hNM.exists_eq_contract_delete_disjoint
  --   have hrw : M ／ C' ＼ D' = M ／ (C' \ X) ＼ (D' \ X) ／ (C' ∩ X) ＼ (D' ∩ X) := sorry
  --   have hss : X ⊆ (M ／ (C' \ X) ＼ (D' \ X)).E := by
  --     rw [delete_ground, contract_ground]; tauto_set
  --   -- simp_rw [hrw]
  --   specialize h (C := C' ∩ X) (D := D' ∩ X) hss
  --     inter_subset_right inter_subset_right (by tauto_set)
  --   grw [hrw, h, hg]
  --   grw [(IsMinor.contract_isMinor_contract (M.contract_delete_isMinor ..) hss).eConn_le P,
  --     (IsMinor.delete_isMinor_delete (M.contract_delete_isMinor ..) hss).eConn_le Q,
  --     (M.contract_delete_isMinor ..).eConn_le]

  -- -- rw [hg, delete_delete, union_eq_self_of_subset_left hDX, hg]
  -- set Y := X \ (C ∪ D) with hY
  -- have hYC : Disjoint Y C := by tauto_set
  -- have hYD : Disjoint Y D := by tauto_set
  -- have hXY : X ∩ ((N.E \ C) \ D) = Y := by sorry
  -- have hXN : X ∩ N.E = C ∪ D ∪ Y := sorry
  -- simp only [hg, ← contract_inter_ground_eq (C := X), ← delete_inter_ground_eq (D := X),
  --   ← eConn_inter_ground (X := X), delete_ground, contract_ground, hXY, hXN]
  -- rw [union_assoc, eConn_union_eq_eConn_contract_add_eConn_delete _
  --   (disjoint_union_right.2 ⟨hdj, hYC.symm⟩), union_comm D,
  --   eConn_union_eq_eConn_contract_add_eConn_delete _ hYD,
  --   ← contract_delete_comm _ hYD, ← contract_contract, ← contract_contract,
  --   delete_delete, contract_delete_comm _ (disjoint_union_right.2 ⟨hdj, hYC.symm⟩), union_comm D,
  --   union_comm C, ← delete_delete (D₂ := C), contract_contract]
  -- grw [eConn_contract_le_eConn_delete_add, eConn_delete_le_eConn_contract_add]
    -- grw [eConn_delete_le, eConn_le_eConn_contract_add_eConn_of_disjoint, ← eConn_inter_ground]
  -- rw [hg, ← contract_inter_ground_eq,  delete_ground, contract_ground, hXY, ]
  -- have hrw := N.eConn_eq_eConn_contract_subset_add hCX
  -- rw [(N ／ C).eConn_eq_eConn_delete_subset_add (subset_diff.2 ⟨hDX, hdj.symm⟩)] at hrw
  -- simp at hrw

  -- wlog hX : X = C ∪ D generalizing N X with aux'
  -- · rw [hg]
  --   have

    -- grw [← h hXE (C := C' ∩ X) (D := D' ∩ X) inter_subset_right inter_subset_right sorry]

    -- grw [hrw, h hXE inter_subset_right inter_subset_right sorry, hg]


  -- set g := fun (P Q )

  -- revert P Q

  intro N M (hNM : N ≤m M)
  simp only


theorem eConn_inter_add_eConn_union_le_conn_contract_add_eConn_delete_add_econn
    (M : Matroid α) {C D X : Set α} (hC : Disjoint C X) (hXD : Disjoint D X) :
    M.eConn (C ∩ D) + M.eConn (X ∪ C ∪ D) ≤ (M ／ X).eConn C + (M ＼ X).eConn D + M.eConn X := by
  by_contra! hlt
  set g := fun (N : Matroid α) ↦ (N ／ X).eConn C + (N ＼ X).eConn D + N.eConn X with hg
  set A := fun b ↦ bif b then C ∩ D else X ∪ C ∪ D
  have hg : Monotone g := by
    -- have hD (N : Matroid α) (Z : Set α) : (N ＼ Z ／ X).eConn C + (N \ Z ＼ X).eConn Q
    suffices hdel : ∀ P Q N Z, (N ＼ Z ／ X).eConn P + (N ＼ Z ＼ X).eConn Q +
      max ((N ＼ Z).eConn X) ((N ／ Z).eConn X) ≤
      (N ／ X).eConn P + (N ＼ X).eConn Q + N.eConn X
    · rintro M₀ M₁ ⟨A, B, rfl⟩
      simp_rw [g]
      -- have := le_max_left ((M₁ ／ A ＼ B).eConn X) ((M₁ ／ A ／ B).eConn X)
      grw [le_max_left ((M₁ ／ A ＼ B).eConn X) ((M₁ ／ A ／ B).eConn X), hdel C D (M₁ ／ A) B]
      have aux := hdel D C M₁✶ A
      grw [← dual_contract_delete, eConn_dual, add_comm (eConn ..), ← le_max_left,
        add_comm ((M₁✶ ／ X).eConn ..)] at aux
      simp_rw [← dual_delete, ← dual_contract, eConn_dual] at aux
      assumption
    intro P Q N Z
    rw [delete_contract_comm', show N ／ X = N ／ (X \ Z) ／ (X ∩ Z) from sorry]
    -- intro M₀ M₁ (hle : M₀ ≤m M₁)

    -- -- obtain ⟨P, Q, hP, hQ, hPQ, rfl⟩ := hle.exists_eq_contract_delete_disjoint

    -- simp_rw [hg, ← contract_inter_ground_eq (C := X)]
    -- rw [← contract_inter_ground_eq]
    -- have := inter_union_diff X M₀.E


    -- wlog hXE : X ⊆ M₁.E with aux1


  -- have hlt : g M < ∑ i, M.eConn (A i) := by simpa [A]
  obtain ⟨N, hNM, hNfin, hN⟩ := M.exists_finite_counterexample_of_lt_sum_eConn g hg A (by simpa)





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
