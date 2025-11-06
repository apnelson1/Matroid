import Matroid.Connectivity.Local
import Matroid.Connectivity.Basic
import Matroid.Minor.Order

open Set

namespace Matroid

variable {α : Type*} {M : Matroid α} {e f x y : α} {X Y I J C D : Set α}

lemma eLocalConn_delete_le (M : Matroid α) : (M ＼ D).eLocalConn X Y ≤ M.eLocalConn X Y := by
  rw [eLocalConn_delete_eq]
  exact M.eLocalConn_mono diff_subset diff_subset

lemma eLocalConn_project_eq_eLocalConn_contract_diff (M : Matroid α) (X Y C : Set α) :
    (M.project C).eLocalConn X Y = (M ／ C).eLocalConn (X \ C) (Y \ C) := by
  rw [project, eLocalConn_restrict_eq, ← eLocalConn_inter_ground, eq_comm,
    ← eLocalConn_inter_ground, contract_ground]
  convert rfl using 2 <;> tauto_set

lemma eLocalConn_project_eq_eLocalConn_contract (M : Matroid α) (X Y C : Set α) :
    (M.project C).eLocalConn X Y = (M ／ C).eLocalConn X Y := by
  rw [project, eLocalConn_restrict_eq, ← eLocalConn_inter_ground, eq_comm,
    ← eLocalConn_inter_ground, contract_ground]
  convert rfl using 2 <;> tauto_set

lemma eLocalConn_contract_le_add (M : Matroid α) (X Y C : Set α) :
    (M ／ C).eLocalConn X Y ≤ M.eLocalConn X Y + M.eRk C := by
  grw [eLocalConn_eq_multiConn, ← multiConn_project_eq_multiConn_contract,
    multiConn_project_le_multiConn_add, eLocalConn_eq_multiConn]

lemma eLocalConn_project_le_add (M : Matroid α) (X Y C : Set α) :
    (M.project C).eLocalConn X Y ≤ M.eLocalConn X Y + M.eRk C := by
  grw [eLocalConn_project_eq_eLocalConn_contract, eLocalConn_contract_le_add]

-- lemma eLocalConn_le_eLocalConn_project_add (M : Matroid α) (X Y C : Set α) :
--     M.eLocalConn X Y ≤ (M.project C).eLocalConn X Y + M.eRk C := by
--   rw [eLocalConn_eq_multiConn, eLocalConn_eq_multiConn]
--   have := M.multiConn_le_

lemma eConn_delete_eq {X D : Set α} (hDX : D ⊆ X) (hX : X ⊆ M.closure (X \ D)) :
    (M ＼ D).eConn (X \ D) = M.eConn X := by
  have hXE : X ⊆ M.E := hX.trans <| closure_subset_ground ..
  obtain ⟨I, hI⟩ := (M ＼ D).exists_isBasis (X \ D) (diff_subset_diff_left hXE)
  obtain ⟨J, hJ⟩ := (M ＼ D).exists_isBasis ((M ＼ D).E \ (X \ D)) diff_subset
  rw [hI.eConn_eq hJ, nullity_delete]
  · rw [delete_isBasis_iff, delete_ground, diff_diff, union_diff_cancel hDX] at hJ
    rw [delete_isBasis_iff] at hI
    rw [(hI.1.isBasis_closure_right.isBasis_subset (hI.1.subset.trans diff_subset) hX).eConn_eq
      hJ.1]
  rw [disjoint_union_left]
  exact ⟨(subset_diff.1 hI.subset).2, (subset_diff.1 (hJ.subset.trans diff_subset)).2⟩

lemma IsBasis'.eConn_delete_diff_eq (hIX : M.IsBasis' I X) : (M ＼ (X \ I)).eConn I = M.eConn X := by
  wlog hX : X ⊆ M.E generalizing X with aux
  · rw [← M.eConn_inter_ground, ← aux hIX.isBasis_inter_ground.isBasis' inter_subset_right,
      ← delete_inter_ground_eq, ← inter_diff_right_comm]
  rw [← M.eConn_delete_eq (show X \ I ⊆ X from diff_subset), diff_diff_cancel_left hIX.subset]
  rw [diff_diff_cancel_left hIX.subset]
  exact hIX.isBasis.subset_closure

lemma IsBasis.eConn_delete_diff_eq (hIX : M.IsBasis I X) : (M ＼ (X \ I)).eConn I = M.eConn X :=
  hIX.isBasis'.eConn_delete_diff_eq

lemma eConn_restrict_le (M : Matroid α) (X R : Set α) : (M ↾ R).eConn X ≤ M.eConn X := by
  rw [eConn_eq_eLocalConn, eLocalConn_restrict_eq, eConn_eq_eLocalConn, restrict_ground_eq,
    ← eLocalConn_inter_ground_right]
  exact M.eLocalConn_mono inter_subset_left (by tauto_set)

lemma eConn_delete_le (M : Matroid α) (X D : Set α) : (M ＼ D).eConn X ≤ M.eConn X := by
  rw [delete_eq_restrict]
  apply eConn_restrict_le

lemma eConn_contract_le (M : Matroid α) (X C : Set α) : (M ／ C).eConn X ≤ M.eConn X := by
  rw [← eConn_dual, dual_contract, ← M.eConn_dual]
  apply eConn_delete_le

lemma IsMinor.eConn_le {N : Matroid α} (hNM : N ≤m M) (X : Set α) : N.eConn X ≤ M.eConn X := by
  obtain ⟨C, D, -, -, -, rfl⟩ := hNM
  exact ((M ／ C).eConn_delete_le X D).trans <| M.eConn_contract_le X C

/-- Contracting a subset of `Y` that is skew to `X` doesn't change the local connectivity
between `X` and `Y`. -/
lemma eLocalConn_contract_right_skew_left' {C Y : Set α} (hXC : M.Skew X C) (hCY : C ⊆ Y) :
    (M ／ C).eLocalConn X (Y \ C) = M.eLocalConn X Y := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  have hI' : (M ／ C).IsBasis' I X := by
    have hI' := hI.isBase_restrict.isBasis_ground.isBasis'
    rwa [← hXC.symm.contract_restrict_eq, restrict_ground_eq, isBasis'_restrict_iff, inter_self,
      and_iff_left hI.subset] at hI'
  rw [hI.eLocalConn_eq_nullity_project_right, hI'.eLocalConn_eq_nullity_project_right,
    nullity_project_eq_nullity_contract, contract_contract, union_diff_cancel hCY,
    nullity_project_eq_nullity_contract]

lemma eLocalConn_contract_skew_union {C : Set α} (h : M.Skew (X ∪ Y) C) :
    (M ／ C).eLocalConn X Y = M.eLocalConn X Y := by
  rw [← (M ／ C).eLocalConn_restrict_of_subset subset_union_left subset_union_right,
    h.symm.contract_restrict_eq,
    eLocalConn_restrict_of_subset _ subset_union_left subset_union_right]

/-- Probably true for `eConn` as well -/
theorem conn_inter_add_conn_union_le_conn_contract_add_conn_delete_add_conn
    (M : Matroid α) [M.RankFinite] {C D X : Set α} (hC : Disjoint C X) (hXD : Disjoint D X) :
    M.conn (C ∩ D) + M.conn (X ∪ C ∪ D) ≤ (M ／ X).conn C + (M ＼ X).conn D + M.conn X := by
  have hsm1 := M.rk_submod (M.E \ C) (M.E \ (X ∪ D))
  have hsm2 := M.rk_submod (C ∪ X) D
  zify at *
  simp only [intCast_conn_eq, contract_rk_cast_int_eq, contract_ground, contract_rank_cast_int_eq,
    delete_ground]
  rw [diff_diff_comm, diff_union_self, ← M.rk_inter_ground (M.E \ C ∪ X), union_inter_distrib_right,
    inter_eq_self_of_subset_left diff_subset,
    union_eq_self_of_subset_right (t := X ∩ M.E) (by tauto_set),
    diff_diff, delete_rk_eq_of_disjoint M hXD, delete_rk_eq_of_disjoint _ (by tauto_set),
    ← (M ＼ X).rk_ground, delete_ground, delete_rk_eq_of_disjoint _ disjoint_sdiff_left]
  rw [diff_inter_diff, union_comm, union_right_comm, ← diff_inter, inter_union_distrib_left,
    hC.inter_eq, empty_union] at hsm1
  rw [union_inter_distrib_right, hXD.symm.inter_eq, union_empty, union_right_comm, union_comm,
    ← union_assoc] at hsm2
  linarith

theorem bixbyCoullard_elem [M.RankFinite] {e : α} (C D : Set α) (heC : e ∉ C) (heD : e ∉ D) :
    M.conn (C ∩ D) + M.conn (insert e (C ∪ D)) ≤ (M ／ {e}).conn C + (M ＼ {e}).conn D + 1 := by
  grw [← singleton_union, ← union_assoc,
    M.conn_inter_add_conn_union_le_conn_contract_add_conn_delete_add_conn (by simpa) (by simpa),
    add_le_add_iff_left, conn_le_ncard _ (by simp), ncard_singleton]


section Connectedness

lemma ConnectedTo.delete_or_contract (hM : M.ConnectedTo x y) (hxe : x ≠ e) (hye : y ≠ e) :
    (M ＼ {e}).ConnectedTo x y ∨ (M ／ {e}).ConnectedTo x y := by
  obtain rfl | hne := eq_or_ne x y
  · simp  [hxe, hM.mem_ground_left]
  suffices (∀ C, M.IsCircuit C → e ∉ C → x ∈ C → y ∉ C) →
    ∃ C, (M ／ {e}).IsCircuit C ∧ x ∈ C ∧ y ∈ C by
    simpa [ConnectedTo, hne, or_iff_not_imp_left]
  intro h
  obtain ⟨C, hC, hxC, hyC⟩ := hM.exists_isCircuit_of_ne hne
  have heC : e ∈ C := by
    contrapose hyC
    exact h C hC hyC hxC
  refine ⟨C \ {e}, ?_, by simpa [hxe], by simpa [hye]⟩
  exact hC.contractElem_isCircuit (nontrivial_of_mem_mem_ne hxC hyC hne) heC

theorem Connected.delete_or_contract (hM : M.Connected) (hnt : M.E.Nontrivial) (e : α) :
    (M ＼ {e}).Connected ∨ (M ／ {e}).Connected := by

  simp only [connected_iff, ← ground_nonempty_iff, delete_ground, Set.mem_diff,
    Set.mem_singleton_iff, and_imp, contract_ground, or_iff_not_imp_left, not_forall,
    exists_and_left, exists_prop, true_and, show (M.E \ { e }).Nonempty from hnt.exists_ne e,
    forall_exists_index, and_imp]

  intro f g hge hgE hfe hfE hnc x y hx hxe hy hye

  have hcon := ((hM.connectedTo f g).delete_or_contract hfe hge).resolve_left hnc

  have h' : ∀ z ∈ M.E, z ≠ e → (M ／ {e}).ConnectedTo z f ∨ (M ／ {e}).ConnectedTo z g := by
    refine fun z hz hze ↦ ?_
    contrapose! hnc
    have hzf := ((hM.connectedTo z f).delete_or_contract hze hfe).resolve_right hnc.1
    have hzg := ((hM.connectedTo z g).delete_or_contract hze hge).resolve_right hnc.2
    exact hzf.symm.trans hzg

  have h'' : ∀ z ∈ M.E, z ≠ e → (M ／ {e}).ConnectedTo z f :=
    fun z hz hze ↦ (h' z hz hze).elim id fun hzg ↦ hzg.trans hcon.symm

  exact (h'' x hx hxe).trans (h'' y hy hye).symm

end Connectedness
