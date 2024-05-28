import Matroid.Minor.Rank
import Matroid.Modular

open Set

variable {α : Type*} {M : Matroid α}

namespace Matroid

section ConnectedTo

variable {C K : Set α} {e f g : α}

def ConnectedTo (M : Matroid α) (e f : α) := (e = f ∧ e ∈ M.E) ∨ ∃ C, M.Circuit C ∧ e ∈ C ∧ f ∈ C

lemma ConnectedTo.exists_circuit_of_ne (h : M.ConnectedTo e f) (hne : e ≠ f) :
    ∃ C, M.Circuit C ∧ e ∈ C ∧ f ∈ C := by
  simpa [ConnectedTo, hne] using h

lemma Circuit.mem_connectedTo_mem (hC : M.Circuit C) (heC : e ∈ C) (hfC : f ∈ C) :
    M.ConnectedTo e f :=
  .inr ⟨C, hC, heC, hfC⟩

lemma connectedTo_self (he : e ∈ M.E) : M.ConnectedTo e e :=
    .inl ⟨rfl, he⟩

lemma ConnectedTo.symm (h : M.ConnectedTo e f) : M.ConnectedTo f e := by
  obtain (⟨rfl, hef⟩ | ⟨C, hC, heC, hfC⟩) := h
  · exact connectedTo_self hef
  exact .inr ⟨C, hC, hfC, heC⟩

lemma connectedTo_comm : M.ConnectedTo e f ↔ M.ConnectedTo f e :=
  ⟨ConnectedTo.symm, ConnectedTo.symm⟩

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma ConnectedTo.mem_ground_left (h : M.ConnectedTo e f) : e ∈ M.E := by
  obtain (⟨rfl, hef⟩ | ⟨C, hC, heC, -⟩) := h
  · exact hef
  exact hC.subset_ground heC

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma ConnectedTo.mem_ground_right (h : M.ConnectedTo e f) : f ∈ M.E :=
  h.symm.mem_ground_left

@[simp] lemma connectedTo_self_iff : M.ConnectedTo e e ↔ e ∈ M.E :=
    ⟨fun h ↦ h.mem_ground_left, connectedTo_self⟩

lemma ConnectedTo.nonloop_left_of_ne (h : M.ConnectedTo e f) (hef : e ≠ f) : M.Nonloop e := by
  obtain ⟨C, hC, heC, hfC⟩ := h.exists_circuit_of_ne hef
  exact hC.nonloop_of_mem ⟨e, heC, f, hfC, hef⟩ heC

lemma ConnectedTo.nonloop_right_of_ne (h : M.ConnectedTo e f) (hef : e ≠ f) : M.Nonloop f :=
  h.symm.nonloop_left_of_ne hef.symm

lemma ConnectedTo.to_dual (h : M.ConnectedTo e f) : M✶.ConnectedTo e f := by
  obtain (rfl | hne) := eq_or_ne e f; exact connectedTo_self h.mem_ground_left
  obtain ⟨C, hC, heC, hfC⟩ := h.exists_circuit_of_ne hne
  have hpara : (M ／ (C \ {e,f})).Parallel e f := by
    rw [parallel_iff_circuit hne]
    apply hC.contract_diff_circuit (by simp) (by simp [pair_subset_iff, heC, hfC])
  obtain ⟨B, hB, heB⟩ := hpara.nonloop_left.exists_mem_base
  have hK := fundCocct_cocircuit heB hB
  refine Circuit.mem_connectedTo_mem hK.of_contract.circuit (mem_fundCocct _ _ _) ?_
  exact hpara.mem_cocircuit_of_mem hK (mem_fundCocct _ _ _)

lemma ConnectedTo.of_dual (h : M✶.ConnectedTo e f) : M.ConnectedTo e f := by
  simpa using h.to_dual

@[simp] lemma connectedTo_dual_iff : M✶.ConnectedTo e f ↔ M.ConnectedTo e f :=
  ⟨ConnectedTo.of_dual, ConnectedTo.to_dual⟩

lemma Cocircuit.mem_connectedTo_mem (hK : M.Cocircuit K) (heK : e ∈ K) (hfK : f ∈ K) :
    M.ConnectedTo e f :=
  (hK.circuit.mem_connectedTo_mem heK hfK).of_dual

lemma ConnectedTo.exists_cocircuit_of_ne (h : M.ConnectedTo e f) (hne : e ≠ f) :
    ∃ K, M.Cocircuit K ∧ e ∈ K ∧ f ∈ K :=
  h.to_dual.exists_circuit_of_ne hne

lemma ConnectedTo.of_restrict {R : Set α} (hR : R ⊆ M.E) (hef : (M ↾ R).ConnectedTo e f) :
    M.ConnectedTo e f := by
  obtain (rfl | hne) := eq_or_ne e f
  · simp [hR hef.mem_ground_left]
  obtain ⟨C, hC, heC, hfC⟩ := hef.exists_circuit_of_ne hne
  rw [restrict_circuit_iff] at hC
  exact hC.1.mem_connectedTo_mem heC hfC

lemma ConnectedTo.of_delete {D : Set α} (hef : (M ＼ D).ConnectedTo e f) : M.ConnectedTo e f := by
  rw [delete_eq_restrict] at hef; apply hef.of_restrict <| diff_subset _ _

lemma ConnectedTo.of_contract {C : Set α} (hef : (M ／ C).ConnectedTo e f) : M.ConnectedTo e f := by
  replace hef := hef.to_dual
  rw [contract_dual_eq_dual_delete] at hef
  exact hef.of_delete.of_dual

lemma ConnectedTo.of_minor {N : Matroid α} (hef : N.ConnectedTo e f) (h : N ≤m M) :
    M.ConnectedTo e f := by
  obtain ⟨C, D, -, -, -, rfl⟩ := h; exact hef.of_delete.of_contract

private lemma connectedTo_of_indep_hyperplane_of_not_coloop {I : Set α} (hI : M.Indep I)
    (hI' : M.Hyperplane I) (heI : e ∈ M.E \ I) (hfI : f ∈ I) (hf : ¬ M.Coloop f) :
    M.ConnectedTo e f := by
  have hB : M.Base (insert e I) := by
    refine Indep.base_of_spanning ?_ (hI'.spanning_of_ssuperset (ssubset_insert heI.2))
    · rwa [hI.insert_indep_iff_of_not_mem heI.2, hI'.flat.cl]
  simp only [hB.mem_coloop_iff_forall_not_mem_fundCct (.inr hfI), mem_diff, mem_insert_iff, not_or,
    and_imp, not_forall, Classical.not_imp, not_not, exists_prop, exists_and_left] at hf
  obtain ⟨x, hx, hxe, hxI, hfC⟩ := hf
  have hxi : M.Indep ((insert x I) \ {e}) := by
    rw [diff_singleton_eq_self (by simp [Ne.symm hxe, heI.2]), hI.insert_indep_iff_of_not_mem hxI,
      hI'.flat.cl]
    exact ⟨hx, hxI⟩
  have hC := Base.fundCct_circuit hB (show x ∈ M.E \ insert e I by simp [hx, hxI, hxe])

  refine hC.mem_connectedTo_mem (by_contra fun heC ↦ ?_) hfC

  have hss := subset_diff_singleton (fundCct_subset_insert x (insert e I)) heC
  simp only [insert_comm, mem_singleton_iff, insert_diff_of_mem] at hss
  exact hC.dep.not_indep (hxi.subset hss)

lemma ConnectedTo.trans {e₁ e₂ : α} (h₁ : M.ConnectedTo e₁ f) (h₂ : M.ConnectedTo f e₂) :
    M.ConnectedTo e₁ e₂ := by
  obtain (rfl | hne) := eq_or_ne e₁ e₂
  · simp [h₁.mem_ground_left]
  obtain (rfl | hne₁) := eq_or_ne e₁ f
  · assumption
  obtain (rfl | hne₂) := eq_or_ne f e₂
  · assumption
  obtain ⟨K₁, hK₁, he₁K₁, hfK₁⟩ := h₁.exists_cocircuit_of_ne hne₁
  obtain ⟨C₂, hC₂, hfC₂, he₂C₂⟩ := h₂.exists_circuit_of_ne hne₂

  obtain (he₂K₁ | he₂K₁) := em (e₂ ∈ K₁); exact (hK₁.mem_connectedTo_mem he₁K₁ he₂K₁)

  have hC₂i : M.Indep (C₂ \ K₁) := (hC₂.diff_singleton_indep hfC₂).subset
      (subset_diff_singleton (diff_subset _ _) (by simp [hfK₁]))

  have hH := hK₁.compl_hyperplane

  obtain ⟨J, hJ, he₂J⟩ :=
    hC₂i.subset_basis_of_subset (diff_subset_diff_left hC₂.subset_ground) hH.subset_ground

  refine (connectedTo_of_indep_hyperplane_of_not_coloop ?_
    (hH.basis_hyperplane_delete hJ) ?_ ?_ ?_).of_delete
  · simp [disjoint_sdiff_right, hJ.indep]
  · simpa [h₁.mem_ground_left, he₁K₁] using
      not_mem_subset hJ.subset (by simp [he₁K₁, h₁.mem_ground_left])
  · exact he₂J ⟨he₂C₂, he₂K₁⟩

  refine Circuit.not_coloop_of_mem ?_ he₂C₂
  rwa [delete_circuit_iff, and_iff_right hC₂, disjoint_iff_inter_eq_empty, ← inter_diff_assoc,
    diff_eq_empty, ← inter_diff_assoc, inter_eq_self_of_subset_left hC₂.subset_ground]

def Connected (M : Matroid α) := M.Nonempty ∧ ∀ ⦃e f⦄, e ∈ M.E → f ∈ M.E → M.ConnectedTo e f

lemma Connected.to_dual (hM : M.Connected) : M✶.Connected :=
  ⟨by have := hM.1; apply dual_nonempty, fun _ _ he hf ↦ (hM.2 he hf).to_dual⟩

lemma Connected.of_dual (hM : M✶.Connected) : M.Connected := by
  simpa using hM.to_dual

@[simp] lemma connected_dual_iff : M✶.Connected ↔ M.Connected :=
  ⟨Connected.of_dual, Connected.to_dual⟩

lemma Coloop.not_connected (he : M.Coloop e) (hE : M.E.Nontrivial) : ¬ M.Connected := by
  obtain ⟨f, hfE, hfe⟩ := hE.exists_ne e
  rintro ⟨-, hconn⟩
  obtain ⟨K, hK, heK, -⟩ := (hconn he.mem_ground hfE).exists_circuit_of_ne hfe.symm
  exact he.not_mem_circuit hK heK

lemma Loop.not_connected (he : M.Loop e) (hE : M.E.Nontrivial) : ¬ M.Connected := by
  rw [← connected_dual_iff]
  exact he.dual_coloop.not_connected hE

lemma Connected.exists_circuit_of_ne (h : M.Connected) (he : e ∈ M.E) (hf : f ∈ M.E) (hne : e ≠ f) :
    ∃ C, M.Circuit C ∧ e ∈ C ∧ f ∈ C :=
  (h.2 he hf).exists_circuit_of_ne hne

lemma Connected.exists_circuit (h : M.Connected) (hM : M.E.Nontrivial) (he : e ∈ M.E)
    (hf : f ∈ M.E) : ∃ C, M.Circuit C ∧ e ∈ C ∧ f ∈ C := by
  obtain (rfl | hne) := eq_or_ne e f
  · obtain (he' | he') := em (M.Coloop e)
    · exact False.elim <| he'.not_connected hM h
    obtain ⟨C, hC, heC⟩ := exists_mem_circuit_of_not_coloop he he'
    exact ⟨C, hC, heC, heC⟩
  exact (h.2 he hf).exists_circuit_of_ne hne

lemma singleton_connected (hM : M.E = {e}) : M.Connected :=
  ⟨⟨by simp [hM]⟩, by simp [hM]⟩

lemma not_connected_iff_exists_separation (M : Matroid α) [M.Nonempty] :
    ¬ M.Connected ↔ ∃ (A B : Set α),
      A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ A ∪ B = M.E ∧ M.Skew A B := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · simp only [Connected, (show M.Nonempty by assumption), true_and, not_forall, Classical.not_imp,
    exists_and_left] at h
    obtain ⟨e, f, he, hf, hef⟩ := h
    set A := {x | M.ConnectedTo e x} with hA_def
    have hA : A ⊆ M.E := fun y hy ↦ hy.mem_ground_right
    refine ⟨A, M.E \ A, ⟨e, by simpa [hA_def]⟩, ⟨f, by simp [hA_def, hef, hf]⟩,
      disjoint_sdiff_right, by simpa, ?_⟩

    rw [skew_iff_forall_circuit hA (diff_subset _ _) disjoint_sdiff_right]
    rintro C hC -
    by_contra! hcon
    simp only [hA_def, not_subset, mem_setOf_eq, mem_diff, not_and, not_not] at hcon
    obtain ⟨⟨a, haC, hec⟩, ⟨b, hbC, hb⟩⟩ := hcon
    exact hec <| (hb (hC.subset_ground hbC)).trans (hC.mem_connectedTo_mem hbC haC)
  rintro ⟨A, B, ⟨a, ha⟩, ⟨b, hb⟩, hdj, hU, hAB⟩ h
  have hAE := (subset_union_left _ _).trans hU.subset
  have hBE := (subset_union_right _ _).trans hU.subset

  rw [skew_iff_forall_circuit hAE hBE hdj] at hAB
  obtain ⟨C, hC, haC, hbC⟩ := h.exists_circuit_of_ne (hAE ha) (hBE hb) (hdj.ne_of_mem ha hb)
  obtain (h' | h') := hAB C hC (hC.subset_ground.trans_eq hU.symm)
  · exact disjoint_left.1 hdj (h' hbC) hb
  exact disjoint_right.1 hdj (h' haC) ha

end ConnectedTo

section Conn

variable {B B' I I' J X Y : Set α}

lemma Base.encard_compl_eq (hB : M.Base B) : (M.E \ B).encard = M✶.erk :=
  (hB.compl_base_dual).encard

lemma Basis.erk_dual_restrict (hB : M.Basis I (I ∪ X)) (hdj : Disjoint I X) :
    (M ↾ (I ∪ X))✶.erk = X.encard := by
  rw [← Base.encard_compl_eq hB.restrict_base]; simp [hdj.sdiff_eq_right]

lemma Indep.contract_er_dual_eq (hI : M.Indep I) : (M ／ I)✶.erk = M✶.erk := by
  rw [contract_dual_eq_dual_delete, hI.coindep.delete_erk_eq]

lemma Basis.encard_dual_switch_eq (hI : M.Basis I X) (hI' : M.Basis I' X) (hJ : M.Indep J)
    (hXJ : Disjoint X J) : (M ↾ (I ∪ J))✶.erk = (M ↾ (I' ∪ J))✶.erk := by

  obtain ⟨K, hK, hIK⟩ := hI.indep.subset_basis_of_subset (subset_union_left I J)
  have hsk := (hK.indep.subset_skew_diff hIK).cl_skew
  rw [hI.cl_eq_cl, ← skew_iff_cl_skew hI.subset_ground
    ((diff_subset _ _).trans hK.indep.subset_ground)] at hsk
  have' hdj := hsk.disjoint_of_indep_subset_right (hK.indep.diff _) Subset.rfl
  have hb : ∀ B, M.Basis B X → (M ／ (K \ I)).Basis B (B ∪ J \ (K \ I)) := by
    refine fun B hB ↦ Indep.basis_of_subset_of_subset_cl ?_ ?_ ?_
    · rw [(hK.indep.diff _).contract_indep_iff]
      exact ⟨hXJ.mono hB.subset (by simpa using hK.subset),
        hsk.union_indep_of_indep_subsets hB.indep hB.subset (hK.indep.diff _) Subset.rfl⟩
    · exact subset_union_left _ _
    simp only [contract_cl_eq, subset_diff, disjoint_union_left]
    have hcl : M.cl (B ∪ (K \ I)) = M.cl (X ∪ J) := by
      rw [← M.cl_union_cl_left_eq, hB.cl_eq_cl, ← hI.cl_eq_cl, M.cl_union_cl_left_eq,
        union_diff_self, union_eq_self_of_subset_left hIK, hK.cl_eq_cl, ← M.cl_union_cl_left_eq,
        hI.cl_eq_cl, M.cl_union_cl_left_eq]
    rw [hcl, and_iff_left disjoint_sdiff_left, and_iff_left (hdj.mono_left hB.subset)]
    exact (union_subset_union hB.subset (diff_subset _ _)).trans (M.subset_cl _)

  have hind : ∀ Y, (M ↾ (Y ∪ J)).Indep (K \ I) := by
    intro Y
    rw [restrict_indep_iff, and_iff_right (hK.indep.diff I), diff_subset_iff, union_comm Y,
      ← union_assoc]
    exact hK.subset.trans (subset_union_left _ _)

  rw [← (hind I).contract_er_dual_eq, ← (hind I').contract_er_dual_eq,
    restrict_contract_eq_contract_restrict, restrict_contract_eq_contract_restrict,
    union_diff_distrib, sdiff_eq_left.2 disjoint_sdiff_right,
    union_diff_distrib, (sdiff_eq_left (x := I')).2, (hb _ hI).erk_dual_restrict,
    (hb _ hI').erk_dual_restrict]
  · exact hXJ.mono hI'.subset (diff_subset _ _)
  · exact hXJ.mono hI.subset (diff_subset _ _)
  · exact hdj.mono_left hI'.subset
  · rw [diff_subset_iff, union_comm I', ← union_assoc]
    exact hK.subset.trans <| subset_union_left _ _
  simpa [diff_subset_iff, ← union_assoc] using hK.subset

lemma encard_dual_switch_switch_eq {I I' J J' X Y : Set α} (hdj : Disjoint X Y)
    (hI : M.Basis I X) (hI' : M.Basis I' X) (hJ : M.Basis J Y) (hJ' : M.Basis J' Y) :
    (M ↾ (I ∪ J))✶.erk = (M ↾ (I' ∪ J'))✶.erk := by
  rw [hI.encard_dual_switch_eq hI' hJ.indep (hdj.mono_right hJ.subset), union_comm,
    hJ.encard_dual_switch_eq hJ' hI'.indep (hdj.symm.mono_right hI'.subset), union_comm]

lemma encard_dual_switch_switch_eq' {I I' J J' X Y : Set α} (hdj : Disjoint X Y)
    (hI : M.Basis' I X) (hI' : M.Basis' I' X) (hJ : M.Basis' J Y) (hJ' : M.Basis' J' Y) :
    (M ↾ (I ∪ J))✶.erk = (M ↾ (I' ∪ J'))✶.erk := by
  rw [basis'_iff_basis_inter_ground] at hI hI' hJ hJ'
  exact encard_dual_switch_switch_eq (hdj.mono (inter_subset_left _ _) (inter_subset_left _ _))
    hI hI' hJ hJ'

noncomputable def localConn (M : Matroid α) (X Y : Set α) : ℕ∞ :=
  let BX := ((M ／ (X ∩ Y)).exists_basis' (X \ Y)).choose
  let BY := ((M ／ (X ∩ Y)).exists_basis' (Y \ X)).choose
  M.er (X ∩ Y) + ((M ／ (X ∩ Y)) ↾ (BX ∪ BY))✶.erk

lemma localConn_eq_of_basis'_basis' (hI : (M ／ (X ∩ Y)).Basis' I (X \ Y))
    (hJ : (M ／ (X ∩ Y)).Basis' J (Y \ X)) :
    M.localConn X Y = M.er (X ∩ Y) + ((M ／ (X ∩ Y)) ↾ (I ∪ J))✶.erk := by
  simp_rw [localConn]
  set M' := M ／ (X ∩ Y)
  have h1 := M'.exists_basis' (X \ Y)
  have h2 := M'.exists_basis' (Y \ X)
  set BX := h1.choose
  set BY := h2.choose
  rw [encard_dual_switch_switch_eq' disjoint_sdiff_sdiff hI h1.choose_spec hJ h2.choose_spec]

lemma er_add_er_eq_er_union_add_dual_er (hdj : Disjoint X Y) (hI : M.Basis' I X)
    (hJ : M.Basis' J Y) : M.er X + M.er Y = M.er (X ∪ Y) + (M ↾ (I ∪ J))✶.erk := by
  obtain ⟨B, hB⟩ := M.exists_basis' (I ∪ J)
  have hB' : M.Basis' B (X ∪ Y) := by
    rw [basis'_iff_basis_cl, ← cl_cl_union_cl_eq_cl_union, ← hI.cl_eq_cl, ← hJ.cl_eq_cl,
      cl_cl_union_cl_eq_cl_union, ← hB.cl_eq_cl]
    exact ⟨hB.indep.basis_cl, hB.subset.trans (union_subset_union hI.subset hJ.subset)⟩

  rw [← (base_restrict_iff'.2 hB).encard_compl_eq, restrict_ground_eq, ← hI.encard, ← hJ.encard,
    ← hB'.encard, add_comm B.encard, encard_diff_add_encard_of_subset hB.subset,
    encard_union_eq (hdj.mono hI.subset hJ.subset)]

lemma er_add_er_eq_er_union_add_localConn (M : Matroid α) (X Y : Set α) :
    M.er X + M.er Y = M.er (X ∪ Y) + M.localConn X Y := by
  set M' := M ／ (X ∩ Y) with hM'
  obtain ⟨BX, hBX⟩ := M'.exists_basis' (X \ Y)
  obtain ⟨BY, hBY⟩ := M'.exists_basis' (Y \ X)
  have hui : (X ∪ Y) \ (X ∩ Y) = (X \ Y) ∪ (Y \ X) := by ext; aesop
  have hrw : ∀ Z, X ∩ Y ⊆ Z  → M.er Z = M'.er (Z \ (X ∩ Y)) + M.er (X ∩ Y) := by
    intro Z hZ
    rwa [hM', ← relRank_eq_er_contract, ← relRank_eq_diff_right, ← relRank_add_er_of_subset]
  rw [localConn_eq_of_basis'_basis' hBX hBY, hrw X (inter_subset_left _ _),
    hrw Y (inter_subset_right _ _ ), hrw _ ((inter_subset_left _ _).trans (subset_union_left _ _) ),
    diff_self_inter, diff_inter_self_eq_diff, add_right_comm, ← add_assoc,
    er_add_er_eq_er_union_add_dual_er disjoint_sdiff_sdiff hBX hBY, ← hM', hui]
  ac_rfl

lemma localConn_cl_left (M : Matroid α) (X Y : Set α) :
    M.localConn X Y = M.localConn (M.cl X) Y := by
  obtain ⟨I, hI⟩ := (M ／ (X ∩ Y)).exists_basis' (X \ Y)
  obtain ⟨J, hJ⟩ := (M ／ (X ∩ Y)).exists_basis' (Y \ X)
  rw [localConn_eq_of_basis'_basis' hI hJ, localConn_eq_of_basis'_basis' (I := I) (J := J),
    contract_restrict_eq_restrict_contract, contract_restrict_eq_restrict_contract,
    er_union_cl_left_eq]

lemma localConn_diff_loops_left (M : Matroid α) (X Y : Set α) :
    M.localConn X Y = M.localConn (X ∪ M.cl ∅) Y := by
  obtain ⟨I, hI⟩ := (M ／ (X ∩ Y)).exists_basis' (X \ Y)
  obtain ⟨J, hJ⟩ := (M ／ (X ∩ Y)).exists_basis' (Y \ X)
  -- have hrw : M ／ (X \ M.cl ∅ ∩ Y) = M ／ (X ∩ Y) ＼ M.cl ∅ := by
  --   rw [← contract_eq_delete_of_subset_loops, contract_contract]
  rw [localConn_eq_of_basis'_basis' hI hJ, localConn_eq_of_basis'_basis' (I := I) (J := J),
    union_inter_distrib_right, er_eq_er_union_er_le_zero, ← contract_contract,
    contract_eq_delete_of_subset_loops (X := M.cl ∅ ∩ Y), delete_eq_restrict (D := M.cl ∅ ∩ Y)]

lemma localConn_eq_zero (M : Matroid α) (hX : X ⊆ M.E) (hY : Y ⊆ M.E) :
    M.localConn X Y = 0 ↔ M.Skew X Y := by
  obtain ⟨I, hI⟩ := (M ／ (X ∩ Y)).exists_basis' (X \ Y)
  obtain ⟨J, hJ⟩ := (M ／ (X ∩ Y)).exists_basis' (Y \ X)
  rw [localConn_eq_of_basis'_basis' hI hJ, add_eq_zero_iff, erk_eq_zero_iff, dual_ground,
    restrict_ground_eq, eq_loopyOn_iff]
  simp only [dual_ground, restrict_ground_eq, true_and]
  rw [skew_iff_exist_bases]
  refine ⟨fun ⟨h0, h⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [er_eq_zero_iff ((inter_subset_left _ _).trans hX)] at h0
    simp_rw [contract_eq_delete_of_subset_loops h0] at *
    rw [delete_basis'_iff, diff_diff, union_eq_self_of_subset_right (inter_subset_right _ _)] at hI
    rw [delete_basis'_iff, diff_diff, union_eq_self_of_subset_right (inter_subset_left _ _)] at hJ

end Conn
