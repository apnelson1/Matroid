import Matroid.Minor.Rank
import Matroid.Modular

open Set

variable {α : Type*} {M : Matroid α}

------------ For mathlib

@[simp] lemma ENat.lt_one_iff (n : ℕ∞) : n < 1 ↔ n = 0 := by
  rw [← not_iff_not, not_lt, ENat.one_le_iff_ne_zero]

------------


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

end ConnectedTo

section conn

variable {B B' I I' J K X Y : Set α}

lemma Indep.encard_inter_add_erk_dual_eq_of_cl_eq_cl (hI : M.Indep I) (hI' : M.Indep I')
    (hII' : M.cl I = M.cl I') (hJ : M.Indep J) :
    (I ∩ J).encard + (M ↾ (I ∪ J))✶.erk = (I' ∩ J).encard + (M ↾ (I' ∪ J))✶.erk := by
  obtain ⟨K, hK, hIK⟩ := hI.subset_basis_of_subset (subset_union_left I J)
  have hsk := (hK.indep.subset_skew_diff hIK)
  rw [skew_iff_cl_skew_left] at hsk
  have' hdj := hsk.disjoint_of_indep_subset_right (hK.indep.diff _) Subset.rfl

  have hb : ∀ ⦃B⦄, M.Basis B (M.cl I) → (M ／ (K \ I)).Basis B (B ∪ J \ (K \ I)) ∧ (K \ I ⊆ B ∪ J) := by
    refine fun B hB ↦ ⟨Indep.basis_of_subset_of_subset_cl ?_ ?_ ?_, ?_⟩
    · rw [(hK.indep.diff _).contract_indep_iff]
      exact ⟨hdj.mono_left hB.subset,
        hsk.union_indep_of_indep_subsets hB.indep hB.subset (hK.indep.diff _) Subset.rfl⟩

    · exact subset_union_left _ _
    · rw [contract_cl_eq, subset_diff, disjoint_union_left, and_iff_left disjoint_sdiff_left,
        and_iff_left (hdj.mono_left hB.subset), ← cl_union_cl_left_eq, hB.cl_eq_cl, cl_cl,
        cl_union_cl_left_eq, union_diff_self, union_eq_self_of_subset_left hIK, hK.cl_eq_cl]
      exact union_subset (hB.subset.trans (M.cl_subset_cl (subset_union_left _ _)))
        (M.subset_cl_of_subset ((diff_subset _ _).trans (subset_union_right _ _)))

    rw [diff_subset_iff, union_comm B, ← union_assoc]
    exact hK.subset.trans <| subset_union_left _ _

  have hb' : ∀ ⦃B⦄, M.Basis B (M.cl I) →
      (B ∩ J).encard + (M ／ (K \ I) ↾ (B ∪ J \ (K \ I)))✶.erk = (J \ (K \ I)).encard := by
    intro B hB
    rw [(hb hB).1.erk_dual_restrict, union_diff_left,
      ← encard_diff_add_encard_inter (J \ (K \ I)) B, add_comm, inter_comm _ B,
      inter_diff_distrib_left, (hdj.mono_left hB.subset).inter_eq, diff_empty]

  have hind : ∀ Y, (M ↾ (Y ∪ J)).Indep (K \ I) := by
    intro Y
    rw [restrict_indep_iff, and_iff_right (hK.indep.diff I), diff_subset_iff, union_comm Y,
      ← union_assoc]
    exact hK.subset.trans (subset_union_left _ _)
  have hI'b := hII'.symm ▸ hI'.basis_cl
  rw [← (hind I).contract_er_dual_eq,  ← (hind I').contract_er_dual_eq,
    restrict_contract_eq_contract_restrict _ (hb hI.basis_cl).2,
    restrict_contract_eq_contract_restrict _ (hb hI'b).2,
    union_diff_distrib, sdiff_eq_left.2 disjoint_sdiff_right,
    union_diff_distrib, sdiff_eq_left.2 (hdj.mono_left hI'b.subset), hb' hI.basis_cl, hb' hI'b]

lemma Basis'.encard_dual_switch_switch_eq {I I' J J' X Y : Set α}
    (hI : M.Basis' I X) (hI' : M.Basis' I' X) (hJ : M.Basis' J Y) (hJ' : M.Basis' J' Y) :
    (I ∩ J).encard + (M ↾ (I ∪ J))✶.erk = (I' ∩ J').encard + (M ↾ (I' ∪ J'))✶.erk := by
  rw [hI.indep.encard_inter_add_erk_dual_eq_of_cl_eq_cl hI'.indep
      (by rw [hI.cl_eq_cl, hI'.cl_eq_cl]) hJ.indep,
    inter_comm, union_comm, hJ.indep.encard_inter_add_erk_dual_eq_of_cl_eq_cl hJ'.indep
      (by rw [hJ.cl_eq_cl, hJ'.cl_eq_cl]) hI'.indep, inter_comm, union_comm]

lemma Basis.encard_dual_switch_switch_eq {I I' J J' X Y : Set α}
    (hI : M.Basis I X) (hI' : M.Basis I' X) (hJ : M.Basis J Y) (hJ' : M.Basis J' Y) :
    (I ∩ J).encard + (M ↾ (I ∪ J))✶.erk = (I' ∩ J').encard + (M ↾ (I' ∪ J'))✶.erk :=
  hI.basis'.encard_dual_switch_switch_eq hI'.basis' hJ.basis' hJ'.basis'

noncomputable def conn (M : Matroid α) (X Y : Set α) : ℕ∞ :=
  let I := (M.exists_basis' X).choose
  let J := (M.exists_basis' Y).choose
  (I ∩ J).encard + (M ↾ (I ∪ J))✶.erk

lemma conn_comm (M : Matroid α) (X Y : Set α) :
    M.conn X Y = M.conn Y X := by
  simp_rw [conn, union_comm, inter_comm]

lemma Basis'.conn_eq (hI : M.Basis' I X) (hJ : M.Basis' J Y) :
    M.conn X Y = (I ∩ J).encard + (M ↾ (I ∪ J))✶.erk := by
  simp_rw [conn, hI.encard_dual_switch_switch_eq (M.exists_basis' X).choose_spec hJ
    (M.exists_basis' Y).choose_spec]

lemma Basis.conn_eq (hI : M.Basis I X) (hJ : M.Basis J Y) :
    M.conn X Y = (I ∩ J).encard + (M ↾ (I ∪ J))✶.erk :=
  hI.basis'.conn_eq hJ.basis'

lemma Indep.conn_eq (hI : M.Indep I) (hJ : M.Indep J) :
    M.conn I J = (I ∩ J).encard + (M ↾ (I ∪ J))✶.erk :=
  hI.basis_self.conn_eq hJ.basis_self

lemma Basis'.conn_eq_of_disjoint (hI : M.Basis' I X) (hJ : M.Basis' J Y) (hXY : Disjoint X Y) :
    M.conn X Y = (M ↾ (I ∪ J))✶.erk := by
  rw [hI.conn_eq hJ, (hXY.mono hI.subset hJ.subset).inter_eq, encard_empty, zero_add]

lemma conn_eq_encard_of_diff {F : Set α} (hXY : Disjoint X Y) (hI : M.Basis' I X)
    (hJ : M.Basis' J Y) (hFIJ : F ⊆ I ∪ J)  (hF : M.Basis' ((I ∪ J) \ F) (X ∪ Y)) :
    M.conn X Y = F.encard := by
  have hF' : M.Basis ((I ∪ J) \ F) (I ∪ J) := by
    refine hF.basis_inter_ground.basis_subset (diff_subset _ _)
      (subset_inter (union_subset_union hI.subset hJ.subset)
      (union_subset hI.indep.subset_ground hJ.indep.subset_ground))
  rw [hI.conn_eq hJ, hF'.erk_dual_restrict, diff_diff_cancel_left hFIJ,
    (hXY.mono hI.subset hJ.subset).inter_eq, encard_empty, zero_add]

lemma conn_eq_encard_of_diff' {F : Set α} (hXY : Disjoint X Y) (hI : M.Basis' I X)
    (hJ : M.Basis' J Y) (hFI : F ⊆ I)  (hF : M.Basis' ((I \ F) ∪ J) (X ∪ Y)) :
    M.conn X Y = F.encard := by
  apply conn_eq_encard_of_diff hXY hI hJ (hFI.trans (subset_union_left _ _))
  rwa [union_diff_distrib, (sdiff_eq_left (x := J)).2 ]
  exact (hXY.symm.mono hJ.subset (hFI.trans hI.subset))

lemma er_add_er_eq_er_union_add_conn (M : Matroid α) (X Y : Set α) :
    M.er X + M.er Y = M.er (X ∪ Y) + M.conn X Y := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  obtain ⟨J, hJ⟩ := M.exists_basis' Y
  obtain ⟨B, hB⟩ := M.exists_basis' (I ∪ J)
  have hB' : M.Basis' B (X ∪ Y) := by
    rw [basis'_iff_basis_cl, ← cl_cl_union_cl_eq_cl_union, ← hI.cl_eq_cl, ← hJ.cl_eq_cl,
       cl_cl_union_cl_eq_cl_union, ← hB.cl_eq_cl]
    exact ⟨hB.indep.basis_cl, hB.subset.trans (union_subset_union hI.subset hJ.subset)⟩
  rw [hI.conn_eq hJ, ← hI.encard, ← hJ.encard, ← encard_union_add_encard_inter, ← hB'.encard,
    ← (base_restrict_iff'.2 hB).encard_compl_eq, restrict_ground_eq, ← add_assoc, add_comm B.encard,
    add_assoc, add_comm B.encard, encard_diff_add_encard_of_subset hB.subset, add_comm]

lemma conn_cl_left (M : Matroid α) (X Y : Set α) :
    M.conn X Y = M.conn (M.cl X) Y := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  obtain ⟨J, hJ⟩ := M.exists_basis' Y
  rw [hI.conn_eq hJ, hI.basis_cl_right.basis'.conn_eq hJ]

lemma conn_cl_right (M : Matroid α) (X Y : Set α) :
    M.conn X Y = M.conn X (M.cl Y) := by
  rw [conn_comm, conn_cl_left, conn_comm]

lemma conn_cl_cl (M : Matroid α) (X Y : Set α) :
    M.conn X Y = M.conn (M.cl X) (M.cl Y) := by
  rw [conn_cl_left, conn_cl_right]

lemma conn_mono_left {X' : Set α} (M : Matroid α) (hX : X' ⊆ X) (Y : Set α) :
    M.conn X' Y ≤ M.conn X Y := by
  obtain ⟨I', hI'⟩ := M.exists_basis' X'
  obtain ⟨I, hI, hII'⟩ := hI'.indep.subset_basis'_of_subset (hI'.subset.trans hX)
  obtain ⟨J, hJ⟩ := M.exists_basis' Y
  rw [hI'.conn_eq hJ, hI.conn_eq hJ]
  refine add_le_add (encard_le_card (inter_subset_inter_left _ hII')) (Minor.erk_le ?_)
  rw [dual_minor_iff]
  exact (Restriction.of_subset M (union_subset_union_left _ hII')).minor

lemma conn_mono_right {Y' : Set α} (M : Matroid α) (X : Set α) (hY : Y' ⊆ Y) :
    M.conn X Y' ≤ M.conn X Y := by
  rw [conn_comm, conn_comm _ X]
  exact M.conn_mono_left hY _

lemma conn_mono {X' Y' : Set α} (M : Matroid α) (hX : X' ⊆ X) (hY : Y' ⊆ Y) :
    M.conn X' Y' ≤ M.conn X Y :=
  ((M.conn_mono_left hX Y').trans (M.conn_mono_right _ hY))

@[simp] lemma empty_conn (M : Matroid α) (X : Set α) : M.conn ∅ X = 0 := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  rw [(M.empty_indep.basis_self.basis').conn_eq hI, empty_inter, encard_empty,
    erk_dual_restrict_eq_zero_iff.2 (by simpa using hI.indep), zero_add]

@[simp] lemma conn_empty (M : Matroid α) (X : Set α) : M.conn X ∅ = 0 := by
  rw [conn_comm, empty_conn]

lemma conn_subset (M : Matroid α) (hXY : X ⊆ Y) : M.conn X Y = M.er X := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_basis'_of_subset (hI.subset.trans hXY)
  rw [hI.conn_eq hJ, inter_eq_self_of_subset_left hIJ, union_eq_self_of_subset_left hIJ,
    hJ.indep.erk_dual_restrict_eq, ← hI.encard, add_zero]

lemma conn_eq_zero (M : Matroid α) (hX : X ⊆ M.E := by aesop_mat) (hY : Y ⊆ M.E := by aesop_mat) :
    M.conn X Y = 0 ↔ M.Skew X Y := by
  obtain ⟨I, hI⟩ := M.exists_basis X
  obtain ⟨J, hJ⟩ := M.exists_basis Y
  rw [skew_iff_cl_skew, conn_cl_cl, ← hI.cl_eq_cl, ← hJ.cl_eq_cl, ← skew_iff_cl_skew,
    ← conn_cl_cl, hI.indep.conn_eq hJ.indep, add_eq_zero_iff, encard_eq_zero,
    ← disjoint_iff_inter_eq_empty, erk_dual_restrict_eq_zero_iff,
    hI.indep.skew_iff_disjoint_union_indep hJ.indep]

lemma conn_compl_dual (M : Matroid α) (hX : X ⊆ M.E) :
    M.conn X (M.E \ X) = M✶.conn X (M.E \ X) := by
  -- obtain ⟨B0, BI0⟩ := M.exists_basis (M.E \ X)
  -- obtain ⟨B1, BI1⟩ := M.exists_basis X
  set Z : Bool → Set α := fun b ↦ bif b then X else M.E \ X
  have hdj : Disjoint (Z true) (Z false) := sorry
  have hu : Z true ∪ Z false = M.E := sorry
  rw [(show M.E \ X = Z false from rfl), show X = Z true from rfl]

  choose B hB using fun b ↦ (M.exists_basis (Z b) (by cases b <;> aesop_mat))


  have hex : ∀ b, ∃ F, F ⊆ B b ∧ (M.Base (B (!b) ∪ (B b \ F))) := by
    intro b
    sorry
  choose F hF using hex

  set B' : Bool → Set α := fun b ↦ ((Z b \ B b) ∪ (F b))

  have hbasis : ∀ b, M✶.Basis' (B' b) (Z b) := by sorry

  have haux : ∀ Y, Y ⊆ Z true → M.E \ (Z true \ Y) = Z false ∪ Y := by
    intro Y hY
    rw [← hu, union_diff_distrib, diff_diff_cancel_left hY, union_comm, sdiff_eq_left.2]
    exact hdj.symm.mono_right (diff_subset _ _)

  have hbase : M✶.Base ((B' true \ F true) ∪ B' false) := by
    simp only [union_diff_right, B']
    rw [diff_diff, union_eq_self_of_subset_right (hF true).1, ← union_assoc, dual_base_iff',
      and_iff_left, ← diff_diff, ← diff_diff, haux, union_diff_distrib,
      diff_diff_cancel_left, (sdiff_eq_left (x := B true)).2, union_diff_distrib,
      (sdiff_eq_left (x := B true)).2, union_comm]
    · exact (hF false).2
    · exact hdj.mono ((hB true).subset) ((hF false).1.trans (hB false).subset)
    · exact hdj.mono ((hB true).subset) (diff_subset _ _)
    · exact (hB false).subset
    · exact (hB true).subset
    rw [← hu]
    refine union_subset (union_subset_union (diff_subset _ _) (diff_subset _ _)) ?_
    exact ((hF false).1.trans (hB false).subset).trans (subset_union_right _ _)

  have hb' := (hF true).2.basis_ground.basis_subset (Y := B true ∪ B false)
    (by rw [union_comm]; refine union_subset_union_left _ (diff_subset _ _))
    ((union_subset_union (hB true).subset (hB false).subset).trans_eq hu)

  rw [(hB true).basis'.conn_eq_of_disjoint (hB false).basis' hdj, hb'.erk_dual_restrict]
  rw [union_comm, Bool.not_true, union_diff_distrib, diff_eq_empty.2 (subset_union_left _ _),
    empty_union, ← diff_diff, sdiff_eq_left.2 (hdj.mono (hB true).subset (hB false).subset),
    diff_diff_cancel_left (hF true).1]

  rw [conn_eq_encard_of_diff' hdj (hbasis true) (hbasis false) (F := F true)]

  · exact subset_union_right _ _
  rwa [hu, basis'_iff_basis, ← dual_ground, basis_ground_iff]




  -- have hconn_dual :


  -- set B : Bool → Set α := fun b ↦ bif b then B1 else B0


  -- set Y := M.E \ X with hY
  -- obtain ⟨IX, hIX⟩ := M.exists_basis X
  -- obtain ⟨IY, hIY⟩ := M.exists_basis Y
  -- rw [hIX.basis'.conn_eq_of_disjoint hIY.basis' disjoint_sdiff_right]

  -- obtain ⟨BX, hBX⟩ := hIX.indep.subset_basis_of_subset (subset_union_left IX IY)

end conn

section separation

variable {k : ℕ} {P : Set α → Prop} {a b : α}

protected structure Partition (M : Matroid α) where
  A : Set α
  B : Set α
  disjoint : Disjoint A B
  union_eq : A ∪ B = M.E

@[simps] def Partition.symm (P : M.Partition) : M.Partition where
  A := P.B
  B := P.A
  disjoint := P.disjoint.symm
  union_eq := by rw [← P.union_eq, union_comm]

@[simps] def Partition.dual (P : M.Partition) : M✶.Partition where
  A := P.A
  B := P.B
  disjoint := P.disjoint
  union_eq := P.union_eq

@[simps] def Partition.of_subset (A : Set α) (hX : A ⊆ M.E := by aesop_mat) : M.Partition where
  A := A
  B := M.E \ A
  disjoint := disjoint_sdiff_right
  union_eq := by simp [hX]

@[simp, aesop unsafe 10% (rule_sets := [Matroid])]
lemma Partition.A_subset_ground (P : M.Partition) : P.A ⊆ M.E := by
  rw [← P.union_eq]; apply subset_union_left

@[simp, aesop unsafe 10% (rule_sets := [Matroid])]
lemma Partition.B_subset_ground (P : M.Partition) : P.B ⊆ M.E := by
  rw [← P.union_eq]; apply subset_union_right

noncomputable abbrev Partition.conn (P : M.Partition) : ℕ∞ := M.conn P.A P.B

@[simp] lemma Partition.conn_symm (P : M.Partition) : P.symm.conn = P.conn :=
  M.conn_comm _ _

def Partition.IsTutteSep (P : M.Partition) (k : ℕ) :=
  P.conn < k ∧ k ≤ P.A.encard ∧ k ≤ P.B.encard

lemma connected_iff_not_exists_tutteSep [M.Nonempty] :
    M.Connected ↔ ¬ ∃ (P : M.Partition), P.IsTutteSep 1 := by
  rw [iff_not_comm]
  simp only [Connected, show M.Nonempty by assumption, true_and, not_forall, Classical.not_imp,
    exists_and_left, exists_prop, exists_and_left, Partition.IsTutteSep, Nat.cast_one,
    ENat.lt_one_iff, one_le_encard_iff_nonempty]
  simp_rw [conn_eq_zero _ (Partition.A_subset_ground _) (Partition.B_subset_ground _),
    skew_iff_forall_circuit (Partition.disjoint _) (Partition.A_subset_ground _)
    (Partition.B_subset_ground _)]

  refine ⟨fun ⟨P, ⟨hc, hA, hB⟩⟩ ↦ ?_, fun ⟨x, y, hy, hx, h⟩ ↦ ?_⟩
  · obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hB
    refine ⟨a, b, by simp [P.union_eq.symm, hb], by simp [P.union_eq.symm, ha], fun hconn ↦ ?_⟩
    obtain ⟨C, hC, haC, hbC⟩ := hconn.exists_circuit_of_ne (P.disjoint.ne_of_mem ha hb)
    obtain (hCA | hCB) := hc C hC (hC.subset_ground.trans_eq P.union_eq.symm)
    · exact P.disjoint.ne_of_mem (hCA hbC) hb rfl
    exact P.symm.disjoint.ne_of_mem (hCB haC) ha rfl
  refine ⟨Partition.of_subset {z | M.ConnectedTo x z} (fun z hz ↦ hz.mem_ground_right),
    ?_, ⟨x, by simpa⟩, ⟨y, by simp [hy, h]⟩⟩
  simp only [Partition.of_subset_A, Partition.of_subset_B, union_diff_self]
  rintro C hC -
  obtain ⟨e, he⟩ := hC.nonempty
  by_cases hex : M.ConnectedTo x e
  · refine .inl (fun y hy ↦ hex.trans <| hC.mem_connectedTo_mem he hy )
  refine .inr fun z hzC ↦ ⟨hC.subset_ground hzC, fun (hz : M.ConnectedTo x z) ↦ ?_⟩
  exact hex <| hz.trans <| hC.mem_connectedTo_mem hzC he




end separation
