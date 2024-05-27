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



-- theorem Base.encard_compl_eq (hB : M.Base B) : (M.E \ B).encard = M✶.erk :=
--   (hB.compl_base_dual).encard

-- theorem Indep.contract_er_dual_eq (hI : M.Indep I) : (M ／ I)✶.erk = M✶.erk := by
--   rw [contract_dual_eq_dual_delete]

-- theorem encard_dual_eq_foo (hI : M.Basis I X) (hI' : M.Basis I' X) (hJ : M.Indep J)
--     (hXJ : Disjoint X J) : (M ↾ (I ∪ J))✶.erk = (M ↾ (I' ∪ J))✶.erk := by
--   obtain ⟨BJ, hBJ, hJBJ⟩ := hJ.subset_basis_of_subset
--     (show J ⊆ (I ∩ I') ∪ J from subset_union_right _ _)
--     (union_subset ((inter_subset_left _ _).trans hI.indep.subset_ground) hJ.subset_ground)

--   have hJ' : ∀ X, (M ↾ (X ∪ J)).Indep J := fun X ↦ by
--     rw [restrict_indep_iff, and_iff_right hJ]; apply subset_union_right

--   obtain ⟨B₀,hB₀⟩ := (M ／ J).exists_basis' (I ∩ I')
--   obtain ⟨BI, hBI, hssBI⟩ :=
--     hB₀.indep.subset_basis'_of_subset (hB₀.subset.trans (inter_subset_left _ _))
--   obtain ⟨BI', hBI', hssBI'⟩ :=
--     hB₀.indep.subset_basis'_of_subset (hB₀.subset.trans (inter_subset_right _ _))

--   have hbas : ∀ Y K B, K ⊆ Y → Y ⊆ X → M.Basis K X → (M ／ J).Basis' B K →
--       ((M ↾ (Y ∪ J)) ／ J).Base B := by
--     intro Y K B hKY hYX hKX hBK
--     rw [← contract_restrict_eq_restrict_contract _ _ _ (hXJ.symm.mono_right hYX),
--       base_restrict_iff']
--     refine (hBK.basis_cl_right.basis_subset (hBK.subset.trans hKY) ?_).basis'
--     rw [contract_cl_eq, subset_diff, and_iff_left (hXJ.mono_left hYX)]
--     exact (hYX.trans hKX.subset_cl).trans (M.cl_subset_cl (subset_union_left _ _))

--   have hBIbas := hbas I I BI Subset.rfl hI.subset hI hBI
--   have hBI'bas := hbas I' I' BI' Subset.rfl hI'.subset hI' hBI'

--   have hb := hbas (I ∪ I') I BI (subset_union_left _ _) (union_subset hI.subset hI'.subset) hI hBI
--   have hb' := hbas _ _ _ (subset_union_right _ _) (union_subset hI.subset hI'.subset) hI' hBI'


--   simp_rw [← (hJ' I).delete_erk_dual_eq, ← hBIbas.encard_compl_eq,  ← (hJ' I').delete_erk_dual_eq,
--     ← hBI'bas.encard_compl_eq, contract_ground, restrict_ground_eq, union_diff_right,
--     (hXJ.mono_left hI.subset).sdiff_eq_left, (hXJ.mono_left hI'.subset).sdiff_eq_left]

--   have hd : (I ∪ I') \ J = I ∪ I' := sorry
--   have := hb'.compl_base_dual.encard_diff_comm hb.compl_base_dual
--   simp [hd, diff_diff_right] at this

  -- have := hb'.encard_diff_comm hb
