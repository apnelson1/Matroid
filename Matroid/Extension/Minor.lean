import Matroid.Extension.ProjectBy

open Set Function Set.Notation Option

namespace Matroid

variable {α : Type*} {M : Matroid α} {I J B F₀ F F' X Y : Set α} {e f : α}

namespace ModularCut

/-- A modular cut `U` in a contraction `M ／ C` gives rise to a modular cut in `M`.
This corresponds to the freeest extension of `M` that contracts to the extension given by `U`. -/
def ofContract {C : Set α} (U : (M ／ C).ModularCut) (hC : C ⊆ M.E) : M.ModularCut where
  carrier := (· ∪ C) '' U
  forall_isFlat := by
    simpa using fun F hF ↦ ((isFlat_contract_iff hC).1 (U.isFlat_of_mem hF)).1
  forall_superset := by
    simp only [mem_image, SetLike.mem_coe, forall_exists_index, and_imp]
    rintro _ F G hGU rfl hF hFF
    have h := (isFlat_contract_iff hC).1 <| U.isFlat_of_mem hGU
    rw [union_subset_iff] at hFF

    refine ⟨_,  U.superset_mem hGU (F' := F \ C) ?_ (by simp [subset_diff, h.2, hFF.1]),
      by simp [hFF.2]⟩
    rwa [isFlat_contract_iff, diff_union_of_subset hFF.2, and_iff_left disjoint_sdiff_left]
  forall_inter := by
    simp only [subset_def, mem_image, SetLike.mem_coe]
    intro Fs hFs hne hmod
    have h_inter := U.sInter_mem (Fs := (· \ C) '' Fs)
    simp only [image_nonempty, hne, subset_def, mem_image, SetLike.mem_coe, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂, sInter_image, forall_const] at h_inter

    refine ⟨_, h_inter (fun F hF ↦ ?_) ?_, ?_⟩
    ·
      obtain ⟨F, hFU, rfl⟩ := hFs F hF
      have hFE := subset_diff.1 (U.isFlat_of_mem hFU).subset_ground
      simpa [hFE.2.symm.sdiff_eq_right]
    · have hcl : ∀ (F : ↑Fs), C ⊆ M.closure F
      · rintro ⟨F, hF⟩
        obtain ⟨F', hF', -, rfl⟩ := hFs F hF
        simp [M.subset_closure_of_subset' subset_union_right hC]
      have h' := hmod.contract (C := C) hcl
      have hφ : ∀ X ∈ ((· \ C) '' Fs), X ∪ C ∈ Fs
      · suffices ∀ F ∈ Fs, F ∪ C ∈ Fs by simpa
        refine fun F hF ↦ ?_
        obtain ⟨F', hF', -, rfl⟩ := hFs F hF
        simpa [union_assoc]
      set φ : ((· \ C) '' Fs) → Fs := fun ⟨X, hX⟩ ↦ ⟨X ∪ C, hφ X hX⟩ with hφ'
      convert h'.comp φ
      ext ⟨A, ⟨B, hB, rfl⟩⟩ e
      simp [hφ']
    simp_rw [diff_eq]
    rw [← biInter_distrib_inter _ hne, sInter_eq_biInter, ← diff_eq, diff_union_of_subset]
    simp only [subset_iInter_iff]
    refine fun F hF ↦ ?_
    obtain ⟨F, -, rfl⟩ := hFs F hF
    exact subset_union_right

@[simp]
lemma mem_ofContract_iff {C : Set α} (U : (M ／ C).ModularCut) {hC : C ⊆ M.E} :
    F ∈ U.ofContract hC ↔ C ⊆ F ∧ F \ C ∈ U := by
  simp only [ModularCut.ofContract, ModularCut.mem_mk_iff, mem_image, SetLike.mem_coe]
  refine ⟨?_, fun h ↦ ⟨_, h.2, diff_union_of_subset h.1⟩⟩
  rintro ⟨F, hF, rfl⟩
  simpa [(subset_diff.1 (U.isFlat_of_mem hF).subset_ground).2.sdiff_eq_left]

/-- A version of `ModularCut.ofContract` without a supportedness hypothesis. -/
def ofContract' {C : Set α} (U : (M ／ C).ModularCut) : M.ModularCut :=
  (U.copy (M.contract_inter_ground_eq C).symm).ofContract inter_subset_right

@[simp]
lemma mem_ofContract'_iff {C : Set α} (U : (M ／ C).ModularCut) :
    F ∈ U.ofContract' ↔ C ∩ M.E ⊆ F ∧ F \ (C ∩ M.E) ∈ U := by
  simp [ModularCut.ofContract']

/-- Given a modular cut `U` of `M`, the corresponding modular cut in some projection of `M`. -/
protected def project (U : M.ModularCut) (C : Set α) : (M.project C).ModularCut where
  carrier := {F | (M.project C).IsFlat F ∧ M.closure (F ∪ C) ∈ U}
  forall_isFlat F := fun h ↦ h.1
  forall_superset F F' := fun h h' hFF' ↦ ⟨h', U.superset_mem h.2 (M.closure_isFlat _)
    (M.closure_subset_closure (union_subset_union_left _ hFF'))⟩
  forall_inter := by
    refine fun Fs hFs hne hmod ↦ ⟨IsFlat.sInter hne fun F hF ↦ (hFs hF).1, ?_⟩
    obtain ⟨I, hI⟩ := M.exists_isBasis' C
    have := hne.to_subtype
    have hmem_U := U.sInter_mem (Fs := (fun X ↦ M.closure (X ∪ C)) '' Fs) (by simpa) ?_ ?_
    · simp only [sInter_image] at hmem_U
      have hrw := hmod.iInter_closure_eq_closure_iInter
      simp only [project_closure, iInter_coe_set, ← sInter_eq_biInter] at hrw
      rwa [← hrw]
    · simp only [subset_def, mem_image, SetLike.mem_coe, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      exact fun F hF ↦ (hFs hF).2
    obtain ⟨B, hB⟩ := hmod
    have hi : M.Indep (B ∪ I) := by
      have hi := hB.indep
      rw [hI.project_eq_project, hI.indep.project_indep_iff] at hi
      exact hi.2
    refine ⟨B ∪ I, hi, ?_⟩
    simp only [Subtype.forall, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      ← closure_union_congr_right hI.closure_eq_closure]
    refine fun F hF ↦ (hi.inter_left _).isBasis_of_subset_of_subset_closure inter_subset_left ?_
    have hcl := hB.closure_inter_eq ⟨F, hF⟩
    simp only [project_closure, ← closure_union_congr_right hI.closure_eq_closure] at hcl
    nth_grw 1 [← hcl, closure_subset_closure]
    grw [inter_union_distrib_right, ← M.subset_closure (X := (F ∪ I)) _]
    exact union_subset (hFs hF).1.subset_ground hI.indep.subset_ground

@[simp]
lemma mem_project_iff (U : M.ModularCut) (C : Set α) :
    F ∈ U.project C ↔ (M.project C).IsFlat F ∧ M.closure (F ∪ C) ∈ U := Iff.rfl

/-- Given a modular cut `U` of `M`, the corresponding modular cut in some projection of `M`. -/
protected def contract (U : M.ModularCut) (C : Set α) : (M ／ C).ModularCut :=
  ((U.project C).delete C).copy <| project_delete_self ..

@[simp]
lemma mem_contract_iff (U : M.ModularCut) (C : Set α) :
    F ∈ U.contract C ↔ (M ／ C).IsFlat F ∧ M.closure (F ∪ C) ∈ U := by
  simp [ModularCut.contract, isFlat_iff_closure_eq, union_assoc]

lemma projectBy_project (U : M.ModularCut) (C : Set α) :
    (M.projectBy U).project C = (M.project C).projectBy (U.project C) := by
  refine ext_closure fun X ↦ ?_
  simp [Set.ext_iff, mem_closure_projectBy_iff, isFlat_iff_closure_eq, union_assoc, insert_union]

lemma projectBy_contract (U : M.ModularCut) (C : Set α) :
    (M.projectBy U).contract C = (M ／ C).projectBy (U.contract C) := by
  rw [← project_delete_self, U.projectBy_project, ModularCut.contract]
  refine ext_closure fun X ↦ ?_
  simp only [delete_closure_eq, Set.ext_iff, mem_diff, mem_closure_projectBy_iff, project_closure,
    diff_union_self, insert_union, mem_project_iff, isFlat_iff_closure_eq,
    closure_union_closure_left_eq, union_assoc, union_self, true_and, contract_closure_eq,
    ModularCut.mem_copy_iff, mem_delete_iff, project_delete_self]
  aesop

-- TODO : versions of the above for `extendBy`.

lemma project_eq_top_iff (U : M.ModularCut) : U.project X = ⊤ ↔ M.closure X ∈ U := by
  rw [ModularCut.eq_top_iff, project_loops, mem_project_iff, isFlat_iff_closure_eq,
    project_closure, ← closure_union_closure_right_eq, union_self, closure_closure,
    and_iff_right rfl]

lemma contract_eq_top_iff (U : M.ModularCut) : U.contract X = ⊤ ↔ M.closure X ∈ U := by
  rw [ModularCut.eq_top_iff, contract_loops_eq, mem_contract_iff, isFlat_iff_closure_eq,
    contract_closure_eq, diff_union_self, ← closure_union_closure_right_eq, union_self,
    closure_closure, and_iff_right rfl]

end ModularCut

section ExtendContract

variable {M N : Matroid α} {C D : Set α}

lemma exists_common_major_of_contract_eq_deleteElem (heC : e ∉ C) (hC : C ⊆ M.E)
    (h_eq : M ／ C = N ＼ {e}) :
      ∃ (P : Matroid α), (e ∈ N.E → e ∈ P.E) ∧ P ＼ {e} = M ∧ P ／ C = N := by
  have heM : e ∉ M.E := fun heM ↦ by simpa [h_eq] using show e ∈ (M ／ C).E from ⟨heM, heC⟩
  obtain heN | heN := em' <| e ∈ N.E
  · use M
    rw [h_eq, ← delete_inter_ground_eq, Disjoint.inter_eq (by simpa),
      ← N.delete_inter_ground_eq, Disjoint.inter_eq (by simpa)]
    simp [heN]

  set UN := ModularCut.ofDeleteElem N e with hUN
  set UM := (UN.copy h_eq.symm).ofContract hC
  use M.extendBy e UM
  rw [ModularCut.extendBy_deleteElem _ heM, and_iff_right rfl, imp_iff_right heN,
    and_iff_right (by simp)]
  refine ext_indep ?_ ?_
  · rw [contract_ground, extendBy_E, insert_diff_of_notMem _ heC, ← contract_ground, h_eq,
      delete_ground]
    simpa
  obtain ⟨IC, hIC⟩ := M.exists_isBasis C
  have heIC : e ∉ IC := notMem_subset hIC.subset heC
  have hIC' : (M.extendBy e UM).IsBasis IC C
  · rw [← UM.extendBy_deleteElem heM, delete_isBasis_iff] at hIC
    exact hIC.1
  intro I
  simp only [contract_ground, extendBy_E]
  rw [hIC'.contract_indep_iff, extendBy_Indep, subset_diff, and_imp, disjoint_comm]
  simp +contextual only [and_true]
  intro hIE hdj

  obtain heI | heI := em' (e ∈ I)
  · rw [ModularCut.extIndep_iff_of_notMem (by simp [heI, heIC]),
      show N.Indep I ↔ (N ＼ {e}).Indep I by simp [heI], ← h_eq, hIC.contract_indep_iff,
      and_iff_left hdj]

  have hrw1 : M.closure ((I ∪ IC) \ {e}) = M.closure ((I \ {e}) ∪ C)
  · rw [union_diff_distrib, diff_singleton_eq_self heIC,
      closure_union_congr_right hIC.closure_eq_closure]

  have hrw2 : (I \ {e}) ∪ IC = (I ∪ IC) \ {e}
  · rw [union_diff_distrib, diff_singleton_eq_self heIC]

  have hrw3 : N.Indep I ↔ (N ＼ {e}).Indep (I \ {e}) ∧ (N ＼ {e}).closure (I \ {e}) ∉ UN
  · nth_rw 1 [← ModularCut.deleteElem_extendBy heN, ← hUN]
    rw [extendBy_Indep, ModularCut.extIndep_iff_of_mem heI]

  have hwin : C ⊆ M.closure (I \ {e} ∪ C) := M.subset_closure_of_subset' subset_union_right

  rw [UM.extIndep_iff_of_mem (.inl heI)]
  simp [← h_eq, hrw1, hrw2, hrw3, hwin, hIC.contract_indep_iff, hdj.mono_right diff_subset, UM]

lemma exists_common_major_of_delete_eq_contractElem (heD : e ∉ D) (hD : D ⊆ M.E)
    (h_eq : M ＼ D = N ／ {e}) :
    ∃ (P : Matroid α), (e ∈ N.E → e ∈ P.E) ∧ P ／ {e} = M ∧ P ＼ D = N := by
  rw [← dual_inj, dual_delete, dual_contract] at h_eq
  -- have := exists_common_major_of_contract_eq_deleteElem (by simpa) (by simpa) h_eq
  obtain ⟨P, himp, hPM, hPN⟩ :=
    exists_common_major_of_contract_eq_deleteElem (by simpa) (by simpa) h_eq
  rw [eq_dual_iff_dual_eq] at hPM hPN
  refine ⟨P✶, himp, by simpa using hPM, by simpa using hPN⟩

/-- If the contract-set is finite and disjoint from the delete-sets,
then any two matroids with a common minor have a common major. -/
lemma exists_common_major_of_contract_eq_delete {D : Finset α} (hCD : Disjoint C D) (hCE : C ⊆ M.E)
    (h_eq : M ／ C = N ＼ (D : Set α)) : ∃ (P : Matroid α),
      ((D : Set α) ⊆ N.E → (D : Set α) ⊆ P.E) ∧ P ＼ (D : Set α) = M ∧ P ／ C = N := by
  classical
  induction' D using Finset.induction with e D heD IH generalizing N
  · exact ⟨M, by simp, by simpa using h_eq⟩

  obtain ⟨hCD, heC⟩ : Disjoint C ↑D ∧ e ∉ C := by simpa [← union_singleton] using hCD

  simp_rw [Finset.coe_insert, ← singleton_union, ← delete_delete] at h_eq ⊢

  obtain ⟨P', himp, hP'M, hP'N⟩ := IH hCD h_eq
  have hCE' : C ⊆ P'.E
  · rw [← hP'M] at hCE
    exact hCE.trans diff_subset
  obtain ⟨Q, hQ, rfl, rfl⟩ := exists_common_major_of_contract_eq_deleteElem heC hCE' hP'N
  exact ⟨Q, by simp +contextual [subset_diff], hP'M, rfl⟩

/-- If `M 0, M 1, ..., M n` is a sequence of matroids
where each is a single projection of the previous one,
then there is a matroid `P` with an `n`-element set `X`
such that `P ＼ X = M 0` and `P ／ X = M n`. -/
lemma exists_eq_delete_eq_contract_of_projectBy_seq {n : ℕ} (M : Fin (n+1) → Matroid α)
    (U : (i : Fin n) → (M i.castSucc).ModularCut)
    (h_eq : ∀ i, M i.succ = (M i.castSucc).projectBy (U i)) {X : Finset α} (hD : X.card = n)
    (hdj : Disjoint (M 0).E X) :
    ∃ (P : Matroid α), (X : Set α) ⊆ P.E ∧ P ＼ X = M 0 ∧ P ／ X = M (Fin.last n) := by
  induction n generalizing X with
  | zero => exact ⟨M 0, by simp [show X = ∅ by simpa using hD]⟩
  | succ n IH =>
  have hE (i) : (M i).E = (M 0).E := by
    induction i using Fin.induction with | zero => rfl | succ i IH =>
      rwa [h_eq, ModularCut.projectBy_ground]
  obtain ⟨D, a, ha, rfl⟩ :=
    Finset.Nonempty.exists_cons_eq (s := X) <| by simp [← X.card_ne_zero, hD]
  simp only [Finset.card_cons, Nat.add_right_cancel_iff] at hD
  obtain ⟨haE : a ∉ (M 0).E, hdj : Disjoint (M 0).E D⟩ := by simpa using hdj
  obtain ⟨P₀, hDE, hd, hc⟩ := IH (M ∘ Fin.castSucc) (fun i ↦ (U i.castSucc).copy (by simp))
    (fun i ↦ h_eq i.castSucc) hD (by simpa)
  simp only [comp_apply, Fin.castSucc_zero] at hc hd
  simp_rw [← Fin.succ_last,  h_eq, Finset.coe_cons, ← union_singleton, ← delete_delete,
    ← contract_contract, union_singleton, insert_subset_iff]
  set Q := extendBy _ a (U (Fin.last n)) with hQ
  have hQP₀ : P₀ ／ D = Q ＼ {a} := by rw [hc, hQ, ModularCut.extendBy_deleteElem _ (by rwa [hE])]
  obtain ⟨P, -, hPP₀, hPQ⟩ := exists_common_major_of_contract_eq_deleteElem
    (by simpa) (by simpa) hQP₀
  refine ⟨P, ⟨?_, ?_⟩, ?_, ?_⟩
  · grw [← diff_subset (s := P.E) (t := D), ← contract_ground, hPQ, hQ]
    simp
  · grw [hDE, ← hPP₀]
    simp
  · rwa [delete_comm, hPP₀]
  rw [hPQ, hQ, ModularCut.extendBy_contractElem _ (by rwa [hE])]

end ExtendContract

end Matroid
