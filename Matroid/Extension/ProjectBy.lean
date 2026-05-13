import Matroid.Extension.ExtendBy

universe u

open Set Function Set.Notation Option

variable {α : Type*} {M : Matroid α} {I J B F₀ F F' X Y : Set α} {e f : α} {U : M.ModularCut}

namespace Matroid.ModularCut

private lemma projectBy_aux (U : M.ModularCut) :
    ((((M.map _ (some_injective _).injOn).extendBy none
    (U.map _ (some_injective _).injOn)) ／ {(none : Option α)}).comap Option.some).Indep I ↔
    M.Indep I ∧ (U ≠ ⊤ → M.closure I ∉ U) := by
  have hinj := Option.some_injective α
  obtain (rfl | hU) := eq_or_ne U ⊤
  · rw [contract_eq_delete_of_subset_loops]
    · simp [ModularCut.extIndep_iff_of_notMem, image_eq_image hinj, hinj.injOn]
    rw [singleton_subset_iff, ← isLoop_iff, ← singleton_dep, dep_iff]
    simp [ModularCut.extIndep_iff_of_mem, map_closure_eq, ModularCut.map, image_eq_image hinj]
  simp only [comap_indep_iff, hinj.injOn, and_true, ne_eq, hU, not_false_eq_true, forall_const]
  rw [Indep.contract_indep_iff]
  · simp [ModularCut.extIndep_iff_of_mem, image_eq_image hinj, map_closure_eq,
    preimage_image_eq _ hinj, ModularCut.map]
  suffices M.loops ∉ U by
    simpa [ModularCut.extIndep_iff_of_mem, (eq_comm (a := ∅)), map_closure_eq, ModularCut.map,
      image_eq_image hinj]
  rwa [Ne, ModularCut.eq_top_iff] at hU

/-- Extend `M` using the modular cut `U`, and contract the new element.
Defining this in terms of `extendBy` would be difficult if `M.E = univ`,
so we define it directly instead.   -/
def _root_.Matroid.projectBy (M : Matroid α) (U : M.ModularCut) : Matroid α :=
    Matroid.ofExistsMatroid
  (E := M.E)
  (Indep := fun I ↦ M.Indep I ∧ (U ≠ ⊤ → M.closure I ∉ U))
  (hM := ⟨_, by simp [(Option.some_injective α).preimage_image], fun _ ↦ projectBy_aux U⟩)

/-- The messier expression for `projectBy`; `projectBy` is obtained from `M` by `map`ping it
into `Option α`, extending by the new element `none` and contracting it, then `comap`ping
back to `α`.  -/
lemma projectBy_eq_map_comap (U : M.ModularCut) :
    M.projectBy U = ((((M.map _ (some_injective _).injOn).extendBy none
      (U.map _ (some_injective _).injOn)) ／ {(none : Option α)}).comap Option.some) := by
  refine ext_indep (by simp [projectBy, (Option.some_injective α).preimage_image]) fun I _ ↦ ?_
  rw [projectBy_aux, projectBy, Matroid.ofExistsMatroid]
  simp

@[simp, grind =] lemma projectBy_ground (U : M.ModularCut) : (M.projectBy U).E = M.E := rfl

@[simp] lemma projectBy_indep_iff (U : M.ModularCut) :
    (M.projectBy U).Indep I ↔ M.Indep I ∧ (U ≠ ⊤ → M.closure I ∉ U) := Iff.rfl

lemma projectBy_indep_iff_of_ne_top {I : Set α} (hU : U ≠ ⊤) :
    (M.projectBy U).Indep I ↔ M.Indep I ∧ M.closure I ∉ U := by
  simp [hU]

@[simp]
lemma projectBy_top : M.projectBy ⊤ = M := by
  simp [ext_iff_indep]

@[simp]
lemma projectBy_bot : M.projectBy ⊥ = M := by
  simp [ext_iff_indep, projectBy_indep_iff]

lemma projectBy_eq_self_iff (U : M.ModularCut) : M.projectBy U = M ↔ U = ⊥ ∨ U = ⊤ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.elim (by simp +contextual) (by simp +contextual)⟩
  by_contra! hcon
  obtain ⟨B, hB⟩ := M.exists_isBase
  have hi := hB.indep
  rw [← h, projectBy_indep_iff_of_ne_top hcon.2, hB.closure_eq, ← ModularCut.eq_bot_iff] at hi
  exact hcon.1 hi.2

@[simp] lemma extendBy_contractElem (U : M.ModularCut) (he : e ∉ M.E) :
    (M.extendBy e U) ／ {e} = M.projectBy U := by
  refine ext_indep (by simpa) fun I hI ↦ ?_
  have ⟨hIE, heI⟩ : I ⊆ M.E ∧ e ∉ I := by simpa [subset_diff] using hI
  obtain rfl | hU := eq_or_ne U ⊤
  · have hl : (M.extendBy e ⊤).IsLoop e
    · rw [← singleton_dep, dep_iff, extendBy_Indep,
      ModularCut.extIndep_iff_of_mem (show e ∈ {e} from rfl)]
      simp
    rw [contract_eq_delete_of_subset_loops (by simp), delete_indep_iff,
      extendBy_Indep, ModularCut.extIndep_iff_of_notMem heI, projectBy_indep_iff]
    simp [heI]
  have hnl : (M.extendBy e U).IsNonloop e
  · rw [← indep_singleton, extendBy_Indep, ModularCut.extIndep_iff_of_mem (by simp)]
    simpa [← U.eq_top_iff, closure_empty]
  rw [hnl.indep.contract_indep_iff, union_singleton, extendBy_Indep,
    ModularCut.extIndep_iff_of_mem (mem_insert _ _), projectBy_indep_iff]
  simp [hU, heI]

lemma closure_subset_closure_projectBy (U : M.ModularCut) (X : Set α) :
    M.closure X ⊆ (M.projectBy U).closure X := by
  rw [projectBy_eq_map_comap, comap_closure_eq, contract_closure_eq, ← image_subset_iff,
    subset_diff, and_iff_left (by simp)]
  refine subset_trans ?_ (closure_subset_closure _ (subset_union_left ..))
  have hrw := M.map_closure_eq some (some_injective ..).injOn (some '' X)
  rw [preimage_image_eq _ (some_injective _)] at hrw
  rw [← hrw]
  apply IsRestriction.closure_subset_closure
  exact ModularCut.isRestriction_extendBy _ (by simp)

lemma mem_closure_projectBy_iff (U : M.ModularCut) :
    f ∈ (M.projectBy U).closure X ↔
    f ∈ M.closure X ∨ (M.closure (insert f X) ∈ U ∧ M.closure X ∉ U) := by
  wlog hfE : f ∈ M.E
  · rw [← M.closure_inter_ground (X := insert ..), insert_inter_of_notMem hfE, closure_inter_ground,
      or_iff_left (by simp)]
    exact iff_of_false (fun h ↦ hfE (by simpa using mem_ground_of_mem_closure h))
      (fun h ↦ hfE (mem_ground_of_mem_closure h))
  suffices aux (N : Matroid (Option α)) (e) (he : e ∈ N.E) (f) (hf : f ∈ N.E) (hef : e ≠ f) (X)
    (heX : e ∉ X) : f ∈ (N ／ {e}).closure X ↔ f ∈ (N ＼ {e}).closure X
      ∨ (e ∈ N.closure (insert f X) ∧ e ∉ N.closure X)
  · have hinj' := Option.some_injective α
    have hinj := hinj'.injOn (s := M.E)
    rw [projectBy_eq_map_comap]
    simp only [map_ground, mem_image, reduceCtorEq, and_false, exists_false, not_false_eq_true,
      ModularCut.extendBy_contractElem, comap_closure_eq, mem_preimage]
    convert aux ((M.map some hinj).extendBy none (U.map some hinj)) none (by simp) (some f)
      (by simpa) (by simp) (some '' X) (by simp) using 1
    · simp
    rw [ModularCut.mem_closure_extendBy_iff _ (by simp),
      ModularCut.mem_closure_extendBy_iff _ (by simp), ← image_insert_eq, map_closure_eq,
      hinj'.preimage_image, map_closure_eq, hinj'.preimage_image,
      ModularCut.extendBy_deleteElem _ (by simp)]
    simp [mem_image, hinj'.preimage_image, ModularCut.map, hinj'.image_injective.eq_iff]
  simp only [contract_closure_eq, union_singleton, mem_diff, mem_singleton_iff, hef.symm,
    not_false_eq_true, and_true, delete_closure_eq, diff_singleton_eq_self heX]
  by_cases heX' : e ∈ N.closure X
  · simp [heX', closure_insert_eq_of_mem_closure heX']
  by_cases hfX : f ∈ N.closure X
  · simp [show f ∈ N.closure (insert e X) from N.closure_subset_closure (subset_insert ..) hfX, hfX]
  simpa [hfX, heX'] using N.closure_exchange_iff (X := X) (e := f) (f := e)

-- lemma projectBy_spanning_iff (P : Prop) (hX : X ⊆ M.E := by aesop_mat) :
--     (M.projectBy U).Spanning X ↔ M.Spanning X ∨ (M.) := by
--   rw [spanning_iff_ground_subset_closure (by simpa)]
--   simp [subset_def, mem_closure_projectBy_iff]

lemma projectBy_map {β : Type*} (U : M.ModularCut) {f : α → β} (hf : InjOn f M.E) :
    ((M.map f hf).projectBy (U.map f hf)) = (M.projectBy U).map f hf := by
  refine ext_indep rfl fun I hI ↦ ?_
  obtain ⟨I, hIE, rfl⟩ := subset_image_iff.1 hI
  obtain rfl | hne := eq_or_ne U ⊤
  · simp
  rw [projectBy_indep_iff_of_ne_top (by simpa), map_image_indep_iff hIE, U.mem_map_iff,
    map_image_indep_iff (by simpa), map_closure_eq, projectBy_indep_iff_of_ne_top hne,
    and_congr_right_iff, not_iff_not]
  simp_rw [← M.closure_inter_ground (f ⁻¹' (f '' _)), hf.preimage_image_inter hIE]
  refine fun hI ↦ ⟨fun ⟨F₀, hF₀U, h_eq⟩ ↦ ?_, fun h ↦ ⟨_, h, rfl⟩⟩
  rw [hf.image_eq_image_iff (U.subset_ground hF₀U) (M.closure_subset_ground ..)] at h_eq
  rwa [← h_eq]

@[simp]
lemma projectBy_copy {N : Matroid α} (U : M.ModularCut) (hMN : M = N) :
    N.projectBy (U.copy hMN) = M.projectBy U := by
  subst hMN; rfl

/-- Projecting out by a flat in a modular cut cancels the projection by the modular cut. -/
lemma projectBy_project_eq_project_of_mem (U : M.ModularCut) (hF : F ∈ U) :
    (M.projectBy U).project F = M.project F := by
  refine ext_closure fun X ↦ Set.ext fun e ↦ ?_
  have hcl : M.closure (X ∪ F) ∈ U := by
    refine U.superset_mem hF (M.closure_isFlat _) ?_
    exact (M.subset_closure_of_subset' subset_union_right (U.isFlat_of_mem hF).subset_ground)
  simp [mem_closure_projectBy_iff, hcl]

lemma projectBy_project_eq_project_of_closure_mem (U : M.ModularCut) (hX : M.closure X ∈ U) :
    (M.projectBy U).project X = M.project X := by
  rw [← M.project_closure_eq, ← U.projectBy_project_eq_project_of_mem hX, ← project_closure_eq,
    eq_comm, ← project_closure_eq]
  convert rfl using 2
  refine subset_antisymm ?_ ?_
  · rw [← closure_inter_ground, projectBy_ground]
    exact closure_subset_closure _ <| M.inter_ground_subset_closure X
  rw [← (M.projectBy U).closure_closure (X := X)]
  exact closure_subset_closure _ <| closure_subset_closure_projectBy U X

lemma projectBy_contract_eq_contract_of_closure_mem (U : M.ModularCut) (hX : M.closure X ∈ U) :
    (M.projectBy U) ／ X = M ／ X := by
  rw [← project_delete_self, U.projectBy_project_eq_project_of_closure_mem hX,
    project_delete_self]

lemma projectBy_base_diff_singleton_iff (hU : U ≠ ⊥) (hB : M.IsBase B) (he : e ∈ B) :
    (M.projectBy U).IsBase (B \ {e}) ↔ M.closure (B \ {e}) ∉ U := by
  obtain rfl | hne := eq_or_ne U ⊤
  · simp only [projectBy_top, ModularCut.mem_top_iff, isFlat_closure, not_true_eq_false, iff_false]
    exact fun h' ↦ by simpa [he] using h'.eq_of_subset_isBase hB
  refine ⟨fun h ↦ ((projectBy_indep_iff_of_ne_top hne).1 h.indep).2, fun h ↦ ?_⟩
  refine Indep.isBase_of_ground_subset_closure ?_ fun x (hx : x ∈ M.E) ↦ ?_
  · rw [projectBy_indep_iff_of_ne_top hne, and_iff_left h]
    exact hB.indep.diff _
  rw [mem_closure_projectBy_iff, and_iff_left h, or_iff_not_imp_left]
  intro hx
  rwa [(hB.exchange_base_of_notMem_closure he hx).closure_eq, ← not_not (a := M.E ∈ U),
    ← ModularCut.eq_bot_iff]

lemma exists_diff_singleton_isBase_projectBy (hU_top : U ≠ ⊤) (hU_bot : U ≠ ⊥) (hB : M.IsBase B) :
    ∃ e ∈ B, (M.projectBy U).IsBase (B \ {e}) := by
  by_contra! hcon
  have aux {e} (he : e ∈ B) : M.closure (B \ {e}) ∈ U := by
    specialize hcon e he
    rwa [U.projectBy_base_diff_singleton_iff hU_bot hB he, not_not] at hcon
  rw [U.ne_bot_iff] at hU_bot
  rw [Ne, U.eq_top_iff] at hU_top
  apply hU_top
  obtain rfl | hne := B.eq_empty_or_nonempty
  · rwa [loops, hB.closure_eq]
  have _ := hne.to_subtype
  have hmod := (hB.indep.isModularFamily_of_subsets
    (Js := fun (e : B) ↦ B \ {e.1}) (iUnion_subset (by simp)))
  have h_inter := U.iInter_mem _ (by simpa) hmod.cls_isModularFamily
  rwa [hmod.iInter_closure_eq_closure_iInter, iInter_coe_set,
    biInter_diff_singleton_eq_diff _ hne, diff_self] at h_inter

lemma projectBy_eRank_add_one_eq (U : M.ModularCut) (hU_top : U ≠ ⊤) (hU_bot : U ≠ ⊥) :
    (M.projectBy U).eRank + 1 = M.eRank := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  obtain ⟨e, heB, hB'⟩ := U.exists_diff_singleton_isBase_projectBy hU_top hU_bot hB
  rw [← hB'.encard_eq_eRank, ← hB.encard_eq_eRank, encard_diff_singleton_add_one heB]

lemma projectBy_restrict (U : M.ModularCut) (R : Set α) :
    (M ↾ R).projectBy (U.restrict R) = (M.projectBy U) ↾ R := by
  refine ext_closure' rfl fun X (hXR : X ⊆ R) ↦ Set.ext fun e ↦ ?_
  by_cases! heR : e ∉ R; grind
  simp only [mem_closure_projectBy_iff, restrict_closure_eq', mem_union, mem_inter_iff, heR,
    and_true, mem_diff, true_and, mem_restrict_iff, not_and, projectBy_ground]
  by_cases! heE : e ∉ M.E
  · simp [heE]
  by_cases heX : e ∈ M.closure (X ∩ R)
  · simp [heX]
  simp only [heX, heE, not_true_eq_false, _root_.or_self, false_or, or_false]
  rw [and_iff_right ((M.closure_isFlat ..).isFlat_restrict' _),
    imp_iff_right ((M.closure_isFlat ..).isFlat_restrict' _),
    ← M.closure_inter_ground, union_inter_distrib_right, disjoint_sdiff_left.inter_eq,
    union_empty, closure_inter_ground, ← M.closure_inter_ground (_ ∪ _), union_inter_distrib_right,
    disjoint_sdiff_left.inter_eq, union_empty, closure_inter_ground, insert_inter_of_mem heR]
  refine ⟨fun h ↦ ⟨?_, fun hXU ↦ h.2 ?_⟩, fun h ↦ ⟨?_, fun hXU ↦ h.2 ?_⟩⟩
  · exact U.superset_mem h.1 (M.closure_isFlat ..) <| by grw [inter_subset_left, closure_closure]
  · refine U.superset_mem hXU (M.closure_isFlat ..) ?_
    grw [← M.closure_inter_ground]
    exact M.closure_subset_closure <| by grind
  · refine U.superset_mem h.1 (M.closure_isFlat ..) ?_
    grw [← M.closure_inter_ground]
    exact M.closure_subset_closure <| by grind
  exact U.superset_mem hXU (M.closure_isFlat ..) <| by grw [inter_subset_left, closure_closure]

lemma projectBy_delete (U : M.ModularCut) (D : Set α) :
    (M ＼ D).projectBy (U.delete D) = (M.projectBy U) ＼ D := by
  simp_rw [delete_eq_restrict, projectBy_ground, ← projectBy_restrict]
  rfl

lemma projectBy_principal_dep {X : Set α} (hXne : X.Nonempty) (hXE : X ⊆ M.E := by aesop_mat) :
    (M.projectBy (ModularCut.principal M X)).Dep X := by
  rw [dep_iff, and_iff_left (by simpa), projectBy_indep_iff]
  suffices M.Indep X → ¬ (X ∩ M.E) ⊆ M.loops by
    simpa [ModularCut.eq_top_iff, mem_principal_iff', inter_ground_subset_closure, loops]
  intro hXi h
  have hdj := hXi.disjoint_loops.mono_right h
  simp [inter_eq_self_of_subset_left hXE, hXne.ne_empty] at hdj

lemma projectBy_principal_eRk_eq_self (M : Matroid α) (hY : ¬ (X ⊆ M.closure Y))
    (hX : X ⊆ M.E := by aesop_mat) : (M.projectBy (ModularCut.principal M X)).eRk Y = M.eRk Y := by
  rw [← eRank_restrict, ← projectBy_restrict, (ModularCut.principal_restrict_eq_bot_iff hX).2 hY,
    projectBy_bot, eRank_restrict]

lemma projectBy_principal_eRk_add_one_eq (M : Matroid α) (hX : ¬ (X ⊆ M.loops))
    (hY : X ⊆ M.closure Y) : (M.projectBy (ModularCut.principal M X)).eRk Y + 1 = M.eRk Y := by
  rw [← eRank_restrict, ← projectBy_restrict, projectBy_eRank_add_one_eq, eRank_restrict]
  · rwa [Ne, principal_restrict_eq_top_iff]
  rwa [Ne, principal_restrict_eq_bot_iff, not_not]

/-- Lift a matroid using a modular cut of the dual. -/
def _root_.Matroid.liftBy (M : Matroid α) (U : M✶.ModularCut) : Matroid α := (M✶.projectBy U)✶

@[simp]
lemma liftBy_dual (M : Matroid α) (U : M✶.ModularCut) : (M.liftBy U)✶ = M✶.projectBy U := by
  rw [liftBy, dual_dual]

@[simp]
lemma projectBy_dual (M : Matroid α) (U : M✶.ModularCut) : (M✶.projectBy U)✶ = M.liftBy U := rfl

lemma liftBy_contract (U : M✶.ModularCut) (C : Set α) :
    ((M ／ C).liftBy ((U.delete C).copy (by simp))) = (M.liftBy U) ／ C := by
  rw [← dual_inj, liftBy_dual, projectBy_copy, dual_contract, liftBy_dual, projectBy_delete]

lemma liftBy_delete_eq_delete_of_dual_closure_mem (U : M✶.ModularCut) (hX : M✶.closure X ∈ U) :
    (M.liftBy U) ＼ X = M ＼ X := by
  rw [← dual_inj, dual_delete, liftBy_dual, projectBy_contract_eq_contract_of_closure_mem _ hX,
    dual_delete]

lemma liftBy_principal_codep (M : Matroid α) (hXne : X.Nonempty) (hX : X ⊆ M.E := by aesop_mat) :
    (M.liftBy (ModularCut.principal M✶ X)).Codep X := by
  rw [Codep, liftBy_dual]
  exact projectBy_principal_dep hXne hX

-- lemma foo (hY : (M.liftBy ((ModularCut.principal M✶ X))).Spanning Y) : M.Spanning Y := by
--   _

-- lemma bar (hI : (M.liftBy ((ModularCut.principal M✶ X))).Indep I) : M.Indep I := by
--   have hIE : I ⊆ M.E := sorry
--   rw [liftBy, ← coindep_def, coindep_iff_compl_spanning, projectBy_ground, dual_ground] at hI

-- lemma liftBy_principal_eRk_eq_self (hY : Y ⊆ M.closure X) :
--     (M.liftBy (ModularCut.principal M✶ X)).eRk Y = M.eRk Y := by

  -- obtain ⟨I, hI⟩ := M.exists_isBasis Y
  -- -- suffices hI' :


end Matroid.ModularCut
