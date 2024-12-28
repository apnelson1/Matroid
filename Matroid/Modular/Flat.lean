import Matroid.Connectivity.Local

namespace Matroid

open Set


variable {α : Type*} {M : Matroid α} {B I J X X' Y Y' F F' F₀ F₁ F₂ : Set α} {e : α}

section ModularFlat


/-- A `ModularFlat` is a set that is a modular pair with every flat. -/
@[mk_iff] structure ModularFlat (M : Matroid α) (X : Set α) : Prop where
  flat : M.Flat X
  modularPair : ∀ ⦃F⦄, M.Flat F → M.ModularPair X F

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma ModularFlat.subset_ground (h : M.ModularFlat X) : X ⊆ M.E :=
  h.flat.subset_ground

lemma modularFlat_iff_forall_exists_basis : M.ModularFlat X ↔
    M.Flat X ∧ ∀ ⦃F⦄, M.Flat F → ∃ I, M.Indep I ∧ M.Basis (X ∩ I) X ∧ M.Basis (F ∩ I) F := by
  simp [modularFlat_iff, modularPair_iff]

lemma modularSet_iff_closure :
    M.ModularFlat X ↔ M.Flat X ∧
      ∀ ⦃F⦄, M.Flat F → ∃ I, M.Indep I ∧ X ⊆ M.closure (X ∩ I) ∧ F ⊆ M.closure (F ∩ I) := by
  rw [modularFlat_iff_forall_exists_basis, and_congr_right_iff]
  refine fun _ ↦ ⟨fun h F hF ↦ ?_, fun h F hF ↦ ?_⟩
  · obtain ⟨I, hI, hI'⟩ := h hF
    refine ⟨I, hI, ?_⟩
    rwa [← hI.inter_basis_closure_iff_subset_closure_inter,
      ← hI.inter_basis_closure_iff_subset_closure_inter]
  obtain ⟨I, hI, hI'⟩ := h hF
  refine ⟨I, hI, ?_⟩
  rwa [hI.inter_basis_closure_iff_subset_closure_inter,
    hI.inter_basis_closure_iff_subset_closure_inter]

@[simp] lemma modularFlat_ground (M : Matroid α) : M.ModularFlat M.E :=
  ⟨M.ground_flat, fun _ hF ↦ (modularPair_of_subset hF.subset_ground Subset.rfl).symm⟩

@[simp] lemma modularFlat_loops (M : Matroid α) : M.ModularFlat (M.closure ∅) :=
  ⟨M.closure_flat ∅, fun _ h ↦ modularPair_of_subset h.loops_subset h.subset_ground⟩

@[simp] lemma modularFlat_empty (M : Matroid α) [Loopless M] : M.ModularFlat ∅ := by
  rw [← M.closure_empty_eq_empty]
  exact M.modularFlat_loops

@[simp] lemma modularFlat_closure_singleton (M : Matroid α) (e : α) :
    M.ModularFlat (M.closure {e}) where
  flat := M.closure_flat _
  modularPair F hF := by
    by_cases h : M.closure {e} ⊆ F
    · apply modularPair_of_subset h hF.subset_ground
    by_cases he : e ∈ M.E
    · refine (modularPair_singleton he hF.subset_ground fun hecl ↦ h ?_).closure_left
      rw [hF.closure] at hecl
      exact hF.closure_subset_of_subset (by simpa)
    rw [← closure_inter_ground, singleton_inter_eq_empty.2 he] at h
    exact (h hF.loops_subset).elim

lemma modularFlat_singleton (M : Matroid α) [Simple M] (e : α) (he : e ∈ M.E := by aesop_mat) :
    M.ModularFlat {e} := by
  rw [← closure_singleton_eq he]
  apply modularFlat_closure_singleton

lemma modularFlat_closure_subsingleton (M : Matroid α) (hX : X.Subsingleton) :
    M.ModularFlat (M.closure X) := by
  obtain rfl | ⟨e, rfl⟩ := hX.eq_empty_or_singleton <;> simp

/-- In a simple matroid, being a modular flat is the same as being a modular pair with each flat. -/
lemma ModularFlat.Flat [Simple M] : M.ModularFlat X ↔ ∀ ⦃F⦄, M.Flat F → M.ModularPair X F := by
  wlog hX : X ⊆ M.E
  · exact iff_of_false (fun h ↦ hX h.subset_ground)
      fun h ↦ hX ((h (M.closure_flat ∅)).subset_ground_left)
  rw [modularFlat_iff, and_iff_right_iff_imp, flat_iff_subset_closure_self]
  intro h e heX
  have heE := M.mem_ground_of_mem_closure heX
  obtain ⟨I, hIu, hIX, hIe, hIi⟩ := (h (M.singleton_flat (heE))).exists_common_basis
  rw [(M.toNonloop heE).indep.basis_iff_eq, inter_eq_right, singleton_subset_iff] at hIe
  refine by_contra fun heX' ↦ hIu.indep.not_mem_closure_diff_of_mem hIe
    (mem_of_mem_of_subset heX (M.closure_subset_closure_of_subset_closure ?_))
  exact hIX.subset_closure.trans
    (M.closure_subset_closure (subset_diff_singleton inter_subset_left (by simp [hIe, heX'])))

lemma ModularFlat.restrict_flat (hF : M.ModularFlat F) (hF' : M.Flat F') (hFF' : F ⊆ F') :
    (M ↾ F').ModularFlat F := by
  refine ⟨?_, fun F₁ hF₂ ↦ ?_⟩
  · rw [flat_restrict_iff', hF.flat.closure, diff_eq_empty.2 hF'.subset_ground,
      inter_eq_self_of_subset_left hFF', union_empty]
  obtain ⟨F₁, hF₁, rfl⟩ := (flat_restrict_iff hF'.subset_ground).1 hF₂
  exact (hF.modularPair (hF₁.inter hF')).restrict hFF' inter_subset_right

lemma ModularFlat.contract_subset {C : Set α} (hF : M.ModularFlat F) (hC : C ⊆ F) :
    (M ／ C).ModularFlat (F \ C) := by
  have hCE : C ⊆ M.E := hC.trans hF.subset_ground
  refine ⟨?_, fun F' hF' ↦ ?_⟩
  · rw [flat_contract_iff, diff_union_of_subset hC, and_iff_right hF.flat]
    exact disjoint_sdiff_left
  rw [flat_contract_iff] at hF'
  simpa [hF'.2.sdiff_eq_left] using (hF.modularPair hF'.1).contract_subset_closure (C := C)
    (by simpa [hF.flat.closure]) (M.subset_closure_of_subset' subset_union_right)

lemma Flat.modularFlat_iff_forall_skew_of_inter (hX : M.Flat X) :
    M.ModularFlat X ↔ ∀ ⦃F⦄, M.Flat F → X ∩ F ⊆ M.closure ∅ → M.Spanning (X ∪ F) → M.Skew X F := by
  rw [modularFlat_iff, and_iff_right hX]
  refine ⟨fun h F hF hr hs ↦ ?_, fun h Y hY ↦ ?_⟩
  · specialize h hF
    rw [modularPair_iff_skew_contract_inter (hr.trans (M.closure_subset_ground _)),
      contract_eq_delete_of_subset_loops hr, ← diff_inter_self_eq_diff,
      ← diff_inter_self_eq_diff (t := X), inter_comm F] at h
    rw [skew_iff_diff_loops_skew]
    exact h.of_delete.mono (diff_subset_diff_right hr) (diff_subset_diff_right hr)

  obtain ⟨W, hW⟩ := hY.exists_modularCompl M.ground_flat (M.closure_flat (X ∪ Y))
    (M.subset_closure_of_subset' subset_union_right) (M.closure_subset_ground _)

  obtain ⟨Z, hZ⟩ := (M.closure_flat ∅).exists_modularCompl hY (hX.inter hY)
    (subset_inter hX.loops_subset hY.loops_subset) inter_subset_right

  obtain ⟨X', hX'⟩ :=
    hZ.flat_right.exists_modularCompl hW.flat_right hY hZ.right_subset hW.subset_right

  specialize h hX'.flat_right ?_ ?_
  · simp [← hZ.inter_eq, ← hX'.inter_eq, subset_inter_iff, inter_subset_left, true_and,
      inter_subset_right, and_true, and_self]
    rw [← hW.inter_eq, subset_inter_iff]
    exact ⟨inter_subset_left.trans (M.subset_closure_of_subset' subset_union_left),
      inter_subset_right.trans hX'.right_subset⟩
  · rw [spanning_iff_ground_subset_closure
      (union_subset hX.subset_ground hX'.flat_right.subset_ground), ← hW.closure_union_eq,
      ← hX'.closure_union_eq, closure_closure_union_closure_eq_closure_union,
      union_comm X Y, ← union_union_distrib_left, ←  hZ.closure_union_eq]
    refine closure_subset_closure_of_subset_closure (union_subset ?_ (M.subset_closure _
      (union_subset hX.subset_ground hX'.flat_right.subset_ground)))
    exact M.closure_mono (union_subset_union inter_subset_left hX'.subset_right)

  obtain ⟨IZ, hIZ⟩ := M.exists_basis Z
  obtain ⟨IXY, hIXY⟩ := M.exists_basis (X ∩ Y)
  obtain ⟨IX', hIX', hIX'Z⟩ := hIZ.exists_basis_inter_eq_of_superset hX'.subset_right

  have hIY : M.Basis (IXY ∪ IZ) Y :=
    hZ.union_basis_top (M.empty_indep.basis_closure) hIXY hIZ (empty_subset _) (empty_subset _)

  obtain ⟨IU, hIU, hIU_eq⟩ := hIY.exists_basis_inter_eq_of_superset (Y := X ∪ Y) subset_union_right


  have hss : IZ ⊆ IX' := by simp [← hIX'Z]

  have hi1 := hX'.basis_inter_basis_eq hIZ hIY hIX' subset_union_right hss
  have hiu := hX'.union_basis_top hIZ hIY hIX' subset_union_right hss

  rw [modularPair_iff_exists_basis_basis]

  have hrw : IU \ IZ = IU ∩ X
  · nth_rewrite 1 [← inter_eq_self_of_subset_left hIU.subset]
    rw [inter_union_distrib_left, hIU_eq, union_diff_distrib, union_diff_right,
      ← union_diff_distrib, ((h.mono ?_ ?_).disjoint_of_indep_right hIZ.indep).sdiff_eq_left,
      union_eq_left, subset_inter_iff]
    · exact ⟨((subset_union_left.trans hIU_eq.symm.subset).trans inter_subset_left),
        hIXY.subset.trans inter_subset_left⟩
    · exact union_subset inter_subset_right (hIXY.subset.trans inter_subset_left)
    exact hss.trans hIX'.subset

  refine ⟨IU ∩ X, _, ?_, hIY, hIU.indep.subset
    (union_subset inter_subset_left (by simp [← hIU_eq]))⟩
  refine (hIU.indep.inter_right _).basis_of_subset_of_subset_closure inter_subset_right ?_

  suffices aux : X ⊆ (M ↾ X).closure (IU ∩ X)
  · rw [restrict_closure_eq _ inter_subset_right, subset_inter_iff] at aux
    exact aux.1

  have hdj := h.symm.diff_loops_disjoint_left.symm

  have hss' : X ⊆ (M ／ (X' \ M.closure ∅)).E := subset_diff.2 ⟨hX.subset_ground, hdj⟩

  replace h := h.mono_right (Y' := X' \ M.closure ∅) diff_subset
  rw [← h.symm.contract_restrict_eq, restrict_closure_eq _ inter_subset_right hss',
    subset_inter_iff, and_iff_left rfl.subset, contract_closure_eq, subset_diff, and_iff_left hdj,
    closure_union_congr_right (M.closure_diff_eq_closure_of_subset_loops _ rfl.subset),
    ← hrw, diff_union_eq_union_of_subset _ (hss.trans hIX'.subset),
    closure_union_congr_left hIU.closure_eq_closure, union_assoc]

  exact M.subset_closure_of_subset' subset_union_left

lemma Hyperplane.modularFlat_iff_forall_line {H : Set α} (hH : M.Hyperplane H) :
    M.ModularFlat H ↔ ∀ L, M.Line L → ¬ (H ∩ L ⊆ M.closure ∅) := by
  rw [hH.flat.modularFlat_iff_forall_skew_of_inter]
  refine ⟨fun h L hL hss ↦ ?_, fun h F hF hi hu ↦ ?_⟩
  · by_cases hLH : L ⊆ H
    · rw [inter_eq_self_of_subset_right hLH] at hss
      simpa [hL.er] using M.er_mono hss
    have hsk := h hL.flat hss (hH.spanning_of_ssuperset (by simpa))
    rw [← localEConn_eq_zero hH.subset_ground] at hsk
    have hr := hH.localEConn_add_one_eq hLH
    rw [localEConn_comm, hsk, hL.er] at hr
    simp at hr
  obtain ⟨I, hI⟩ := M.exists_basis F
  rw [skew_iff_closure_skew_right, ← hI.closure_eq_closure, ← skew_iff_closure_skew_right]
  obtain hI' | hI' := I.subsingleton_or_nontrivial
  · obtain rfl | ⟨e, rfl⟩ := hI'.eq_empty_or_singleton
    · apply skew_empty hH.subset_ground
    have he : M.Nonloop e := by simpa using hI.indep
    rw [he.skew_right_iff, hH.flat.closure]
    exact fun heH ↦ he.not_loop <| hi ⟨heH, by simpa using hI.subset⟩
  exfalso
  obtain ⟨e, f, hne, hss⟩ := nontrivial_iff_pair_subset.1 hI'
  refine h (M.closure {e,f}) ⟨M.closure_flat _, ?_⟩ (subset_trans ?_ hi)
  · rw [er_closure_eq, (hI.indep.subset hss).er, encard_pair hne]
  refine inter_subset_inter_right _ ?_
  rw [hF.eq_closure_of_basis hI]
  exact M.closure_mono hss

lemma ModularFlat.exists_parallel_mem_of_contract (hX : M.ModularFlat X) {C : Set α}
    (he : (M ／ C).Nonloop e) (hecl : e ∈ (M ／ C).closure X) : ∃ f ∈ X, (M ／ C).Parallel e f := by
  wlog hC : M.Indep C with aux
  · obtain ⟨I, hI⟩ := M.exists_basis' C
    rw [hI.contract_eq_contract_delete, delete_nonloop_iff] at he
    rw [hI.contract_eq_contract_delete, delete_closure_eq] at hecl
    obtain ⟨f, hfX, hef⟩ := aux hX (C := I) he.1
      (mem_of_mem_of_subset hecl.1 (closure_subset_closure _ diff_subset)) hI.indep
    refine ⟨f, hfX, ?_⟩
    rw [hI.contract_eq_contract_delete, delete_parallel_iff, and_iff_right he.2, and_iff_right hef]
    intro ⟨hfC, hfI⟩
    have hIf := hef.nonloop_right
    rw [contract_nonloop_iff, hI.closure_eq_closure] at hIf
    exact hIf.2 <| M.mem_closure_of_mem' hfC
  have heE := he.of_contract.mem_ground

  have hnl := contract_nonloop_iff.1 he
  rw [contract_closure_eq] at hecl

  obtain ⟨J, hJ, hJX, hJI, hi⟩ := (hX.modularPair (M.closure_flat C)).exists_common_basis
  have hJE := hJ.indep.subset_ground
  have hsk := hJ.indep.subset_skew_diff (J := J ∩ X) inter_subset_left

  rw [skew_iff_closure_skew_left (inter_subset_left.trans hJE), diff_self_inter,
    hJX.closure_eq_closure, ← skew_iff_closure_skew_left hX.subset_ground] at hsk

  have hnsk : ¬ M.Skew X (M.closure (insert e (J \ X)))
  · rw [← skew_iff_closure_skew_right (insert_subset heE hsk.subset_ground_right),
      skew_comm, skew_insert_iff heE, diff_union_self,
      closure_union_congr_left hJ.closure_eq_closure, union_comm X, union_assoc, union_self,
      closure_union_closure_left_eq, union_comm]
    simp only [hsk.symm, hecl.1, forall_const, true_and]
    refine not_mem_subset (M.closure_subset_closure_of_subset_closure ?_) hnl.2
    rw [diff_subset_iff]
    exact hJ.subset

  by_contra! hcon

  refine hnsk <| (hX.modularPair (M.closure_flat _)).skew_of_inter_subset_loops ?_
  nth_rewrite 1 [← diff_union_inter X (M.closure (J \ X)), union_inter_distrib_right]
  rw [union_subset_iff, inter_assoc,
    inter_eq_self_of_subset_left (M.closure_subset_closure (subset_insert _ _)),
    and_iff_left hsk.closure_skew_right.inter_subset_loops, ← inter_diff_right_comm,
    diff_subset_iff, union_eq_self_of_subset_right (M.closure_subset_closure (empty_subset _))]

  refine fun f ⟨hfX, hfcl⟩  ↦ by_contra fun hfcl' ↦ hcon f hfX ?_

  rw [he.parallel_iff_mem_closure, contract_closure_eq, singleton_union, mem_diff,
    and_iff_left hecl.2]

  refine mem_of_mem_of_subset (Matroid.closure_exchange ⟨hfcl, hfcl'⟩).1 ?_
  refine M.closure_subset_closure_of_subset_closure (insert_subset ?_ ?_)
  · exact M.mem_closure_of_mem' (mem_insert _ _) (mem_ground_of_mem_closure hfcl)
  rw [diff_subset_iff]
  exact hJ.subset.trans <| union_subset_union_right _
    (M.closure_subset_closure (subset_insert _ _))



lemma Flat.modularSet_iff_forall_contract_exists_parallel (hX : M.Flat X) :
    M.ModularFlat X ↔ ∀ ⦃C : Set α⦄ ⦃e⦄, Disjoint C X → (M ／ C).Nonloop e → e ∈ (M ／ C).closure X →
      ∃ f ∈ X, (M ／ C).Parallel e f := by
  refine ⟨fun h C e _ henl hecl ↦ h.exists_parallel_mem_of_contract henl hecl , fun h ↦ ?_⟩
  rw [hX.modularFlat_iff_forall_skew_of_inter]
  intro F hF hXFcl hXFsp
  obtain ⟨I, hI⟩ := M.exists_basis F
  obtain ⟨J, hJ⟩ := M.exists_basis X

  rw [skew_iff_closure_skew, ← hI.closure_eq_closure, ← hJ.closure_eq_closure,
    ← skew_iff_closure_skew, Indep.skew_iff_disjoint_union_indep hJ.indep hI.indep,
    disjoint_iff_inter_eq_empty, (hJ.indep.inter_right _).eq_empty_of_subset_loops
      ((inter_subset_inter hJ.subset hI.subset).trans hXFcl), and_iff_right rfl,
      Indep.union_indep_iff_forall_not_mem_closure_right hJ.indep hI.indep]
  intro e heIJ hecl

  have hdj : Disjoint X (I \ {e})
  · rw [disjoint_iff_inter_eq_empty, ((hI.indep.diff _).inter_left _).eq_empty_of_subset_loops]
    exact (inter_subset_inter_right _ (diff_subset.trans hI.subset)).trans hXFcl

  specialize h hdj.symm (e := e)
  simp only [contract_ground, subset_diff, hJ.subset_ground, true_and, contract_closure_eq, ←
    closure_union_congr_left hJ.closure_eq_closure, mem_diff, hecl, mem_singleton_iff,
    not_true_eq_false, and_false, not_false_eq_true, and_self, contract_nonloop_iff, hdj,
    hI.indep.subset_ground heIJ.1, hI.indep.not_mem_closure_diff_of_mem heIJ.1, forall_const] at h

  obtain ⟨f, hfX, hef⟩ := h

  refine hef.nonloop_right.of_contract.not_loop (hXFcl ⟨hfX, ?_⟩)

  replace hef := hef.symm.mem_closure
  rw [contract_closure_eq, union_diff_self, singleton_union, insert_eq_of_mem heIJ.1,
    ← hF.eq_closure_of_basis hI] at hef
  exact hef.1

/-- If `X` is a modular set, then any nonloop `e` spanned by `X` in a minor `N` is parallel
in `N` to an element of `X`. -/
lemma ModularFlat.exists_parallel_mem_of_minor (hX : M.ModularFlat X) {N : Matroid α}
    (hNM : N ≤m M) (hXE : X ⊆ N.E) (he : N.Nonloop e) (heX : e ∈ N.closure X) :
    ∃ f ∈ X, N.Parallel e f := by
  obtain ⟨I, R, hI, hdj, hsp, rfl⟩ := hNM.exists_eq_contract_spanning_restrict
  rw [restrict_closure_eq _ (show X ⊆ R from hXE) hsp.subset_ground] at heX
  obtain ⟨f, hfX, hef⟩ := hX.exists_parallel_mem_of_contract he.of_restrict heX.1
  refine ⟨f, hfX, ?_⟩
  rw [restrict_parallel_iff, and_iff_right hef, and_iff_right heX.2]
  exact hXE hfX

lemma Flat.modularSet_iff_forall_minor_exists_parallel (hX : M.Flat X) :
    M.ModularFlat X ↔ ∀ ⦃N : Matroid α⦄ e, N ≤m M → X ⊆ N.E → e ∈ N.closure X → N.Nonloop e →
      ∃ f ∈ X, N.Parallel e f := by
  refine ⟨fun h N e hNM hXE heX hnl ↦ h.exists_parallel_mem_of_minor hNM hXE hnl heX, fun h ↦ ?_⟩
  rw [hX.modularSet_iff_forall_contract_exists_parallel]
  intro C e hCX he hecl
  exact h e (M.contract_minor C) (subset_diff.2 ⟨hX.subset_ground, hCX.symm⟩) hecl he

-- Is this actually true? Easy-ish to show it's true for pairs.
-- lemma ModularFlat.iInter {ι : Type*} [Nonempty ι] (Xs : ι → Set α) (hXs : ∀ i, M.ModularFlat (Xs i))
--     (hF : ∀ i, M.Flat (Xs i)) : M.ModularFlat (⋂ i, Xs i) := by
--   rw [(Flat.iInter hF).modularSet_iff_forall_contract_exists_parallel]
--   intro C e hCdj henl hecl

--   rw [Flat.modularSet_iff_forall_contract_exists_parallel]

-- -- y ≤ v
-- -- (y ⊔ x) ⊓ v = y ⊔ (x ⊓ v)
lemma Flat.modularSet_iff_distrib_of_subset (hF : M.Flat F) :
    M.ModularFlat F ↔ ∀ X Y, M.Flat X → M.Flat Y → X ⊆ Y →
        M.closure (X ∪ F) ∩ Y = M.closure (X ∪ (F ∩ Y)) := by
  refine ⟨fun h X Y hX hY hXY ↦ subset_antisymm ?_ (subset_inter ?_ ?_), fun h ↦ ?_⟩
  ·
    -- have hp := h.modularPair hY
    -- rw [modularPair_iff_skew_contract_inter sorry] at hp
    obtain ⟨I, hIu, hIF, hIY, hIi⟩ := (h.modularPair hY).exists_common_basis
    have hmod' := (h.modularPair hY).contract_subset_left (C := I \ Y)
        (diff_subset_iff.2 (union_comm _ _ ▸ hIu.subset))
    rw [sdiff_eq_left.2 disjoint_sdiff_right] at hmod'
    sorry

  · refine M.closure_mono (union_subset_union_right _ inter_subset_left)
  · rw [← hY.closure]
    exact M.closure_subset_closure_of_subset_closure
      (union_subset (by rwa [hY.closure]) inter_subset_right)
  rw [modularFlat_iff_forall_skew_of_inter hF]
  intro Z hZ hdj hsp
  obtain ⟨I, hI⟩ := M.exists_basis F
  obtain ⟨J, hJ⟩ := M.exists_basis Z
  rw [← skew_iff_bases_skew hI hJ, hI.indep.skew_iff_disjoint_union_indep hJ.indep,
    disjoint_iff_inter_eq_empty, (hI.indep.inter_right J).eq_empty_of_subset_loops
    ((inter_subset_inter hI.subset hJ.subset).trans hdj), and_iff_right rfl]

  rw [hI.indep.union_indep_iff_forall_not_mem_closure_right hJ.indep]
  refine fun e ⟨heJ, heI⟩ hecl ↦ hJ.indep.not_mem_closure_diff_of_mem heJ ?_
  have hcon := h _ _ (M.closure_flat (J \ {e})) (M.closure_flat J) (M.closure_mono diff_subset)
  rw [closure_union_closure_left_eq, ← closure_union_congr_right hI.closure_eq_closure,
    union_comm, ← hZ.eq_closure_of_basis hJ, hdj.antisymm (hF.inter hZ).loops_subset,
      closure_closure_union_closure_eq_closure_union, union_empty] at hcon
  exact hcon.subset ⟨hecl, hJ.subset heJ⟩






end ModularFlat


section Modular

/-- A modular matroid is one where every flat is modular. The simple finite modular matroids
are the free matroids, the rank-two uniform matroids, the projective planes, and the
finite Desarguesian projective geometries. -/
def Modular (M : Matroid α) : Prop := ∀ ⦃F⦄, M.Flat F → M.ModularFlat F

lemma Modular.modularSet_of_flat (hM : M.Modular) (hF : M.Flat F) : M.ModularFlat F :=
  hM hF

lemma modular_iff : M.Modular ↔ ∀ ⦃F⦄, M.Flat F → M.ModularFlat F := Iff.rfl

lemma modular_iff_forall_modularPair :
    M.Modular ↔ ∀ ⦃F F'⦄, M.Flat F → M.Flat F' → M.ModularPair F F' := by
  simp_rw [Modular, modularFlat_iff]
  aesop

lemma Modular.modularPair (h : M.Modular) (hF : M.Flat F) (hF' : M.Flat F') : M.ModularPair F F' :=
  (h hF).modularPair hF'

lemma freeOn_modular (E : Set α) : (freeOn E).Modular := by
  intro F
  simp only [freeOn_flat_iff, modularFlat_iff, modularPair_iff, freeOn_indep_iff, freeOn_basis_iff,
    inter_eq_left]
  aesop

lemma Modular.restrict_flat (hM : M.Modular) (hF : M.Flat F) : (M ↾ F).Modular := by
  intro F' hF'
  obtain ⟨F₁, hF₁, rfl⟩ := (flat_restrict_iff hF.subset_ground).1 hF'
  exact ModularFlat.restrict_flat (hM (hF₁.inter hF)) hF hF'.subset_ground

lemma Modular.contract (hM : M.Modular) (C : Set α) : (M ／ C).Modular := by
  wlog h : C ⊆ M.E generalizing C with h'
  · rw [← contract_inter_ground_eq]
    apply h' _ inter_subset_right

  refine fun F hF ↦ ⟨hF, fun F' hF' ↦ ?_⟩
  rw [flat_contract_iff] at hF hF'
  convert (hM.modularPair (M.closure_flat (F ∪ C)) (M.closure_flat (F' ∪ C))).contract (C := C)
    (M.subset_closure_of_subset' subset_union_right)
    (M.subset_closure_of_subset' subset_union_right)

  · rw [hF.1.closure, union_diff_right, hF.2.sdiff_eq_left]
  rw [hF'.1.closure, union_diff_right, hF'.2.sdiff_eq_left]

-- lemma modular_foo (h : ∀ ⦃L H⦄, M.Line L → M.Hyperplane H → ¬ (L ∩ H ⊆ M.closure ∅))

-- lemma modular_foo : M.Modular ↔ ∀ ⦃L H⦄, M.Line L → M.Hyperplane H → M.er (L ∩ H) ≠ 0 := by
--   refine ⟨fun h L H hL hH ↦ ?_, fun h ↦ ?_⟩
--   · have := h.localConn




end Modular
