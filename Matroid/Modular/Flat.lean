import Matroid.Connectivity.Local
import Matroid.ForMathlib.Data.Set.Finite

namespace Matroid

open Set


variable {α : Type*} {M : Matroid α} {B I J X X' Y Y' F F' F₀ F₁ F₂ : Set α} {e : α}

section ModularFlat


/-- A `ModularFlat` is a flat that is a modular pair with every other flat. -/
@[mk_iff] structure ModularFlat (M : Matroid α) (X : Set α) : Prop where
  flat : M.Flat X
  modularPair : ∀ ⦃F⦄, M.Flat F → M.ModularPair X F

lemma Flat.modularFlat_of_forall (hX : M.Flat X) (h : ∀ ⦃F⦄, M.Flat F → M.ModularPair X F) :
    M.ModularFlat X :=
  ⟨hX, h⟩

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

lemma Flat.modularFlat_of_eRk_le_one (hF : M.Flat F) (hr : M.eRk F ≤ 1) : M.ModularFlat F := by
  obtain ⟨I, hI⟩ := M.exists_basis F
  rw [hI.eRk_eq_encard, encard_le_one_iff_eq] at hr
  rw [← hF.closure, ← hI.closure_eq_closure]
  obtain rfl | ⟨e, rfl⟩ := hr <;> simp

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

/-- A flat is modular iff it is skew to every complementary flat. -/
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

/-- A hyperplane is a modular flat iff it meets every line. -/
lemma Hyperplane.modularFlat_iff_forall_line {H : Set α} (hH : M.Hyperplane H) :
    M.ModularFlat H ↔ ∀ L, M.Line L → ¬ (L ∩ H ⊆ M.closure ∅) := by
  simp_rw [inter_comm _ H]
  rw [hH.flat.modularFlat_iff_forall_skew_of_inter]
  refine ⟨fun h L hL hss ↦ ?_, fun h F hF hi hu ↦ ?_⟩
  · by_cases hLH : L ⊆ H
    · rw [inter_eq_self_of_subset_right hLH] at hss
      simpa [hL.eRk] using M.eRk_mono hss
    have hsk := h hL.flat hss (hH.spanning_of_ssuperset (by simpa))
    rw [← localEConn_eq_zero hH.subset_ground] at hsk
    have hr := hH.localEConn_add_one_eq hLH
    rw [localEConn_comm, hsk, hL.eRk] at hr
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
  · rw [eRk_closure_eq, (hI.indep.subset hss).eRk, encard_pair hne]
  refine inter_subset_inter_right _ ?_
  rw [hF.eq_closure_of_basis hI]
  exact M.closure_mono hss

lemma Line.modularFlat_of_forall_hyperplane {L : Set α} (hL : M.Line L)
    (h : ∀ ⦃H⦄, M.Hyperplane H → ¬ (L ∩ H ⊆ M.closure ∅)) : M.ModularFlat L := by
  rw [hL.flat.modularFlat_iff_forall_skew_of_inter]
  intro F hF hcl hsp
  rw [← localEConn_eq_zero, ← ENat.lt_one_iff_eq_zero, ← not_le]
  intro hle
  have hlc := M.localEConn_add_eRelRk_union_eq_eRk L F
  rw [hL.eRk, ← eRelRk_closure_right, hsp.closure_eq, add_comm] at hlc
  obtain h_eq | hlt := hle.eq_or_lt
  · rw [← h_eq, (show (2 : ℕ∞) = 1 + 1 from rfl), WithTop.add_right_cancel_iff (by simp),
      ← hF.hyperplane_iff_eRelRk_ground_eq_one] at hlc
    exact h hlc hcl
  replace hlt := show (2 : ℕ∞) ≤ _ from Order.add_one_le_of_lt hlt
  rw [← zero_add (a := M.localEConn L F), ← hlc, WithTop.add_le_add_iff_right,
    nonpos_iff_eq_zero, eRelRk_ground_eq_zero_iff, spanning_iff_closure_eq, hF.closure] at hlt
  · rw [hlt, inter_eq_self_of_subset_left hL.subset_ground] at hcl
    simpa [hL.eRk] using M.eRk_mono hcl
  rw [← lt_top_iff_ne_top]
  exact (M.localEConn_le_eRk_left _ _).trans_lt (lt_top_iff_ne_top.2 (by simp [hL.eRk]))

/-- If `X` is a modular flat, then in any contraction-minor in which `X` spans a nonloop `e`,
there is an element of `X` parallel to `e`.
TODO: clean up this proof. -/
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

lemma Flat.modularFlat_iff_forall_contract_exists_parallel (hX : M.Flat X) :
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

/-- If `X` is a modular flat, then any nonloop `e` spanned by `X` in a minor `N` is parallel
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
  rw [hX.modularFlat_iff_forall_contract_exists_parallel]
  intro C e hCX he hecl
  exact h e (M.contract_minor C) (subset_diff.2 ⟨hX.subset_ground, hCX.symm⟩) hecl he

lemma ModularFlat.inter_insert_closure_point_of_skew (hF : M.ModularFlat F)
    (hFX : M.Skew F X) (heFX : e ∈ M.closure (F ∪ X)) (heX : e ∉ M.closure X) :
    M.Point (F ∩ M.closure (insert e X)) := by
  have hc := (hF.modularPair (M.closure_flat (insert e X))).localEConn_eq_eRk_inter
  rw [localEConn_closure_right, localEConn_insert_right_eq_add_one heX heFX, hFX.localEConn,
    zero_add] at hc
  rw [Point, ← hc, and_iff_left rfl]
  exact hF.flat.inter (M.closure_flat _)

section Lattice

/-- This isn't true with just a simple `ModularPair F X` assumption,
for example when `M` is a triangle `{e,f,g}` in which `X = {e} ⊆ {e,f} = Y` and `F = {g}`.-/
lemma ModularFlat.distrib_of_subset (hF : M.ModularFlat F) (hX : M.Flat X) (hY : M.Flat Y)
    (hXY : X ⊆ Y) : M.closure (X ∪ F) ∩ Y = M.closure (X ∪ (F ∩ Y)) := by
  refine subset_antisymm ?_ (subset_inter ?_ ?_)
  · refine fun e ⟨heXF, heY⟩ ↦ by_contra fun hecl ↦ ?_
    have heX : e ∉ X := not_mem_subset (M.subset_closure_of_subset' subset_union_left) hecl

    obtain ⟨f, hfF, hef⟩ := hF.exists_parallel_mem_of_contract (C := X) (e := e)
      (by simp [hY.subset_ground heY, not_mem_subset (M.closure_mono subset_union_left) hecl])
      (by simp [heX, union_comm F, heXF])

    replace hef := show e ∈ M.closure (insert f X) ∧ e ∉ X by simpa using hef.mem_closure
    have hfY := (Matroid.closure_exchange ⟨hef.1, by simpa [hX.closure]⟩).1
    refine hecl (mem_of_mem_of_subset hef.1 (M.closure_subset_closure ?_))
    refine insert_subset (.inr ⟨hfF, ?_⟩) subset_union_left
    exact mem_of_mem_of_subset hfY (hY.closure_subset_of_subset (insert_subset heY hXY))
  · refine M.closure_mono (union_subset_union_right _ inter_subset_left)
  rw [← hY.closure]
  exact M.closure_subset_closure_of_subset_closure
      (union_subset (by rwa [hY.closure]) inter_subset_right)

lemma Flat.modularFlat_iff_forall_distrib_of_subset (hF : M.Flat F) :
    M.ModularFlat F ↔ ∀ X Y, M.Flat X → M.Flat Y → X ⊆ Y →
        M.closure (X ∪ F) ∩ Y ⊆ M.closure (X ∪ (F ∩ Y)) := by
  refine ⟨fun h X Y hX hY hXY ↦ (h.distrib_of_subset hX hY hXY).subset, fun h ↦ ?_⟩
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

lemma ModularPair.distrib_of_subset_left (hFX : M.ModularPair F X) (hF : M.Flat F) (hYF : Y ⊆ F) :
    F ∩ M.closure (X ∪ Y) = M.closure ((F ∩ X) ∪ Y) := by
  have hss : Y \ (F ∩ X) ⊆ F \ X
  · rw [← diff_self_inter (s := F)]
    exact diff_subset_diff_left hYF
  have hsk := hFX.skew_contract_inter.contract_subset_left hss
  rw [contract_contract, union_diff_self, diff_diff_right, diff_diff_right,
    (disjoint_sdiff_left.mono_right inter_subset_right).inter_eq, union_empty,
    (disjoint_sdiff_left.mono_right inter_subset_left).inter_eq, union_empty] at hsk

  have h := hsk.inter_closure_eq
  simp only [contract_closure_eq, diff_inter_diff_right, empty_union] at h
  rw [union_comm (F ∩ X), ← union_assoc, ← union_assoc, diff_union_self, union_right_comm,
    diff_union_inter, union_eq_self_of_subset_right hYF, diff_union_self, union_right_comm,
    inter_comm F, diff_union_inter, hF.closure, union_comm Y, inter_comm X] at h

  apply_fun (· ∪ (F ∩ X ∪ Y)) at h
  have hE : F ∩ X ∪ Y ⊆ M.E := union_subset (inter_subset_left.trans hF.subset_ground)
    (hYF.trans hF.subset_ground)
  rwa [diff_union_of_subset (M.subset_closure _), diff_union_of_subset] at h
  refine subset_inter (union_subset inter_subset_left hYF) (M.subset_closure_of_subset' ?_)
  exact union_subset_union_left _ inter_subset_right

lemma modularPair_iff_forall_distrib_of_subset_left (hF : M.Flat F) (hXE : X ⊆ M.E) :
    M.ModularPair F X ↔ ∀ Y ⊆ F, M.Flat Y → F ∩ M.closure (X ∪ Y) ⊆ M.closure ((F ∩ X) ∪ Y) := by
  refine ⟨fun h Y hYF hY ↦ (h.distrib_of_subset_left hF hYF).subset, fun h ↦ ?_⟩
  have hFXE : F ∩ X ⊆ M.E := (inter_subset_left.trans hF.subset_ground)
  rw [modularPair_iff_skew_contract_inter hFXE]
  obtain ⟨I, hI⟩ := M.exists_basis (F ∩ X)
  obtain ⟨IF, hIF, hIF_eq⟩ := hI.exists_basis_inter_eq_of_superset inter_subset_left
  obtain ⟨IX, hIX, hIX_eq⟩ := hI.exists_basis_inter_eq_of_superset inter_subset_right
  have hIIF : I ⊆ IF := by simp [← hIF_eq]
  have hIIX : I ⊆ IX := by simp [← hIX_eq]
  have hIF' := hI.contract_diff_basis_diff hIF hIIF
  have hIX' := hI.contract_diff_basis_diff hIX hIIX

  rw [diff_inter_self_eq_diff] at hIX'
  rw [diff_self_inter] at hIF'

  rw [hI.contract_eq_contract_delete, skew_delete_iff]
  refine ⟨?_, disjoint_sdiff_left.mono_right (diff_subset.trans inter_subset_right),
    disjoint_sdiff_left.mono_right (diff_subset.trans inter_subset_left)⟩

  suffices hIu : M.Indep (IF ∪ IX)
  · rw [← skew_iff_bases_skew hIF' hIX', hIF'.indep.skew_iff_disjoint_union_indep hIX'.indep,
      hI.indep.contract_indep_iff, ← union_diff_distrib, diff_union_of_subset,
      and_iff_right disjoint_sdiff_left, and_iff_left hIu]
    · rw [disjoint_iff_inter_eq_empty, diff_inter_diff_right, diff_eq_empty]
      rw [hI.eq_of_subset_indep (hIF.indep.inter_right _) (subset_inter hIIF hIIX)]
      exact inter_subset_inter hIF.subset hIX.subset
    exact hIIF.trans subset_union_left

  rw [union_comm, hIX.indep.union_indep_iff_forall_not_mem_closure_right hIF.indep]
  refine fun e ⟨heIF, heIX⟩ hecl ↦ hIF.indep.not_mem_closure_diff_of_mem heIF ?_
  specialize h _ (hF.closure_subset_of_subset (diff_subset.trans hIF.subset))
    (M.closure_flat (IF \ {e}))
  simp only [closure_union_closure_right_eq, ← closure_union_congr_left hIX.closure_eq_closure,
    ← closure_union_congr_left hI.closure_eq_closure] at h
  rw [union_eq_self_of_subset_left (subset_diff_singleton hIIF (not_mem_subset hIIX heIX))] at h

  exact h.subset ⟨hIF.subset heIF, hecl⟩

lemma ModularFlat.distrib_of_subset_self (hF : M.ModularFlat F) (hX : M.Flat X) (hY : Y ⊆ F) :
    F ∩ M.closure (X ∪ Y) = M.closure (F ∩ X ∪ Y) := by
  rw [← closure_union_closure_left_eq,
    (hF.modularPair (M.closure_flat X)).distrib_of_subset_left hF.flat hY, hX.closure]

lemma Flat.modularFlat_iff_forall_distrib_of_subset_self (hF : M.Flat F) :
    M.ModularFlat F ↔ ∀ X Y, M.Flat X → M.Flat Y → Y ⊆ F →
      F ∩ M.closure (X ∪ Y) ⊆ M.closure ((F ∩ X) ∪ Y) := by
  refine ⟨fun h X Y hX hY hYF ↦ ?_, fun h ↦ ?_⟩
  · exact ((h.modularPair hX).distrib_of_subset_left h.flat hYF).subset
  rw [hF.modularFlat_iff_forall_skew_of_inter]
  rintro X hX hFX -
  obtain ⟨I, hI⟩ := M.exists_basis F
  obtain ⟨J, hJ⟩ := M.exists_basis X
  rw [← skew_iff_bases_skew hI hJ, hI.indep.skew_iff_disjoint_union_indep hJ.indep,
    disjoint_iff_inter_eq_empty, (hI.indep.inter_right J).eq_empty_of_subset_loops
    ((inter_subset_inter hI.subset hJ.subset).trans hFX), and_iff_right rfl]
  rw [union_comm, hJ.indep.union_indep_iff_forall_not_mem_closure_right hI.indep]
  intro e ⟨heI, heJ⟩ hecl
  specialize h _ _ hX (M.closure_flat (I \ {e}))
    (hF.closure_subset_of_subset (diff_subset.trans hI.subset))

  replace h := h.subset ⟨hI.subset heI, ?_⟩
  · rw [hFX.antisymm (hF.inter hX).loops_subset,
      closure_closure_union_closure_eq_closure_union, empty_union] at h
    exact hI.indep.not_mem_closure_diff_of_mem heI h

  rwa [← closure_union_congr_left hJ.closure_eq_closure, closure_union_closure_right_eq]

/-- If `F` gives a modular pair with every set in some directed collection, then it gives
a modular pair with the span of their union. -/
lemma Flat.modularPair_iUnion_of_directed [Finitary M] {ι : Type*} {D : ι → Set α}
    (hF : M.Flat F) (hdir : Directed (· ⊆ ·) D) (hFD : ∀ i, M.ModularPair F (D i)) :
    M.ModularPair F (M.closure (⋃ i, D i)) := by
  obtain hι | hι := isEmpty_or_nonempty ι
  · simp only [iUnion_of_empty]
    exact M.modularPair_loops hF.subset_ground

  rw [modularPair_iff_forall_distrib_of_subset_left hF (M.closure_subset_ground _)]
  intro Y hYss hY
  have hdir' : Directed (· ⊆ ·) fun i ↦ M.closure (D i ∪ Y)
  · intro i j
    obtain ⟨k, hik, hjk⟩ := hdir i j
    exact ⟨k, M.closure_mono (union_subset_union_left _ hik),
      M.closure_mono (union_subset_union_left _ hjk)⟩

  have hrw : ⋃ i, (F ∩ M.closure (D i ∪ Y)) = ⋃ i, M.closure (F ∩ D i ∪ Y) :=
    iUnion_congr fun i ↦ by rw [(hFD i).distrib_of_subset_left hF hYss]

  rw [closure_union_closure_left_eq, iUnion_union, ← closure_iUnion_closure_eq_closure_iUnion,
    inter_iUnion_closure_of_directed hF (fun i ↦ M.closure_flat _) hdir', hrw,
    closure_iUnion_closure_eq_closure_iUnion, ← iUnion_union, ← inter_iUnion]

  refine M.closure_mono (union_subset_union_left _ (inter_subset_inter_right _ ?_))
  exact M.subset_closure _ <| (iUnion_subset fun i ↦ (hFD i).subset_ground_right)

/-- The union of a directed family of modular flats spans a modular flat.
Possibly true without `Finitary`. -/
lemma ModularFlat.closure_iUnion_of_directed [Finitary M] {ι : Type*} (Fs : ι → Set α)
    (hFs : ∀ i, M.ModularFlat (Fs i)) (hdir : Directed (· ⊆ ·) Fs) :
    M.ModularFlat (M.closure (⋃ i, Fs i)) := by
  rw [modularFlat_iff, and_iff_right (M.closure_flat _)]
  exact fun X hX ↦ (hX.modularPair_iUnion_of_directed hdir
    (fun i ↦ ((hFs i).modularPair hX).symm)).symm

lemma ModularFlat.inter (hX : M.ModularFlat X) (hY : M.ModularFlat Y) : M.ModularFlat (X ∩ Y) := by
  have hXY := hX.flat.inter hY.flat
  rw [hXY.modularFlat_iff_forall_distrib_of_subset_self]
  intro S T hS hT hST
  rw [subset_inter_iff] at hST
  rw [inter_comm, ← inter_assoc, inter_comm _ X, inter_comm _ Y, ← inter_assoc, inter_comm Y,
    inter_assoc, hY.distrib_of_subset_self hS hST.2,
    hX.distrib_of_subset_self (hY.flat.inter hS) hST.1, ← inter_assoc]

lemma ModularFlat.biInter_finite {ι : Type*} {Xs : ι → Set α} {A : Set ι}
    (hXs : ∀ i, M.ModularFlat (Xs i)) (hAne : A.Nonempty) (hAfin : A.Finite) :
    M.ModularFlat (⋂ i ∈ A, Xs i) := by
  revert hAne
  refine hAfin.induction_on_subset _ (by simp) ?_
  simp only [insert_nonempty, mem_insert_iff, iInter_iInter_eq_or_left, forall_const]
  intro i B hiA hBA hiB h
  obtain rfl | hBne := B.eq_empty_or_nonempty
  · simp [hXs i]
  exact (hXs i).inter (h hBne)


/-- This might be true without `Finitary`. The proof follows Sachs 1960  -/
lemma ModularFlat.iInter {ι : Type*} [Nonempty ι] [Finitary M] {X : ι → Set α}
    (hX : ∀ i, M.ModularFlat (X i)) : M.ModularFlat (⋂ i, X i) := by
  classical
  -- We can assume the collection is directed, by instead considering the collection
  -- of all its finite intersections.
  wlog hdir : Directed (fun A B ↦ B ⊆ A) X generalizing X ι with aux
  · set Z := fun S : Finset ι ↦ (⋂ i ∈ S, X i) ∩ M.E with hZ_def
    have hZ' : ∀ ⦃S : Finset ι⦄, S.Nonempty → Z S = (⋂ i ∈ S, X i) := by
      refine fun S hS ↦ inter_eq_left.2 (iInter_subset_of_subset hS.choose ?_)
      simp [hS.choose_spec, (hX _).subset_ground]
    have hZ_mono : ∀ ⦃A B⦄, B ⊆ A → Z A ⊆ Z B :=
      fun A B h ↦ inter_subset_inter_left _ <| biInter_mono h fun x a ⦃a⦄ a ↦ a
    specialize aux (X := Z) (fun S ↦ ?_) ?_
    · obtain rfl | hne := S.eq_empty_or_nonempty
      · simp [hZ_def]
      convert ModularFlat.biInter_finite hX (A := (S : Set ι)) (by simpa) (by simp)
      simp [hZ' hne]
    · exact fun A B ↦ ⟨A ∪ B, hZ_mono Finset.subset_union_left, hZ_mono Finset.subset_union_right⟩
    convert aux
    simp only [hZ_def, subset_antisymm_iff, subset_iInter_iff, subset_inter_iff]
    exact ⟨fun S ↦ ⟨fun i hi ↦ iInter_subset _ _,
      (iInter_subset_of_subset (Classical.arbitrary _) (hX _).subset_ground)⟩,
      fun i ↦ iInter_subset_of_subset {i} (by simp)⟩

  -- The intersection is modular with every finite-rank flat.
  have hfin : ∀ F, M.Flat F → M.FinRk F → M.ModularPair (⋂ i, X i) F
  · intro F hF hfin
    rw [modularPair_iff_forall_distrib_of_subset_left (Flat.iInter (fun i ↦ (hX i).flat))
      hF.subset_ground]
    simp only [subset_iInter_iff]
    intro Y hYss hY
    have hdir' : Directed (fun A B ↦ B ⊆ A) fun i ↦ X i ∩ F
    · refine hdir.mono_comp (fun (A : Set α) B ↦ B ⊆ A) (g := (· ∩ F)) ?_
      simp only [subset_inter_iff, inter_subset_right, and_true]
      exact fun _ _ ↦ inter_subset_left.trans

    obtain ⟨i₀, hi₀⟩ := Flat.iInter_mem_of_directed_of_finRk (fun i ↦ (hX i).flat.inter hF) hdir'
      ⟨Classical.arbitrary ι, hfin.inter_left⟩
    rw [iInter_inter (s := F), ← hi₀, ← (hX i₀).distrib_of_subset_self hF (hYss i₀)]
    exact inter_subset_inter_left _ (iInter_subset _ _)

  -- The collection of finite-rank subflats of some `F` is upwards directed and has union `F`.
  -- Since `⋂ i, X i` is a modular pair with every flat in the collection, it is modular with `F`.
  rw [modularFlat_iff, and_iff_right (Flat.iInter fun i ↦ (hX i).flat)]
  intro F hF
  set D := fun F₀ : {F₀ : Set α // M.Flat F₀ ∧ M.FinRk F₀ ∧ F₀ ⊆ F} ↦ F₀.1 with hD_def
  have hdirD : Directed (· ⊆ ·) D
  · rintro ⟨A, hA, hAfin, hAF⟩ ⟨B, hB, hBfin, hBF⟩
    refine ⟨⟨_, M.closure_flat (A ∪ B), (hAfin.union hBfin).closure,
      hF.closure_subset_of_subset (union_subset hAF hBF)⟩,
      M.subset_closure_of_subset' subset_union_left, M.subset_closure_of_subset' subset_union_right⟩

  have hU : M.closure (⋃ F₀, D F₀) = F
  · rw [subset_antisymm_iff, hD_def]
    refine ⟨hF.closure_subset_of_subset (iUnion_subset fun F₀ ↦ F₀.2.2.2), fun e heF ↦ ?_⟩
    have heE := hF.subset_ground heF
    refine M.mem_closure_of_mem' (mem_iUnion_of_mem ⟨M.closure {e}, ?_⟩ ?_)
    · rw [FinRk.closure_iff]
      exact ⟨M.closure_flat _, M.finRk_of_finite (by simp), hF.closure_subset_of_subset (by simpa)⟩
    simp
    exact M.mem_closure_of_mem' rfl

  rw [← hU]
  refine (Flat.iInter (fun i ↦ (hX i).flat)).modularPair_iUnion_of_directed hdirD  ?_
  rintro ⟨F₀, hF₀, hF₀fin, hmod⟩
  exact hfin F₀ hF₀ hF₀fin

lemma ModularFlat.sInter [Finitary M] {Xs : Set (Set α)} (hne : Xs.Nonempty)
    (hXs : ∀ X ∈ Xs, M.ModularFlat X) : M.ModularFlat (⋂₀ Xs) := by
  rw [sInter_eq_iInter]
  have := hne.coe_sort
  exact ModularFlat.iInter (by simpa)


end Lattice

lemma ModularFlat.restrict (hF : M.ModularFlat F) (hFX : F ⊆ X) (hXE : X ⊆ M.E := by aesop_mat) :
    (M ↾ X).ModularFlat F := by
  have hF' := hF.flat.flat_restrict X
  rw [inter_eq_self_of_subset_left hFX] at hF'
  rw [hF'.modularFlat_iff_forall_contract_exists_parallel]
  refine fun C e hCF he hecl  ↦ hF.exists_parallel_mem_of_minor ?_ ?_ he hecl
  · exact (contract_minor _ _).trans (restrict_minor _ hXE)
  simp [subset_diff, hFX, hCF.symm]

lemma ModularFlat.contract (hF : M.ModularFlat F) (C : Set α) :
    (M ／ C).ModularFlat ((M ／ C).closure F) := by
  rw [← closure_inter_ground, contract_ground, ← inter_diff_assoc,
    inter_eq_self_of_subset_left hF.subset_ground,
    (closure_flat _ _).modularFlat_iff_forall_contract_exists_parallel]
  intro A e hdj hnl hcl
  rw [contract_contract] at hnl hcl
  have h_ex := hF.exists_parallel_mem_of_contract hnl ?_
  · obtain ⟨f, hfF, hfcl⟩ := h_ex
    rw [← contract_contract] at hfcl
    refine ⟨f, ?_, hfcl⟩
    simp only [contract_closure_eq, diff_union_self, mem_diff]
    exact ⟨mem_of_mem_of_subset hfF
      (M.subset_closure_of_subset' subset_union_left hF.subset_ground), hfcl.mem_ground_right.1.2⟩
  simp only [contract_closure_eq, diff_union_self, mem_diff, mem_union, not_or] at hcl ⊢
  rwa [diff_union_eq_union_of_subset _ subset_union_left, closure_union_closure_left_eq,
    union_comm C, ← union_union_distrib_right, union_right_comm, union_assoc] at hcl

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

lemma Circuit.chord_split_of_modular_subset {C I : Set α} (hC : M.Circuit C) (hIC : I ⊆ C)
    (hnt : I.Nontrivial) (hnt' : (C \ I).Nontrivial) (hmod : M.ModularFlat (M.closure I)) :
    ∃ e, e ∉ C ∧ M.Circuit (insert e I) ∧ M.Circuit (insert e (C \ I)) := by
  have hssu : I ⊂ C := hIC.ssubset_of_ne (by rintro rfl; simp at hnt')
  have hI := hC.ssubset_indep hssu
  have hli := (hmod.modularPair (M.closure_flat (C \ I))).localEConn_eq_eRk_inter
  obtain ⟨J, hJ⟩ := M.exists_basis (M.closure I ∩ M.closure (C \ I))
  rw [localEConn_closure_closure, hC.localEConn_subset_compl hnt.nonempty hssu, eq_comm,
    ← hJ.encard, encard_eq_one] at hli
  obtain ⟨e, rfl⟩ := hli

  suffices aux : ∀ X ⊂ C, X.Nontrivial → (C \ X).Nontrivial →
      M.Basis {e} (M.closure X ∩ M.closure (C \ X)) → M.Circuit (insert e X)
  · have hc1 := aux _ hssu hnt hnt' hJ

    refine ⟨e, fun heC ↦ hc1.dep.not_indep (hC.ssubset_indep ?_), hc1, ?_⟩
    · refine (insert_subset heC hssu.subset).ssubset_of_ne ?_
      rintro rfl
      have heI : e ∉ I
      · intro heI
        rw [insert_eq_of_mem heI] at hssu
        exact hssu.ne rfl
      simp [insert_diff_of_not_mem _ heI] at hnt'
    refine aux _ ?_ hnt' (by rwa [diff_diff_cancel_left hIC]) ?_
    · simpa [inter_eq_self_of_subset_right hIC] using hnt.nonempty
    rwa [inter_comm, diff_diff_cancel_left hIC]

  intro J hJC hJnt hCJnt hb

  refine (hC.ssubset_indep hJC).insert_circuit_of_forall_of_nontrivial hJnt
    (by simpa using hb.subset.trans inter_subset_left) fun f hfI heclf ↦ ?_
  have hsk : M.Skew (J \ {f}) (C \ J)
  · rw [Indep.skew_iff_disjoint]
    · exact disjoint_sdiff_right.mono_left diff_subset
    refine (hC.diff_singleton_indep (hJC.subset hfI)).subset
      (union_subset (diff_subset_diff_left hJC.subset) (diff_subset_diff_right (by simpa)))
  have henl : M.Nonloop e := indep_singleton.1 hJ.indep

  refine henl.not_loop <| hsk.closure_skew.inter_subset_loops ⟨heclf, ?_⟩
  simpa using hb.subset.trans inter_subset_right

/- If `x,y, e1, e2, ...` is a countable circuit in a simple matroid, then there exist
`y = f0, f1, f2, ...` so that for each `i`, both `ei, fi, f(i+1)` and `x,fi, ei, ...` are circuits.
This is used to show that matroids with modular lines are finitary. -/
private lemma modular_finitary_aux (hM : ∀ F, M.Flat F → M.eRk F ≤ 2 → M.ModularFlat F)
    {e : ℕ → α} (h_inj : e.Injective) {x y : α} (hxy : x ≠ y) (hxe : x ∉ range e)
    (hye : y ∉ range e) (h_circuit : M.Circuit (insert x (insert y (range e)))) :
    ∃ f : ℕ → α, f 0 = y ∧ x ∉ range f
    ∧ (Disjoint (range e) (range f)) ∧
      (∀ i, M.Circuit {f i, f (i+1), e i}) ∧
      (∀ i, M.Circuit (insert x (insert (f i) (e '' (Ici i))))) := by
  have aux1 : ∀ ⦃g i⦄, M.Circuit (insert x (insert g (e '' Ici i))) → x ≠ g ∧ g ∉ range e
  · intro g i h
    rw [ne_comm, ← not_or, ← mem_insert_iff]
    refine fun hgins ↦ h.dep.not_indep (h_circuit.ssubset_indep ?_)
    refine HasSubset.Subset.ssubset_of_mem_not_mem (x := y) ?_ (by simp) ?_
    · rw [insert_comm (b := y)]
      refine subset_trans ?_ (subset_insert _ _)
      obtain (rfl | hg) := hgins
      · simp only [mem_insert_iff, mem_image, mem_Ici, true_or, insert_eq_of_mem]
        exact insert_subset_insert (image_subset_range _ _)
      exact insert_subset_insert (insert_subset hg (image_subset_range _ _))
    rw [mem_insert_iff, not_or, and_iff_right hxy.symm, mem_insert_iff, not_or,
      and_iff_left (not_mem_subset (image_subset_range _ _) hye)]
    contrapose! hye
    rwa [mem_insert_iff, ← hye, or_iff_right hxy.symm] at hgins

  have aux2 : ∀ i (g : ↑(M.E \ range e)), M.Circuit (insert x (insert g.1 (e '' (Ici i)))) →
    ∃ (g' : ↑(M.E \ range e)), (∀ j, g'.1 ≠ e j) ∧ M.Circuit {g.1,g'.1, e i} ∧
      M.Circuit (insert x (insert g'.1 (e '' Ici (i+1))))
  · rintro i ⟨g, hgE, hge⟩ hC
    simp only [mem_diff, mem_range, not_exists, exists_and_left, exists_prop] at hC ⊢
    have hxi : x ≠ e i := by rintro rfl; simp at hxe
    have hg : ∀ j, g ≠ e j := by rintro j rfl; simp at hge
    obtain ⟨hxg, hge⟩ := aux1 hC

    have h_ex := hC.chord_split_of_modular_subset (I := {g, e i})
      (by simp [pair_subset_iff, h_inj.eq_iff])
      (by simp [hg i]) ?_ ?_
    rotate_left
    · refine Infinite.nontrivial (Infinite.diff ?_ (by simp))
      simp only [insert_infinite_iff, infinite_image_iff h_inj.injOn]
      exact Ici_infinite i
    · refine hM _ (M.closure_flat _) ?_
      rw [eRk_closure_eq]
      exact (M.eRk_le_encard _).trans (by simp)
    obtain ⟨g', hg'C, hgg', hg'x⟩ := h_ex
    rw [insert_comm] at hgg'
    rw [insert_diff_of_not_mem _ (by simp [hxg, hxi]), insert_diff_of_mem _ (by simp),
      ← union_singleton (a := g), ← diff_diff, diff_singleton_eq_self, insert_comm,
      ← Ioi_insert, image_insert_eq, insert_diff_of_mem _ (by simp),
      diff_singleton_eq_self, show Ioi i = Ici (i+1) from rfl] at hg'x
    · refine ⟨⟨g',?_⟩, ?_, hgg', hg'x⟩
      · exact ⟨hgg'.subset_ground (by simp), (aux1 hg'x).2⟩
      · rintro j rfl
        refine hg'x.dep.not_indep (h_circuit.ssubset_indep ?_)
        refine HasSubset.Subset.ssubset_of_mem_not_mem (x := y) ?_ (by simp) ?_
        · refine insert_subset_insert (insert_subset (by simp) ?_)
          exact (image_subset_range _ _).trans (subset_insert _ _)
        rw [mem_insert_iff, or_iff_right hxy.symm]
        exact not_mem_subset (by simp [insert_subset_iff]) hye
    · simp [h_inj.eq_iff]
    exact not_mem_subset (by simp) hge

  choose! φ hφ using aux2

  set y' : ↑(M.E \ range e) := ⟨y, h_circuit.subset_ground (by simp), hye⟩ with y'_def
  set f : ℕ → ↑(M.E \ range e) := Nat.recAux y' φ with f_def
  have hf_succ : ∀ n, f (n+1) = φ n (f n) := fun _ ↦ rfl

  rw [← image_univ, ← show Ici 0 = univ by simp [Set.ext_iff, Nat.zero_le]] at h_circuit
  have big : ∀ i, M.Circuit (insert x (insert ↑(f i) (e '' (Ici i))))
  · intro n
    induction' n with n IH
    · exact h_circuit
    exact (hφ n (f n) IH).2.2

  have tri : ∀ i, M.Circuit {(f i).1, (f (i + 1)).1, e i}
  · intro n
    induction' n with n IH
    · exact (hφ 0 y' h_circuit).2.1
    exact (hφ (n+1) (f (n+1)) (big _)).2.1

  refine ⟨Subtype.val ∘ f, rfl, ?_, ?_, tri, big⟩
  · refine fun ⟨i, hi⟩ ↦ (big i).dep.not_indep (h_circuit.ssubset_indep ?_)
    simp only [Function.comp_apply] at hi
    rw [hi, insert_eq_of_mem (by simp), insert_comm]
    refine (ssubset_insert ?_ ).trans_subset (insert_subset_insert (insert_subset_insert ?_))
    · simp only [mem_insert_iff, hxy.symm, mem_image, mem_Ici, false_or, not_exists, not_and]
      rintro _ _ rfl
      simp at hye
    exact image_mono fun x hx ↦ (by simp)
  rw [disjoint_comm, disjoint_iff_forall_ne]
  rintro _ ⟨n, hn, rfl⟩ _ ⟨m, hm, rfl⟩
  induction' n with n IH
  · simp [f_def, y'_def, show y ≠ e m by rintro rfl; simp at hye]
  exact (hφ n (f n) (big n)).1 m

private lemma exists_of_modular_not_finitary (hM : ∀ L, M.Line L → M.ModularFlat L)
    (hnotfin : ¬ M.Finitary) :
    ∃ (N : Matroid α) (e f : ℕ → α) (x y : α),
    x ≠ y
    ∧ e.Injective
    ∧ x ∉ range e
    ∧ y ∉ range e
    ∧ (Disjoint (range e) (range f))
    ∧ x ∉ range f
    ∧ f 0 = y
    ∧ (∀ n, N.Circuit {f n, f (n+1), e n})
    ∧ ∀ n, N.Circuit (insert x ((insert (f n)) (e '' Ici n))) := by
  simp only [finitary_iff_forall_circuit_finite, not_forall, Classical.not_imp] at hnotfin
  obtain ⟨C, hC, hCinf : C.Infinite⟩ := hnotfin
  obtain ⟨x, hxC⟩ := hCinf.nonempty
  obtain ⟨y, hyC, hyx : y ≠ x⟩ := (hCinf.diff (finite_singleton x)).nonempty
  let e' := (hCinf.diff (t := {x,y}) (by simp)).natEmbedding
  set e := Subtype.val ∘ e' with he_def
  set X := (C \ {x,y}) \ range e with X_def
  set N := M ／ X with hN_def
  have hX' : range e = (C \ X) \ {x,y}
  · have hss : range e ⊆ C \ {x,y}
    · rw [he_def, range_comp]
      refine (image_mono (subset_univ _)).trans ?_
      rw [image_univ, Subtype.range_coe]
    rw [X_def, diff_diff_right, diff_diff_cancel_left (pair_subset hxC hyC), union_diff_cancel_left,
      eq_comm, inter_eq_right]
    · exact hss.trans diff_subset
    rw [Disjoint.inter_eq]
    exact Disjoint.mono_right inter_subset_right (disjoint_sdiff_right.mono_right hss)
  have he_inj : e.Injective := Subtype.val_injective.comp e'.injective
  have hxe : x ∉ range e := by simp [hX']
  have hye : y ∉ range e := by simp [hX']
  have h_aux := modular_finitary_aux (M := N) (e := e) ?_ he_inj hyx.symm hxe hye
  rotate_left
  · intro F hF hr
    obtain hlt | h2 := hr.lt_or_eq
    · exact hF.modularFlat_of_eRk_le_one <| Order.le_of_lt_add_one hlt
    obtain ⟨I, hI⟩ := (M ／ X).exists_basis F hF.subset_ground
    rw [← hI.encard, le_iff_eq_or_lt] at hr
    have hmod := (hM (M.closure I) ⟨M.closure_flat _, ?_⟩).contract X
    · rwa [contract_closure_eq, closure_union_closure_left_eq, ← contract_closure_eq,
        hI.closure_eq_closure, hF.closure] at hmod
    rwa [eRk_closure_eq, hI.indep.of_contract.eRk, ← hI.eRk_eq_encard]
  simp only [hX', not_exists] at h_aux

  rw [← singleton_union, ← singleton_union, ← union_assoc, singleton_union,
    union_diff_cancel] at h_aux
  swap
  · simp [pair_subset_iff, X_def, hxC, hyC]
  specialize h_aux <| hC.contract_circuit (C := X) ?_
  · exact (diff_subset.trans diff_subset).ssubset_of_mem_not_mem hxC (by simp [X_def])
  obtain ⟨f, rfl, hrange, hne, htri, hcirc⟩ := h_aux
  exact ⟨N, e, f, x, f 0, hyx.symm, he_inj, hxe, hye,
    by rwa [← hX'] at hne, hrange, rfl, htri, hcirc⟩

/-- Every matroid whose lines are modular is finitary. -/
lemma finitary_of_forall_line_modular (hM : ∀ L, M.Line L → M.ModularFlat L) : M.Finitary := by
  by_contra hnotfin
  obtain ⟨N, e, f, x, y, hxy, he, hxe, hye, hdj, hxf, rfl, htri, hcirc⟩ :=
    exists_of_modular_not_finitary hM hnotfin

  have hef : N.closure (range e) ⊆ N.closure (range f)
  · refine N.closure_subset_closure_of_subset_closure ?_
    rintro _ ⟨i, rfl⟩
    refine mem_of_mem_of_subset
      ((htri i).mem_closure_diff_singleton_of_mem (e := e i) (by simp)) ?_
    exact N.closure_mono <| by simp [insert_subset_iff]

  have hcl1 : x ∈ N.closure (range f)
  · rw [← closure_closure, ← union_eq_self_of_subset_left hef,
      closure_closure_union_closure_eq_closure_union]
    refine mem_of_mem_of_subset ((hcirc 0).mem_closure_diff_singleton_of_mem (by simp)) ?_
    refine N.closure_subset_closure ?_
    rw [diff_subset_iff, singleton_union, ← union_singleton (a := f 0)]
    exact insert_subset_insert (union_subset_union (by simp) (by simp))

  rw [mem_closure_iff_exists_circuit_of_not_mem hxf] at hcl1
  obtain ⟨C', hC', hxC', hC'ss⟩ := hcl1

  rw [← singleton_union, ← diff_subset_iff, subset_range_iff_exists_image_eq] at hC'ss
  obtain ⟨I, hI⟩ := hC'ss
  obtain rfl | hIne := I.eq_empty_or_nonempty
  · rw [image_empty, eq_comm, diff_eq_empty] at hI
    refine hC'.dep.not_indep ((hcirc 0).ssubset_indep (hI.trans_ssubset ?_))
    refine (ssubset_insert (s := {x}) (a := f 0) (by simp [hxy.symm])).trans_subset ?_
    simp [pair_subset_iff]

  set j := sInf I with hj
  have hsp : N.closure (insert x (f '' (I \ {j}))) ⊆ N.closure (insert x (e '' (Ioi j)))
  · refine N.closure_subset_closure_of_subset_closure (insert_subset ?_ ?_)
    · exact mem_closure_of_mem' _ (by simp) (hC'.subset_ground hxC')
    rintro _ ⟨i, hj, rfl⟩
    refine mem_of_mem_of_subset
      ((hcirc i).mem_closure_diff_singleton_of_mem (e := f i) (by simp))
      (N.closure_subset_closure ?_)
    rw [diff_subset_iff, singleton_union, insert_comm]
    refine insert_subset_insert (insert_subset_insert (image_mono (fun x (hx : i ≤ x) ↦ ?_)))
    exact ((Nat.sInf_le hj.1).lt_of_ne' hj.2).trans_le hx

  have hcl : f j ∈ N.closure (insert x (C' \ {f j}))
  · refine mem_of_mem_of_subset (hC'.mem_closure_diff_singleton_of_mem ?_) ?_
    · exact mem_of_mem_of_subset (mem_image_of_mem f (Nat.sInf_mem hIne)) (by simp [hI])
    exact N.closure_mono (subset_insert _ _)

  have hC₀ : f j ∈ N.closure (insert x (e '' Ioi j))
  · refine mem_of_mem_of_subset hcl (subset_trans (N.closure_subset_closure ?_) hsp)
    rw [← insert_diff_singleton, diff_diff_comm, ← hI]
    refine insert_subset_insert ?_
    rw [diff_subset_iff, ← image_singleton, ← image_union, singleton_union, insert_diff_singleton]
    exact image_mono (subset_insert _ _)

  rw [mem_closure_iff_exists_circuit_of_not_mem] at hC₀
  swap
  · rintro (rfl | ⟨i, -, h⟩)
    · simp at hxf
    exact hdj.ne_of_mem (by simp) (by simp) h

  obtain ⟨C₀, hC₀, hjC₀, hC₀ss⟩ := hC₀

  refine hC₀.dep.not_indep ((hcirc j).ssubset_indep ?_)
  refine (hC₀ss.trans ?_).ssubset_of_mem_not_mem (x := e j) ?_ ?_
  · rw [insert_comm]
    refine insert_subset_insert (insert_subset_insert (image_mono ?_))
    exact Ioi_subset_Ici_self
  · exact .inr (.inr ⟨j, by simp, rfl⟩)
  refine not_mem_subset hC₀ss ?_

  rintro (h1 | (rfl | h3))
  · exact hdj.ne_of_mem (by simp) (by simp) h1
  · simp at hxe
  simp [he.eq_iff] at h3

/-- A matroid is modular iff every line meets every hyperplane in a point. -/
lemma modular_iff_forall_line_hyperplane :
    M.Modular ↔ ∀ ⦃L H⦄, M.Line L → M.Hyperplane H → ¬ (L ∩ H ⊆ M.closure ∅) := by
  refine ⟨fun h L H hL hH ↦ ?_, fun h F hF ↦ ?_⟩
  · exact hH.modularFlat_iff_forall_line.1 (h hH.flat) L hL
  obtain rfl | hssu := hF.subset_ground.eq_or_ssubset
  · simp
  obtain ⟨Hs, hne, hHs, rfl⟩ := hF.eq_sInter_hyperplanes_of_ne_ground hssu.ne
  have hfin : M.Finitary
  · refine finitary_of_forall_line_modular fun L hL ↦ ?_
    exact hL.modularFlat_of_forall_hyperplane <| fun H hH ↦ h hL hH
  refine ModularFlat.sInter hne fun H hH ↦ ?_
  rw [(hHs _ hH).modularFlat_iff_forall_line]
  exact fun L hL ↦ h hL (hHs _ hH)

lemma modular_iff_forall_line_hyperplane_nonempty_inter [Loopless M] :
    M.Modular ↔ ∀ ⦃L H⦄, M.Line L → M.Hyperplane H → (L ∩ H).Nonempty := by
  rw [modular_iff_forall_line_hyperplane]
  exact ⟨fun h L H hL hH ↦ nonempty_iff_ne_empty.2 fun h_eq ↦ by simpa [h_eq] using h hL hH,
    fun h L H hL hH hss ↦ (h hL hH).ne_empty <| by simpa using hss⟩

lemma Modular.finitary (hM : M.Modular) : M.Finitary :=
  finitary_of_forall_line_modular fun _ hL ↦ hM hL.flat

end Modular
