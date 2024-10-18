import Matroid.Constructions.ClosureAxioms

open Set

structure FlatMatroid (α : Type*) where
  E : Set α
  Flat : Set α → Prop
  flat_sInter : ∀ Fs : Set (Set α), (∀ F ∈ Fs, Flat F) → Flat (⋂₀ Fs ∩ E)
  flat_partition : ∀ F e, Flat F → e ∈ E → e ∉ F →
    ∃! F', e ∈ F' ∧ Minimal (fun X ↦ F ⊂ X ∧ Flat X) F'
  Indep : Set α → Prop
  indep_iff : ∀ ⦃I⦄, Indep I ↔ (∀ e ∈ I, ∃ F, Flat F ∧ I ∩ F = I \ {e}) ∧ I ⊆ E
  indep_maximal : ∀ ⦃X⦄, X ⊆ E → Matroid.ExistsMaximalSubsetProperty Indep X
  subset_ground : ∀ F, Flat F → F ⊆ E

namespace FlatMatroid

variable {α : Type*} {E F F' F₁ F₂ X Y I J : Set α} {M : FlatMatroid α}

lemma ground_flat (M : FlatMatroid α) : M.Flat M.E := by
  simpa using M.flat_sInter ∅

lemma Flat.subset_ground (hF : M.Flat F) : F ⊆ M.E :=
  M.subset_ground F hF

@[reducible] def closure (M : FlatMatroid α) (X : Set α) : Set α := ⋂₀ {F | X ∩ M.E ⊆ F ∧ M.Flat F}

lemma closure_subset_closure (M : FlatMatroid α) (hXY : X ⊆ Y) : M.closure X ⊆ M.closure Y := by
  simp only [closure, subset_sInter_iff, mem_setOf_eq, and_imp]
  exact fun F hYF hF ↦ sInter_subset_of_mem  ⟨(inter_subset_inter_left M.E hXY).trans hYF, hF⟩

@[simp] lemma closure_closure (M : FlatMatroid α) (X : Set α) :
    M.closure (M.closure X) = M.closure X := by
  simp only [subset_antisymm_iff, subset_sInter_iff, mem_setOf_eq, and_imp]
  refine ⟨fun F hXF hF ↦ sInter_subset_of_mem ⟨inter_subset_left.trans ?_, hF⟩, ?_⟩
  · exact sInter_subset_of_mem ⟨hXF, hF⟩
  refine fun F hssF hF ↦ ?_
  convert hssF using 1
  simp only [left_eq_inter]
  refine (sInter_subset_of_mem ?_).trans hF.subset_ground
  simp only [mem_setOf_eq, hF, and_true]
  exact subset_trans (by simp (config := {contextual := true})) hssF

lemma subset_closure (hX : X ⊆ M.E) : X ⊆ M.closure X := by
  simp (config := { contextual := true }) only [subset_sInter_iff, mem_setOf_eq, and_imp]
  exact fun F hXF _ ↦ by rwa [← inter_eq_self_of_subset_left hX]

lemma closure_inter_ground (M : FlatMatroid α) (X : Set α) :
    M.closure (X ∩ M.E) = M.closure X := by
  refine (M.closure_subset_closure inter_subset_left).antisymm (subset_sInter fun F hF ↦ ?_)
  simp only [inter_assoc, inter_self, mem_setOf_eq] at hF
  exact sInter_subset_of_mem <| by simpa

lemma closure_subset_ground (M : FlatMatroid α) (X : Set α) : M.closure X ⊆ M.E :=
  sInter_subset_of_mem ⟨inter_subset_right, M.ground_flat⟩

lemma closure_flat (M : FlatMatroid α) (X : Set α) : M.Flat (M.closure X) := by
  rw [← inter_eq_self_of_subset_left (M.closure_subset_ground X)]
  exact M.flat_sInter _ <| by simp

lemma Flat.closure (hF : M.Flat F) : M.closure F = F :=
  subset_antisymm (sInter_subset_of_mem (by simp [hF])) (M.subset_closure hF.subset_ground)

lemma Indep.subset_ground (hI : M.Indep I) : I ⊆ M.E :=
  (M.indep_iff.1 hI).2



lemma foo (M : FlatMatroid α) (X : Set α) (e : α) (heE : e ∈ M.E) (heX : e ∉ M.closure X) :
    Minimal (fun F ↦ M.closure X ⊂ F ∧ M.Flat F) (M.closure (insert e X)) := by



  simp_rw [← M.closure_inter_ground X, ← M.closure_inter_ground (insert e X),
    inter_comm, inter_insert_of_mem heE, inter_comm M.E]
  rw [← closure_inter_ground] at heX
  rw [minimal_iff_forall_ssubset, and_iff_left (M.closure_flat _),
    ssubset_iff_subset_ne, and_iff_right (M.closure_subset_closure (subset_insert _ _))]
  refine ⟨fun h_eq ↦ heX ?_, fun F hFss ⟨hXF, hF⟩ ↦ ?_⟩
  · rw [h_eq, ← singleton_subset_iff]
    exact (M.subset_closure (X := {e}) (by simpa)).trans (M.closure_subset_closure (by simp))
  by_cases heF : e ∈ F
  · rw [← hF.closure] at hFss
    refine hFss.not_subset (M.closure_subset_closure (insert_subset heF ?_))
    exact (M.subset_closure inter_subset_right).trans hXF.subset
  simp at heX
  obtain ⟨x, hxcl, hxF⟩ := exists_of_ssubset hFss
  have h_unique_x := M.flat_partition F x hF (M.closure_subset_ground _ hxcl) hxF
  have h_unique_e := M.flat_partition F e hF heE heF

  obtain ⟨Fx, hxFx, hFx⟩ := h_unique_x.exists
  obtain ⟨Fe, heFe, hFe⟩ := h_unique_e.exists
  have hss1 : Fx ⊆ M.closure (insert x X) := by
    simp
    intro G hXG hG

  have hss : Fx ⊆ Fe := by
    rw [← (hFe.prop.2.closure)]



protected def closureMatroid (M : FlatMatroid α) : ClosureMatroid α where
  E := M.E
  closure := M.closure
  subset_closure_self := fun _ ↦ M.subset_closure
  closure_subset_closure := fun _ _  ↦ M.closure_subset_closure
  closure_closure_eq_closure := M.closure_closure

  closure_exchange := by
    simp only [mem_diff, mem_sInter, mem_setOf_eq, and_imp, not_forall, Classical.not_imp,
      forall_exists_index]

    intro X e f h F hXF hF hfF F' hXF' hF'
    have hfE : f ∈ M.E := h M.E inter_subset_right M.ground_flat
    have heE : e ∈ M.E := by
      contrapose! hfF
      refine h _ ?_ hF
      rwa [inter_comm, inter_insert_of_not_mem hfF, inter_comm]
    simp_rw [inter_comm _ M.E, inter_insert_of_mem hfE, inter_comm _ X] at hXF'
    simp_rw [inter_comm _ M.E, inter_insert_of_mem heE, inter_comm _ X] at h

    specialize h (M.closure (insert e (X ∩ M.E)))
      (M.subset_closure (insert_subset heE inter_subset_right)) (M.closure_flat _)
    set X' := X ∩ M.E with hX'
    have hfX' : f ∉ M.closure X' := by
      refine not_mem_subset ?_ hfF
      rw [← hF.closure]
      exact M.closure_subset_closure hXF
    have h_ex := M.flat_partition _ f (M.closure_flat X') hfE hfX'
    have := h_ex.unique (y₁ := M.closure (insert e X')) (y₂ := M.closure (insert e X'))
      ⟨h, ?_⟩




  Indep := M.Indep
  indep_iff := by
    simp_rw [indep_iff, and_congr_left_iff]
    refine fun I hI ↦ ⟨fun h e heI hecl ↦ ?_, fun h e heI ↦ ⟨_, M.closure_flat (I \ {e}), ?_⟩⟩
    · obtain ⟨F, hF, hfI⟩ := h e heI
      simp only [closure, mem_sInter, mem_setOf_eq, and_imp] at hecl
      have := hfI.subset ⟨heI, (hecl F ?_ hF)⟩
      · simp at this
      rw [inter_eq_self_of_subset_left (diff_subset.trans hI), ← hfI]
      simp
    rw [subset_antisymm_iff, subset_diff, disjoint_singleton_right, mem_inter_iff,
      and_iff_right heI, and_iff_right inter_subset_left, subset_inter_iff,
      and_iff_right diff_subset, and_iff_left (M.subset_closure (diff_subset.trans hI))]
    exact h e heI

  indep_maximal := M.indep_maximal
  closure_inter_inter_ground := fun X ↦ by
    rw [closure_inter_ground, inter_eq_self_of_subset_left (M.closure_subset_ground X)]
