import Matroid.Constructions.ClosureAxioms
import Matroid.Flat

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

variable {α : Type*} {E F F' F₁ F₂ X Y I J : Set α} {e f : α} {M : FlatMatroid α}

lemma ground_flat (M : FlatMatroid α) : M.Flat M.E := by
  simpa using M.flat_sInter ∅

lemma Flat.subset_ground (hF : M.Flat F) : F ⊆ M.E :=
  M.subset_ground F hF

@[reducible] def closure (M : FlatMatroid α) (X : Set α) : Set α := ⋂₀ {F | X ∩ M.E ⊆ F ∧ M.Flat F}

lemma closure_subset_closure (M : FlatMatroid α) (hXY : X ⊆ Y) : M.closure X ⊆ M.closure Y := by
  simp only [closure, subset_sInter_iff, mem_setOf_eq, and_imp]
  exact fun F hYF hF ↦ sInter_subset_of_mem  ⟨(inter_subset_inter_left M.E hXY).trans hYF, hF⟩

lemma closure_closure (M : FlatMatroid α) (X : Set α) : M.closure (M.closure X) = M.closure X := by
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
  suffices ∀ F, X ∩ M.E ⊆ F → M.Flat F → X ⊆ F by simpa (config := { contextual := true })
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

lemma mem_closure_insert_self (M : FlatMatroid α) (heE : e ∈ M.E) (X : Set α) :
    e ∈ M.closure (insert e X) := by
  rw [← singleton_subset_iff]
  exact (M.subset_closure (by simpa)).trans (M.closure_subset_closure (by simp))

lemma closure_insert_minimal (M : FlatMatroid α) (X : Set α) (e : α) (heE : e ∈ M.E)
    (heX : e ∉ M.closure X) :
    Minimal (fun F ↦ M.closure X ⊂ F ∧ M.Flat F) (M.closure (insert e X)) := by
  have h_ex := M.flat_partition _ e (M.closure_flat X) heE heX
  obtain ⟨F₀, heF₀, hF₀⟩ := h_ex.exists
  convert hF₀

  refine subset_antisymm (sInter_subset_of_mem ⟨?_, hF₀.prop.2⟩) ?_
  · rw [inter_comm, inter_insert_of_mem heE, insert_subset_iff, and_iff_right heF₀,
      inter_comm]
    refine (M.subset_closure inter_subset_right).trans ?_
    rw [closure_inter_ground]
    exact hF₀.prop.1.subset

  rw [← inter_eq_left]
  refine hF₀.eq_of_subset ⟨?_, ?_⟩ inter_subset_left
  · rw [ssubset_iff_subset_ne, subset_inter_iff, and_iff_right,
      ne_eq, Set.ext_iff, not_forall]
    · use e
      rw [iff_false_left heX, mem_inter_iff, not_not, and_iff_right heF₀]
      exact mem_closure_insert_self M heE X
    exact ⟨hF₀.prop.1.subset, (M.closure_subset_closure (subset_insert _ _))⟩
  convert M.flat_sInter {F₀, M.closure (insert e X)} _ using 1
  · simp only [sInter_insert, sInter_singleton, left_eq_inter]
    exact inter_subset_right.trans (M.closure_subset_ground _)
  simp [hF₀.prop.2, M.closure_flat]

protected def closureMatroid (M : FlatMatroid α) : ClosureMatroid α where
  E := M.E
  closure := M.closure
  subset_closure_self := fun _ ↦ M.subset_closure
  closure_subset_closure := fun _ _  ↦ M.closure_subset_closure
  closure_closure_eq_closure := M.closure_closure

  closure_exchange := by

    simp only [mem_diff, and_imp]
    refine fun X e f hX heE hfE hfeX hfX ↦ ?_

    have heXcl : e ∉ M.closure X := by
      refine fun heXcl ↦ hfX (mem_of_mem_of_subset hfeX ?_)
      rw [← M.closure_closure X]
      exact M.closure_subset_closure (insert_subset heXcl (M.subset_closure hX))

    have heX : e ∉ X := not_mem_subset (M.subset_closure hX) heXcl
    refine ⟨by_contra fun hcon ↦ ?_, heX⟩

    suffices hcl : M.closure (insert e X) = M.closure (insert f X) by
      rw [← hcl] at hcon
      exact hcon (mem_closure_insert_self M heE X)

    have hmin := M.closure_insert_minimal X e heE heXcl
    refine Eq.symm <| hmin.eq_of_subset ⟨?_, M.closure_flat _⟩ ?_
    · refine (M.closure_subset_closure (by simp)).ssubset_of_ne (fun h ↦ hfX ?_)
      rw [h]
      exact mem_closure_insert_self M hfE X

    rw [← (M.closure_flat (insert e X)).closure]

    exact M.closure_subset_closure (insert_subset hfeX ((M.subset_closure hX).trans
      (M.closure_subset_closure (subset_insert _ _))))



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

protected def matroid (M : FlatMatroid α) : Matroid α := M.closureMatroid.matroid

@[simp] lemma matroid_flat_iff : M.matroid.Flat F ↔ M.Flat F := by
  rw [Matroid.flat_iff_closure_self, FlatMatroid.matroid, ClosureMatroid.matroid_closure_eq]
  refine ⟨fun h ↦ ?_, Flat.closure⟩
  rw [← h]
  apply M.closure_flat
