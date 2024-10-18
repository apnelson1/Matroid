import Mathlib.Data.Matroid.Basic
import Matroid.Closure
import Mathlib.Data.Matroid.IndepAxioms

open Set Matroid

variable {α : Type*} {I J B X : Set α}

section ClosureMatroid

structure ClosureMatroid (α : Type*) where
  (E : Set α)
  (closure : Set α → Set α)
  (subset_closure_self : ∀ X ⊆ E, X ⊆ closure X)
  (closure_subset_closure : ∀ ⦃X Y : Set α⦄, X ⊆ Y → closure X ⊆ closure Y )
  (closure_closure_eq_closure : ∀ X, closure (closure X) = closure X)
  (closure_exchange : ∀ ⦃Z x y⦄, y ∈ closure (insert x Z) \ closure Z → x ∈ closure (insert y Z))
  (Indep : Set α → Prop)
  (indep_iff : ∀ ⦃I⦄, Indep I ↔ (∀ x ∈ I, x ∉ closure (I \ {x})) ∧ I ⊆ E)
  (indep_maximal : ∀ ⦃X⦄, X ⊆ E → ExistsMaximalSubsetProperty Indep X)
  (closure_inter_inter_ground : ∀ X, closure (X ∩ E) ∩ E = closure X)

namespace ClosureMatroid

lemma closure_subset_ground (M : ClosureMatroid α) (X : Set α) : M.closure X ⊆ M.E := by
  rw [← M.closure_inter_inter_ground]
  apply inter_subset_right

lemma closure_inter_ground (M : ClosureMatroid α) (X : Set α) : M.closure (X ∩ M.E) = M.closure X := by
  rw [← inter_eq_self_of_subset_left (M.closure_subset_ground (X ∩ M.E)),
    M.closure_inter_inter_ground]

lemma Indep.subset_ground {M : ClosureMatroid α} (hI : M.Indep I) : I ⊆ M.E := by
  rw [indep_iff] at hI
  exact hI.2

lemma Indep.subset {M : ClosureMatroid α} (hJ : M.Indep J) (hIJ : I ⊆ J) : M.Indep I := by
  rw [M.indep_iff] at *
  refine ⟨fun x hxI hx ↦ hJ.1 x (hIJ hxI) ?_, hIJ.trans hJ.2⟩
  exact mem_of_mem_of_subset hx <| M.closure_subset_closure (diff_subset_diff_left hIJ)

lemma Indep.mem_closure_iff {M : ClosureMatroid α} {e : α} (hI : M.Indep I) (he : e ∈ M.E)
    (heI : e ∉ I) : e ∈ M.closure I ↔ ¬ M.Indep (insert e I) := by
  suffices (e ∉ M.closure I → ∃ x ∈ I, x ∈ M.closure (insert e I \ {x})) → e ∈ M.closure I by
    simpa (config := { contextual := true }) [M.indep_iff, mem_insert_iff,
      diff_singleton_eq_self heI, insert_subset_iff, he, hI.subset_ground,  iff_def]

  simp only [not_imp_comm (a := _ ∈ _), not_exists, not_and]

  refine fun h ↦ by_contra fun hcon ↦ hcon <| h fun x hxI hxcl ↦ hcon ?_
  rw [M.indep_iff] at hI
  rw [← insert_diff_singleton_comm (by rintro rfl; contradiction)] at hxcl
  have hex := M.closure_exchange (Z := I \ {x}) (x := e) (y := x)
  simpa [mem_diff, hxcl, hI.1 x hxI, insert_eq_of_mem hxI] using hex

@[simps!] protected def matroid (M : ClosureMatroid α) : Matroid α :=
    IndepMatroid.matroid <| IndepMatroid.mk
  (E := M.E)
  (Indep := M.Indep)
  (indep_empty := by simp [M.indep_iff])
  (indep_subset := fun _ _ h ↦ h.subset)
  (indep_aug := by
    intro I I' hIindep hInotmax hI'max

    have hclI' : M.closure I' = M.E := by
      refine subset_antisymm (M.closure_subset_ground _) fun y hy ↦ ?_
      by_cases hyI' : y ∈ I'
      · exact M.subset_closure_self _ hI'max.prop.subset_ground hyI'
      rw [hI'max.prop.mem_closure_iff hy hyI']
      contrapose! hyI'
      exact hI'max.mem_of_prop_insert hyI'

    by_contra! hcon

    have hclI : M.closure I = M.E := by
      rw [subset_antisymm_iff, and_iff_right (M.closure_subset_ground _), ← hclI',
        ← M.closure_closure_eq_closure I]
      refine closure_subset_closure _ fun x hxI' ↦ by_contra fun hxclI ↦ ?_
      by_cases hxI : x ∈ I
      · exact hxclI <| M.subset_closure_self _ hIindep.subset_ground hxI
      rw [hIindep.mem_closure_iff (hI'max.prop.subset_ground hxI') hxI, not_not] at hxclI
      exact hcon x ⟨hxI', hxI⟩ hxclI

    obtain ⟨y, hyI, hi⟩ := exists_insert_of_not_maximal (fun _ _ h ↦ h.subset) hIindep hInotmax

    rw [indep_iff, insert_subset_iff] at hi
    have hy := hi.1 y (by simp)
    simp only [mem_singleton_iff, insert_diff_of_mem, diff_singleton_eq_self hyI, hclI] at hy
    exact hy hi.2.1 )
  (indep_maximal := fun _ h ↦ M.indep_maximal h)
  (subset_ground := fun _ ↦ Indep.subset_ground)

@[simp] lemma matroid_indep_eq (M : ClosureMatroid α) : M.matroid.Indep = M.Indep := rfl

@[simp] lemma matroid_closure_eq (M : ClosureMatroid α) : M.matroid.closure = M.closure := by
  suffices aux : ∀ X ⊆ M.E, M.matroid.closure X = M.closure X by
    refine funext fun X ↦ ?_
    rw [← closure_inter_ground, ← Matroid.closure_inter_ground, matroid_E, aux _ (by simp)]
  refine fun X hX ↦ ?_
  obtain ⟨I, hI⟩ := M.matroid.exists_basis X
  have hi := hI.indep
  simp only [ClosureMatroid.matroid, IndepMatroid.matroid_Indep] at hi
  rw [← hI.closure_eq_closure]
  refine subset_antisymm ?_ fun e he ↦ ?_
  · simp only [subset_def, hI.indep.mem_closure_iff', matroid_E, matroid_Indep, and_imp]
    refine fun e he h ↦ by_contra fun heX ↦ ?_
    have heI : e ∉ I := not_mem_subset (hI.subset.trans (M.subset_closure_self X hX)) heX
    rw [← not_imp_not, ← hi.mem_closure_iff he heI, imp_iff_right heI] at h
    exact heX (M.closure_subset_closure hI.subset h)
  have heE : e ∈ M.E := M.closure_subset_ground X he
  by_cases heI : e ∈ I
  · exact M.matroid.subset_closure I hi.subset_ground heI
  suffices ¬ M.Indep (insert e I) by
    simpa [hI.indep.mem_closure_iff', M.closure_subset_ground X he, heI]
  rw [← hi.mem_closure_iff heE heI, ← M.closure_closure_eq_closure]
  refine mem_of_mem_of_subset he (M.closure_subset_closure fun f hfX ↦ ?_)
  have hfE : f ∈ M.E := hI.subset_ground hfX
  by_cases hfI : f ∈ I
  · exact M.subset_closure_self _ hi.subset_ground hfI

  rw [hi.mem_closure_iff hfE hfI]
  contrapose! hfI
  exact hI.mem_of_insert_indep hfX <| by simpa

end ClosureMatroid
