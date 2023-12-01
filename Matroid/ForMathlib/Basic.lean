import Mathlib.Data.Matroid.Basic

namespace Matroid

variable {M : Matroid α}

theorem finite_setOf_matroid {E : Set α} (hE : E.Finite) : {M : Matroid α | M.E ⊆ E}.Finite := by
  set f : Matroid α → Set α × (Set (Set α)) := fun M ↦ ⟨M.E, {B | M.Base B}⟩
  have hf : f.Injective
  · refine fun M M' hMM' ↦ ?_
    rw [Prod.mk.injEq, and_comm, Set.ext_iff, and_comm] at hMM'
    exact eq_of_base_iff_base_forall hMM'.1 (fun B _ ↦ hMM'.2 B)
  rw [← Set.finite_image_iff (hf.injOn _)]
  refine (hE.finite_subsets.prod hE.finite_subsets.finite_subsets).subset ?_
  rintro _ ⟨M, hE : M.E ⊆ E, rfl⟩
  simp only [Set.mem_prod, Set.mem_setOf_eq, Set.setOf_subset_setOf]
  exact ⟨hE, fun B hB ↦ hB.subset_ground.trans hE⟩

theorem finite_setOf_matroid' {E : Set α} (hE : E.Finite) : {M : Matroid α | M.E = E}.Finite :=
  (finite_setOf_matroid hE).subset (fun M ↦ by rintro rfl; exact rfl.subset)

open Set
