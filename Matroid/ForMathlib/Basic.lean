import Mathlib.Data.Matroid.Basic

open Set
namespace Matroid

variable {α : Type*} {M : Matroid α} {I J X Y : Set α} {e : α}

theorem Basis'.mem_of_insert_indep (hI : M.Basis' I X) (he : e ∈ X) (hIe : M.Indep (insert e I)) :
    e ∈ I :=
  hI.basis_inter_ground.mem_of_insert_indep ⟨he, hIe.subset_ground (mem_insert _ _)⟩ hIe

theorem Basis'.inter_eq_of_subset_indep (hI : M.Basis' I X) (hIJ : I ⊆ J) (hJ : M.Indep J) :
    J ∩ X = I := by
  rw [← hI.basis_inter_ground.inter_eq_of_subset_indep hIJ hJ, inter_comm X, ← inter_assoc,
    inter_eq_self_of_subset_left hJ.subset_ground]


theorem exists_basis_disjoint_basis_of_subset (M : Matroid α) {X Y : Set α} (hXY : X ⊆ Y)
    (hY : Y ⊆ M.E := by aesop_mat) : ∃ I J, M.Basis I X ∧ M.Basis (I ∪ J) Y ∧ Disjoint X J := by
  obtain ⟨I, I', hI, hI', hII'⟩ := M.exists_basis_subset_basis hXY
  refine ⟨I, I' \ I, hI, by rwa [union_diff_self, union_eq_self_of_subset_left hII'], ?_⟩
  rw [disjoint_iff_forall_ne]
  rintro e heX _ ⟨heI', heI⟩ rfl
  exact heI <| hI.mem_of_insert_indep heX (hI'.indep.subset (insert_subset heI' hII'))

/-- For finite `E`, finitely many matroids have ground set contained in `E`. -/
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

/-- For finite `E`, finitely many matroids have ground set `E`. -/
theorem finite_setOf_matroid' {E : Set α} (hE : E.Finite) : {M : Matroid α | M.E = E}.Finite :=
  (finite_setOf_matroid hE).subset (fun M ↦ by rintro rfl; exact rfl.subset)


open Set
