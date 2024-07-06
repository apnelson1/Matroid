import Matroid.Constructions.DirectSum
import Matroid.Constructions.Coexpand

import Mathlib.Order.Closure

open Set

namespace Matroid

variable {α ι : Type*} {M : Matroid α} {F I J X Y B C R : Set α} {e f x y : α}

@[mk_iff]
structure Flat (M : Matroid α) (F : Set α) : Prop where
  subset_of_basis_of_basis : ∀ ⦃I X⦄, M.Basis I F → M.Basis I X → X ⊆ F
  subset_ground : F ⊆ M.E

attribute [aesop unsafe 20% (rule_sets := [Matroid])] Flat.subset_ground

@[simp] lemma ground_flat (M : Matroid α) : M.Flat M.E :=
  ⟨fun _ _ _ ↦ Basis.subset_ground, Subset.rfl⟩

lemma Flat.iInter {ι : Type*} [Nonempty ι] {Fs : ι → Set α}
    (hFs : ∀ i, M.Flat (Fs i)) : M.Flat (⋂ i, Fs i) := by
  refine ⟨fun I X hI hIX ↦ subset_iInter fun i ↦ ?_,
    (iInter_subset _ (Classical.arbitrary _)).trans (hFs _).subset_ground⟩
  obtain ⟨J, hIJ, hJ⟩ := hI.indep.subset_basis_of_subset (hI.subset.trans (iInter_subset _ i))
  refine' subset_union_right.trans ((hFs i).1 (X := Fs i ∪ X) hIJ _)
  convert hIJ.basis_union (hIX.basis_union_of_subset hIJ.indep hJ) using 1
  rw [← union_assoc, union_eq_self_of_subset_right hIJ.subset]

lemma flat_iff_forall_indep_insert :
    M.Flat F ↔ (∀ ⦃I e⦄, I ⊆ F → M.Indep I → e ∈ M.E \ F → M.Indep (insert e I)) ∧ F ⊆ M.E := by
  rw [flat_iff, and_congr_left_iff]
  refine fun hF ↦ ⟨fun h I e hIF hI ⟨he, heF⟩↦ ?_, fun h I X hIF hIX e he ↦ by_contra fun heF ↦ ?_⟩
  · obtain ⟨J, hJF, hIJ⟩ := hI.subset_basis_of_subset hIF
    by_contra hcon
    rw [not_indep_iff] at hcon
    refine False.elim <| heF <| (h (X := insert e J) hJF
      (hJF.indep.basis_of_forall_insert (subset_insert _ _) ?_)) (mem_insert e _)
    simp (config := {contextual := true}) [hcon.superset (insert_subset_insert hIJ)]
  by_cases heI : e ∈ I
  · exact heF <| hIF.subset heI
  apply (hIX.insert_dep ⟨he, heI⟩).not_indep
  exact h hIF.subset hIF.indep ⟨hIX.subset_ground he, heF⟩

lemma flat_coexpand_iff {F : Set α} : M.coexpand.Flat F ↔ M.Flat (F ∩ M.E) := by
  simp only [flat_iff_forall_indep_insert, coexpand_indep_iff, coexpand_ground_eq, mem_diff,
    mem_univ, true_and, subset_univ, and_true, subset_inter_iff, diff_inter_self_eq_diff, and_imp,
    inter_subset_right]
  refine ⟨fun h I e hIF hIE hI he heF ↦ ?_, fun h I e hIF hI heF ↦ ?_⟩
  · specialize h hIF (by rwa [inter_eq_self_of_subset_left hIE]) heF
    rwa [insert_inter_of_mem he, inter_eq_self_of_subset_left hIE] at h
  by_cases he : e ∈ M.E
  · rw [insert_inter_of_mem he]
    exact h (inter_subset_left.trans hIF) inter_subset_right hI he heF
  rwa [insert_inter_of_not_mem he]


-- lemma sigma_flat_iff {α : ι → Type*} {M : (i : ι) → Matroid (α i)} {F : Set ((i : ι) × α i)} :
--     (Matroid.sigma M).Flat F ↔ ∀ i, (M i).Flat (Sigma.mk i ⁻¹' F) := by
--   simp only [flat_iff, sigma_basis_iff, sigma_ground_eq]
--   refine ⟨fun ⟨h1, h2⟩ i ↦ ⟨fun I X hIF hIX ↦ ?_, ?_⟩, fun h ↦ ?_⟩
--   ·
--     have := h1 (I := Sigma.mk i '' I) (X := Sigma.mk i '' X) (fun j ↦ ?_) sorry
--     · simpa using this
--     obtain (rfl | hne) := eq_or_ne i j
--     · simpa [sigma_mk_preimage_image_eq_self]
--     rw [sigma_mk_preimage_image']



-- (Matroid.sigma M).Base B ↔ ∀ i, (M i).Base (Sigma.mk i ⁻¹' B) := Iff.rfl


-- def closure (M : Matroid α) : ClosureOperator (Set α) := by
--   refine ClosureOperator.ofCompletePred (fun X ↦ M.Flat (X ∩ M.E)) fun s hs ↦ ?_
--   obtain (rfl | hne) := s.eq_empty_or_nonempty
--   · simp
--   have _ := hne.coe_sort
--   simpa [biInter_inter hne, ← sInter_eq_biInter] using
--     Flat.iInter (M := M) (Fs := fun (F : s) ↦ F ∩ M.E) (by simpa)

-- lemma flat_iff_isClosed : M.Flat F ↔ M.closure.IsClosed F ∧ F ⊆ M.E := by
--   simp only [closure, ClosureOperator.ofCompletePred_isClosed]
--   exact ⟨fun h ↦ by simpa [inter_eq_self_of_subset_left h.subset_ground, h.subset_ground],
--     fun ⟨h,h'⟩ ↦ by rwa [← inter_eq_self_of_subset_left h']⟩

-- lemma flat_iff_isClosed' (hF : F ⊆ M.E := by aesop_mat) :
--     M.closure.IsClosed F ↔ M.Flat F := by
--   rw [flat_iff_isClosed, and_iff_left hF]

-- lemma Flat.isClosed (hF : M.Flat F) : M.closure.IsClosed F := by
--   rwa [flat_iff_isClosed']
