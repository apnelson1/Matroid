import Mathlib.Combinatorics.Matroid.Sum
import Matroid.Modular.Flat
import Matroid.Connectivity.Skew

variable {α β ι : Type*} {M N : Matroid α} {F I X : Set α}

set_option linter.style.longLine false

open Set

namespace Matroid

@[mk_iff]
structure ModularSumIndep (M : ι → Matroid α) (N : Matroid α) (I : Set α) where
  subset_iUnion : I ⊆ ⋃ i, (M i).E
  forall_indep : ∀ i, (M i).Indep (I ∩ (M i).E)
  skew : N.IsSkewFamily fun i ↦ ((M i).closure (I ∩ (M i).E) ∩ N.E)

lemma ModularSumIndep.mono {M : ι → Matroid α} {N : Matroid α} (h : ModularSumIndep M N I)
    {J : Set α} (hJI : J ⊆ I) : ModularSumIndep M N J :=
  ⟨hJI.trans h.subset_iUnion, fun i ↦ (h.forall_indep i).subset (by grind),
    h.skew.mono fun i ↦ by grw [hJI]⟩

lemma bar {M : ι → Matroid α} {B : Set α} : Maximal (ModularSumIndep M N) B ↔
    ModularSumIndep M N B ∧ (∀ i, (M i).IsBase (B ∩ (M i).E)) := by
  refine ⟨fun h ↦ ⟨h.prop, fun i ↦ ?_⟩, fun h ↦ ?_⟩
  · sorry
  rw [maximal_iff_forall_insert, and_iff_right h.1]



def foo (M : ι → Matroid α) (hN : ∀ i, N ≤r M i) (h_inter : ∀ ⦃i j⦄, i ≠ j → (M i).E ∩ (M j).E = N.E)
    (hmod : ∀ i, (M i).IsModularFlat N.E) : IndepMatroid α where
  E := ⋃ i, (M i).E
  Indep I := ModularSumIndep M N I
  indep_empty := by
    have h (i) : (M i).closure ∅ ∩ N.E = N.closure ∅ := by rw [(hN i).closure_eq]
    simp only [modularSumIndep_iff, empty_subset, empty_inter, empty_indep, implies_true, h,
      true_and, ← isSkewFamily_iff_cls_isSkewFamily]
    rw [Indep.isSkewFamily_iff_pairwise_disjoint (by simp)]
    simp [Pairwise]
  indep_subset I J hJ hIJ := ⟨hIJ.trans hJ.subset_iUnion,
    fun i ↦ (hJ.forall_indep i).subset (by grind), hJ.skew.mono fun i ↦ by grw [hIJ]⟩
  indep_aug I B hI hInotmax hBmax := by
    _
  indep_maximal := sorry
  subset_ground := sorry

-- @[reducible] def ModularSumIndep (M N : Matroid α) (F I : Set α) :=
--   M.Indep (I ∩ M.E) ∧ (N ／ (M.closure I)).Indep ((I ∩ N.E) \ F) ∧ I ⊆ M.E ∪ N.E

-- lemma ModularSumIndep.subset {F I J : Set α} (hJ : M.ModularSumIndep N F J) (hIJ : I ⊆ J) :
--     M.ModularSumIndep N F I := by
--   refine ⟨hJ.1.subset (inter_subset_inter_left _ hIJ), ?_, hIJ.trans hJ.2.2⟩
--   refine (hJ.2.1.of_minor ?_).subset (diff_subset_diff_left (inter_subset_inter_left _ hIJ))
--   exact contract_minor_of_subset  _ <| M.closure_subset_closure hIJ

-- def foo (M N : Matroid α) (F : Set α) (hFE : F = M.E ∩ N.E) (hF : M ↾ F = N ↾ F) (hMF : M.ModularSet F) : IndepMatroid α where
--   E := M.E ∪ N.E
--   Indep := M.ModularSumIndep N F
--   indep_empty := by simp [ModularSumIndep]
--   indep_subset I J hJ hIJ := hJ.subset hIJ
--   indep_aug := by
--     intro I B ⟨hIM, hIn, hIE⟩ hInotmax hBmax
--     simp only [maximal_iff_forall_insert (fun _ _ ↦ ModularSumIndep.subset), not_and, not_forall,
--       Classical.not_imp, not_not, and_imp, hIM, hIn, hIE, and_self, true_implies,
--       exists_prop, exists_and_left, insert_subset_iff, and_true] at hInotmax



--   indep_maximal := _
--   subset_ground := _
