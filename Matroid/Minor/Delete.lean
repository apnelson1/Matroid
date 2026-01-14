import Matroid.Loop
import Matroid.ForMathlib.Matroid.Dual
import Matroid.ForMathlib.Matroid.Closure
import Mathlib.Combinatorics.Matroid.Minor.Delete
import Matroid.Closure

open Set

variable {α : Type*} {M M' N : Matroid α} {e f : α} {I J R B X Y Z K S : Set α}

namespace Matroid

section Delete

variable {D D₁ D₂ R : Set α}

attribute [simp] Matroid.delete_inter_ground_eq


@[simp] lemma delete_ground_self (M : Matroid α) : M ＼ M.E = emptyOn α := by
  simp [← ground_eq_empty_iff]

lemma Loopless.delete (h : M.Loopless) (D : Set α) : (M ＼ D).Loopless := by
  simp [loopless_iff]

instance [h : M.Loopless] {D : Set α} : (M ＼ D).Loopless :=
  h.delete D

lemma removeLoops_eq_delete (M : Matroid α) : M.removeLoops = M ＼ M.loops := by
  rw [← restrict_compl, removeLoops]
  convert rfl using 2
  simp [Set.ext_iff, isNonloop_iff, isLoop_iff, mem_diff, and_comm]

lemma removeLoops_del_eq_removeLoops (h : X ⊆ M.loops) :
    (M ＼ X).removeLoops = M.removeLoops := by
  rw [removeLoops_eq_delete, delete_delete, removeLoops_eq_delete, loops, delete_closure_eq,
    empty_diff, union_diff_self, closure_empty, union_eq_self_of_subset_left h]

lemma Dep.delete_of_disjoint (hX : M.Dep X) (hXD : Disjoint X D) : (M ＼ D).Dep X := by
  rwa [delete_dep_iff, and_iff_left hXD]

lemma Dep.of_delete (h : (M ＼ D).Dep X) : M.Dep X :=
  (delete_dep_iff.1 h).1

@[simp]
lemma loopyOn_delete (E X : Set α) : (loopyOn E) ＼ X = loopyOn (E \ X) := by
  rw [← restrict_compl, loopyOn_restrict, loopyOn_ground]

@[simp] lemma freeOn_delete (E X : Set α) : (freeOn E) ＼ X = freeOn (E \ X) := by
  simp [ext_iff_indep, subset_diff]

lemma delete_restrict_eq_restrict (M : Matroid α) {D R : Set α} (hDR : Disjoint D R) :
    M ＼ D ↾ R = M ↾ R := by
  suffices ∀ ⦃I : Set α⦄, I ⊆ R → M.Indep I → Disjoint I D from ext_indep rfl <| by simpa
  exact fun I hIR _ ↦ hDR.symm.mono_left hIR

lemma IsRestriction.delete (h : N ≤r M) (D : Set α) : N ＼ D ≤r M ＼ D := by
  obtain ⟨R, hR, rfl⟩ := h
  rw [delete_eq_restrict, delete_eq_restrict, restrict_ground_eq,
    restrict_restrict_eq _ diff_subset]
  exact IsRestriction.of_subset M <| diff_subset_diff_left hR

lemma restrict_comap {β : Type*} (M : Matroid β) (f : α → β) (R : Set β) :
    (M ↾ R).comap f = M.comap f ↾ (f ⁻¹' R) := by
  simp only [ext_iff_indep, comap_ground_eq, restrict_ground_eq, comap_indep_iff,
    restrict_indep_iff, image_subset_iff, true_and]
  tauto

lemma delete_comap {β : Type*} (M : Matroid β) (f : α → β) (D : Set β) :
    (M ＼ D).comap f = M.comap f ＼ (f ⁻¹' D) := by
  rw [delete_eq_restrict, restrict_comap, preimage_diff, ← comap_ground_eq, delete_eq_restrict]

lemma restrict_map {β : Type*} {f : α → β} (hf : InjOn f M.E) (hR : R ⊆ M.E) :
    (M ↾ R).map f (hf.mono hR) = M.map f hf ↾ (f '' R) := by
  refine ext_indep (by simp) fun I hI ↦ ?_
  obtain ⟨I, hIR : I ⊆ R, rfl⟩ := subset_image_iff.1 hI
  simp only [map_indep_iff, restrict_indep_iff, image_subset_iff]
  rw [and_iff_left (hIR.trans (subset_preimage_image ..))]
  refine ⟨fun ⟨I₀, hI₀⟩ ↦ ⟨I₀, hI₀.1.1, hI₀.2⟩, fun ⟨I₀, hI₀, heq⟩ ↦ ⟨I₀, ⟨⟨hI₀, ?_⟩, heq⟩⟩⟩
  rw [hf.image_eq_image_iff (hIR.trans hR) hI₀.subset_ground] at heq
  rwa [← heq]

lemma delete_map {β : Type*} {f : α → β} (hf : InjOn f M.E) (hD : D ⊆ M.E) :
    (M ＼ D).map f (hf.mono diff_subset) = M.map f hf ＼ (f '' D) := by
  simp_rw [delete_eq_restrict, restrict_map hf diff_subset, image_diff_of_injOn hf hD, map_ground]

-- This belongs in `Constructions`.
lemma indep_iff_restrict_eq_freeOn : M.Indep I ↔ (M ↾ I = freeOn I) := by
  refine ⟨Indep.restrict_eq_freeOn, fun h ↦ ?_⟩
  have h' := restrict_indep_iff (M := M) (I := I) (R := I)
  rwa [h, freeOn_indep_iff, iff_true_intro Subset.rfl, and_true, true_iff] at h'

lemma deleteElem_of_notMem_ground (h : e ∉ M.E) : M ＼ {e} = M := by
  rw [← delete_inter_ground_eq, singleton_inter_eq_empty.2 h, delete_empty]

-- These belong in `Restrict`.
@[simp] lemma emptyOn_isRestriction (M : Matroid α) : emptyOn α ≤r M :=
  ⟨∅, empty_subset _, by simp⟩

@[simp]
lemma isRestriction_emptyOn_iff : M ≤r emptyOn α ↔ M = emptyOn α := by
  simp [isRestriction_iff_exists]

lemma Coindep.delete_nonspanning_iff (hD : M.Coindep D) :
    (M ＼ D).Nonspanning X ↔ M.Nonspanning X ∧ Disjoint X D := by
  wlog hX : X ⊆ (M ＼ D).E generalizing with aux
  · exact iff_of_false (fun h ↦ hX h.subset_ground)
      fun h ↦ hX <| subset_diff.2 ⟨h.1.subset_ground, h.2⟩
  obtain ⟨hXE, hdj⟩ := subset_diff.1 hX
  rw [and_iff_left hdj, ← not_spanning_iff, hD.delete_spanning_iff, and_iff_left hdj,
    not_spanning_iff]

lemma Coindep.delete_coindep_iff (hD : M.Coindep D) :
    (M ＼ D).Coindep X ↔ M.Coindep (X ∪ D) ∧ Disjoint X D := by
  wlog hX : X ⊆ (M ＼ D).E generalizing with aux
  · exact iff_of_false (fun h ↦ hX h.subset_ground)
      (fun h ↦ hX <| subset_diff.2 ⟨subset_union_left.trans h.1.subset_ground, h.2⟩)
  have hX' := subset_diff.1 hX
  rw [coindep_iff_compl_spanning, coindep_iff_compl_spanning, hD.delete_spanning_iff, delete_ground,
    diff_diff, union_comm, and_iff_left hX'.2, and_iff_left (by grind)]

lemma girth_le_girth_delete (M : Matroid α) (D : Set α) : M.girth ≤ (M ＼ D).girth :=
    (delete_isRestriction ..).girth_ge

lemma Nonspanning.of_delete (h : (M ＼ D).Nonspanning X) : M.Nonspanning X := by
  rw [nonspanning_iff, spanning_iff_closure_eq] at *
  rw [delete_closure_eq, delete_ground, subset_diff, h.2.2.sdiff_eq_left] at h
  grind

lemma Nonspanning.of_isRestriction (h : N.Nonspanning X) (hNM : N ≤r M) :
    M.Nonspanning X := by
  obtain ⟨D, hD, rfl⟩ := hNM.exists_eq_delete
  exact h.of_delete

lemma Coindep.delete_isSpanningRestriction (hX : M.Coindep X) : M ＼ X ≤sr M :=
  restrict_compl _ _ ▸ hX.compl_spanning.restrict_isSpanningRestriction

lemma delete_isSpanningRestriction_iff (hX : X ⊆ M.E := by aesop_mat) :
    M ＼ X ≤sr M ↔ M.Coindep X := by
  refine ⟨fun h ↦ ?_, Coindep.delete_isSpanningRestriction⟩
  rw [← diff_diff_cancel_left hX]
  exact h.spanning.compl_coindep

end Delete
