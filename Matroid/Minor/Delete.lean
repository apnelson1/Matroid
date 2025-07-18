import Matroid.Loop
import Mathlib.Data.Matroid.Minor.Delete

open Set

variable {α : Type*} {M M' N : Matroid α} {e f : α} {I J R B X Y Z K S : Set α}

namespace Matroid

section Delete

variable {D D₁ D₂ R : Set α}


@[simp] lemma delete_ground_self (M : Matroid α) : M ＼ M.E = emptyOn α := by
  simp [← ground_eq_empty_iff]

lemma Loopless.delete (h : M.Loopless) (D : Set α) : (M ＼ D).Loopless := by
  simp [loopless_iff]

instance [h : M.Loopless] {D : Set α} : (M ＼ D).Loopless :=
  h.delete D

lemma removeLoops_eq_delete (M : Matroid α) : M.removeLoops = M ＼ M.loops := by
  rw [← restrict_compl, removeLoops]
  convert rfl using 2
  simp [Set.ext_iff, mem_setOf, isNonloop_iff, isLoop_iff, mem_diff, and_comm]

lemma removeLoops_del_eq_removeLoops (h : X ⊆ M.loops) :
    (M ＼ X).removeLoops = M.removeLoops := by
  rw [removeLoops_eq_delete, delete_delete, removeLoops_eq_delete, loops, delete_closure_eq,
    empty_diff, union_diff_self, closure_empty, union_eq_self_of_subset_left h]

@[simp]
lemma loopyOn_delete (E X : Set α) : (loopyOn E) ＼ X = loopyOn (E \ X) := by
  rw [← restrict_compl, loopyOn_restrict, loopyOn_ground]

@[simp] lemma freeOn_delete (E X : Set α) : (freeOn E) ＼ X = freeOn (E \ X) := by
  simp [ext_iff_indep, subset_diff]

lemma delete_restrict_eq_restrict (M : Matroid α) {D R : Set α} (hDR : Disjoint D R) :
    M ＼ D ↾ R = M ↾ R := by
  suffices ∀ ⦃I : Set α⦄, I ⊆ R → M.Indep I → Disjoint I D from ext_indep rfl <| by simpa
  exact fun I hIR _ ↦ hDR.symm.mono_left hIR

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


-- These belong in `Restrict`.
@[simp] lemma emptyOn_isRestriction (M : Matroid α) : emptyOn α ≤r M :=
  ⟨∅, empty_subset _, by simp⟩

@[simp]
lemma isRestriction_emptyOn_iff : M ≤r emptyOn α ↔ M = emptyOn α := by
  simp [isRestriction_iff_exists]



end Delete
