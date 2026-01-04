import Matroid.Minor.Delete
import Mathlib.Combinatorics.Matroid.Minor.Contract
import Matroid.ForMathlib.Matroid.Constructions

variable {α : Type*} {M M' N : Matroid α} {e f : α} {I J R B C X Y Z K S : Set α}

open Set

namespace Matroid

@[simp] lemma freeOn_contract (E X : Set α) : (freeOn E) ／ X = freeOn (E \ X) := by
  rw [← loopyOn_dual_eq, ← dual_delete, loopyOn_delete, loopyOn_dual_eq]

@[simp]
lemma loopyOn_contract (E X : Set α) : (loopyOn E) ／ X = loopyOn (E \ X) := by
  rw [← dual_inj, dual_contract, loopyOn_dual_eq, freeOn_delete, loopyOn_dual_eq]

lemma contract_eq_loopyOn_of_spanning (h : M.Spanning C) : M ／ C = loopyOn (M.E \ C) := by
  rw [eq_loopyOn_iff_loops, contract_ground, and_iff_left rfl, contract_loops_eq, h.closure_eq]

@[simp] lemma contract_ground_self (M : Matroid α) : M ／ M.E = emptyOn α := by
  simp [← ground_eq_empty_iff]

lemma contract_map {β : Type*} {M : Matroid α} {f : α → β} (hf : InjOn f M.E) {C : Set α}
    (hC : C ⊆ M.E) : (M ／ C).map f (hf.mono diff_subset) = (M.map f hf) ／ (f '' C) := by
  simp_rw [← M.dual_delete_dual C]
  rw [← map_dual, delete_map (by simpa) (by simpa), ← map_dual, ← dual_contract, dual_dual]

lemma contract_comap {β : Type*} (M : Matroid β) (f : α → β) {C : Set β} (hC : C ⊆ range f) :
    (M ／ C).comap f = M.comap f ／ (f ⁻¹' C) := by
  obtain ⟨C, rfl⟩ := subset_range_iff_exists_image_eq.1 hC
  exact ext_closure fun X ↦ by simp [image_union, image_preimage_image]

lemma contract_closure_congr (h : M.closure X = M.closure Y) (C : Set α) :
    (M ／ C).closure X = (M ／ C).closure Y := by
  rw [contract_closure_eq, contract_closure_eq, closure_union_congr_left h]

lemma contract_codep_iff {C X : Set α} : (M ／ C).Codep X ↔ M.Codep X ∧ Disjoint X C := by
  rw [codep_def, dual_contract, delete_dep_iff, codep_def]

lemma contractElem_of_notMem_ground (he : e ∉ M.E) : M ／ {e} = M := by
  rw [← dual_delete_dual, deleteElem_of_notMem_ground (by simpa), dual_dual]

lemma contract_nonspanning_iff (hC : C ⊆ M.E := by aesop_mat) :
    (M ／ C).Nonspanning X ↔ M.Nonspanning (X ∪ C) ∧ Disjoint X C := by
  wlog hXC : X ⊆ (M ／ C).E generalizing X with aux
  · refine iff_of_false (fun h ↦ hXC h.subset_ground) fun ⟨h1, h2⟩ ↦ hXC <| subset_diff.2 ⟨?_, h2⟩
    grw [dual_ground, ← h1.subset_ground, ← subset_union_left]
  obtain ⟨hXE, hdj⟩ := subset_diff.1 hXC
  rw [and_iff_left hdj, nonspanning_iff, contract_spanning_iff, and_iff_left hdj, and_iff_left hXC,
    ← not_spanning_iff]

lemma girth_le_girth_contract_add (M : Matroid α) (C : Set α) :
    M.girth ≤ (M ／ C).girth + M.eRk C := by
  wlog hC : M.Indep C generalizing C with aux
  · obtain ⟨I, hI⟩ := M.exists_isBasis' C
    grw [hI.contract_eq_contract_delete, ← girth_le_girth_delete, aux _ hI.indep, hI.eRk_eq_eRk]
  rw [hC.eRk_eq_encard]
  obtain ⟨E, h_eq⟩ | hpos := (M ／ C).exists_eq_freeOn_or_rankPos_dual
  · simp [h_eq]
  obtain ⟨K, hK, hKg⟩ := (M ／ C).exists_isCircuit_girth
  obtain ⟨K', hK'ss, hK'⟩ := (hC.contract_dep_iff.1 hK.dep).2.exists_isCircuit_subset
  grw [hK'.girth_le_card, ← hKg, ← encard_union_le, encard_le_encard hK'ss]

lemma Dep.contract_of_delete {D : Set α} (hX : (M ＼ X).Dep (D \ X)) : (M ／ X).Dep (D \ X) := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [delete_dep_iff] at hX
  rw [hI.contract_dep_iff, and_iff_left disjoint_sdiff_right]
  exact hX.1.superset subset_union_left (union_subset hX.1.subset_ground hI.indep.subset_ground)

lemma Dep.contract_of_disjoint {D : Set α} (hD : M.Dep D) (hDC : Disjoint D C) :
    (M ／ C).Dep D := by
  have aux : (M ＼ C).Dep (D \ C) := by
    rwa [delete_dep_iff, and_iff_left disjoint_sdiff_left, hDC.sdiff_eq_left]
  exact hDC.sdiff_eq_left ▸ aux.contract_of_delete

/-- Contracting a set whose intersection with `D` is independent never turns a dependent set `D`
into an independent set. -/
lemma Dep.contract_of_indep {D : Set α} (hD : M.Dep D) (hI : M.Indep (D ∩ I)) :
    (M ／ I).Dep (D \ I) := by
  nth_rw 1 [← inter_union_diff I D, inter_comm, ← contract_contract]
  refine Dep.contract_of_disjoint ?_ disjoint_sdiff_sdiff
  rwa [hI.isBasis_self.contract_dep_iff, diff_union_inter, disjoint_comm,
    and_iff_left disjoint_sdiff_inter]

lemma Codep.of_contract (h : (M ／ C).Codep X) : M.Codep X :=
  (dual_contract _ _ ▸ h.dep_dual).of_delete

lemma Coindep.of_contract (h : (M ／ C).Coindep I) : M.Coindep I :=
  (dual_contract _ _ ▸ h.indep).of_delete

lemma Codep.of_delete {D : Set α} (h : (M ＼ D).Codep X) (hD : D ⊆ M.E := by aesop_mat) :
    M.Codep (X ∪ D) := by
  rw [← dep_dual_iff, dual_delete] at h
  exact union_comm _ _ ▸ h.of_contract

lemma removeLoops_eq_contract (M : Matroid α) : M.removeLoops = M ／ M.loops := by
  rw [contract_eq_delete_of_subset_loops rfl.subset, removeLoops_eq_delete]

lemma removeColoops_eq_contract (M : Matroid α) : M.removeColoops = M ／ M.coloops := by
  rw [removeColoops, removeLoops_eq_delete, dual_delete, dual_dual, dual_loops]

lemma removeColoops_eq_delete (M : Matroid α) : M.removeColoops = M ＼ M.coloops := by
  rw [removeColoops, removeLoops_eq_contract, dual_contract, dual_dual, dual_loops]

lemma IsRestriction.contract (h : N ≤r M) (hC : C ⊆ N.E) : N ／ C ≤r M ／ C := by
  obtain ⟨R, hR, rfl⟩ := h
  exact ⟨R \ C, diff_subset_diff_left hR, by rwa [restrict_contract_eq_contract_restrict]⟩

lemma IsSpanningRestriction.contract (h : N ≤sr M) (hC : C ⊆ N.E) : N ／ C ≤sr M ／ C := by
  refine ⟨h.isRestriction.contract hC, ?_⟩
  rw [contract_spanning_iff (hC.trans h.subset), contract_ground, and_iff_left disjoint_sdiff_left,
    diff_union_self]
  exact h.spanning.superset subset_union_left <| union_subset h.subset <| hC.trans h.subset
