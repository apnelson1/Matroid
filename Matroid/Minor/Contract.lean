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
