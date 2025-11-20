import Matroid.Minor.Delete
import Mathlib.Combinatorics.Matroid.Minor.Contract

variable {α : Type*} {M M' N : Matroid α} {e f : α} {I J R B X Y Z K S : Set α}

open Set

namespace Matroid

@[simp] lemma freeOn_contract (E X : Set α) : (freeOn E) ／ X = freeOn (E \ X) := by
  rw [← loopyOn_dual_eq, ← dual_delete, loopyOn_delete, loopyOn_dual_eq]

@[simp]
lemma loopyOn_contract (E X : Set α) : (loopyOn E) ／ X = loopyOn (E \ X) := by
  rw [← dual_inj, dual_contract, loopyOn_dual_eq, freeOn_delete, loopyOn_dual_eq]

lemma contract_eq_loopyOn_of_spanning {C : Set α} (h : M.Spanning C) :
    M ／ C = loopyOn (M.E \ C) := by
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
