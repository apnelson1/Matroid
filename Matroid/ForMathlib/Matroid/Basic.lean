import Mathlib.Data.Matroid.Closure
import Mathlib.Tactic

open Set

variable {α : Type*} {M : Matroid α}
namespace Matroid

lemma basis_restrict_univ_iff {I X : Set α} : (M ↾ univ).Basis I X ↔ M.Basis' I X := by
  rw [basis_restrict_iff', basis'_iff_basis_inter_ground, and_iff_left (subset_univ _)]

lemma Indep.basis_iff_eq {I J : Set α} (hI : M.Indep I) : M.Basis J I ↔ J = I := by
  refine ⟨fun h ↦ h.eq_of_subset_indep hI h.subset rfl.subset, ?_⟩
  rintro rfl
  exact hI.basis_self

lemma eq_loopyOn_or_rankPos' (M : Matroid α) : (∃ E, M = loopyOn E) ∨ M.RankPos := by
  obtain h | h := M.eq_loopyOn_or_rankPos
  · exact .inl ⟨M.E, h⟩
  exact .inr h

lemma rankPos_iff_empty_not_spanning : M.RankPos ↔ ¬ M.Spanning ∅ := by
  rw [rankPos_iff, not_iff_not]
  exact ⟨fun h ↦ h.spanning, fun h ↦ h.base_of_indep M.empty_indep⟩

lemma exists_base_finset (M : Matroid α) [RankFinite M] : ∃ B : Finset α, M.Base B := by
  obtain ⟨B, hB⟩ := M.exists_base
  exact ⟨hB.finite.toFinset, by simpa⟩

lemma exists_basis_finset (M : Matroid α) [RankFinite M] (X : Set α) (hXE : X ⊆ M.E := by aesop_mat) :
    ∃ I : Finset α, M.Basis I X := by
  obtain ⟨I, hI⟩ := M.exists_basis X
  refine ⟨hI.indep.finite.toFinset, by simpa⟩

/-- This needs `Finitary`.
A counterexample would be the matroid on `[0,1)` whose ground set is a circuit,
where the `Is` are the sets `[0,x)` for `x < 1`. -/
lemma Indep.iUnion_directed [Finitary M] {ι : Type*} {Is : ι → Set α} (hIs : ∀ i, M.Indep (Is i))
    (h_dir : Directed (· ⊆ ·) Is) : M.Indep (⋃ i, Is i) := by
  obtain he | hne := isEmpty_or_nonempty ι
  · simp
  have aux : ∀ A : Set ι, A.Finite → ∃ j, ⋃ i ∈ A, Is i ⊆ Is j
  · intro A hA
    refine hA.induction_on_subset _ ⟨hne.some, by simp⟩ ?_
    rintro i B hiA hBA hiB ⟨jB, hssjb⟩
    obtain ⟨k, hk⟩ := h_dir i jB
    simp only [mem_insert_iff, iUnion_iUnion_eq_or_left, union_subset_iff]
    exact ⟨k, hk.1, hssjb.trans hk.2⟩

  rw [indep_iff_forall_finite_subset_indep]
  intro J hJss hJfin
  obtain ⟨A, hAfin, hJA⟩ := finite_subset_iUnion hJfin hJss
  obtain ⟨j, hj⟩ := aux A hAfin
  exact ((hIs j).subset hj).subset hJA

/-- This needs `Finitary`.
A counterexample would be the matroid on `[0,1)` whose ground set is a circuit,
where the `Is` are the sets `[0,x)` for `x < 1`. -/
lemma Indep.sUnion_chain [Finitary M] {Is : Set (Set α)} (hIs : ∀ I ∈ Is, M.Indep I)
    (h_chain : IsChain (· ⊆ ·) Is) : M.Indep (⋃₀ Is) := by
  simpa [sUnion_eq_iUnion] using Indep.iUnion_directed (M := M) (Is := fun i : Is ↦ i.1)
    (by simpa) h_chain.directed

lemma Basis'.exists_basis'_inter_eq_of_superset {I X Y : Set α} (hIX : M.Basis' I X) (hXY : X ⊆ Y) :
    ∃ J, M.Basis' J Y ∧ J ∩ X = I := by
  obtain ⟨J, hJ, rfl⟩ :=
    hIX.basis_inter_ground.exists_basis_inter_eq_of_superset (inter_subset_inter_left M.E hXY)
  simp_rw [basis'_iff_basis_inter_ground]
  refine ⟨J, hJ, ?_⟩
  rw [inter_comm X, ← inter_assoc, inter_eq_self_of_subset_left hJ.indep.subset_ground]

@[simp] lemma uniqueBaseOn_spanning_iff {X I E : Set α} :
    (uniqueBaseOn I E).Spanning X ↔ I ∩ E ⊆ X ∧ X ⊆ E := by
  rw [← uniqueBaseOn_inter_ground_eq, spanning_iff_exists_base_subset']
  simp [uniqueBaseOn_base_iff (show I ∩ E ⊆ E from inter_subset_right)]

@[simp] lemma freeOn_spanning_iff {X E : Set α} : (freeOn E).Spanning X ↔ X = E := by
  rw [← uniqueBaseOn_self, uniqueBaseOn_spanning_iff]
  simp [← subset_antisymm_iff, eq_comm]

@[simp] lemma emptyOn_spanning_iff {X : Set α} : (emptyOn α).Spanning X ↔ X = ∅ := by
  rw [← loopyOn_empty, loopyOn_spanning_iff, subset_empty_iff]
