import Mathlib.Combinatorics.Matroid.Closure
import Mathlib.Tactic.Have

open Set

variable {α : Type*} {M : Matroid α}
namespace Matroid

lemma isBasis_restrict_univ_iff {I X : Set α} : (M ↾ univ).IsBasis I X ↔ M.IsBasis' I X := by
  rw [isBasis_restrict_iff', isBasis'_iff_isBasis_inter_ground, and_iff_left (subset_univ _)]

lemma Indep.isBasis_iff_eq {I J : Set α} (hI : M.Indep I) : M.IsBasis J I ↔ J = I := by
  refine ⟨fun h ↦ h.eq_of_subset_indep hI h.subset rfl.subset, ?_⟩
  rintro rfl
  exact hI.isBasis_self

lemma eq_loopyOn_or_rankPos' (M : Matroid α) : (∃ E, M = loopyOn E) ∨ M.RankPos := by
  obtain h | h := M.eq_loopyOn_or_rankPos
  · exact .inl ⟨M.E, h⟩
  exact .inr h

lemma rankPos_iff_empty_not_spanning : M.RankPos ↔ ¬ M.Spanning ∅ := by
  rw [rankPos_iff, not_iff_not]
  exact ⟨fun h ↦ h.spanning, fun h ↦ h.isBase_of_indep M.empty_indep⟩

lemma exists_isBase_finset (M : Matroid α) [RankFinite M] : ∃ B : Finset α, M.IsBase B := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  exact ⟨hB.finite.toFinset, by simpa⟩

lemma exists_isBasis_finset (M : Matroid α) [RankFinite M] (X : Set α)
    (hXE : X ⊆ M.E := by aesop_mat) : ∃ I : Finset α, M.IsBasis I X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis X
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

lemma IsBasis'.exists_isBasis'_inter_eq_of_superset {I X Y : Set α} (hIX : M.IsBasis' I X)
    (hXY : X ⊆ Y) : ∃ J, M.IsBasis' J Y ∧ J ∩ X = I := by
  obtain ⟨J, hJ, rfl⟩ :=
    hIX.isBasis_inter_ground.exists_isBasis_inter_eq_of_superset (inter_subset_inter_left M.E hXY)
  simp_rw [isBasis'_iff_isBasis_inter_ground]
  refine ⟨J, hJ, ?_⟩
  rw [inter_comm X, ← inter_assoc, inter_eq_self_of_subset_left hJ.indep.subset_ground]

@[simp] lemma uniqueBaseOn_spanning_iff {X I E : Set α} :
    (uniqueBaseOn I E).Spanning X ↔ I ∩ E ⊆ X ∧ X ⊆ E := by
  rw [← uniqueBaseOn_inter_ground_eq, spanning_iff_exists_isBase_subset']
  simp [uniqueBaseOn_isBase_iff (show I ∩ E ⊆ E from inter_subset_right)]

@[simp] lemma freeOn_spanning_iff {X E : Set α} : (freeOn E).Spanning X ↔ X = E := by
  rw [← uniqueBaseOn_self, uniqueBaseOn_spanning_iff]
  simp [← subset_antisymm_iff, eq_comm]

@[simp] lemma emptyOn_spanning_iff {X : Set α} : (emptyOn α).Spanning X ↔ X = ∅ := by
  rw [← loopyOn_empty, loopyOn_spanning_iff, subset_empty_iff]

lemma IsRestriction.restrict {N : Matroid α} (h : N ≤r M) {R : Set α} (hR : R ⊆ N.E) :
    N ↾ R ≤r M ↾ R := by
  obtain ⟨R', hR', rfl⟩ := h
  rw [restrict_restrict_eq _ (by simpa using hR)]
  exact IsRestriction.refl
