import Matroid.Rank.Nullity
import Matroid.Connectivity.Skew
import Matroid.ForMathlib.Topology.ENat

open Set ENat Function

namespace Matroid

variable {α ι : Type*} {M N : Matroid α} {I J C B X X' Y Y' Z R : Set α} {n : ℕ∞} {e f : α}

lemma inter_iUnion_eq_of_pairwiseDisjoint_of_forall_subset {s t : ι → Set α}
    (h : Pairwise (Disjoint on t)) (hst : ∀ i, s i ⊆ t i) (i : ι) : t i ∩ ⋃ j, s j = s i := by
  refine subset_antisymm (fun x hx ↦ ?_) (subset_inter (hst i) (subset_iUnion s i))
  simp only [mem_inter_iff, mem_iUnion] at hx
  obtain ⟨hxi, j, hxj⟩ := hx
  obtain rfl | hne := eq_or_ne i j
  · assumption
  exact False.elim <| (h hne).notMem_of_mem_left hxi (hst _ hxj)

-- lemma nullity_foo {X : ι → Set α} : ∃ (I : ι → Set α) (J : Set α),
--     ∀ i, M.IsBasis (I i) (X i) ∧ M.IsBasis J (⋃ i, X i) ∧ ∀ i, J ∩ X i ⊆ I i := by
--   sorry


lemma tsum_nullity_le (M : Matroid α) {X : ι → Set α} (hX : Pairwise (Disjoint on X)) :
    ∑' i, M.nullity (X i) ≤ M.nullity (⋃ i, X i) := by
  wlog hM : M.E = univ generalizing M with aux
  · simp_rw [← M.nullity_restrict_univ]
    apply aux _ rfl
  obtain ⟨I, hI⟩ := M.exists_isBasis (⋃ i, X i)
  choose Is hIs using
    fun i ↦ (hI.indep.inter_right (X i)).subset_isBasis_of_subset inter_subset_right
  grw [tsum_congr (fun i ↦ (hIs i).1.nullity_eq), hI.nullity_eq, iUnion_diff,
    ENat.tsum_encard_eq_encard_iUnion]
  refine encard_le_encard <| iUnion_mono fun i ↦ ?_
  · grw [← diff_inter_self_eq_diff (t := I), (hIs i).2]
  exact hX.mono fun i j h ↦ h.mono diff_subset diff_subset

lemma IsSkewFamily.nullity_iUnion_eq {X : ι → Set α} (hX : M.IsSkewFamily X)
    (h : Pairwise (Disjoint on X)) : M.nullity (⋃ i, X i) = ∑' i, M.nullity (X i) := by
  obtain ⟨I, hI⟩ := M.exists_isBasis (⋃ i, X i)
  choose Is hIs using
    fun i ↦ (hI.indep.inter_left (X i)).subset_isBasis_of_subset inter_subset_left
  have hi := hX.iUnion_indep_subset_indep (fun i ↦ (hIs i).1.subset) (fun i ↦ (hIs i).1.indep)
  have hss : I ⊆ ⋃ i, Is i := by
    grw [← inter_eq_self_of_subset_right hI.subset, iUnion_inter, iUnion_mono (fun i ↦ (hIs i).2)]
  obtain rfl : I = ⋃ i, Is i :=
    hI.eq_of_subset_indep hi hss (iUnion_mono (fun i ↦ (hIs i).1.subset))
  rw [hI.nullity_eq, iUnion_diff, tsum_congr (fun i ↦ (hIs i).1.nullity_eq),
    ENat.tsum_encard_eq_encard_iUnion]
  · convert rfl using 2
    apply iUnion_congr fun i ↦ subset_antisymm ?_ (diff_subset_diff_right (subset_iUnion ..))
    grw [← diff_inter_self_eq_diff (t := ⋃ i, Is i), inter_comm, (hIs i).2]
  exact h.mono fun i j h ↦ h.mono diff_subset diff_subset

lemma tsum_nullity_eq_nullity_iUnion_iff_isSkewFamily {X : ι → Set α}
    (hX : Pairwise (Disjoint on X)) (hXE : ∀ i, X i ⊆ M.E) (hfin : M.nullity (⋃ i, X i) < ⊤) :
    M.nullity (⋃ i, X i) = ∑' i, M.nullity (X i) ↔ M.IsSkewFamily X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis (⋃ i, X i)
  choose Is hIs using
    fun i ↦ (hI.indep.inter_left (X i)).subset_isBasis_of_subset inter_subset_left
  have hrw (i) : (X i \ I).encard = (X i \ Is i).encard + (Is i \ I).encard := by
    rw [← encard_union_eq, diff_union_diff_cancel' (hIs i).2]
    · exact (hIs i).1.subset.trans subset_union_left
    exact disjoint_sdiff_left.mono_right diff_subset
  rw [hI.nullity_eq, iUnion_diff,
    ← ENat.tsum_encard_eq_encard_iUnion (hX.mono fun _ _ h ↦ h.mono diff_subset diff_subset)]
    at hfin ⊢
  have hfin' : ∑' i, (X i \ Is i).encard < ⊤ := by
    refine lt_of_le_of_lt (ENat.tsum_le_tsum fun i ↦ (encard_le_encard ?_)) hfin
    grw [← diff_self_inter (t := I), (hIs i).2]
  rw [tsum_congr (fun i ↦ (hIs i).1.nullity_eq), tsum_congr hrw, ENat.tsum_add,
    add_eq_left_iff, ENat.tsum_eq_zero, or_iff_right hfin'.ne]
  simp only [encard_eq_zero, diff_eq_empty, ← fun i ↦ (hIs i).1.closure_eq_closure]
  refine ⟨fun h ↦ ?_, fun h i ↦ ?_⟩
  · exact Indep.isSkewFamily_of_disjoint_isBases (hI.indep.subset (iUnion_subset h))
      (hX.mono fun i j h ↦ h.mono (hIs i).1.subset (hIs j).1.subset) (fun i ↦ (hIs i).1)
  rw [hI.eq_of_subset_indep (J := ⋃ i, Is i) (h.iUnion_isBasis_iUnion (fun i ↦ (hIs i).1)).indep]
  · apply subset_iUnion
  · grw [← inter_eq_self_of_subset_right hI.subset, iUnion_inter, iUnion_mono (fun i ↦ (hIs i).2)]
  exact iUnion_mono fun i ↦ (hIs i).1.subset

lemma nullity_union_eq_iff (hdj : Disjoint X Y) (hfin : M.nullity (X ∪ Y) ≠ ⊤)
    (hXE : X ⊆ M.E := by aesop_mat) (hYE : Y ⊆ M.E := by aesop_mat) :
    M.nullity (X ∪ Y) = M.nullity X + M.nullity Y ↔ M.Skew X Y := by
  rw [Skew, ← tsum_nullity_eq_nullity_iUnion_iff_isSkewFamily]
  · simp [tsum_bool, add_comm]
  · rwa [pairwise_on_bool Disjoint.symm]
  · simp [hXE, hYE]
  simpa [lt_top_iff_ne_top]

lemma nullity_iUnion_mono {X Y : ι → Set α} (hX : Pairwise (Disjoint on X))
    (hY : Pairwise (Disjoint on Y)) (hn : ∀ i, M.nullity (X i) ≤ M.nullity (Y i))
    (hcl : ∀ i, M.closure (X i) ⊆ M.closure (Y i)) :
    M.nullity (⋃ i, X i) ≤ M.nullity (⋃ i, Y i) := by
  wlog hE : M.E = univ generalizing M with aux
  · simp_rw [← M.nullity_restrict_univ] at *
    grw [aux hn _ rfl]
    simp only [restrict_closure_eq', inter_univ, union_subset_iff, subset_union_right, and_true]
    exact fun i ↦ (hcl i).trans subset_union_left

  by_cases hsk : M.IsSkewFamily Y
  · have hsk' : M.IsSkewFamily X :=
      (hsk.cls_isSkewFamily.mono hcl).mono (fun i ↦ M.subset_closure (X i))
    grw [hsk.nullity_iUnion_eq hY, hsk'.nullity_iUnion_eq hX, ENat.tsum_le_tsum hn ]
  rw [isSkewFamily_iff_forall_skew_compl_singleton, not_forall] at hsk
  obtain ⟨j, hj⟩ := hsk
  rw [← nullity_union_eq_iff] at hj
  · sorry
  · simp
    sorry
  simp_rw [← biUnion_insert, ← union_singleton, compl_union_self, biUnion_univ]
