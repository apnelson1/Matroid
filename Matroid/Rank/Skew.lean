import Matroid.Rank.Nullity
import Matroid.Connectivity.Skew
import Matroid.ForMathlib.Topology.ENat


theorem ENat.strong_induction_on {p : ℕ∞ → Prop} (n : ℕ∞)
    (h : ∀ (n : ℕ∞), (∀ (m : ℕ∞), m < n → p m) → p n) : p n := by
  have aux (k : ℕ) : p k := by
    induction k using Nat.strong_induction_on with
    | h n IH =>
      refine h _ fun m hm ↦ ?_
      lift m to ℕ using (hm.trans_le <| le_top).ne
      exact IH _ (by simpa using hm)
  apply h _ fun i hin ↦ ?_
  lift i to ℕ using (hin.trans_le le_top).ne
  apply aux

theorem ENat.nat_strong_induction_on {p : ℕ∞ → Prop} (n : ℕ∞) (htop : p ⊤)
    (h : ∀ (n : ℕ), (∀ (m : ℕ), m < n → p m) → p n) : p n := by
  apply ENat.strong_induction_on _ fun n hn ↦ ?_
  cases n using ENat.recTopCoe with
  | top => exact htop
  | coe a => exact h _ fun m hm ↦ hn _ <| by simpa

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

lemma Skew.nullity_union_eq (hXY : M.Skew X Y) (hdj : Disjoint X Y) :
    M.nullity (X ∪ Y) = M.nullity X + M.nullity Y := by
  simpa using IsSkewFamily.nullity_iUnion_eq hXY <| by rwa [pairwise_disjoint_on_bool]

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
    ENat.add_eq_left_iff, ENat.tsum_eq_zero, or_iff_right hfin'.ne]
  simp only [encard_eq_zero, diff_eq_empty]
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
  · simp
  · rwa [pairwise_on_bool Disjoint.symm]
  · simp [hXE, hYE]
  simpa [lt_top_iff_ne_top]

lemma not_skew_iff_nullity_lt_nullity_project (hfin : M.nullity Y ≠ ⊤) (hdj : Disjoint X Y)
    (hX : X ⊆ M.E := by aesop_mat) (hY : Y ⊆ M.E := by aesop_mat) :
    ¬ M.Skew X Y ↔ M.nullity Y < (M.project X).nullity Y := by
  refine Iff.symm ⟨fun h hi ↦ h.ne ?_, fun h ↦ ?_⟩
  · rw [nullity_project_eq_nullity_contract, ← (M ／ X).nullity_restrict_self,
      hi.contract_restrict_eq, nullity_restrict_self]
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  obtain ⟨J, hJ⟩ := M.exists_isBasis Y
  have hfin : (Y \ J).Finite := by rwa [← encard_ne_top_iff, ← hJ.nullity_eq]
  obtain ⟨J', hJ'⟩ := (M.project I).exists_isBasis J
  have hJ'Y : (M.project I).IsBasis J' Y := by
    refine hJ'.isBasis_of_closure_eq_closure (hJ'.subset.trans hJ.subset) ?_
    rw [project_closure, project_closure, closure_union_congr_left hJ.closure_eq_closure]
  rw [← skew_iff_isBases_skew hI hJ, hI.indep.skew_iff_disjoint_union_indep hJ.indep,
    and_iff_right (hdj.mono hI.subset hJ.subset)] at h
  rw [hI.project_eq_project, hJ'Y.nullity_eq, hJ.nullity_eq]
  apply hfin.encard_lt_encard
  rw [← diff_union_diff_cancel hJ.subset hJ'.subset, ssubset_union_left_iff,
    subset_diff, and_iff_right (diff_subset.trans hJ.subset), disjoint_iff_inter_eq_empty,
    ← inter_diff_right_comm, inter_self, diff_eq_empty]
  intro hss
  obtain rfl : J = J' := hss.antisymm hJ'.subset
  replace hJ' := hJ'.indep
  rw [project_indep_iff, hI.indep.contract_indep_iff, union_comm] at hJ'
  exact h hJ'.2

lemma not_skew_iff_nullity_union_gt (hfin : M.nullity (X ∪ Y) ≠ ⊤) (hdj : Disjoint X Y)
    (hX : X ⊆ M.E := by aesop_mat) (hY : Y ⊆ M.E := by aesop_mat) :
    ¬ M.Skew X Y ↔ M.nullity X + M.nullity Y < M.nullity (X ∪ Y) := by
  rw [← nullity_union_eq_iff hdj hfin, lt_iff_le_and_ne, eq_comm, and_iff_right]
  apply M.nullity_add_nullity_le_nullity_union hdj

lemma nullity_biUnion_mono {X Y : ι → Set α} {I : Set ι} (hX : I.PairwiseDisjoint X)
    (hY : I.PairwiseDisjoint Y) (hn : ∀ i ∈ I, M.nullity (X i) ≤ M.nullity (Y i))
    (hcl : ∀ i ∈ I, M.closure (X i) ⊆ M.closure (Y i)) :
    M.nullity (⋃ i ∈ I, X i) ≤ M.nullity (⋃ i ∈ I, Y i) := by
  wlog hE : M.E = univ generalizing M with aux
  · simp_rw [← M.nullity_restrict_univ] at *
    grw [aux hn _ rfl]
    simp only [restrict_closure_eq', inter_univ, union_subset_iff, subset_union_right, and_true]
    exact fun i hi ↦ (hcl i hi).trans subset_union_left
  generalize h_eq : M.nullity (⋃ i ∈ I, Y i) = k
  -- induct on the nullity of `⋃ i ∈ I, Y i`.
  induction k using ENat.strong_induction_on generalizing I with
  | h n IH =>
  · obtain rfl | hlt := eq_top_or_lt_top n
    · simp
    obtain rfl := h_eq
    -- If `Y` is a skew family, then the closure hypothesis gives that `X` is too,
    -- so nullity is additive for both families, and the result is easy.
    by_cases hsk : M.IsSkewFamily (fun i : I ↦ Y i)
    · have hsk' : M.IsSkewFamily (fun i : I ↦ X i) :=
      (hsk.cls_isSkewFamily.mono (fun i : I ↦ hcl i.1 i.2)).mono fun i ↦ M.subset_closure ..
      grw [biUnion_eq_iUnion, biUnion_eq_iUnion, hsk.nullity_iUnion_eq, hsk'.nullity_iUnion_eq,
        ENat.tsum_le_tsum (fun i : I ↦ hn i.1 i.2)]
      · rwa [PairwiseDisjoint, ← pairwise_subtype_iff_pairwise_set] at hX
      rwa [PairwiseDisjoint, ← pairwise_subtype_iff_pairwise_set] at hY
    -- Otherwise, there exists `Y j` that is not skew to the union of the other `Y i`.
    obtain ⟨j, J, hIJ, hjJ, hj⟩ :
      ∃ j J, I = insert j J ∧ j ∉ J ∧ ¬ M.Skew (Y j) (⋃ i ∈ J, Y i) := by
      simp_rw [isSkewFamily_set_coe_iff_forall_skew_compl_singleton, not_forall, exists_prop] at hsk
      obtain ⟨j, hj, hsk⟩ := hsk
      exact ⟨j, I \ {j}, by simp [hj], by simp, hsk⟩
    -- Let `J = I \ {j}`.
    simp only [hIJ, mem_insert_iff, forall_eq_or_imp] at hn hcl
    rw [hIJ, PairwiseDisjoint, pairwise_insert_of_symmetric_of_notMem (fun _ _ h ↦ h.symm) hjJ]
      at hX hY
    simp_rw [Function.onFun, ← disjoint_iUnion_right] at hX hY
    -- by the choice of `J`, the union of `Y i` over `J` has lower nullity than the union over `I`
    have hlt : M.nullity (⋃ i ∈ J, Y i) < M.nullity (⋃ i ∈ I, Y i) := by
      rw [not_skew_iff_nullity_union_gt _ hY.2 (by simp [hE]) (by simp [hE]),
        ← biUnion_insert, ← hIJ] at hj
      · exact (le_add_self ..).trans_lt hj
      simpa [← biUnion_insert, ← hIJ] using hlt.ne
    -- We can now apply the inductive hypothesis to `J`
    have hle := IH _ hlt hX.1 hY.1 hn.2 hcl.2 rfl
    have hcl' : M.closure (⋃ j ∈ J, X j) ⊆ M.closure (⋃ j ∈ J, Y j) := by
      refine M.closure_subset_closure_of_subset_closure ?_
      simp_rw [iUnion_subset_iff]
      intro i hiJ
      grw [M.subset_closure (X i) (by simp [hE]), hcl.2 i hiJ]
      exact M.closure_subset_closure (subset_biUnion_of_mem hiJ)
    -- the result follows by calculations.
    replace hle := nullity_project_le_of_le hle (C := Y j) hcl'
    simp_rw [hIJ, biUnion_insert, nullity_union_eq_nullity_contract_add_nullity,
      ← nullity_project_eq_nullity_contract, hX.2.sdiff_eq_right, hY.2.sdiff_eq_right]
    grw [nullity_project_ge _ (Y j), project_project, ← project_closure_eq,
      ← closure_closure_union_closure_eq_closure_union,
      union_eq_self_of_subset_left (hcl.1), closure_closure, project_closure_eq, hle, hn.1]

lemma nullity_iUnion_mono {X Y : ι → Set α} (hX : Pairwise (Disjoint on X))
    (hY : Pairwise (Disjoint on Y)) (hn : ∀ i, M.nullity (X i) ≤ M.nullity (Y i))
    (hcl : ∀ i, M.closure (X i) ⊆ M.closure (Y i)) :
    M.nullity (⋃ i, X i) ≤ M.nullity (⋃ i, Y i) := by
  rw [← biUnion_univ, ← biUnion_univ (s := Y)]
  exact nullity_biUnion_mono (by simpa [PairwiseDisjoint, pairwise_univ])
    (by simpa [PairwiseDisjoint, pairwise_univ]) (by simpa) (by simpa)

lemma nullity_iUnion_congr {X Y : ι → Set α} (hX : Pairwise (Disjoint on X))
    (hY : Pairwise (Disjoint on Y)) (hn : ∀ i, M.nullity (X i) = M.nullity (Y i))
    (hcl : ∀ i, M.closure (X i) = M.closure (Y i)) :
    M.nullity (⋃ i, X i) = M.nullity (⋃ i, Y i) :=
  (nullity_iUnion_mono hX hY (fun i ↦ (hn i).le) (fun i ↦ (hcl i).subset)).antisymm
  (nullity_iUnion_mono hY hX (fun i ↦ (hn i).symm.le) (fun i ↦ (hcl i).symm.subset))
