import Matroid.Connectivity.Local
import Matroid.Connectivity.Basic
import Matroid.Minor.Order

open Set Function

namespace Matroid

variable {α ι : Type*} {M : Matroid α} {e f x y : α} {C D : Set α}


section Multi

variable {I X : ι → Set α}

lemma multiConn_restrict (M : Matroid α) (X : ι → Set α) (R : Set α) :
    (M ↾ R).multiConn X = M.multiConn (fun i ↦ (X i ∩ R)) := by
  choose I hI using fun i ↦ M.exists_isBasis' (X i ∩ R)
  have hIR (i) : I i ⊆ R := (hI i).subset.trans inter_subset_right
  rw [multiConn_eq_comap_nullity (I := I), multiConn_eq_comap_nullity (I := I) hI,
    comap_restrict, nullity_restrict_of_subset]
  · simpa [preimage_preimage] using hIR
  simpa [isBasis'_restrict_iff, hIR]

lemma multiConn_restrict_of_subset (M : Matroid α) {R : Set α} (hX : ∀ i, X i ⊆ R) :
    (M ↾ R).multiConn X = M.multiConn X := by
  simp_rw [multiConn_restrict,
    show ∀ i, X i ∩ R = X i from fun i ↦ inter_eq_self_of_subset_left (hX i)]

lemma multiConn_restrict_le (M : Matroid α) (X : ι → Set α) (R : Set α) :
    (M ↾ R).multiConn (fun i ↦ (X i) ∩ R) ≤ M.multiConn X := by
  rw [multiConn_restrict]
  exact multiConn_mono _ fun i ↦ inter_subset_left.trans inter_subset_left

lemma multiConn_delete (M : Matroid α) (X : ι → Set α) (D : Set α) :
    (M ＼ D).multiConn X = M.multiConn fun i ↦ (X i \ D) := by
  rw [delete_eq_restrict, multiConn_restrict, eq_comm, ← multiConn_inter_ground]
  convert rfl using 3 with i
  tauto_set

lemma multiConn_delete_of_disjoint (M : Matroid α) {D : Set α} (hXD : ∀ i, Disjoint (X i) D) :
    (M ＼ D).multiConn X = M.multiConn X := by
  simp_rw [multiConn_delete, (hXD _).sdiff_eq_left]

lemma multiConn_le_multiConn_delete_add_encard (M : Matroid α)
    (hdj : Pairwise (Disjoint on X)) (D : Set α) :
    M.multiConn X ≤ (M ＼ D).multiConn X + D.encard := by
  choose I hI using fun i ↦ (M ＼ D).exists_isBasis' (X i)
  choose J hJ using fun i ↦ (hI i).indep.of_delete.subset_isBasis'_of_subset (hI i).subset
  have hID (i) : Disjoint (I i) D := (subset_diff.1 (hI i).indep.subset_ground).2
  obtain rfl : I = fun i ↦ J i \ D := by
    refine funext fun i ↦ (hI i).eq_of_subset_indep ?_ (subset_diff.2 ⟨(hJ i).2, hID i⟩)
      (diff_subset.trans (hJ i).1.subset)
    rw [delete_indep_iff, and_iff_left disjoint_sdiff_left]
    exact (hJ i).1.indep.diff D
  grw [multiConn_eq_nullity_iUnion'' hdj hI, multiConn_eq_nullity_iUnion'' hdj (fun i ↦ (hJ i).1),
    nullity_delete_of_disjoint _ (by simp [disjoint_sdiff_left]),
    ← iUnion_diff, ← nullity_union_le_nullity_add_encard, diff_union_self]
  exact M.nullity_le_of_subset subset_union_left

lemma multiConn_project_eq_multiConn_contract (M : Matroid α) (C : Set α) :
    (M.project C).multiConn (ι := ι) = (M ／ C).multiConn := by
  ext X
  wlog hXE : ∀ i, X i ⊆ M.E generalizing X with aux
  · rw [← multiConn_inter_ground, aux _ (by simp), ← multiConn_inter_ground, eq_comm,
      ← multiConn_inter_ground]
    simp [inter_assoc, inter_eq_self_of_subset_right diff_subset]
  rwa [eq_comm, ← (M ／ C).multiConn_restrict_of_subset (R := M.E), project]

end Multi

section Dual

variable {ι : Type*} {I X : ι → Set α}

lemma multiConn_dual_eq_eRank_project (hdj : Pairwise (Disjoint on X)) (hu : ⋃ i, X i = M.E)
    (hI : ∀ i, (M.project (M.E \ X i)).IsBasis (I i) (X i)) :
    M✶.multiConn X = (M.project (⋃ i, I i)).eRank := by
  have hXE (i) : X i ⊆ M.E := by grw [← hu, ← subset_iUnion]
  have hI' (i) : M✶.IsBasis (X i \ I i) (X i) := by
    rw [← isBase_restrict_iff, ← delete_compl, ← dual_contract, dual_ground,
      dual_isBase_iff _, ← isBasis_ground_iff, contract_ground, diff_diff_cancel_left (hXE i),
      diff_diff_cancel_left (hI i).subset, ← project_isBasis_iff disjoint_sdiff_right]
    · exact hI i
    grw [contract_ground, diff_diff_cancel_left (hXE i), diff_subset]
  rw [multiConn_eq_nullity_iUnion'' hdj (fun i ↦ (hI' i).isBasis'), nullity_eq_eRank_restrict_dual,
    ← delete_compl, dual_delete_dual, dual_ground, eRank_project]
  congr
  grw [subset_antisymm_iff, diff_subset_iff, ← iUnion_union_distrib, subset_diff,
    iUnion_congr (fun i ↦ diff_union_of_subset (hI i).subset), hu, and_iff_right rfl.subset,
    ← hu, and_iff_right (iUnion_mono (fun i ↦ (hI i).subset)), disjoint_iUnion_right]
  simp_rw [disjoint_iUnion_left]
  intro i j
  obtain rfl | hne := eq_or_ne i j
  · exact disjoint_sdiff_right
  exact (hdj hne).symm.mono (hI j).subset diff_subset

lemma multiConn_dual_eq_eRank_contract (hdj : Pairwise (Disjoint on X)) (hu : ⋃ i, X i = M.E)
    (hI : ∀ i, (M ／ (M.E \ X i)).IsBasis (I i) (X i)) :
    M✶.multiConn X = (M ／ (⋃ i, I i)).eRank := by
  rw [multiConn_dual_eq_eRank_project hdj hu, eRank_project]
  intro i
  rw [project_isBasis_iff disjoint_sdiff_right]
  exact hI i

end Dual

section Local

variable {I X C : Set α}

lemma project_nullity_eq_nullity_add_eLocalConn (M : Matroid α) (X C : Set α) :
    (M.project C).nullity X = M.nullity X + M.eLocalConn X C := by
  wlog hX : X ⊆ M.E generalizing X with aux
  · rw [nullity_eq_nullity_inter_ground_add_encard_diff, project_ground,
      M.nullity_eq_nullity_inter_ground_add_encard_diff, ← eLocalConn_inter_ground_left,
      aux _ inter_subset_right, add_right_comm]
  wlog hC : M.Indep C generalizing C with aux
  · obtain ⟨I, hI⟩ := M.exists_isBasis' C
    rw [hI.project_eq_project, aux _ hI.indep, ← eLocalConn_closure_right, hI.closure_eq_closure,
      eLocalConn_closure_right]
  obtain ⟨J, hJ⟩ := (M.project C).exists_isBasis X
  obtain ⟨K, hK, hJK⟩ := hJ.indep.of_project.subset_isBasis_of_subset hJ.subset
  have hKX := hK.subset
  obtain ⟨hJ'b, hCJ⟩ := hC.project_isBasis_iff.1 hJ
  have hb : M.IsBasis (C ∪ J) (C ∪ K) := by
    exact hJ'b.isBasis_subset (by tauto_set) (union_subset_union_right _ hK.subset)
  rw [hK.eLocalConn_eq hC.isBasis_self, union_comm, hb.nullity_eq, hK.nullity_eq, hJ.nullity_eq,
    ← encard_union_eq (by tauto_set), ← encard_union_eq (by tauto_set)]
  congr
  tauto_set

/-- An explicit description of the slack term in the monotonicity of local connectivity -/
lemma eLocalConn_add_project_eLocalConn_of_subset (M : Matroid α) {X Y : Set α} (hXY : X ⊆ Y)
    (Z : Set α) :
    M.eLocalConn X Z + (M.project X).eLocalConn Y Z = M.eLocalConn Y Z := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  obtain ⟨J, hJ⟩ := (M.project I).exists_isBasis' Y
  obtain ⟨hIJ, hdj⟩ := hI.indep.project_isBasis'_iff.1 hJ
  rw [union_eq_self_of_subset_left (hI.subset.trans hXY)] at hIJ
  rw [hI.project_eq_project, hJ.eLocalConn_eq_nullity_project_right, project_project, union_comm,
    ← project_project, hI.eLocalConn_eq_nullity_project_right,
    hIJ.eLocalConn_eq_nullity_project_right, add_comm, nullity_project_add_nullity_eq,
    union_comm, hdj.symm.inter_eq]
  simp

lemma eLocalConn_union_eq_eLocalConn_project_add_eLocalConn (M : Matroid α) (X Y C : Set α) :
    M.eLocalConn (X ∪ C) Y = (M.project C).eLocalConn X Y + M.eLocalConn Y C := by
  rw [eq_comm, ← M.eLocalConn_add_project_eLocalConn_of_subset (Y := X ∪ C) subset_union_right,
    add_comm, eLocalConn_comm, ← (M.project C).eLocalConn_closure_left, project_closure,
    ← (M.project C).eLocalConn_closure_left (X := X ∪ C), project_closure, union_assoc, union_self]

end Local

section Multi

variable {I X : ι → Set α}

private lemma multiConn_add_tsum_eLocalConn_eq_aux {ι : Type*} {I : ι → Set α}
    (hI : ∀ i, M.Indep (I i)) (hC : M.Indep C) (hdj : Pairwise (Disjoint on I))
    (hIC : ∀ i, Disjoint (I i) C) (a : ι) :
    (M.project C).multiConn I + ∑' i : {i // i ≠ a}, M.eLocalConn (I i) C =
    M.multiConn I + (M.project (I a)).eLocalConn (⋃ i : {i // i ≠ a}, I i) C := by
  choose J hJ using fun i ↦ (M.project C).exists_isBasis (I i)
  rw [multiConn_eq_nullity_iUnion hdj (fun i ↦ (hI i).isBasis_self),
    multiConn_eq_nullity_iUnion'' hdj (fun i ↦ (hJ i).isBasis')]
  have hJ' := hJ
  simp_rw [hC.project_isBasis_iff, forall_and, union_comm C] at hJ'
  have hrw (i : {i // i ≠ a}) : M.eLocalConn (I i) C = (I i \ J i).encard := by
    rw [(hI i).isBasis_self.eLocalConn_eq_of_disjoint hC.isBasis_self (hIC _),
    (hJ'.1 _).nullity_eq, ← diff_diff, diff_diff_comm,
    union_diff_cancel_right (by simp [(hIC _).inter_eq])]
  have hrwu (X : ι → Set α) : (⋃ i, X i) = X a ∪ ⋃ i : {i // i ≠ a}, X i := by
    convert biUnion_insert a {a}ᶜ X with i
    · simp [em]
    apply iUnion_subtype
  rw [tsum_congr hrw, ENat.tsum_encard_eq_encard_iUnion,
    ← Disjoint.nullity_union_eq_of_subset_closure, hrwu J, union_assoc,
    ← iUnion_union_distrib, iUnion_congr (fun i : {i // i ≠ a} ↦ union_diff_cancel (hJ i).subset),
    ← (hJ a).indep.nullity_project_of_disjoint, ← (hJ a).project_eq_project, project_project,
    union_comm, ← project_project, hrwu I, ← Indep.nullity_project_of_disjoint (hI a),
    project_nullity_eq_nullity_add_eLocalConn]
  · simp only [ne_eq, disjoint_iUnion_right, Subtype.forall]
    exact fun i hia ↦ (hdj hia).symm
  · simp only [ne_eq, disjoint_iUnion_right, Subtype.forall]
    exact fun i hia ↦ (hdj hia).symm.mono_left (hJ a).subset
  · simp only [ne_eq, disjoint_iUnion_right, disjoint_iUnion_left, Subtype.forall]
    refine fun i hi j ↦ ?_
    obtain rfl | hne := eq_or_ne i j
    · exact disjoint_sdiff_right
    exact (hdj hne.symm).mono (hJ j).subset diff_subset
  · simp only [ne_eq, project_closure, iUnion_subset_iff, Subtype.forall]
    intro i hia
    grw [diff_subset, (hJ i).subset_closure, project_closure, closure_subset_closure,
      ← subset_iUnion J i]
    rfl
  · exact fun ⟨i,hi⟩ ⟨j,hj⟩ hne ↦ (hdj (show i ≠ j by simpa using hne)).mono (by simp) (by simp)

private lemma multiConn_add_tsum_eLocalConn_eq_aux' {ι : Type*} {I : ι → Set α}
    (hI : ∀ i, M.Indep (I i)) (hC : M.Indep C) (a : ι) :
    (M.project C).multiConn I + ∑' i : {i // i ≠ a}, M.eLocalConn (I i) C =
    M.multiConn I + (M.project (I a)).eLocalConn (⋃ i : {i // i ≠ a}, I i) C := by
  set M' : Matroid (α × Option ι) := M.comap Prod.fst with hM'_def
  set I' : ι → Set (α × Option ι) := fun i ↦ (·, some i) '' (I i) with hI'_def
  set C' : Set (α × Option ι) := (·, none) '' C with hC'_def
  have hrw1 : M.multiConn I = M'.multiConn I' := by
    simp [I', M', image_image]
  have hrw2 (i : {i // i ≠ a}) : M.eLocalConn (I i) C = M'.eLocalConn (I' i.1) C' := by
    simp [hM'_def, I', C', image_image]
  have hrw3 : (M.project C).multiConn I = (M'.project C').multiConn I' := by
    simp [C', M', I', ← project_comap_image, image_image]
  have hrw4 : (M.project (I a)).eLocalConn (⋃ i : {i // i ≠ a}, I i) C =
      (M'.project (I' a)).eLocalConn (⋃ i : {i // i ≠ a}, I' i) C' := by
    simp [M', I', C', ← project_comap_image, image_image, image_iUnion]
  rw [hrw1, tsum_congr hrw2, hrw3, hrw4, multiConn_add_tsum_eLocalConn_eq_aux]
  · simp only [comap_indep_iff, image_image, image_id', hI, true_and, M', I']
    exact fun i ↦ LeftInvOn.injOn_image fun ⦃x⦄ ↦ congrFun rfl
  · simp only [comap_indep_iff, image_image, image_id', hC, true_and, M', C']
    exact LeftInvOn.injOn_image fun ⦃x⦄ ↦ congrFun rfl
  · simp +contextual [Pairwise, disjoint_iff_forall_ne, I']
  simp [I', C', disjoint_iff_forall_ne]

lemma multiConn_project_add_tsum_eLocalConn_ne_eq (M : Matroid α) (X : ι → Set α) (C : Set α)
    (a : ι) : (M.project C).multiConn X + ∑' i : {i | i ≠ a}, M.eLocalConn (X i) C =
    M.multiConn X + (M.project (X a)).eLocalConn (⋃ i ≠ a, X i) C := by
  obtain ⟨J, hJ⟩ := M.exists_isBasis' C
  have hrwC : (M.project (X a)).closure C = (M.project (X a)).closure J := by
    simp only [project_closure, closure_union_congr_left hJ.closure_eq_closure]
  choose I hI using fun i ↦ M.exists_isBasis' (X i)
  rw [← multiConn_closure_congr (fun i ↦ (hI i).closure_eq_closure), hJ.project_eq_project,
    ← eLocalConn_closure_closure, hrwC, (hI a).project_eq_project]
  convert multiConn_add_tsum_eLocalConn_eq_aux' (fun i ↦ (hI i).indep) hJ.indep a using 2
  · apply multiConn_closure_congr fun i ↦ ?_
    rw [project_closure, ← closure_union_congr_left (hI i).closure_eq_closure, ← project_closure]
  · apply tsum_congr
    simp only [ne_eq, Subtype.forall]
    rintro i -
    rw [← eLocalConn_closure_closure, ← (hI i).closure_eq_closure, ← hJ.closure_eq_closure,
      eLocalConn_closure_closure]
  rw [← eLocalConn_closure_closure, eq_comm, ← eLocalConn_closure_closure]
  simp only [project_closure, closure_union_closure_left_eq, union_assoc, union_self]
  rw [closure_union_congr_left
    (closure_iUnion_congr _ _ (fun i : {i // i ≠ a} ↦ (hI i).closure_eq_closure)), iUnion_subtype]

lemma multiConn_project_add_tsum_eLocalConn_eq (M : Matroid α) (X : ι → Set α) (C : Set α) :
    (M.project C).multiConn X + ∑' i, M.eLocalConn (X i) C
      = M.multiConn X + M.eLocalConn (⋃ i, X i) C := by
  obtain hι | ⟨⟨a⟩⟩ := isEmpty_or_nonempty ι; simp
  rw [← M.eLocalConn_add_project_eLocalConn_of_subset (X := X a) (subset_iUnion ..) (Z := C),
    ← tsum_univ, show univ = insert a {i | i ≠ a} by ext; simp [em],
    ENat.tsum_insert (f := fun i ↦ M.eLocalConn (X i) C) (by simp),
    add_comm (M.eLocalConn ..), add_comm (M.eLocalConn ..), ← add_assoc, ← add_assoc,
    multiConn_project_add_tsum_eLocalConn_ne_eq, ← eLocalConn_closure_left,
    project_closure_eq_project_closure_union, eLocalConn_closure_left]
  convert rfl
  rw [union_comm, ← biUnion_univ, show univ = insert a {a}ᶜ by ext; simp [em]]
  simp

-- /-- An auxiliary lemma used to numerically relate the `multiConn` in a matroid its projection,
-- in terms of chosen bases.  -/
-- lemma multiConn_project_aux' (M : Matroid α) {C : Set α} (hI : ∀ i, M.IsBasis' (I i) (X i)) :
--     (M.project C).multiConn X + (M.project (⋃ i, X i)).eRk C + ∑' i, (M.project C).nullity (I i)
--     = M.multiConn X + M.eRk C := by
--   sorry

private lemma multiConn_project_add_disjoint_aux (M : Matroid α) {C : Set α} (hCX : C ⊆ ⋃ i, X i)
    (hdj : Pairwise (Disjoint on X)) (hC : M.Indep C) :
    (M.project C).multiConn X + ∑' i, (M.project (X i ∩ C)).eLocalConn (X i) C = M.multiConn X := by
  choose I hI using fun i ↦ (M.project (X i ∩ C)).exists_isBasis' (X i)
  have h' (i) : (M.project (X i ∩ C)).IsBasis' (C \ X i) C := by
    rw [(hC.inter_left _).project_isBasis'_iff, inter_comm, and_iff_left disjoint_sdiff_inter.symm,
      inter_union_diff, union_eq_self_of_subset_left inter_subset_left]
    exact hC.isBasis_self.isBasis'
  choose J hJ using fun i ↦ (M.project C).exists_isBasis' (I i)
  have hJX (i : ι) : (M.project C).closure (I i) = (M.project C).closure (X i) := by
    rw [← inter_union_diff C (X i), ← project_project, inter_comm, project_closure,
      closure_union_congr_left (hI i).closure_eq_closure, project_closure]
    simp only [union_diff_self, project_project, project_closure]
    convert rfl using 2
    tauto_set
  have hdjC (i) : Disjoint (I i) C := by
    rw [← inter_eq_self_of_subset_left (hI i).subset, disjoint_iff_inter_eq_empty, inter_assoc,
      ((hC.inter_left _).project_isBasis'_iff.1 (hI i)).2.symm.inter_eq]
  have hI' (i) := (hC.inter_left _).project_isBasis'_iff.1 (hI i)
  have hb (i) : M.IsBasis' ((C ∩ X i) ∪ I i) (X i) := by
    convert ((hC.inter_left _).project_isBasis'_iff.1 (hI i)).1 using 2 <;> tauto_set
  have hsumrw (i) : (M.project (X i ∩ C)).eLocalConn (X i) C = (I i \ J i).encard := by
    rw [(hI i).eLocalConn_eq_of_disjoint' (h' i) (disjoint_sdiff_right.mono_left (hI i).subset),
      inter_comm, (hC.inter_right _).nullity_project_of_disjoint, union_comm (I i), ← union_assoc,
      inter_union_diff]
    · rw [(hC.project_isBasis'_iff.1 (hJ i)).1.nullity_eq, ← diff_diff, union_diff_left,
      (hdjC i).sdiff_eq_left]
    simp only [disjoint_union_right]
    exact ⟨(hdjC i).symm.mono_left inter_subset_left, disjoint_sdiff_inter.symm⟩
  rw [← multiConn_closure_congr hJX, multiConn_eq_nullity_iUnion' _ hJ,
    hC.nullity_project_of_disjoint _, tsum_congr hsumrw, multiConn_eq_nullity_iUnion' _ hb,
    ENat.tsum_encard_eq_encard_iUnion, ← Disjoint.nullity_union_eq_of_subset_closure,
    union_assoc, ← iUnion_union_distrib, iUnion_congr (fun i ↦ union_diff_cancel (hJ i).subset),
    iUnion_union_distrib, ← inter_iUnion, inter_eq_self_of_subset_left hCX]
  · simp only [disjoint_iUnion_right, disjoint_union_left, disjoint_iUnion_left]
    refine fun i ↦ ⟨(hdjC i).symm.mono_right diff_subset, fun j ↦ ?_⟩
    obtain rfl | hne := eq_or_ne i j
    · exact disjoint_sdiff_right
    grw [(hJ j).subset, diff_subset, (hI _).subset, (hI _).subset]
    exact hdj hne.symm
  · refine iUnion_subset fun i ↦ ?_
    grw [diff_subset, union_comm, ← project_closure, ← subset_iUnion (s := J) (i := i),
      (hJ i).closure_eq_closure, ← (M.project C).subset_closure _ (hI i).indep.subset_ground]
  · exact hdj.mono fun i j hdj' ↦ hdj'.mono (diff_subset.trans (hI i).subset)
      (diff_subset.trans (hI j).subset)
  · exact hdj.mono fun i j ↦ Disjoint.mono (by simp [(hI i).subset]) (by simp [(hI j).subset])
  · simp only [disjoint_iUnion_right]
    exact fun i ↦ (hdjC i).symm.mono_right (hJ i).subset
  exact hdj.mono fun i j ↦ Disjoint.mono ((hJ i).subset.trans (hI i).subset)
    ((hJ j).subset.trans (hI j).subset)

lemma multiConn_project_add_disjoint (M : Matroid α) {C : ι → Set α} (hCX : ∀ i, C i ⊆ X i)
    (hdj : Pairwise (Disjoint on C)) (hi : M.Indep (⋃ i, C i)) : (M.project (⋃ i, C i)).multiConn X
    + ∑' i, (M.project (C i)).eLocalConn (X i) (⋃ i, C i) = M.multiConn X := by
  have hrw (j) : (·, j) '' X j ∩ ⋃ i, (·, i) '' (C i) = (·, j) '' C j := by aesop
  convert (M.comap Prod.fst).multiConn_project_add_disjoint_aux (C := ⋃ i, (·, i) '' (C i))
    (X := fun i ↦ (·, i) '' (X i)) (iUnion_mono fun i ↦ image_mono (hCX i)) _ _ with i
  · simp_rw [← project_comap_image, image_iUnion, image_image, image_id', multiConn_comap,
      image_image, image_id']
  · simp [← project_comap_image, image_image, image_iUnion, hrw]
  · simp [image_image]
  · simp +contextual [Pairwise, disjoint_iff_forall_ne]
  simp only [comap_indep_iff, image_iUnion, image_image, image_id', hi, true_and]
  rwa [injOn_prod_fst_mk_left_iff_pairwise_disjoint]

lemma multiConn_project_le (M : Matroid α) {C : Set α} (hC : C ⊆ ⋃ i, X i) :
    (M.project C).multiConn X ≤ M.multiConn X := by
  obtain hι | hι := isEmpty_or_nonempty ι; simp
  obtain ⟨I, hI⟩ := M.exists_isBasis' C
  have chooser (e) : e ∈ I →  ∃ i, e ∈ X i := fun h ↦ by simpa using (hI.subset.trans hC) h
  choose! inds hinds using chooser
  have h_eq : ⋃ i, I ∩ inds ⁻¹' {i} = I := by
    rw [← inter_iUnion, ← preimage_iUnion, iUnion_of_singleton, preimage_univ, inter_univ]
  rw [← M.multiConn_project_add_disjoint (C := fun i ↦ I ∩ inds ⁻¹' {i}) (X := X) ?_]
  · grw [h_eq, hI.project_eq_project, ← le_self_add]
  · simp +contextual [Pairwise, disjoint_left]
  · rw [h_eq]
    exact hI.indep
  simp only [subset_def, mem_inter_iff, mem_preimage, mem_singleton_iff, and_imp]
  rintro i e hei rfl
  exact hinds e hei

lemma multiConn_contract_le (M : Matroid α) {C : Set α} (hC : C ⊆ ⋃ i, X i) :
    (M ／ C).multiConn X ≤ M.multiConn X := by
  grw [← multiConn_project_eq_multiConn_contract, multiConn_project_le _ hC]

lemma multiConn_le_multiConn_project_add_mul_eLocalConn
    (M : Matroid α) (X : ι → Set α) (C : Set α) :
    M.multiConn X ≤ (M.project C).multiConn X + (ENat.card ι - 1) * M.eLocalConn (⋃ i, X i) C := by
  obtain hι | ⟨⟨a⟩⟩ := isEmpty_or_nonempty ι; simp
  have hcard : ENat.card ι - 1 = ENat.card {i | i ≠ a} := by
    rw [← encard_univ, ← encard_diff_singleton_of_mem (a := a) (by simp), ENat.card_coe_set_eq]
    congr
    ext
    simp
  have hle := (M.multiConn_project_add_tsum_eLocalConn_ne_eq X C a).symm.le
  grw [← le_self_add] at hle
  grw [hle, add_le_add_left]
  grw [ENat.tsum_le_tsum (g := fun i ↦ M.eLocalConn (⋃ j, X j) C)
    fun i ↦ eLocalConn_mono_left _ (by simp [subset_iUnion]) _, ENat.tsum_const, hcard, mul_comm]


    -- ENat.tsum_le_tsum (f := fun i : { i // i ≠ a } ↦ M.eLocalConn (⋃ j, X j) C)]

  -- grw [this]


-- lemma multiConn_project_aux_indep (M : Matroid α) {C : Set α} (hC : M.Indep C) (X : ι → Set α) :
--     (M.project C).multiConn X + ∑' i, (M.project (X i)).nullity C
--     = M.multiConn X + (M.project (⋃ i, X i)).nullity C := by
--   -- We may assume that `ι` is nonempty and `C` is independent.
--   obtain hι | hι := isEmpty_or_nonempty ι
--   · simp [hC.nullity_eq]
--   choose I hI using fun i ↦ M.exists_isBasis' (X i)
--   choose J hJ using fun i ↦ (M.project C).exists_isBasis' (I i)
--   -- Choose `C'` to be an arbitrary injective preimage of `C`,
--   -- and prove that `C'` is a basis of the preimage of `C` in the comap.
--   set C' : Set (α × ι) := (· , Classical.arbitrary ι) '' C with hC'_def
--   have hC'bas : (M.comap Prod.fst).IsBasis' C' (Prod.fst ⁻¹' C) := by
--     suffices M.IsBasis' C (Prod.fst '' (Prod.fst ⁻¹' C)) by
--       simpa [hC'_def, image_image, InjOn, preimage_preimage]
--     rw [image_preimage_eq _ Prod.fst_surjective]
--     exact hC.isBasis_self.isBasis'
--   -- Each `J i` spans `X i` in `M.project C`, so is a basis.
--   have hJX (i) : (M.project C).IsBasis' (J i) (X i) := by
--     rw [isBasis'_iff_isBasis_closure, and_iff_left ((hJ i).subset.trans (hI i).subset)]
--     refine (hJ i).indep.isBasis_of_subset_of_subset_closure ?_ ?_
--     · grw [(hJ i).subset, ← closure_subset_closure _ (hI i).subset]
--       exact subset_closure _ _ (by simpa using (hI i).indep.subset_ground)
--     rw [(hJ i).closure_eq_closure, project_closure, project_closure,
--       ← closure_union_congr_left (hI i).closure_eq_closure]
--   -- the sum of cardinality term is equal to the cardinality of a union.
--   have hsrw (i) : (M.project (X i)).nullity C = (I i \ J i).encard := by
--     rw [(hI i).project_eq_project, ← add_zero (nullity ..), ← (hI i).indep.nullity_eq,
--       nullity_project_add_nullity_comm, hC.nullity_eq, add_zero, (hJ i).nullity_eq]
--   have hcard : ∑' i, (M.project (X i)).nullity C
--       = ((⋃ i, ((·, i) '' I i)) \ (⋃ i, ((·, i) '' J i))).encard := by
--     rw [tsum_congr hsrw, ← iUnion_diff_iUnion
--       (fun i ↦ (image_mono (hJ i).subset)) disjoint_map_prod_right,
--       ← ENat.tsum_encard_eq_encard_iUnion, tsum_congr]
--     · intro i
--       rw [← image_diff (Prod.mk_left_injective i), (Prod.mk_left_injective i).encard_image ]
--     exact (disjoint_map_prod_right (f := I)).mono fun _ _ ↦ Disjoint.mono diff_subset diff_subset
--   -- the union of the lifted `I`s is spanned by the union of the lifted `J`s in `M.project C`.
--   have hcl : ⋃ i, (·, i) '' I i ⊆ ((M.project C).comap Prod.fst).closure (⋃ i, (·, i) '' J i) :=
--     suffices ∀ (i : ι), I i ⊆ M.closure ((⋃ i, J i) ∪ C) by
--       simpa [preimage_preimage, image_iUnion, image_image]
--     intro i
--     rw [← project_closure, closure_iUnion_congr _ _ fun i ↦ (hJ i).closure_eq_closure]
--     exact subset_closure_of_subset' _ (subset_iUnion ..) (hI i).indep.subset_ground
--   -- We are now done by a calculation.
--   rw [multiConn_eq_comap_nullity hI, multiConn_eq_comap_nullity hJX, hcard,
--     ← nullity_eq_nullity_add_encard_diff (iUnion_mono fun i ↦ image_mono (hJ i).subset) hcl,
--     ← add_zero (nullity ..), ← hC'bas.indep.nullity_eq, project_comap _ _ _ (by simp),
--     hC'bas.project_eq_project, nullity_project_add_nullity_comm, ← project_comap_image]
--   simp only [image_iUnion, image_image, image_id']
--   rw [← project_closure_eq, closure_iUnion_congr _ _ (fun i ↦ (hI i).closure_eq_closure),
--     project_closure_eq, add_comm (nullity ..),  nullity_comap (X := C')]
--   · simp only [hC'_def, image_image, image_id']
--   simp [hC'_def, InjOn]


-- /-- An auxiliary lemma used to numerically relate the `multiConn` in a matroid its projection,
-- in terms of chosen bases.  -/
-- lemma multiConn_project_aux (M : Matroid α) {C : Set α} (hI : ∀ i, M.IsBasis' (I i) (X i)) :
--     (M.project C).multiConn X + (M.project (⋃ i, X i)).eRk C + ∑' i, (M.project C).nullity (I i)
--     = M.multiConn X + M.eRk C := by
--   wlog hC : M.Indep C generalizing C with aux
--   · obtain ⟨K, hK⟩ := M.exists_isBasis' C
--     simp_rw [hK.project_eq_project, ← hK.eRk_eq_eRk]
--     convert aux hK.indep using 3
--     rw [← eRk_closure_eq, project_closure, ← closure_union_congr_left hK.closure_eq_closure,
--       ← project_closure, eRk_closure_eq]
--   have hrw := M.multiConn_project_aux_indep hC X
--   apply_fun (· + (M.project (⋃ i, X i)).eRk C) at hrw
--   rw [add_right_comm, add_right_comm (a := M.multiConn X), add_assoc (a := M.multiConn X),
--     eRk_add_nullity_eq_encard, ← hC.eRk_eq_encard] at hrw
--   convert hrw using 4 with i
--   rw [hC.nullity_project, (hI i).project_eq_project, (hI i).indep.nullity_project,
--     union_comm, inter_comm]

-- lemma multiConn_project_add_tsum_eLocalConn_eq (M : Matroid α) (X : ι → Set α) (C : Set α) :
--     (M.project C).multiConn X + ∑' i, M.eLocalConn (X i) C
--       = M.multiConn X + M.eLocalConn (⋃ i, X i) C := by
--   wlog hC : M.Indep C generalizing C with aux
--   · obtain ⟨I, hI⟩ := M.exists_isBasis' C
--     convert aux _ hI.indep using 2
--     · rw [hI.project_eq_project]
--     · convert rfl using 3 with i
--       obtain ⟨J, hJ⟩ := M.exists_isBasis' (X i)
--       rw [hJ.eLocalConn_eq hI, hJ.eLocalConn_eq hI.indep.isBasis_self.isBasis']
--     obtain ⟨J, hJ⟩ := M.exists_isBasis' (⋃ i, X i)
--     rw [hJ.eLocalConn_eq hI, hJ.eLocalConn_eq hI.indep.isBasis_self.isBasis']
--   have aux {Y : Set α} : M.eLocalConn Y C = (M.project Y).nullity C := by
--     obtain ⟨J, hJ⟩ := M.exists_isBasis' Y
--     rw [hJ.eLocalConn_eq hC.isBasis_self.isBasis', hJ.project_eq_project,
--       hJ.indep.nullity_project, union_comm, inter_comm, add_comm]
--   simp [aux]
--   apply M.multiConn_project_aux_indep hC

-- lemma multiConn_le_multiConn_project_add (M : Matroid α) (X : ι → Set α) (C : Set α) :
--     M.multiConn X ≤ (M.project C).multiConn X + (ENat.card ι - 1) * M.eLocalConn (⋃ i, X i) C :=
--   obtain hss | hnt := subsingleton_or_nontrivial ι
--   · simp
--   obtain hfin | hinf := eq_top_or_lt_top (M.eLocalConn (⋃ i, X i) C)
--   · have hlt : 0 < ENat.card ι - 1 := by simp
--     simp [hfin, ENat.mul_top hlt.ne.symm]
--   obtain hc0 | hnz := eq_or_ne (M.eLocalConn (⋃ i, X i) C) 0
--   · simp [hc0]
--     sorry

    -- rw [eLocalConn, multiConn_eq_zero_iff] at hc0


lemma multiConn_project_le_multiConn_add (M : Matroid α) (X : ι → Set α) (C : Set α) :
    (M.project C).multiConn X ≤ M.multiConn X + M.eRk C := by
  grw [← M.eLocalConn_le_eRk_right (⋃ i, X i) C, ← M.multiConn_project_add_tsum_eLocalConn_eq,
    ← le_self_add]

lemma multiConn_project_eq_multiConn_add_iff (M : Matroid α) {X : ι → Set α} {C : Set α}
    (hXfin : M.multiConn X ≠ ⊤) (hXE : ∀ i, X i ⊆ M.E) (hCfin : M.IsRkFinite C) (hCE : C ⊆ M.E):
    (M.project C).multiConn X = M.multiConn X + M.eRk C ↔
      C ⊆ M.closure (⋃ i, X i) ∧ ∀ i, M.Skew (X i) C := by
  have hlt : (M.project C).multiConn X < ⊤ := by
    grw [M.multiConn_project_le_multiConn_add]
    simpa [hCfin, lt_top_iff_ne_top]
  rw [← M.eLocalConn_add_eRelRk_union_eq_eRk C (⋃ i, X i), ← add_assoc, eLocalConn_comm,
    ← multiConn_project_add_tsum_eLocalConn_eq, add_assoc, ENat.eq_add_left_iff, add_eq_zero,
      ENat.tsum_eq_zero, eRelRk_eq_zero_iff, union_subset_iff,
      and_iff_left (M.subset_closure _), and_comm, or_iff_left hlt.ne]
  convert Iff.rfl with i
  rw [eLocalConn_eq_zero]

lemma multiConn_projectElem_eq_multiConn_add_iff (M : Matroid α) {X : ι → Set α} {e : α}
    (hXfin : M.multiConn X ≠ ⊤) (he : M.IsNonloop e) :
    (M.project {e}).multiConn X = M.multiConn X + 1 ↔
      e ∈ M.closure (⋃ i, X i) ∧ ∀ i, e ∉ M.closure (X i) := by
  wlog hXE : ∀ i, X i ⊆ M.E generalizing X with aux
  · rw [← multiConn_inter_ground, ← M.multiConn_inter_ground, project_ground, aux
      (by rwa [multiConn_inter_ground]) (fun i ↦ inter_subset_right), ← iUnion_inter]
    simp
  rw [← he.eRk_eq, multiConn_project_eq_multiConn_add_iff _ hXfin hXE (by simp)
    (by simpa using he.mem_ground), singleton_subset_iff]
  simp_rw [he.skew_right_iff (hXE _)]


end Multi

section Pair

variable {X Y I J}

lemma eLocalConn_delete_le (M : Matroid α) : (M ＼ D).eLocalConn X Y ≤ M.eLocalConn X Y := by
  rw [eLocalConn_delete_eq]
  exact M.eLocalConn_mono diff_subset diff_subset

lemma eLocalConn_project_eq_eLocalConn_contract_diff (M : Matroid α) (X Y C : Set α) :
    (M.project C).eLocalConn X Y = (M ／ C).eLocalConn (X \ C) (Y \ C) := by
  rw [project, eLocalConn_restrict_eq, ← eLocalConn_inter_ground, eq_comm,
    ← eLocalConn_inter_ground, contract_ground]
  convert rfl using 2 <;> tauto_set

lemma eLocalConn_project_eq_eLocalConn_contract (M : Matroid α) (X Y C : Set α) :
    (M.project C).eLocalConn X Y = (M ／ C).eLocalConn X Y := by
  rw [project, eLocalConn_restrict_eq, ← eLocalConn_inter_ground, eq_comm,
    ← eLocalConn_inter_ground, contract_ground]
  convert rfl using 2 <;> tauto_set

lemma eLocalConn_le_eLocalConn_project_add_left (M : Matroid α) (X Y C : Set α) :
    M.eLocalConn X Y ≤ (M.project C).eLocalConn X Y + M.eLocalConn X C := by
  have hle :=
    (M.multiConn_project_add_tsum_eLocalConn_ne_eq (fun b ↦ bif b then X else Y) C false).symm.le
  grw [← le_self_add] at hle
  grw [eLocalConn, eLocalConn, hle, add_le_add_left]
  have hrw : {i : Bool | i ≠ false} = {true} := by ext; simp
  rw [tsum_congr_set_coe (f := fun x ↦ M.eLocalConn (bif x then X else Y) C) hrw,
    tsum_singleton (f := fun x ↦ M.eLocalConn (bif x then X else Y) C)]
  simp

lemma eLocalConn_le_eLocalConn_project_add_right (M : Matroid α) (X Y C : Set α) :
    M.eLocalConn X Y ≤ (M.project C).eLocalConn X Y + M.eLocalConn Y C := by
  grw [eLocalConn_comm, M.eLocalConn_le_eLocalConn_project_add_left _ _ C, eLocalConn_comm]

lemma eLocalConn_contract_le_add (M : Matroid α) (X Y C : Set α) :
    (M ／ C).eLocalConn X Y ≤ M.eLocalConn X Y + M.eRk C := by
  grw [eLocalConn_eq_multiConn, ← multiConn_project_eq_multiConn_contract,
    multiConn_project_le_multiConn_add, eLocalConn_eq_multiConn]

lemma eLocalConn_project_le_add (M : Matroid α) (X Y C : Set α) :
    (M.project C).eLocalConn X Y ≤ M.eLocalConn X Y + M.eRk C := by
  grw [eLocalConn_project_eq_eLocalConn_contract, eLocalConn_contract_le_add]

-- lemma eLocalConn_le_eLocalConn_project_add (M : Matroid α) (X Y C : Set α) :
--     M.eLocalConn X Y ≤ (M.project C).eLocalConn X Y + M.eRk C := by
--   rw [eLocalConn_eq_multiConn, eLocalConn_eq_multiConn]
--   have := M.multiConn_le_

lemma eConn_delete_eq {X D : Set α} (hDX : D ⊆ X) (hX : X ⊆ M.closure (X \ D)) :
    (M ＼ D).eConn (X \ D) = M.eConn X := by
  have hXE : X ⊆ M.E := hX.trans <| closure_subset_ground ..
  obtain ⟨I, hI⟩ := (M ＼ D).exists_isBasis (X \ D) (diff_subset_diff_left hXE)
  obtain ⟨J, hJ⟩ := (M ＼ D).exists_isBasis ((M ＼ D).E \ (X \ D)) diff_subset
  rw [hI.eConn_eq hJ, nullity_delete]
  · rw [delete_isBasis_iff, delete_ground, diff_diff, union_diff_cancel hDX] at hJ
    rw [delete_isBasis_iff] at hI
    rw [(hI.1.isBasis_closure_right.isBasis_subset (hI.1.subset.trans diff_subset) hX).eConn_eq
      hJ.1]
  rw [disjoint_union_left]
  exact ⟨(subset_diff.1 hI.subset).2, (subset_diff.1 (hJ.subset.trans diff_subset)).2⟩

lemma IsBasis'.eConn_delete_diff_eq (hIX : M.IsBasis' I X) : (M ＼ (X \ I)).eConn I = M.eConn X := by
  wlog hX : X ⊆ M.E generalizing X with aux
  · rw [← M.eConn_inter_ground, ← aux hIX.isBasis_inter_ground.isBasis' inter_subset_right,
      ← delete_inter_ground_eq, ← inter_diff_right_comm]
  rw [← M.eConn_delete_eq (show X \ I ⊆ X from diff_subset), diff_diff_cancel_left hIX.subset]
  rw [diff_diff_cancel_left hIX.subset]
  exact hIX.isBasis.subset_closure

lemma IsBasis.eConn_delete_diff_eq (hIX : M.IsBasis I X) : (M ＼ (X \ I)).eConn I = M.eConn X :=
  hIX.isBasis'.eConn_delete_diff_eq

lemma eConn_restrict_le (M : Matroid α) (X R : Set α) : (M ↾ R).eConn X ≤ M.eConn X := by
  rw [eConn_eq_eLocalConn, eLocalConn_restrict_eq, eConn_eq_eLocalConn, restrict_ground_eq,
    ← eLocalConn_inter_ground_right]
  exact M.eLocalConn_mono inter_subset_left (by tauto_set)

lemma eConn_delete_le (M : Matroid α) (X D : Set α) : (M ＼ D).eConn X ≤ M.eConn X := by
  rw [delete_eq_restrict]
  apply eConn_restrict_le

lemma eConn_contract_le (M : Matroid α) (X C : Set α) : (M ／ C).eConn X ≤ M.eConn X := by
  rw [← eConn_dual, dual_contract, ← M.eConn_dual]
  apply eConn_delete_le

lemma IsMinor.eConn_le {N : Matroid α} (hNM : N ≤m M) (X : Set α) : N.eConn X ≤ M.eConn X := by
  obtain ⟨C, D, -, -, -, rfl⟩ := hNM
  exact ((M ／ C).eConn_delete_le X D).trans <| M.eConn_contract_le X C

lemma eConn_le_eConn_contract_add_eLocalConn (M : Matroid α) (X C : Set α) :
    M.eConn X ≤ (M ／ C).eConn X + M.eLocalConn X C := by
  wlog hC : C ⊆ M.E generalizing C with aux
  · grw [← contract_inter_ground_eq, ← eLocalConn_inter_ground_right, aux _ inter_subset_right]
  grw [eConn, eConn, ← eLocalConn_project_eq_eLocalConn_contract,
    M.eLocalConn_le_eLocalConn_project_add_left X (M.E \ X) C, add_le_add_right,
    contract_ground, ← eLocalConn_closure_right (Y := (_ \ _) \ _),
    project_closure_eq_project_closure_union, diff_diff_comm, diff_union_self,
    ← project_closure_eq_project_closure_union, eLocalConn_closure_right]
  rfl

lemma eConn_le_eConn_contract_add_eRk (M : Matroid α) (X C : Set α) :
    M.eConn X ≤ (M ／ C).eConn X + M.eRk C := by
  grw [M.eConn_le_eConn_contract_add_eLocalConn X C, eLocalConn_le_eRk_right]

lemma eConn_le_eConn_contract_add_encard (M : Matroid α) (X C : Set α) :
    M.eConn X ≤ (M ／ C).eConn X + C.encard := by
  grw [eConn_le_eConn_contract_add_eRk _ X C, eRk_le_encard]

lemma eConn_le_eConn_delete_add_encard (M : Matroid α) (X D : Set α) :
    M.eConn X ≤ (M ＼ D).eConn X + D.encard := by
  grw [← eConn_dual, ← (M ＼ D).eConn_dual, dual_delete, eConn_le_eConn_contract_add_encard]

/-- Contracting a subset of `Y` that is skew to `X` doesn't change the local connectivity
between `X` and `Y`. -/
lemma eLocalConn_contract_right_skew_left' {C Y : Set α} (hXC : M.Skew X C) (hCY : C ⊆ Y) :
    (M ／ C).eLocalConn X (Y \ C) = M.eLocalConn X Y := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  have hI' : (M ／ C).IsBasis' I X := by
    have hI' := hI.isBase_restrict.isBasis_ground.isBasis'
    rwa [← hXC.symm.contract_restrict_eq, restrict_ground_eq, isBasis'_restrict_iff, inter_self,
      and_iff_left hI.subset] at hI'
  rw [hI.eLocalConn_eq_nullity_project_right, hI'.eLocalConn_eq_nullity_project_right,
    nullity_project_eq_nullity_contract, contract_contract, union_diff_cancel hCY,
    nullity_project_eq_nullity_contract]

lemma eLocalConn_contract_skew_union {C : Set α} (h : M.Skew (X ∪ Y) C) :
    (M ／ C).eLocalConn X Y = M.eLocalConn X Y := by
  rw [← (M ／ C).eLocalConn_restrict_of_subset subset_union_left subset_union_right,
    h.symm.contract_restrict_eq,
    eLocalConn_restrict_of_subset _ subset_union_left subset_union_right]

/-- Probably true for `eConn` as well. Generalizes submodularity of `conn`.  -/
theorem conn_inter_add_conn_union_le_conn_contract_add_conn_delete_add_conn
    (M : Matroid α) [M.RankFinite] {C D X : Set α} (hC : Disjoint C X) (hXD : Disjoint D X) :
    M.conn (C ∩ D) + M.conn (X ∪ C ∪ D) ≤ (M ／ X).conn C + (M ＼ X).conn D + M.conn X := by
  have hsm1 := M.rk_submod (M.E \ C) (M.E \ (X ∪ D))
  have hsm2 := M.rk_submod (C ∪ X) D
  zify at *
  simp only [intCast_conn_eq, contract_rk_cast_int_eq, contract_ground, contract_rank_cast_int_eq,
    delete_ground]
  rw [diff_diff_comm, diff_union_self, ← M.rk_inter_ground (M.E \ C ∪ X), union_inter_distrib_right,
    inter_eq_self_of_subset_left diff_subset,
    union_eq_self_of_subset_right (t := X ∩ M.E) (by tauto_set),
    diff_diff, delete_rk_eq_of_disjoint M hXD, delete_rk_eq_of_disjoint _ (by tauto_set),
    ← (M ＼ X).rk_ground, delete_ground, delete_rk_eq_of_disjoint _ disjoint_sdiff_left]
  rw [diff_inter_diff, union_comm, union_right_comm, ← diff_inter, inter_union_distrib_left,
    hC.inter_eq, empty_union] at hsm1
  rw [union_inter_distrib_right, hXD.symm.inter_eq, union_empty, union_right_comm, union_comm,
    ← union_assoc] at hsm2
  linarith

theorem bixbyCoullard_elem [M.RankFinite] {e : α} (C D : Set α) (heC : e ∉ C) (heD : e ∉ D) :
    M.conn (C ∩ D) + M.conn (insert e (C ∪ D)) ≤ (M ／ {e}).conn C + (M ＼ {e}).conn D + 1 := by
  grw [← singleton_union, ← union_assoc,
    M.conn_inter_add_conn_union_le_conn_contract_add_conn_delete_add_conn (by simpa) (by simpa),
    add_le_add_iff_left, conn_le_ncard _ (by simp), ncard_singleton]

end Pair

section Multi


lemma Indep.nullity_union_eq {I X : Set α} (hI : M.Indep I) (hdj : Disjoint I X) :
    M.nullity (I ∪ X) = M.nullity X + M.eLocalConn I X := by
  rw [← hI.nullity_project_of_disjoint hdj, project_nullity_eq_nullity_add_eLocalConn,
    eLocalConn_comm]

  -- rw [hI.project_eq_project, hJ.nullity_eq]
  -- obtain ⟨K, hK, hJK⟩ := hJ.indep.of_project.subset_isBasis'_of_subset hJ.subset
  -- rw [hI.indep.project_isBasis'_iff] at hJ
  -- have hb : M.IsBasis' (I ∪ J) (K ∪ I) := by
  --   -- apply Indep.isBais
  -- rw [hK.eLocalConn_eq hI, hK.nullity_eq, ← diff_union_diff_cancel hK.subset hJK,
  --   encard_union_eq (by tauto_set)]


-- lemma multiConn_add_tsum_eLocalConn_eq' {ι : Type*} (M : Matroid α) (X : ι → Set α) (a : ι) :
--     M.multiConn X + ∑' i : {i // i ≠ a}, M.eLocalConn (X i) C =
--     (M.project C).multiConn X + (M.project (X a)).eLocalConn (⋃ i : {i // i ≠ a}, X i) C := by
--   have hC : M.Indep C := sorry
--   choose I hI using fun i ↦ (M.project C).exists_isBasis' (X i)
--   choose J hJ using fun i ↦ (hI i).indep.of_project.subset_isBasis'_of_subset ((hI i).subset)
--   rw [forall_and] at hJ
--   rw [multiConn_eq]


end Multi

section Connectedness

lemma ConnectedTo.delete_or_contract (hM : M.ConnectedTo x y) (hxe : x ≠ e) (hye : y ≠ e) :
    (M ＼ {e}).ConnectedTo x y ∨ (M ／ {e}).ConnectedTo x y := by
  obtain rfl | hne := eq_or_ne x y
  · simp  [hxe, hM.mem_ground_left]
  suffices (∀ C, M.IsCircuit C → e ∉ C → x ∈ C → y ∉ C) →
    ∃ C, (M ／ {e}).IsCircuit C ∧ x ∈ C ∧ y ∈ C by
    simpa [ConnectedTo, hne, or_iff_not_imp_left]
  intro h
  obtain ⟨C, hC, hxC, hyC⟩ := hM.exists_isCircuit_of_ne hne
  have heC : e ∈ C := by
    contrapose hyC
    exact h C hC hyC hxC
  refine ⟨C \ {e}, ?_, by simpa [hxe], by simpa [hye]⟩
  exact hC.contractElem_isCircuit (nontrivial_of_mem_mem_ne hxC hyC hne) heC

theorem Connected.delete_or_contract (hM : M.Connected) (hnt : M.E.Nontrivial) (e : α) :
    (M ＼ {e}).Connected ∨ (M ／ {e}).Connected := by

  simp only [connected_iff, ← ground_nonempty_iff, delete_ground, Set.mem_diff,
    Set.mem_singleton_iff, and_imp, contract_ground, or_iff_not_imp_left, not_forall,
    exists_and_left, exists_prop, true_and, show (M.E \ { e }).Nonempty from hnt.exists_ne e,
    forall_exists_index, and_imp]

  intro f g hge hgE hfe hfE hnc x y hx hxe hy hye

  have hcon := ((hM.connectedTo f g).delete_or_contract hfe hge).resolve_left hnc

  have h' : ∀ z ∈ M.E, z ≠ e → (M ／ {e}).ConnectedTo z f ∨ (M ／ {e}).ConnectedTo z g := by
    refine fun z hz hze ↦ ?_
    contrapose! hnc
    have hzf := ((hM.connectedTo z f).delete_or_contract hze hfe).resolve_right hnc.1
    have hzg := ((hM.connectedTo z g).delete_or_contract hze hge).resolve_right hnc.2
    exact hzf.symm.trans hzg

  have h'' : ∀ z ∈ M.E, z ≠ e → (M ／ {e}).ConnectedTo z f :=
    fun z hz hze ↦ (h' z hz hze).elim id fun hzg ↦ hzg.trans hcon.symm

  exact (h'' x hx hxe).trans (h'' y hy hye).symm

end Connectedness

section Extension

variable {ι : Type*}

lemma ModularCut.multiconn_add_eq_multiConn_projectBy_add (U : M.ModularCut)
    (X : ι → Set α) [DecidablePred (· ∈ U)] (hU : U ≠ ⊤) :
    M.multiConn X + (if M.closure (⋃ i, X i) ∈ U then 1 else 0) =
        (M.projectBy U).multiConn X + {a | M.closure (X a) ∈ U}.encard := by
  classical
  wlog hXE : ∀ i, X i ⊆ M.E generalizing X with aux
  · convert aux (fun i ↦ X i ∩ M.E) (fun i ↦ inter_subset_right) using 2 with i
    · rw [multiConn_inter_ground]
    · simp [← iUnion_inter]
    · exact multiConn_inter_ground_congr <| by simp [inter_assoc]
    simp
  wlog h : ∃ e, e ∉ M.E generalizing α M X U with aux
  · have ho := Option.some_injective α
    specialize aux (U.map _ ho.injOn) (by simpa) (fun i ↦ .some '' X i) (fun i ↦ image_mono (hXE i))
      ⟨none, by simp⟩
    rw [multiConn_map_image _ _ _ (by simpa), U.projectBy_map, multiConn_map_image _ _ _ (by simpa),
      ← image_iUnion] at aux
    simp_rw [map_closure_eq, preimage_image_eq _ ho,
      U.image_mem_map_iff _ _ (closure_subset_ground ..)] at aux
    assumption
  obtain ⟨e, he⟩ := h
  have heX : e ∉ ⋃ i, X i := by simpa using fun i ↦ notMem_subset (hXE i) he
  have heX' (i) : e ∉ X i := by simpa using notMem_subset (hXE i) he
  nth_rw 1 [← U.extendBy_contractElem he,  ← U.extendBy_deleteElem he,
    multiConn_delete_of_disjoint _ (fun i ↦ disjoint_singleton_right.2 (notMem_subset (hXE i) he)),
    ← multiConn_project_eq_multiConn_contract, ENat.encard_eq_tsum_ite, eq_comm]
  convert (M.extendBy e U).multiConn_project_add_tsum_eLocalConn_eq X {e} with i
  · rw [eLocalConn_comm, IsNonloop.eLocalConn_eq_ite (by simpa), mem_closure_extendBy_iff _ he,
      or_iff_right (heX' i)]
    simp
  rw [eLocalConn_comm, IsNonloop.eLocalConn_eq_ite (by simpa), mem_closure_extendBy_iff _ he,
    or_iff_right heX]
  simp

/-- The formula relating the dual connectivity and the dual connectivity for the projection
by a modular cut. -/
lemma ModularCut.multiconn_dual_add_eq_multiConn_projectBy_dual_add (U : M.ModularCut)
    (X : ι → Set α) [DecidablePred (· ∈ U)] (hU : U ≠ ⊥) :
    M✶.multiConn X + {a | M.closure (M.E \ X a) ∉ U}.encard =
        (M.projectBy U)✶.multiConn X + (if M.closure (M.E \ (⋃ i, X i)) ∈ U then 0 else 1) := by
  classical
  wlog hXE : ∀ i, X i ⊆ M.E generalizing X with aux
  · convert aux (fun i ↦ X i ∩ M.E) (fun i ↦ inter_subset_right) using 2 with i
    · rw [← M.dual_ground, multiConn_inter_ground]
    · simp
    · exact multiConn_inter_ground_congr <| by simp [inter_assoc]
    simp [← iUnion_inter]
  wlog h : ∃ e, e ∉ M.E generalizing α M X U with aux
  · have ho := Option.some_injective α
    specialize aux (U.map _ ho.injOn) (by simpa) (fun i ↦ .some '' X i) (fun i ↦ image_mono (hXE i))
      ⟨none, by simp⟩
    rw [map_dual, multiConn_map_image _ _ _ (by simpa), U.projectBy_map, map_ground,
      map_dual, map_closure_eq, multiConn_map_image _ _ _ (by simpa)] at aux
    simp_rw [← image_iUnion, ← image_diff ho, map_closure_eq, preimage_image_eq _ ho,
      U.image_mem_map_iff _ _  (closure_subset_ground ..)] at aux
    exact aux
  obtain ⟨e, he⟩ := h
  nth_rw 1 [← U.extendBy_deleteElem he, ← U.extendBy_contractElem he, dual_delete, dual_contract,
    multiConn_delete_of_disjoint _ (fun i ↦ disjoint_singleton_right.2 (notMem_subset (hXE i) he)),
    ← multiConn_project_eq_multiConn_contract, eq_comm, ← ite_not]
  simp_rw [← U.mem_closure_extendBy_dual_iff he (hXE _),
      ← U.mem_closure_extendBy_dual_iff he (iUnion_subset hXE), eq_comm (a := _ + ite ..),
      ENat.encard_eq_tsum_ite, mem_setOf_eq]
  have hni : (M.extendBy e U)✶.Indep {e} := by
    rwa [indep_singleton, U.extendBy_isNonloop_dual_iff he]
  convert (M.extendBy e U)✶.multiConn_project_add_tsum_eLocalConn_eq (C := {e}) (X := X) with i <;>
  rw [eLocalConn_comm, IsNonloop.eLocalConn_eq_ite (by simpa using hni)]

lemma ModularCut.multiConn_dual_le_multiConn_projectBy_dual_add_one (U : M.ModularCut)
    (X : ι → Set α) : M✶.multiConn X ≤ (M.projectBy U)✶.multiConn X + 1 := by
  classical
  obtain rfl | hne := eq_or_ne U ⊥
  · simp
  have h_le := (U.multiconn_dual_add_eq_multiConn_projectBy_dual_add X hne).le
  grw [← le_self_add] at h_le
  grw [h_le, add_le_add_left]
  split_ifs <;> simp

lemma ModularCut.multiConn_dual_eq_multiConn_projectBy_dual_add_one_iff [Nonempty ι]
    (U : M.ModularCut) (X : ι → Set α) (hX : M✶.multiConn X ≠ ⊤) :
    M✶.multiConn X = (M.projectBy U)✶.multiConn X + 1 ↔
      M.closure (M.E \ ⋃ i, X i) ∉ U ∧ ∀ a, M.closure (M.E \ X a) ∈ U := by
  classical
  obtain rfl | hne := eq_or_ne U ⊥
  · simpa [eq_comm (a := M✶.multiConn X)] using hX.symm
  have h_eq := U.multiconn_dual_add_eq_multiConn_projectBy_dual_add X hne
  split_ifs at h_eq with h
  · simp only [add_zero] at h_eq
    rw [← h_eq, add_assoc, eq_comm]
    simpa [h]
  rw [← h_eq, eq_comm]
  simp [hX, h, eq_empty_iff_forall_notMem]

lemma ModularCut.multiConn_dual_eq_multiConn_projectBy_dual_add_one_iff' [Nonempty ι]
    (U : M.ModularCut) (X : ι → Set α) : M✶.multiConn X = (M.projectBy U)✶.multiConn X + 1 ↔
      (M✶.multiConn X = ⊤) ∨ (M.closure (M.E \ ⋃ i, X i) ∉ U ∧ ∀ a, M.closure (M.E \ X a) ∈ U) := by
  obtain htop | hnot := eq_or_ne (M✶.multiConn X) ⊤
  · simp only [htop, true_or, iff_true]
    grw [eq_comm, ← top_le_iff, ← htop]
    apply U.multiConn_dual_le_multiConn_projectBy_dual_add_one
  rw [U.multiConn_dual_eq_multiConn_projectBy_dual_add_one_iff _ hnot, or_iff_right hnot]

end Extension

section Submod

-- lemma IsBase.aux {B : Set α} (hB : M.IsBase B) (X : Set α) :
--     ∃ I ⊆ B, I.encard ≤ M.eConn X ∧ ∀ J ⊆ B \ I, (M ／ J).eConn X = M.eConn X := by
--   sorry

-- lemma aux_subset (M : Matroid α) (X : Set α) (k : ℕ∞) (hk : k ≤ M.eConn X) :
--     ∃ N : Matroid α, N ≤ M ∧ N.eConn X = k := sorry

-- lemma foo (M : Matroid α) (X Y : Set α) :
--     M.eConn (X ∪ Y) + M.eConn (X ∩ Y) ≤ M.eConn X + M.eConn Y := by
--   wlog hu : M.eConn (X ∪ Y) < ⊤ generalizing M with aux
--   · by_contra! hcon
--     simp only [not_lt, top_le_iff] at hu
--     obtain ⟨N, hNM, hconn⟩ := M.aux_subset (X ∪ Y) (M.eConn X + M.eConn Y + 1) (by simp [hu])
--     have hXY : M.eConn X + M.eConn Y < ⊤ := hcon.trans_le le_top
--     specialize aux N
--     grw [← le_self_add, hconn, hNM.eConn_le, hNM.eConn_le, ENat.add_one_le_iff hXY.ne,
--       ENat.add_lt_top] at aux
--     simp [hXY] at aux
--   wlog hi : M.eConn (X ∩ Y) < ⊤ generalizing M with aux
--   · by_contra! hcon
--     simp only [not_lt, top_le_iff] at hi
--     obtain ⟨N, hNM, hconn⟩ := M.aux_subset (X ∩ Y) (M.eConn X + M.eConn Y + 1) (by simp [hi])
--     have hXY : M.eConn X + M.eConn Y < ⊤ := hcon.trans_le le_top
--     specialize aux N ((hNM.eConn_le _).trans_lt hu)
--     grw [← le_add_self, hconn, hNM.eConn_le, hNM.eConn_le, ENat.add_one_le_iff hXY.ne,
--       ENat.add_lt_top] at aux
--     simp [hXY] at aux
--   by_contra! hlt
--   have hX : M.eConn X < ⊤ := by
--     grw [← le_self_add] at hlt
--     exact hlt.trans_le le_top
--   have hY : M.eConn Y < ⊤ := by
--     grw [← le_add_self] at hlt
--     exact hlt.trans_le le_top

--   obtain ⟨B, hB⟩ := M.exists_isBase
--   obtain ⟨IX, hIXB, hIXcard, hIX⟩ := hB.aux X
--   obtain ⟨IY, hIYB, hIYcard, hIY⟩ := hB.aux Y
--   obtain ⟨Ii, hIiB, hIiBcard, hIi⟩ := hB.aux (X ∩ Y)
--   obtain ⟨Iu, hIuB, hIuBcard, hIu⟩ := hB.aux (X ∪ Y)

--   set N := M ／ (B \ (IX ∪ IY ∪ Iu ∪ Ii)) with hN
--   have hbas : N.IsBase (IX ∪ IY ∪ Iu ∪ Ii) := by
--     rw [hN, (hB.indep.subset diff_subset).contract_isBase_iff, union_diff_cancel
--       (by simp [hIXB, hIYB, hIuB, hIiB])]
--     exact ⟨hB, disjoint_sdiff_right⟩

--   have hufin := encard_lt_top_iff.1 <| hIuBcard.trans_lt hu
--   have hifin := encard_lt_top_iff.1 <| hIiBcard.trans_lt hi
--   have hIXfin := encard_lt_top_iff.1 <| hIXcard.trans_lt hX
--   have hIYfin := encard_lt_top_iff.1 <| hIYcard.trans_lt hY
--   have hfin : RankFinite N := hbas.rankFinite_of_finite <| by simp [hIXfin, hIYfin, hifin, hufin]

--   have hcon := N.conn_submod X Y
--   rw [← Nat.cast_le (α := ℕ∞), Nat.cast_add, Nat.cast_add, cast_conn_eq,
--     cast_conn_eq, cast_conn_eq, cast_conn_eq, hN, hIi _ (by tauto_set), hIu _ (by tauto_set),
--     hIX _ (by tauto_set), hIY _ (by tauto_set), add_comm] at hcon
--   exact hlt.not_ge hcon


  -- by_cases hinfu : M.eConn (X ∪ Y) = ⊤
  -- · obtain ⟨N, hNM, hN⟩ := M.aux_subset (X ∪ Y) (M.eConn X + M.eConn Y + 1) (by simp [hinfu])
  --   have hcon : N.eConn X + N.eConn Y < N.eConn (X ∪ Y) := by
  --     grw [hNM.eConn_le, hNM.eConn_le, ← N.eConn_inter_ground, hN, ENat.lt_add_one_iff]
  --     grw [← lt_top_iff_ne_top]
  --     exact hcon.trans_le le_top





end Submod
