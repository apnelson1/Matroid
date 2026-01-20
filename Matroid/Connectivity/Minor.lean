import Matroid.Connectivity.Finitize
import Matroid.Connectivity.Nat
import Matroid.Minor.Order

open Set Function

namespace Matroid

variable {α ι : Type*} {M : Matroid α} {e f x y : α} {C D : Set α}

section Multi

variable {I X : ι → Set α}

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





  -- obtain hι | hι := subsingleton_or_nontrivial ι
  -- · simp [tsub_eq_zero_iff_le]
  -- obtain ⟨I, hI⟩ := M.exists_isBasis' X
  -- have hI' (i : ι) : M.IsBasis' I ((fun (i : ι) ↦ X) i) := hI
  -- rw [multiConn_eq_comap_nullity hI']

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

lemma multiConn_union_eq_multiConn_project_add (M : Matroid α) (X : ι → Set α) (A : Set α) :
    M.multiConn (fun i ↦ X i ∪ A) = (M.project A).multiConn X + (ENat.card ι - 1) * M.eRk A := by
  obtain hι | ⟨⟨i⟩⟩ := isEmpty_or_nonempty ι
  · simp [tsub_eq_zero_iff_le]
  convert Eq.symm <| M.multiConn_project_add_tsum_eLocalConn_ne_eq (fun i ↦ (X i ∪ A)) A i using 1
  · rw [← eLocalConn_closure_right, union_comm, ← project_project,
      project_closure_congr (Y := ∅) (by simp), eLocalConn_closure_right, eLocalConn_empty,
      add_zero]
  rw [tsum_congr (fun _ ↦ M.eLocalConn_comm ..), tsum_congr (fun _ ↦ M.eLocalConn_subset (by simp)),
    ENat.tsum_const, ENat.card_coe_setOf_ne, mul_comm]
  convert rfl using 2
  apply multiConn_closure_congr
  simp [union_assoc]

lemma multiConn_project_add_disjoint (M : Matroid α) {C : Set α} (hCX : C ⊆ ⋃ i, X i)
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

lemma multiConn_project_add_of_subset (M : Matroid α) {C : ι → Set α} (hCX : ∀ i, C i ⊆ X i)
    (hdj : Pairwise (Disjoint on C)) (hi : M.Indep (⋃ i, C i)) : (M.project (⋃ i, C i)).multiConn X
    + ∑' i, (M.project (C i)).eLocalConn (X i) (⋃ i, C i) = M.multiConn X := by
  have hrw (j) : (·, j) '' X j ∩ ⋃ i, (·, i) '' (C i) = (·, j) '' C j := by aesop
  convert (M.comap Prod.fst).multiConn_project_add_disjoint (C := ⋃ i, (·, i) '' (C i))
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
  rw [← M.multiConn_project_add_of_subset (C := fun i ↦ I ∩ inds ⁻¹' {i}) (X := X) ?_]
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
  have hle := (M.multiConn_project_add_tsum_eLocalConn_ne_eq X C a).symm.le
  grw [← le_self_add] at hle
  grw [hle, add_le_add_right]
  grw [ENat.tsum_le_tsum (g := fun i ↦ M.eLocalConn (⋃ j, X j) C)
    fun i ↦ eLocalConn_mono_left _ (by simp [subset_iUnion]) _, ENat.tsum_const,
    ENat.card_coe_setOf_ne, mul_comm]

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
  grw [eLocalConn, eLocalConn, hle, add_le_add_right]
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

lemma eConn_delete_eq_of_subset_closure (hDcl : D ⊆ M.closure X) (hDX : Disjoint X D) :
    (M ＼ D).eConn X = M.eConn (X ∪ D) := by
  wlog hXE : X ⊆ M.E generalizing X with aux
  · specialize aux (X := X ∩ M.E) (by simpa) (by grind) inter_subset_right
    rw [← eConn_inter_ground, ← M.eConn_inter_ground, delete_ground] at aux ⊢
    convert aux using 2 <;> grind
  rw [← M.eConn_delete_eq (X := X ∪ D) subset_union_right, union_diff_right, hDX.sdiff_eq_left]
  grw [union_diff_right, hDX.sdiff_eq_left, union_subset_iff, and_iff_left hDcl,
    ← M.subset_closure X]

lemma IsBasis'.eConn_delete_diff_eq (hIX : M.IsBasis' I X) : (M ＼ (X \ I)).eConn I = M.eConn X := by
  wlog hX : X ⊆ M.E generalizing X with aux
  · rw [← M.eConn_inter_ground, ← aux hIX.isBasis_inter_ground.isBasis' inter_subset_right,
      ← delete_inter_ground_eq, ← inter_diff_right_comm]
  rw [← M.eConn_delete_eq (show X \ I ⊆ X from diff_subset), diff_diff_cancel_left hIX.subset]
  rw [diff_diff_cancel_left hIX.subset]
  exact hIX.isBasis.subset_closure

lemma IsBasis.eConn_delete_diff_eq (hIX : M.IsBasis I X) : (M ＼ (X \ I)).eConn I = M.eConn X :=
  hIX.isBasis'.eConn_delete_diff_eq

lemma eConn_contract_diff_eq_eConn_project (M : Matroid α) (C X : Set α) :
    (M ／ C).eConn (X \ C) = (M.project C).eConn X := by
  rw [eConn_eq_eLocalConn, contract_ground, diff_diff_right, disjoint_sdiff_left.inter_eq,
    union_empty, diff_diff_comm, ← eLocalConn_project_eq_eLocalConn_contract_diff,
    eConn_eq_eLocalConn, project_ground]

lemma eConn_contract_eq_eConn_project (M : Matroid α) (X C : Set α) :
    (M ／ C).eConn X = (M.project C).eConn X := by
  rw [← eConn_contract_diff_eq_eConn_project, ← eConn_inter_ground, eq_comm, ← eConn_inter_ground,
    contract_ground, eq_comm, diff_inter_diff_right, inter_diff_assoc]

lemma eConn_contract_eq_eConn_contract_diff (M : Matroid α) (X C : Set α) :
    (M ／ C).eConn X = (M ／ C).eConn (X \ C) := by
  rw [eConn_contract_diff_eq_eConn_project, eConn_contract_eq_eConn_project]

lemma eConn_contract_diff_le (M : Matroid α) (X C : Set α) : (M ／ C).eConn (X \ C) ≤ M.eConn X := by
  grw [← eConn_contract_eq_eConn_contract_diff, eConn_contract_le]

lemma eConn_delete_diff_le (M : Matroid α) (X D : Set α) : (M ＼ D).eConn (X \ D) ≤ M.eConn X := by
  grw [← eConn_dual, dual_delete, eConn_contract_diff_le, eConn_dual]

lemma eConn_contract_union_eq_eConn (M : Matroid α) (X C : Set α) :
    (M ／ C).eConn (X ∪ C) = (M ／ C).eConn X := by
  rw [eConn_contract_eq_eConn_contract_diff, union_diff_right,
    ← eConn_contract_eq_eConn_contract_diff]

lemma eConn_delete_eq_eConn_delete_diff (M : Matroid α) (X D : Set α) :
    (M ＼ D).eConn X = (M ＼ D).eConn (X \ D) := by
  rw [← eConn_dual, dual_delete, eConn_contract_eq_eConn_contract_diff, ← dual_delete, eConn_dual]

lemma eConn_eq_eConn_contract_subset_add (M : Matroid α) (hCX : C ⊆ X) :
    M.eConn X = (M ／ C).eConn (X \ C) + M.eLocalConn (M.E \ X) C := by
  rw [eConn_contract_diff_eq_eConn_project]
  wlog hC : M.Indep C generalizing C with aux
  · obtain ⟨I, hI⟩ := M.exists_isBasis' C
    rw [hI.project_eq_project,
      ← M.eLocalConn_closure_right, ← M.eLocalConn_closure_right (X := M.E \ X),
      ← hI.closure_eq_closure, eLocalConn_closure_right, eLocalConn_closure_right,
      aux (hI.subset.trans hCX) hI.indep]
  have hrw := M.multiConn_project_add_disjoint (X := fun b ↦ bif b then X else M.E \ X)
    (by simp [hC.subset_ground.trans subset_union_right])
    (by simp [pairwise_disjoint_on_bool, disjoint_sdiff_right]) hC
  grw [eq_comm, eConn_eq_eLocalConn, project_ground, eLocalConn_eq_multiConn,
    eConn_eq_eLocalConn, eLocalConn_eq_multiConn (Y := M.E \ X), ← hrw]
  simp only [tsum_bool, cond_false, (disjoint_sdiff_left.mono_right hCX).inter_eq,
    project_empty, cond_true, inter_eq_self_of_subset_right hCX]
  rw [← (M.project C).eLocalConn_closure_right,
    show (M.project C).closure C = (M.project C).closure ∅ by simp, eLocalConn_closure_right,
    eLocalConn_empty, add_zero]

lemma eConn_eq_eConn_contract_disjoint_add (M : Matroid α) (hdj : Disjoint X C) :
    M.eConn X = (M ／ C).eConn X + M.eLocalConn X C := by
  wlog hC : C ⊆ M.E generalizing C with aux
  · rw [← contract_inter_ground_eq, ← eLocalConn_inter_ground_right,
      ← aux (hdj.mono_right inter_subset_left) inter_subset_right]
  wlog hX : X ⊆ M.E generalizing X with aux
  · rw [← eConn_inter_ground, aux (hdj.mono_left inter_subset_left) inter_subset_right,
      eLocalConn_inter_ground_left, ← eConn_inter_ground, eq_comm, ← eConn_inter_ground,
      contract_ground, inter_assoc, inter_eq_self_of_subset_right diff_subset]
  rw [← M.eConn_compl X, eConn_eq_eConn_contract_subset_add _ (subset_diff.2 ⟨hC, hdj.symm⟩),
    diff_diff_cancel_left hX, diff_diff_comm, ← contract_ground, eConn_compl]

lemma Skew.eConn_contract_diff_eq_self (h : M.Skew X C) : (M ／ C).eConn (X \ C) = M.eConn X := by
  nth_rw 1 [← inter_union_diff C X, eConn_contract_eq_eConn_project, ← project_closure_eq,
    union_comm, closure_union_eq_closure_of_subset_loops _ _ h.symm.inter_subset_loops,
    project_closure_eq, ← eConn_contract_eq_eConn_project, M.eConn_eq_eConn_contract_disjoint_add
      (show Disjoint X (C \ X) from disjoint_sdiff_right), (h.mono_right diff_subset).eLocalConn,
      eConn_contract_eq_eConn_project, eConn_contract_eq_eConn_project,
      add_zero, ← eConn_union_eq_of_subset_loops (Y := X ∩ C), diff_union_inter]
  grw [h.inter_subset_loops]
  simp

lemma Skew.eConn_contract_diff_eq_self_of_skew (h : M.Skew X (C \ X))
    (h' : M.Skew (M.E \ X) (C ∩ X)) : (M ／ C).eConn (X \ C) = M.eConn X := by
  rw [M.eConn_eq_eConn_contract_disjoint_add (C := C \ X) disjoint_sdiff_right,
    h.eLocalConn, add_zero, (M ／ (C \ X)).eConn_eq_eConn_contract_subset_add (C := C ∩ X)
    inter_subset_right, contract_contract, diff_union_inter, diff_inter_self_eq_diff,
    contract_ground, diff_diff, diff_union_self, Skew.eLocalConn, add_zero]
  rw [contract_skew_iff (by grind) (by grind) h.subset_ground_right, inter_union_diff,
    Disjoint.inter_eq (by grind), and_iff_left (empty_subset ..)]
  convert h'.isModularPair_union_union_of_subset (Z := C \ X) (by grind [h.subset_ground_right])
    using 1 <;> grind

lemma eConn_contract_diff_eq_self_iff_skew_skew (hconn : (M ／ C).eConn (X \ C) ≠ ⊤)
    (hX : X ⊆ M.E := by aesop_mat) (hC : C ⊆ M.E := by aesop_mat) :
    (M ／ C).eConn (X \ C) = M.eConn X ↔ M.Skew X (C \ X) ∧ M.Skew (M.E \ X) (C ∩ X) := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ h.1.eConn_contract_diff_eq_self_of_skew h.2⟩
  · rw [M.eConn_eq_eConn_contract_disjoint_add (C := C \ X) disjoint_sdiff_right] at h
    replace h := h.symm.le
    grw [← eConn_contract_le (C := C ∩ X), contract_contract, diff_union_inter,
      eConn_contract_eq_eConn_contract_diff, ENat.add_le_left_iff, or_iff_right hconn] at h
    rwa [← eLocalConn_eq_zero]
  rw [M.eConn_eq_eConn_contract_subset_add (C := C ∩ X) inter_subset_right] at h
  replace h := h.symm.le
  grw [← (eConn_contract_le (C := C \ X)), contract_contract, inter_union_diff,
    diff_inter_self_eq_diff, ENat.add_le_left_iff, or_iff_right hconn] at h
  rwa [← eLocalConn_eq_zero]

/-- A version of `eConn_contract_diff_eq_self_iff_skew_skew` with the simpler but weaker assumption
that `M.eConn X ≠ ⊤`. -/
lemma eConn_contract_diff_eq_self_iff_skew_skew' (hconn : M.eConn X ≠ ⊤)
    (hX : X ⊆ M.E := by aesop_mat) (hC : C ⊆ M.E := by aesop_mat) :
    (M ／ C).eConn (X \ C) = M.eConn X ↔ M.Skew X (C \ X) ∧ M.Skew (M.E \ X) (C ∩ X) := by
  rw [eConn_contract_diff_eq_self_iff_skew_skew]
  grw [← lt_top_iff_ne_top, eConn_contract_diff_le, lt_top_iff_ne_top]
  assumption

lemma eConn_eq_eConn_delete_subset_add (M : Matroid α) (hDX : D ⊆ X) :
    M.eConn X = (M ＼ D).eConn (X \ D) + M✶.eLocalConn (M.E \ X) D := by
  simp [← M.eConn_dual, M✶.eConn_eq_eConn_contract_subset_add hDX, ← (M✶ ／ D).eConn_dual]

lemma eConn_eq_eConn_delete_disjoint_add (M : Matroid α) (hDX : Disjoint X D) :
    M.eConn X = (M ＼ D).eConn X + M✶.eLocalConn X D := by
  simp [← M.eConn_dual, M✶.eConn_eq_eConn_contract_disjoint_add hDX, ← (M✶ ／ D).eConn_dual]

lemma Coindep.delete_eConn_eq_union_iff' (hD : M.Coindep D) (hDX : Disjoint X D)
    (hX : (M ＼ D).eConn X ≠ ⊤) : (M ＼ D).eConn X = M.eConn (X ∪ D) ↔ D ⊆ M.closure X := by
  wlog hXE : X ⊆ M.E generalizing X with aux
  · rw [← closure_inter_ground, ← aux (by grind) _ inter_subset_right,
      ← eConn_inter_ground, ← (M ＼ D).eConn_inter_ground (X ∩ M.E), ← M.eConn_inter_ground,
      ← M.eConn_inter_ground (X ∩ M.E ∪ D), delete_ground]
    · convert Iff.rfl using 3 <;> grind
    rw [← eConn_inter_ground, delete_ground] at hX ⊢
    convert hX using 2; grind
  refine ⟨fun h ↦ ?_, fun h ↦ eConn_delete_eq_of_subset_closure h hDX⟩
  grw [M.eConn_eq_eConn_delete_subset_add (X := X ∪ D) subset_union_right, union_diff_right,
    hDX.sdiff_eq_left, eq_comm, ENat.add_eq_left_iff, or_iff_right hX, eLocalConn_eq_zero,
    skew_comm, hD.skew_dual_iff (by grind), union_comm, ← diff_diff,
      diff_diff_cancel_left (union_subset hXE hD.subset_ground),
      union_diff_cancel_right hDX.inter_eq.subset] at h
  exact h

lemma Coindep.delete_eConn_eq_union_iff (hD : M.Coindep D) (hDX : Disjoint X D)
    (hX : M.eConn X ≠ ⊤) : (M ＼ D).eConn X = M.eConn (X ∪ D) ↔ D ⊆ M.closure X := by
  rw [hD.delete_eConn_eq_union_iff' hDX]
  grw [← lt_top_iff_ne_top, eConn_delete_le, lt_top_iff_ne_top]
  assumption

lemma Coindep.delete_eConn_eq_self_iff (hD : M.Coindep D) (hDX : Disjoint X D)
    (hX : M.eConn (X ∪ D) ≠ ⊤) : (M ＼ D).eConn X = M.eConn X ↔ D ⊆ M.closure (M.E \ (X ∪ D)) := by
  rw [← eConn_compl, delete_ground, ← M.eConn_compl, diff_diff_comm]
  have hDE := hD.subset_ground
  nth_rw 2 [show M.E \ X = ((M.E \ X) \ D) ∪ D by grind]
  rw [hD.delete_eConn_eq_union_iff disjoint_sdiff_left, diff_diff]
  rwa [diff_diff, eConn_compl]

lemma eConn_union_eq_eConn_contract_add (M : Matroid α) (hdj : Disjoint X C) :
    M.eConn (X ∪ C) = (M ／ C).eConn X + M.eLocalConn (M.E \ (X ∪ C)) C := by
  rw [M.eConn_eq_eConn_contract_subset_add subset_union_right,
    union_diff_cancel_right hdj.inter_eq.subset]

lemma eConn_le_eConn_contract_add_eLocalConn (M : Matroid α) (X C : Set α) :
    M.eConn X ≤ (M ／ C).eConn X + M.eLocalConn X C := by
  wlog hC : C ⊆ M.E generalizing C with aux
  · grw [← contract_inter_ground_eq, ← eLocalConn_inter_ground_right, aux _ inter_subset_right]
  grw [eConn, eConn, ← eLocalConn_project_eq_eLocalConn_contract, contract_ground,
    M.eLocalConn_le_eLocalConn_project_add_left X (M.E \ X) C, add_le_add_right,
    ← eLocalConn_closure_right (Y := (_ \ _) \ _), project_closure_eq_project_closure_union,
    diff_diff_comm, diff_union_self, ← project_closure_eq_project_closure_union,
    eLocalConn_closure_right]
  rfl

lemma eConn_union_eq_eConn_contract_add_eConn_delete (M : Matroid α) (hXY : Disjoint X Y) :
    M.eConn (X ∪ Y) = (M ／ X).eConn Y + (M ＼ Y).eConn X := by
  rw [eConn_eq_eConn_contract_subset_add _ subset_union_left, (M ＼ Y).eConn_eq_eLocalConn,
    union_diff_cancel_left hXY.inter_eq.subset, eq_comm, delete_ground, diff_diff, union_comm,
    delete_eq_restrict, ← eLocalConn_inter_ground_left, restrict_ground_eq,
    eLocalConn_restrict_of_subset _ (by simp) (diff_subset_diff_right subset_union_right),
    ← inter_diff_assoc, (hXY.mono_left inter_subset_left).sdiff_eq_left,
    eLocalConn_inter_ground_left, eLocalConn_comm]

lemma eConn_insert_le_eConn_contract_add_one (M : Matroid α) (X : Set α) (e : α) :
    M.eConn (insert e X) ≤ (M ／ {e}).eConn X + 1 := by
  grw [eConn_le_eConn_contract_add_eLocalConn (C := {e}), eLocalConn_le_eRk_right,
    eRk_singleton_le, eConn_contract_eq_eConn_contract_diff, insert_diff_of_mem _ (by simp),
      ← eConn_contract_eq_eConn_contract_diff]

lemma eConn_insert_le_eConn_delete_add_one (M : Matroid α) (X : Set α) (e : α) :
    M.eConn (insert e X) ≤ (M ＼ {e}).eConn X + 1 := by
  grw [← eConn_dual, eConn_insert_le_eConn_contract_add_one, ← dual_delete, eConn_dual]

lemma eConn_le_eConn_contract_singleton_add_one (M : Matroid α) (X : Set α) (e : α) :
    M.eConn X ≤ (M ／ {e}).eConn X + 1 := by
  grw [eConn_le_eConn_contract_add_eLocalConn (C := {e}), eLocalConn_le_eRk_right,
    eRk_singleton_le]

lemma eConn_le_eConn_delete_singleton_add_one (M : Matroid α) (X : Set α) (e : α) :
    M.eConn X ≤ (M ＼ {e}).eConn X + 1 := by
  grw [← eConn_dual, eConn_le_eConn_contract_singleton_add_one _ _ e, ← eConn_dual,
    dual_contract_dual]

/-- Note : the lemma below is true with either `C ⊆ X` or `Disjoint C X` as a hypothesis,
but not with both hypotheses removed, even if we insist that `X,C ⊆ M.E`.
A counterexample is the direct sum of two parallel pairs, where `C` is one pair,
and `X` is a transversal of the two. The versions with cardinality and rank are
true unconditionally. -/
lemma eConn_le_eConn_contract_add_eConn_of_subset (M : Matroid α) (hCX : C ⊆ X) :
    M.eConn X ≤ (M ／ C).eConn (X \ C) + M.eConn C := by
  grw [eConn_eq_eConn_contract_subset_add _ hCX, ← (M.delete_isMinor (X \ C)).eConn_le,
    (M ＼ _).eConn_eq_eLocalConn, delete_ground, diff_diff, diff_union_of_subset hCX,
    eLocalConn_comm, eLocalConn_delete_eq_of_disjoint _ disjoint_sdiff_right (by tauto_set)]

lemma eConn_le_eConn_contract_add_eConn_of_disjoint (M : Matroid α) (hdj : Disjoint X C) :
    M.eConn X ≤ (M ／ C).eConn X + M.eConn C := by
  grw [eConn_eq_eConn_contract_disjoint_add _ hdj, M.eConn_eq_eLocalConn, eLocalConn_comm,
  ← eLocalConn_inter_ground_right, eLocalConn_mono_right _ _ (show X ∩ M.E ⊆ M.E \ C by tauto_set)]

lemma eConn_le_eConn_delete_add_eConn_of_subset (M : Matroid α) (hDX : D ⊆ X) :
    M.eConn X ≤ (M ＼ D).eConn (X \ D) + M.eConn D := by
  grw [← dual_contract_dual, eConn_dual, ← M.eConn_dual D,
    ← eConn_le_eConn_contract_add_eConn_of_subset _ hDX, eConn_dual]

lemma eConn_le_eConn_delete_add_eConn_of_disjoint (M : Matroid α) (hdj : Disjoint X D) :
    M.eConn X ≤ (M ＼ D).eConn X + M.eConn D := by
  grw [← dual_contract_dual, eConn_dual, ← M.eConn_dual D,
    ← eConn_le_eConn_contract_add_eConn_of_disjoint _ hdj, eConn_dual]

lemma eConn_le_eConn_contract_add_eRk (M : Matroid α) (X C : Set α) :
    M.eConn X ≤ (M ／ C).eConn X + M.eRk C := by
  grw [M.eConn_le_eConn_contract_add_eLocalConn X C, eLocalConn_le_eRk_right]

lemma eConn_le_eConn_contract_add_encard (M : Matroid α) (X C : Set α) :
    M.eConn X ≤ (M ／ C).eConn X + C.encard := by
  grw [eConn_le_eConn_contract_add_eRk _ X C, eRk_le_encard]

lemma eConn_le_eConn_delete_add_encard (M : Matroid α) (X D : Set α) :
    M.eConn X ≤ (M ＼ D).eConn X + D.encard := by
  grw [← eConn_dual, ← (M ＼ D).eConn_dual, dual_delete, eConn_le_eConn_contract_add_encard]

lemma eConn_delete_le_eConn_contract_add (M : Matroid α) (X Y : Set α) :
    (M ＼ Y).eConn X ≤ (M ／ Y).eConn X + M.eConn Y := by
  grw [← eConn_inter_ground, eConn_delete_le,
    eConn_le_eConn_contract_add_eConn_of_disjoint (C := Y) _ (by rw [delete_ground]; tauto_set),
    ← (M ／ Y).eConn_inter_ground X, delete_ground, contract_ground]

lemma eConn_contract_le_eConn_delete_add (M : Matroid α) (X Y : Set α) :
    (M ／ Y).eConn X ≤ (M ＼ Y).eConn X + M.eConn Y := by
  rw [← dual_delete_dual, ← M.dual_contract_dual, ← M.eConn_dual, eConn_dual, eConn_dual]
  apply eConn_delete_le_eConn_contract_add

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

/-- The right-hand side of the generalized Bixby-Coullard inequality is minor monotone.
Required to reduce the proof to the finite case. -/
private lemma monotone_rhs_aux {P Q X : Set α} :
    Monotone (fun N : Matroid α ↦ (N ／ X).eConn P + (N ＼ X).eConn Q + N.eConn X) := by
  rintro N M (hNM : N ≤m M)
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := hNM.exists_eq_contract_delete_disjoint
  simp only
  have hmin1 : M ／ C ＼ D ／ X ≤m M ／ (X \ D) ＼ (X ∩ D) := by
    rw [contract_delete_contract']
    refine IsMinor.delete_isMinor_delete_of_subset ?_ inter_subset_right ?_
    · exact contract_isMinor_of_subset _ subset_union_right
    simp_rw [contract_ground]
    tauto_set
  have hmin2 : M ／ C ＼ D ＼ X ≤m M ＼ (X \ C) ／ (X ∩ C) := by
    rw [delete_delete, contract_delete_comm']
    refine IsMinor.contract_isMinor_contract_of_subset ?_ inter_subset_right ?_
    · exact (delete_isRestriction_of_subset _ (by tauto_set)).isMinor
    simp_rw [delete_ground]
    tauto_set
  have hmin3 : M ／ C ＼ D ≤m M ／ (X ∩ C) ＼ (X ∩ D) :=
    (contract_isMinor_of_subset _ inter_subset_right).delete_isMinor_delete_of_subset
       inter_subset_right (by simp_rw [contract_ground]; tauto_set)
  grw [hmin1.eConn_le, hmin2.eConn_le, eConn_delete_le_eConn_contract_add,
    contract_contract, diff_union_inter, eConn_contract_le_eConn_delete_add _ _ (X ∩ C),
      delete_delete, diff_union_inter, hmin3.eConn_le, ← add_assoc,
      add_right_comm (c := (M ＼ X).eConn Q), add_assoc, add_assoc]
  convert rfl.le
  nth_rw 1 [← diff_union_inter X D, M.eConn_union_eq_eConn_contract_add_eConn_delete
    disjoint_sdiff_inter]
  convert rfl
  rw [← diff_union_inter (X \ D) C, union_comm,
    eConn_union_eq_eConn_contract_add_eConn_delete _ disjoint_sdiff_inter.symm,
    delete_delete, show (X \ D) ∩ C = X ∩ C by tauto_set,
    show X ∩ D ∪ (X \ D) \ C = X \ C by tauto_set, add_comm, contract_delete_comm _ (by tauto_set),
    ← eConn_inter_ground, eq_comm, ← eConn_inter_ground, contract_ground,
    delete_ground]
  convert rfl using 3
  tauto_set

/-- A three-set generalization of the Bixby-Coullard inequality for `ℕ∞` -/
theorem eConn_inter_add_eConn_union_union_le (M : Matroid α) (hC : Disjoint C X)
    (hD : Disjoint D X) :
    M.eConn (C ∩ D) + M.eConn (X ∪ C ∪ D) ≤ (M ／ X).eConn C + (M ＼ X).eConn D + M.eConn X := by
  by_contra! hlt
  set g := fun (N : Matroid α) ↦ (N ／ X).eConn C + (N ＼ X).eConn D + N.eConn X with hg
  obtain ⟨N, hNM, hNfin, hN⟩ := M.exists_finite_counterexample_of_lt_sum_eConn g
    (monotone_rhs_aux ..) (fun b ↦ bif b then C ∩ D else X ∪ C ∪ D) (by simpa)
  simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
    Finset.sum_insert, cond_true, Finset.sum_singleton, cond_false, g, ← cast_conn_eq,
    ← Nat.cast_add, Nat.cast_lt] at hN
  exact (N.conn_inter_add_conn_union_union_le hC hD).not_gt hN

/-- Connectivity is submodular. -/
lemma eConn_inter_add_eConn_union_le (M : Matroid α) (X Y : Set α) :
    M.eConn (X ∩ Y) + M.eConn (X ∪ Y) ≤ M.eConn X + M.eConn Y := by
  simpa using M.eConn_inter_add_eConn_union_union_le (disjoint_empty X) (disjoint_empty Y)

alias eConn_submod := eConn_inter_add_eConn_union_le

/-- The Bixby-Coullard inequality for `ℕ∞` -/
theorem eConn_inter_add_eConn_insert_union_le (M : Matroid α) (heC : e ∉ C) (heD : e ∉ D) :
    M.eConn (C ∩ D) + M.eConn (insert e (C ∪ D)) ≤ (M ／ {e}).eConn C + (M ＼ {e}).eConn D + 1 := by
  grw [← singleton_union, ← union_assoc, M.eConn_inter_add_eConn_union_union_le (by simpa)
    (by simpa), eConn_le_encard _ {e}, encard_singleton]



end Pair
