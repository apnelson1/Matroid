import Matroid.Connectivity.Local
import Mathlib.Data.Set.Prod

open Set Function

lemma disjoint_map_prod_right {α ι : Type*} {f : ι → Set α} :
    Pairwise (Disjoint on fun i ↦ (·, i) '' f i) := by
  simp +contextual [Pairwise, disjoint_right]

lemma disjoint_map_prod_left {α ι : Type*} {f : ι → Set α} :
    Pairwise (Disjoint on fun i ↦ (i, ·) '' f i) := by
  simp +contextual [Pairwise, disjoint_right]


namespace Matroid

variable {α : Type*} {M : Matroid α} {B B' I I' J J' K : Set α} {ι : Type*} {I X Y : ι → Set α}

/-- An auxiliary version of multi-connectivity used in the real definition.
If the sets are disjoint, then this is equal to `multiConn`, but otherwise it is badly behaved.-/
private noncomputable def multiConnAux (M : Matroid α) (X : ι → Set α) : ℕ∞ :=
  ⨅ (I : {I : ι → Set α // ∀ i, M.IsBasis' (I i) (X i)}), M.nullity (⋃ i, I.1 i)

private lemma multiConnAux_eq_nullity_iUnion (M : Matroid α) (hI : ∀ i, M.IsBasis' (I i) (X i))
    (hdj : Pairwise (Disjoint on X)) : M.multiConnAux X = M.nullity (⋃ i, I i) := by
  have aux (J : ι → Set α) (hJ : ∀ i, M.IsBasis' (J i) (X i)) :
      M.nullity (⋃ i, J i) = M.nullity (⋃ i, I i) := by
    rw [nullity_iUnion_congr (Y := I)
      (hdj.mono fun i j ↦ Disjoint.mono (hJ i).subset (hJ j).subset)
      (hdj.mono fun i j ↦ Disjoint.mono (hI i).subset (hI j).subset)
      (fun i ↦ by rw [(hI i).indep.nullity_eq, (hJ i).indep.nullity_eq])
      (fun i ↦ by rw [(hI i).closure_eq_closure, (hJ i).closure_eq_closure])]
  exact ((iInf_le _ ⟨I, hI⟩).trans (by simp)).antisymm <| by simpa using fun i h ↦ (aux i h).symm.le

/-- The local connectivity of an indexed collection `X : ι → Set α` of sets.
This is defined indirectly using comaps so that it is meaningful even when the `X` are not disjoint.
If they are disjoint, it is equal to `M.nullity (⋃ i, I i)` for any bases `I i` for the `X i`;
see `multiConn_eq_nullity_iUnion`.
If the `X i` are not disjoint, then there is no simple formula in general, but for pairs,
an expression using cardinality is given in `multiConn_cond`. -/
noncomputable def multiConn (M : Matroid α) (X : ι → Set α) : ℕ∞ :=
  (M.comap Prod.fst).multiConnAux fun i ↦ ((· , i) '' (X i ∩ M.E))

lemma multiConn_inter_ground (M : Matroid α) (X : ι → Set α) :
    M.multiConn (fun i ↦ (X i) ∩ M.E) = M.multiConn X := by
  simp_rw [multiConn, inter_assoc, inter_self]

lemma multiConn_eq_comap_nullity (h : ∀ i, M.IsBasis' (I i) (X i)) :
    M.multiConn X = (M.comap Prod.fst).nullity (⋃ i, (·, i) '' I i) := by
  have h' (i) : M.IsBasis' (I i) (X i ∩ M.E) := (h i).isBasis_inter_ground.isBasis'
  rw [multiConn, multiConnAux_eq_nullity_iUnion _
    (fun i ↦ (h' i).comap _) disjoint_map_prod_right]
  exact fun i ↦ RightInverse.rightInvOn (congr_fun rfl) _

lemma multiConn_eq_nullity_iUnion_add_tsum (hI : ∀ i, M.IsBasis' (I i) (X i)) :
    M.multiConn X = M.nullity (⋃ i, I i) + ∑' (e : ⋃ i, I i), ({i | e.1 ∈ I i}.encard - 1) := by
  rw [multiConn_eq_comap_nullity hI]
  obtain hι | hι := isEmpty_or_nonempty ι; simp
  have h_ex (e) : ∃ i, e ∈ ⋃ i, I i → e ∈ I i := by
    obtain ⟨_, ⟨⟨i, hi, rfl⟩, hi⟩⟩ | he := em <| e ∈ ⋃ i, I i
    · exact ⟨i, fun _ ↦ hi⟩
    simp [he]
  choose φ hφ using h_ex
  have hmem {e : ⋃ i, I i} : φ e ∈ {i | e.1 ∈ I i} := hφ _ e.2
  simp only [mem_iUnion, forall_exists_index] at hφ
  rw [nullity_eq_nullity_add_encard_diff (X := ⋃ i, (fun e ↦ (e, φ e)) '' I i), nullity_comap]
  · have hrw (e : ⋃ i, I i) :
        {i | e.1 ∈ I i}.encard - 1 = ((e.1, ·) '' {i | e.1 ∈ I i ∧ i ≠ φ e}).encard := by
      rw [(Prod.mk_right_injective e.1).encard_image, ← encard_diff_singleton_of_mem hmem]
      rfl
    simp_rw [image_iUnion, image_image, image_id', hrw]
    rw [ENat.tsum_encard_eq_encard_iUnion]
    · congr
      aesop
    simp_rw [Pairwise, disjoint_left]
    aesop
  · simp_rw [InjOn]
    aesop
  · simp only [iUnion_subset_iff, image_subset_iff, preimage_iUnion]
    exact fun i e heI ↦ mem_iUnion.2 ⟨φ e, by simp [hφ _ _ heI]⟩
  suffices ∀ (i : ι), I i ⊆ M.closure (⋃ i, I i) by
    simpa [preimage_preimage, image_iUnion, image_image]
  exact fun i ↦ M.subset_closure_of_subset' (subset_iUnion ..) (hI i).indep.subset_ground

lemma multiConn_eq_nullity_iUnion (hdj : Pairwise (Disjoint on X))
    (hIX : ∀ i, M.IsBasis' (I i) (X i)) : M.multiConn X = M.nullity (⋃ i, I i) := by
  rw [multiConn_eq_comap_nullity hIX, nullity_comap, image_iUnion]
  · simp [image_image]
  simp +contextual only [InjOn, mem_iUnion, mem_image, forall_exists_index, and_imp, Prod.forall,
    Prod.mk.injEq, true_and]
  rintro _ _ i a ha rfl rfl _ _ j _ ha' rfl rfl rfl
  by_contra hne
  exact (hdj hne).notMem_of_mem_left ((hIX i).subset ha) ((hIX j).subset ha')

lemma multiConn_mono (M : Matroid α) (hXY : ∀ i, X i ⊆ Y i) :
    M.multiConn X ≤ M.multiConn Y := by
  choose I hI using fun i ↦ M.exists_isBasis' (X i)
  choose J hJ using fun i ↦ (hI i).indep.subset_isBasis'_of_subset <| (hI i).subset.trans (hXY i)
  rw [multiConn_eq_comap_nullity hI, multiConn_eq_comap_nullity (fun i ↦ (hJ i).1)]
  exact nullity_le_of_subset _ (iUnion_mono fun i ↦ image_subset _ (hJ i).2)

/-- The local connectivity of a pair of sets `X,Y` is the nullity of `I ∪ J` plus the
cardinality of `I ∩ J`, for any respective bases `I` and `J` for `X` and `Y`. -/
lemma multiConn_cond {I J X Y : Set α} (hIX : M.IsBasis' I X) (hJY : M.IsBasis' J Y) :
    M.multiConn (fun b ↦ bif b then X else Y) = M.nullity (I ∪ J) + (I ∩ J).encard := by
  have hinv {b : Bool} {U : Set α} : LeftInvOn Prod.fst (·, b) U :=
    LeftInverse.leftInvOn (congrFun rfl) _
  have aux_dj {A B : Set α} : Disjoint ((·, true) '' A) ((·, false) '' B) := by
    simp [disjoint_left]
  have hb (b : Bool) : M.IsBasis' (bif b then I else J) ((bif b then X else Y)) := by
    cases b with simpa
  simp only [multiConn_eq_comap_nullity hb, iUnion_bool, cond_true, cond_false]
  have hI : (M.comap Prod.fst).Indep ((·, true) '' I) := hIX.indep.comap hinv
  rw [← hI.nullity_project_of_disjoint aux_dj, nullity_eq_nullity_add_encard_diff
    (X := (·, false) '' (J \ I)) (image_subset _ diff_subset),
    hI.nullity_project_of_disjoint aux_dj, nullity_comap, image_union,
    hinv.image_image, hinv.image_image, union_diff_self, InjOn.image_diff (by simp),
    diff_diff_right_self, inter_eq_self_of_subset_right (image_subset _ inter_subset_left),
    Injective.encard_image (Prod.mk_left_injective false), inter_comm]
  · rw [injOn_union aux_dj, and_iff_right hinv.injOn_image, and_iff_right hinv.injOn_image]
    aesop
  suffices J ⊆ M.closure (J ∪ I) by
    simpa [project_closure, preimage_preimage, image_union, hinv.image_image]
  refine M.subset_closure_of_subset' subset_union_left hJY.indep.subset_ground

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

-- lemma multiConn_project_le (M : Matroid α) (X : ι → Set α) (C : Set α) :
--     (M.project C).multiConn X ≤ M.multiConn X := by
--   wlog hC : M.Indep C generalizing C with aux
--   · obtain ⟨I, hI⟩ := M.exists_isBasis' C
--     grw [hI.project_eq_project, aux _ hI.indep]
--   choose I hI using fun i ↦ (M.project C).exists_isBasis' (X i)
--   choose J hJ using fun i ↦ (hI i).indep.of_project.subset_isBasis'_of_subset (hI i).subset

--   -- have hCcl : M.closure
--   rw [multiConn_eq_comap_nullity hI, multiConn_eq_comap_nullity (fun i ↦ (hJ i).1),
--     project_comap]
--   sorry



lemma multiConn_closure (M : Matroid α) (X : ι → Set α) :
    M.multiConn (fun i ↦ M.closure (X i)) = M.multiConn X := by
  choose I hI using fun i ↦ M.exists_isBasis' (X i)
  rw [multiConn_eq_comap_nullity (I := I), multiConn_eq_comap_nullity (I := I) hI]
  exact fun i ↦ (hI i).isBasis_closure_right.isBasis'

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
  grw [multiConn_eq_nullity_iUnion hdj hI, multiConn_eq_nullity_iUnion hdj (fun i ↦ (hJ i).1),
    nullity_delete_of_disjoint _ (by simp [disjoint_sdiff_left]),
    ← iUnion_diff, ← nullity_union_le_nullity_add_encard, diff_union_self]
  exact M.nullity_le_of_subset subset_union_left

lemma multiConn_project_eq_multiconn_contract (M : Matroid α) (C : Set α) :
    (M.project C).multiConn (ι := ι) = (M ／ C).multiConn := by
  ext X
  wlog hXE : ∀ i, X i ⊆ M.E generalizing X with aux
  · rw [← multiConn_inter_ground, aux _ (by simp), ← multiConn_inter_ground, eq_comm,
      ← multiConn_inter_ground]
    simp [inter_assoc, inter_eq_self_of_subset_right diff_subset]
  rwa [eq_comm, ← (M ／ C).multiConn_restrict_of_subset (R := M.E), project]

-- lemma multiConn_dual_le_multiConn_projectBy_dual_add_one (U : M.ModularCut) (X : ι → Set α) :
--     M✶.multiConn X ≤ (M.projectBy U)✶.multiConn X + 1 := by
--   obtain ⟨e, he⟩ : ∃ e, e ∉ M.E := sorry
--   nth_rw 1 [← ModularCut.extendBy_deleteElem U he, dual_delete,
--     ← extendBy_contract_eq _ he, dual_contract]
--   grw [multiConn_delete]

-- lemma multiConn_mapEmbedding {β : Type*} (M : Matroid α) (f : α ↪ β) :
--     (M.mapEmbedding f).multiConn (fun i ↦ f '' (X i)) = M.multiConn X := by
--   choose I hI using fun i ↦ M.exists_isBasis' (X i)
--   -- have hJ := fun i ↦ (hI i).mapEmbedding
--   rw [multiConn_eq_comap_nullity hI, multiConn_eq_comap_nullity fun i ↦ (hI i).mapEmbedding,
--     mapEmbedding]


-- lemma multiConn_dual_project_le_multiConn_dual_add_encard (M : Matroid α)
--     (hdj : Pairwise (Disjoint on X)) (C : Set α) :
--     M✶.multiConn X ≤ (M.project C)✶.multiConn X + C.encard := by
