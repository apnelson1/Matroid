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

variable {α : Type*} {M : Matroid α} {B B' I I' J J' K X Y : Set α} {ι : Type*}

/-- An auxiliary version of multi-connectivity used in the real definition.
If the sets are disjoint, then this is equal to `multiConn`, but otherwise it is badly behaved.-/
private noncomputable def multiConnAux (M : Matroid α) (X : ι → Set α) : ℕ∞ :=
  ⨅ (I : {I : ι → Set α // ∀ i, M.IsBasis' (I i) (X i)}), M.nullity (⋃ i, I.1 i)

private lemma multiConnAux_eq_nullity_iUnion (M : Matroid α) {I X : ι → Set α}
    (hI : ∀ i, M.IsBasis' (I i) (X i)) (hdj : Pairwise (Disjoint on X)) :
    M.multiConnAux X = M.nullity (⋃ i, I i) := by
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

lemma multiConn_eq_comap_nullity {I X : ι → Set α} (h : ∀ i, M.IsBasis' (I i) (X i)) :
    M.multiConn X = (M.comap Prod.fst).nullity (⋃ i, (·, i) '' I i) := by
  have h' (i) : M.IsBasis' (I i) (X i ∩ M.E) := (h i).isBasis_inter_ground.isBasis'
  rw [multiConn, multiConnAux_eq_nullity_iUnion _
    (fun i ↦ (h' i).comap _) disjoint_map_prod_right]
  exact fun i ↦ RightInverse.rightInvOn (congr_fun rfl) _

lemma multiConn_eq_nullity_iUnion {M : Matroid α} {X I : ι → Set α} (hdj : Pairwise (Disjoint on X))
    (hIX : ∀ i, M.IsBasis' (I i) (X i)) : M.multiConn X = M.nullity (⋃ i, I i) := by
  rw [multiConn_eq_comap_nullity hIX, nullity_comap, image_iUnion]
  · simp [image_image]
  simp +contextual only [InjOn, mem_iUnion, mem_image, forall_exists_index, and_imp, Prod.forall,
    Prod.mk.injEq, true_and]
  rintro _ _ i a ha rfl rfl _ _ j _ ha' rfl rfl rfl
  by_contra hne
  exact (hdj hne).notMem_of_mem_left ((hIX i).subset ha) ((hIX j).subset ha')

lemma multiConn_mono (M : Matroid α) {X Y : ι → Set α} (hXY : ∀ i, X i ⊆ Y i) :
    M.multiConn X ≤ M.multiConn Y := by
  choose I hI using fun i ↦ M.exists_isBasis' (X i)
  choose J hJ using fun i ↦ (hI i).indep.subset_isBasis'_of_subset <| (hI i).subset.trans (hXY i)
  rw [multiConn_eq_comap_nullity hI, multiConn_eq_comap_nullity (fun i ↦ (hJ i).1)]
  exact nullity_le_of_subset _ (iUnion_mono fun i ↦ image_subset _ (hJ i).2)

/-- The local connectivity of a pair of sets `X,Y` is the nullity of `I ∪ J` plus the
cardinality of `I ∩ J`, for any respective bases `I` and `J` for `X` and `Y`. -/
lemma multiConn_cond (M : Matroid α) (hIX : M.IsBasis' I X) (hJY : M.IsBasis' J Y) :
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

lemma multiConn_restrict (M : Matroid α) {X : ι → Set α} (R : Set α) :
    (M ↾ R).multiConn X = M.multiConn (fun i ↦ (X i ∩ R)) := by
  choose I hI using fun i ↦ M.exists_isBasis' (X i ∩ R)
  have hIR (i) : I i ⊆ R := (hI i).subset.trans inter_subset_right
  rw [multiConn_eq_comap_nullity (I := I), multiConn_eq_comap_nullity (I := I) hI,
    comap_restrict, nullity_restrict_of_subset]
  · simpa [preimage_preimage] using hIR
  simpa [isBasis'_restrict_iff, hIR]

lemma multiConn_restrict_le (M : Matroid α) (X : ι → Set α) (R : Set α) :
    (M ↾ R).multiConn (fun i ↦ (X i) ∩ R) ≤ M.multiConn X := by
  rw [multiConn_restrict]
  exact multiConn_mono _ fun i ↦ inter_subset_left.trans inter_subset_left

lemma multiConn_delete (M : Matroid α) (X : ι → Set α) (D : Set α) :
    (M ＼ D).multiConn X = M.multiConn fun i ↦ (X i \ D) := by
  rw [delete_eq_restrict, multiConn_restrict, eq_comm, ← multiConn_inter_ground]
  convert rfl using 3 with i
  tauto_set

lemma multiConn_closure (M : Matroid α) (X : ι → Set α) :
    M.multiConn (fun i ↦ M.closure (X i)) = M.multiConn X := by
  choose I hI using fun i ↦ M.exists_isBasis' (X i)
  rw [multiConn_eq_comap_nullity (I := I), multiConn_eq_comap_nullity (I := I) hI]
  exact fun i ↦ (hI i).isBasis_closure_right.isBasis'
