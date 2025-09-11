import Matroid.Connectivity.Local
import Mathlib.Data.Set.Prod

open Set Function

lemma disjoint_map_prod_right {α ι : Type*} {f : ι → Set α} :
    Pairwise (Disjoint on fun i ↦ (·, i) '' f i) := by
  simp +contextual [Pairwise, disjoint_right]

lemma disjoint_map_prod_left {α ι : Type*} {f : ι → Set α} :
    Pairwise (Disjoint on fun i ↦ (i, ·) '' f i) := by
  simp +contextual [Pairwise, disjoint_right]

-- generalize this more to remove some of the `aesop`s, and do the right version too.
lemma injOn_prod_fst_mk_left_iff_pairwise_disjoint {α ι : Type*} (f : ι → Set α) :
    InjOn Prod.fst (⋃ i, (·, i) '' f i) ↔ Pairwise (Disjoint on f) := by
  refine ⟨fun h i j hij ↦ disjoint_left.2 fun x hxi hxj ↦ hij ?_, fun h i hi j hj hij ↦ ?_⟩
  · simpa using @h (x,i) (by simpa) (x,j) (by simpa) rfl
  obtain ⟨i, x, hx, rfl⟩ := by simpa using hi
  obtain ⟨j, y, hy, rfl⟩ := by simpa using hj
  obtain rfl : x = y := hij
  obtain rfl | hne := eq_or_ne i j; simp
  exact ((h hne).notMem_of_mem_left hx hy).elim


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

lemma multiConn_inter_ground_congr {X Y : ι → Set α} (hXY : ∀ i, X i ∩ M.E = Y i ∩ M.E) :
    M.multiConn X = M.multiConn Y := by
  rw [← multiConn_inter_ground, eq_comm, ← multiConn_inter_ground]
  simp_rw [hXY]

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
  · simp only [InjOn, mem_iUnion, mem_image, forall_exists_index, and_imp, Prod.forall,
    Prod.mk.injEq]
    rintro _ _ _ _ _ rfl rfl _ _ _ _ _ rfl rfl rfl
    exact ⟨rfl, rfl⟩
  · simp only [iUnion_subset_iff, image_subset_iff, preimage_iUnion]
    exact fun i e heI ↦ mem_iUnion.2 ⟨φ e, by simp [hφ _ _ heI]⟩
  suffices ∀ (i : ι), I i ⊆ M.closure (⋃ i, I i) by
    simpa [preimage_preimage, image_iUnion, image_image]
  exact fun i ↦ M.subset_closure_of_subset' (subset_iUnion ..) (hI i).indep.subset_ground

lemma multiConn_eq_nullity_iUnion_add_tsum' (hI : ∀ i, M.IsBasis' (I i) (X i)) :
    M.multiConn X = M.nullity (⋃ i, I i) + ∑' e, ({i | e ∈ I i}.encard - 1) := by
  rw [multiConn_eq_nullity_iUnion_add_tsum hI, eq_comm]
  convert rfl using 2
  rw [← tsum_subtype_eq_of_support_subset (s := ⋃ i, I i)]
  simp only [support_subset_iff, ne_eq, mem_iUnion, not_imp_comm, not_exists]
  intro e he
  simp [show {i | e ∈ I i} = ∅ by simpa [eq_empty_iff_forall_notMem] ]

lemma multiConn_eq_nullity_iUnion' (hdj : Pairwise (Disjoint on I))
    (hIX : ∀ i, M.IsBasis' (I i) (X i)) : M.multiConn X = M.nullity (⋃ i, I i) := by
  rw [multiConn_eq_comap_nullity hIX, nullity_comap, image_iUnion]
  · simp [image_image]
  simp +contextual only [InjOn, mem_iUnion, mem_image, forall_exists_index, and_imp, Prod.forall,
    Prod.mk.injEq, true_and]
  rintro _ _ i a ha rfl rfl _ _ j _ ha' rfl rfl rfl
  by_contra hne
  exact (hdj hne).notMem_of_mem_left ha ha'

lemma multiConn_eq_nullity_iUnion (hdj : Pairwise (Disjoint on X))
    (hIX : ∀ i, M.IsBasis' (I i) (X i)) : M.multiConn X = M.nullity (⋃ i, I i) :=
  multiConn_eq_nullity_iUnion' (hdj.mono fun i j ↦ Disjoint.mono (hIX i).subset (hIX j).subset) hIX

@[simp]
lemma multiConn_subsingleton [Subsingleton ι] (M : Matroid α) (X : ι → Set α) :
    M.multiConn X = 0 := by
  choose I hI using fun i ↦ M.exists_isBasis' (X i)
  rw [multiConn_eq_nullity_iUnion Subsingleton.pairwise hI, nullity_eq_zero]
  obtain hι | ⟨⟨i⟩⟩ := isEmpty_or_nonempty ι
  · simp
  exact (hI i).indep.subset <| iUnion_subset_iff.2 fun j ↦ by rw [Subsingleton.elim i j]

lemma multiconn_eq_comap_prod_multiConn (X : ι → Set α) :
    M.multiConn X = (M.comap Prod.fst).multiConn (fun i ↦ (· , i) '' X i) := by
  choose I hI using fun i ↦ M.exists_isBasis' (X i)
  rwa [multiConn_eq_nullity_iUnion (M := M.comap Prod.fst)
    (I := fun i ↦ (·, i) '' I i) disjoint_map_prod_right,
    multiConn_eq_comap_nullity (I := I)]
  exact fun i ↦ (hI i).comap <| RightInverse.rightInvOn (congr_fun rfl) _

lemma multiConn_mono (M : Matroid α) (hXY : ∀ i, X i ⊆ Y i) :
    M.multiConn X ≤ M.multiConn Y := by
  choose I hI using fun i ↦ M.exists_isBasis' (X i)
  choose J hJ using fun i ↦ (hI i).indep.subset_isBasis'_of_subset <| (hI i).subset.trans (hXY i)
  rw [multiConn_eq_comap_nullity hI, multiConn_eq_comap_nullity (fun i ↦ (hJ i).1)]
  exact nullity_le_of_subset _ (iUnion_mono fun i ↦ image_mono (hJ i).2)

lemma multiConn_map_image {β : Type*} {f : α → β} (M : Matroid α) (hf : InjOn f M.E)
    (X : ι → Set α) (hXE : ∀ i, X i ⊆ M.E) :
    (M.map f hf).multiConn (fun i ↦ f '' (X i)) = M.multiConn X := by
  choose I hI using fun i ↦ M.exists_isBasis (X i) (hXE i)
  grw [multiConn_eq_nullity_iUnion_add_tsum (fun i ↦ (hI i).isBasis'),
    multiConn_eq_nullity_iUnion_add_tsum (fun i ↦ ((hI i).map hf).isBasis'), ← image_iUnion,
    nullity_map_image _ (iUnion_subset fun i ↦ (hI i).subset.trans (hXE i))]
  convert rfl
  rw [eq_comm]
  have hIE := iUnion_subset fun i ↦ (hI i).indep.subset_ground
  convert tsum_image (α := ℕ∞) (s := (⋃ i, I i)) (g := f)
    (f := fun (x : β) ↦ {i : ι | x ∈ f '' (I i)}.encard - 1) (hf.mono hIE) with e i
  rw [hf.mem_image_iff (hI i).indep.subset_ground (hIE e.2)]

lemma multiConn_map {β : Type*} {f : α → β} (M : Matroid α) (hf : InjOn f M.E) (X : ι → Set β) :
    (M.map f hf).multiConn X = (M.multiConn fun i ↦ f ⁻¹' (X i)) := by
  wlog hXss : ∀ i, X i ⊆ f '' M.E generalizing X with aux
  · rw [← multiConn_inter_ground, ← M.multiConn_inter_ground, map_ground,
      aux _ (fun i ↦ inter_subset_right), ← multiConn_inter_ground]
    convert rfl using 3 with i
    rw [preimage_inter, inter_assoc, inter_eq_self_of_subset_right (subset_preimage_image ..)]
  choose Y hY using fun i ↦ subset_image_iff.1 (hXss i)
  rw [forall_and] at hY
  obtain rfl : X = fun i ↦ f '' (Y i) := funext fun i ↦ (hY.2 i).symm
  rw [multiConn_map_image _ _ _ hY.1]
  apply multiConn_inter_ground_congr
  simp only
  refine fun i ↦ subset_antisymm (inter_subset_inter_left _ (subset_preimage_image ..))
    (subset_inter ?_ inter_subset_right)
  rw [hf.preimage_image_inter (hY.1 i)]

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
    (X := (·, false) '' (J \ I)) (image_mono diff_subset),
    hI.nullity_project_of_disjoint aux_dj, nullity_comap, image_union,
    hinv.image_image, hinv.image_image, union_diff_self, InjOn.image_diff (by simp),
    diff_diff_right_self, inter_eq_self_of_subset_right (image_mono inter_subset_left),
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

lemma multiConn_delete_of_disjoint (M : Matroid α) {D : Set α} (hXD : ∀ i, Disjoint (X i) D) :
    (M ＼ D).multiConn X = M.multiConn X := by
  simp_rw [multiConn_delete, (hXD _).sdiff_eq_left]

lemma multiConn_closure (M : Matroid α) (X : ι → Set α) :
    M.multiConn (fun i ↦ M.closure (X i)) = M.multiConn X := by
  choose I hI using fun i ↦ M.exists_isBasis' (X i)
  rw [multiConn_eq_comap_nullity (I := I), multiConn_eq_comap_nullity (I := I) hI]
  exact fun i ↦ (hI i).isBasis_closure_right.isBasis'

lemma multiConn_closure_congr {X Y : ι → Set α} (hXY : ∀ i, M.closure (X i) = M.closure (Y i)) :
    M.multiConn X = M.multiConn Y := by
  rw [← M.multiConn_closure X, ← M.multiConn_closure Y]
  simp [hXY]

lemma multiConn_comap {β : Type*} (M : Matroid β) (X : ι → Set α) (f : α → β) :
    (M.comap f).multiConn X = M.multiConn (fun i ↦ f '' (X i)) := by
  choose I hI using fun i ↦ (M.comap f).exists_isBasis' (X i)
  rw [multiConn_eq_comap_nullity hI]
  simp_rw [comap_isBasis'_iff, forall_and] at hI
  simp_rw [multiConn_eq_comap_nullity hI.1, image_image]
  have := (M.comap Prod.fst : Matroid (β × ι)).nullity_comap (X := ⋃ i, (· , i) '' I i)
      (f := fun x : (α × ι) ↦ (f x.1, x.2)) ?_
  · convert this
    · simp_rw [comap_comap]
      rfl
    aesop
  simp only [InjOn, mem_iUnion, mem_image, Prod.mk.injEq, and_imp, forall_exists_index, Prod.forall]
  rintro a i j x hx rfl rfl y k l z hz rfl rfl hf rfl
  rw [(hI.2.1 j).eq_iff hx hz] at hf
  exact ⟨hf, rfl⟩

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

lemma multiConn_project_eq_multiConn_contract (M : Matroid α) (C : Set α) :
    (M.project C).multiConn (ι := ι) = (M ／ C).multiConn := by
  ext X
  wlog hXE : ∀ i, X i ⊆ M.E generalizing X with aux
  · rw [← multiConn_inter_ground, aux _ (by simp), ← multiConn_inter_ground, eq_comm,
      ← multiConn_inter_ground]
    simp [inter_assoc, inter_eq_self_of_subset_right diff_subset]
  rwa [eq_comm, ← (M ／ C).multiConn_restrict_of_subset (R := M.E), project]

lemma IsSkewFamily.multiConn (h : M.IsSkewFamily X) : M.multiConn X = 0 := by
  obtain ⟨B, hB, hBX⟩ := h.isModularFamily.exists_isMutualBasis_isBase
  rw [multiConn_eq_nullity_iUnion' (h.pairwise_disjoint_of_isBases hBX.isBasis_inter)
    (fun i ↦ (hBX.isBasis_inter i).isBasis'), nullity_eq_zero]
  exact hB.indep.subset <| by simp

lemma multiConn_eq_zero_iff (hX : ∀ i, X i ⊆ M.E) :
    M.multiConn X = 0 ↔ M.IsSkewFamily X := by
  choose I hI using fun i ↦ M.exists_isBasis' (X i)
  rw [multiConn_eq_comap_nullity hI, nullity_eq_zero, comap_indep_iff, image_iUnion,
    isSkewFamily_iff_cls_isSkewFamily hX]
  simp only [image_image, image_id', ← (hI _).closure_eq_closure]
  rw [← isSkewFamily_iff_cls_isSkewFamily (fun i ↦ (hI i).indep.subset_ground),
    Indep.isSkewFamily_iff_pairwise_disjoint_union_indep (fun i ↦ (hI i).indep), and_comm,
    injOn_prod_fst_mk_left_iff_pairwise_disjoint]

/-- A version of `multiConn_eq_zero_iff` where the union is `M.E`,
since this is a common application -/
lemma multiConn_eq_zero_iff' (hX : ⋃ i, X i = M.E) :
    M.multiConn X = 0 ↔ M.IsSkewFamily X := by
  rw [multiConn_eq_zero_iff (fun i ↦ by grw [← hX, ← subset_iUnion])]

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
  rw [multiConn_eq_nullity_iUnion hdj (fun i ↦ (hI' i).isBasis'), nullity_eq_eRank_restrict_dual,
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

private lemma multiConn_project_le_aux (M : Matroid α) {C : Set α} (hCX : C ⊆ ⋃ i, X i)
    (hdj : Pairwise (Disjoint on X)) (hC : M.Indep C) :
    (M.project C).multiConn X ≤ M.multiConn X := by
  choose I hI using fun i ↦ (hC.inter_left (X i)).subset_isBasis'_of_subset inter_subset_left
  choose J hJ using fun i ↦ (M.project C).exists_isBasis' (I i)
  have hJ' (i) : (M.project C).IsBasis' (J i) (X i) := by
    rw [isBasis'_iff_isBasis_closure, project_closure,
      ← closure_union_congr_left (hI i).1.closure_eq_closure, ← project_closure]
    exact ⟨(hJ i).isBasis_closure_right, (hJ i).subset.trans (hI i).1.subset⟩
  grw [multiConn_eq_nullity_iUnion hdj hJ', multiConn_eq_nullity_iUnion hdj (fun i ↦ (hI i).1),
    hC.nullity_project_of_disjoint, nullity_le_of_subset]
  · refine union_subset ?_ (iUnion_mono (fun i ↦ (hJ i).subset))
    rw [← inter_eq_self_of_subset_right hCX, iUnion_inter]
    exact iUnion_mono fun i ↦ (hI i).2
  exact disjoint_iUnion_right.2 fun i ↦ (hC.project_indep_iff.1 (hJ i).indep).1.symm

lemma multiConn_project_le (M : Matroid α) {C : Set α} (hC : C ⊆ ⋃ i, X i) :
    (M.project C).multiConn X ≤ M.multiConn X := by
  choose I hI using fun i ↦ M.exists_isBasis' (X i)
  obtain ⟨IC, hIC⟩ := M.exists_isBasis' C
  obtain ⟨K, hKdj, rfl, hKX⟩ := exists_partition_of_subset_iUnion (hIC.subset.trans hC)
  have hwin := multiConn_project_le_aux (M.comap Prod.fst) (X := fun i ↦ (·, i) '' (X i))
    (C := ⋃ (i : ι), (·, i) '' (K i)) ?_ ?_ ?_; rotate_left
  · exact iUnion_mono fun i ↦ image_mono (hKX i)
  · exact disjoint_map_prod_right
  · simp [image_iUnion, image_image, injOn_prod_fst_mk_left_iff_pairwise_disjoint, hKdj, hIC.indep]
  simp only [← project_comap_image, image_iUnion, image_image, image_id'] at hwin
  grw [hIC.project_eq_project, multiconn_eq_comap_prod_multiConn, hwin,
    M.multiconn_eq_comap_prod_multiConn]

lemma multiConn_contract_le (M : Matroid α) {C : Set α} (hC : C ⊆ ⋃ i, X i) :
    (M ／ C).multiConn X ≤ M.multiConn X := by
  grw [← multiConn_project_eq_multiConn_contract, multiConn_project_le _ hC]

lemma multiConn_project_aux_indep (M : Matroid α) {C : Set α} (hC : M.Indep C) (X : ι → Set α) :
    (M.project C).multiConn X + ∑' i, (M.project (X i)).nullity C
    = M.multiConn X + (M.project (⋃ i, X i)).nullity C := by
  -- We may assume that `ι` is nonempty and `C` is independent.
  obtain hι | hι := isEmpty_or_nonempty ι
  · simp [hC.nullity_eq]
  choose I hI using fun i ↦ M.exists_isBasis' (X i)
  choose J hJ using fun i ↦ (M.project C).exists_isBasis' (I i)

  -- Choose `C'` to be an arbitrary injective preimage of `C`,
  -- and prove that `C'` is a basis of the preimage of `C` in the comap.
  set C' : Set (α × ι) := (· , Classical.arbitrary ι) '' C with hC'_def
  have hC'bas : (M.comap Prod.fst).IsBasis' C' (Prod.fst ⁻¹' C) := by
    suffices M.IsBasis' C (Prod.fst '' (Prod.fst ⁻¹' C)) by
      simpa [hC'_def, image_image, InjOn, preimage_preimage]
    rw [image_preimage_eq _ Prod.fst_surjective]
    exact hC.isBasis_self.isBasis'
  -- Each `J i` spans `X i` in `M.project C`, so is a basis.
  have hJX (i) : (M.project C).IsBasis' (J i) (X i) := by
    rw [isBasis'_iff_isBasis_closure, and_iff_left ((hJ i).subset.trans (hI i).subset)]
    refine (hJ i).indep.isBasis_of_subset_of_subset_closure ?_ ?_
    · grw [(hJ i).subset, ← closure_subset_closure _ (hI i).subset]
      exact subset_closure _ _ (by simpa using (hI i).indep.subset_ground)
    rw [(hJ i).closure_eq_closure, project_closure, project_closure,
      ← closure_union_congr_left (hI i).closure_eq_closure]
  -- the sum of cardinality term is equal to the cardinality of a union.
  have hsrw (i) : (M.project (X i)).nullity C = (I i \ J i).encard := by
    rw [(hI i).project_eq_project, ← add_zero (nullity ..), ← (hI i).indep.nullity_eq,
      nullity_project_add_nullity_comm, hC.nullity_eq, add_zero, (hJ i).nullity_eq]
  have hcard : ∑' i, (M.project (X i)).nullity C
      = ((⋃ i, ((·, i) '' I i)) \ (⋃ i, ((·, i) '' J i))).encard := by
    rw [tsum_congr hsrw, ← iUnion_diff_iUnion
      (fun i ↦ (image_mono (hJ i).subset)) disjoint_map_prod_right,
      ← ENat.tsum_encard_eq_encard_iUnion, tsum_congr]
    · intro i
      rw [← image_diff (Prod.mk_left_injective i), (Prod.mk_left_injective i).encard_image ]
    exact (disjoint_map_prod_right (f := I)).mono fun _ _ ↦ Disjoint.mono diff_subset diff_subset
  -- the union of the lifted `I`s is spanned by the union of the lifted `J`s in `M.project C`.
  have hcl : ⋃ i, (·, i) '' I i ⊆ ((M.project C).comap Prod.fst).closure (⋃ i, (·, i) '' J i) := by
    suffices ∀ (i : ι), I i ⊆ M.closure ((⋃ i, J i) ∪ C) by
      simpa [preimage_preimage, image_iUnion, image_image]
    intro i
    rw [← project_closure, closure_iUnion_congr _ _ fun i ↦ (hJ i).closure_eq_closure]
    exact subset_closure_of_subset' _ (subset_iUnion ..) (hI i).indep.subset_ground
  -- We are now done by a calculation.
  rw [multiConn_eq_comap_nullity hI, multiConn_eq_comap_nullity hJX, hcard,
    ← nullity_eq_nullity_add_encard_diff (iUnion_mono fun i ↦ image_mono (hJ i).subset) hcl,
    ← add_zero (nullity ..), ← hC'bas.indep.nullity_eq, project_comap _ _ _ (by simp),
    hC'bas.project_eq_project, nullity_project_add_nullity_comm, ← project_comap_image]
  simp only [image_iUnion, image_image, image_id']
  rw [← project_closure_eq, closure_iUnion_congr _ _ (fun i ↦ (hI i).closure_eq_closure),
    project_closure_eq, add_comm (nullity ..),  nullity_comap (X := C')]
  · simp only [hC'_def, image_image, image_id']
  simp [hC'_def, InjOn]


/-- An auxiliary lemma used to numerically relate the `multiConn` in a matroid its projection,
in terms of chosen bases.  -/
lemma multiConn_project_aux (M : Matroid α) {C : Set α} (hI : ∀ i, M.IsBasis' (I i) (X i)) :
    (M.project C).multiConn X + (M.project (⋃ i, X i)).eRk C + ∑' i, (M.project C).nullity (I i)
    = M.multiConn X + M.eRk C := by
  wlog hC : M.Indep C generalizing C with aux
  · obtain ⟨K, hK⟩ := M.exists_isBasis' C
    simp_rw [hK.project_eq_project, ← hK.eRk_eq_eRk]
    convert aux hK.indep using 3
    rw [← eRk_closure_eq, project_closure, ← closure_union_congr_left hK.closure_eq_closure,
      ← project_closure, eRk_closure_eq]
  have hrw := M.multiConn_project_aux_indep hC X
  apply_fun (· + (M.project (⋃ i, X i)).eRk C) at hrw
  rw [add_right_comm, add_right_comm (a := M.multiConn X), add_assoc (a := M.multiConn X),
    eRk_add_nullity_eq_encard, ← hC.eRk_eq_encard] at hrw
  convert hrw using 4 with i
  rw [hC.nullity_project, (hI i).project_eq_project, (hI i).indep.nullity_project,
    union_comm, inter_comm]


lemma multiConn_project_le_multiConn_add (M : Matroid α) (X : ι → Set α) (C : Set α) :
    (M.project C).multiConn X ≤ M.multiConn X + M.eRk C := by
  choose I hI using fun i ↦ M.exists_isBasis' (X i)
  -- choose J hJ using fun i ↦ (M.project C).exists_isBasis' (I i)
  rw [← M.multiConn_project_aux hI, add_assoc]
  exact le_self_add

lemma multiConn_project_eq_multiConn_add_iff (M : Matroid α) {X : ι → Set α} {C : Set α}
    (hXfin : M.multiConn X ≠ ⊤) (hXE : ∀ i, X i ⊆ M.E) (hCfin : M.eRk C ≠ ⊤) (hCE : C ⊆ M.E):
    (M.project C).multiConn X = M.multiConn X + M.eRk C ↔
      C ⊆ M.closure (⋃ i, X i) ∧ ∀ i, M.Skew (X i) C := by
  choose I hI using fun i ↦ M.exists_isBasis' (X i)
  rw [← M.multiConn_project_aux hI, add_assoc, eq_comm]
  simp only [ENat.add_eq_left_iff, add_eq_zero, ENat.tsum_eq_zero, nullity_eq_zero]
  rw [or_iff_right, eRk_eq_zero_iff (by simpa using hCE), project_loops, and_congr_right_iff]
  · have hrw (i) : M.Skew (X i) C ↔ (M.project C).Indep (I i) := by
      rw [project_indep_eq, ← (hI i).indep.skew_iff_contract_indep hCE,
        skew_iff_closure_skew_left (hXE i), skew_iff_closure_skew_left (hI i).indep.subset_ground,
        (hI i).closure_eq_closure]
    simp [hrw]
  grw [← Ne, ← lt_top_iff_ne_top, multiConn_project_le_multiConn_add, lt_top_iff_ne_top,
    Ne, ENat.add_eq_top, or_iff_right hXfin]
  assumption

lemma multiConn_projectElem_eq_multiConn_add_iff (M : Matroid α) {X : ι → Set α} {e : α}
    (hXfin : M.multiConn X ≠ ⊤) (he : M.IsNonloop e) :
    (M.project {e}).multiConn X = M.multiConn X + 1 ↔
      e ∈ M.closure (⋃ i, X i) ∧ ∀ i, e ∉ M.closure (X i) := by
  wlog hXE : ∀ i, X i ⊆ M.E generalizing X with aux
  · rw [← multiConn_inter_ground, ← M.multiConn_inter_ground, project_ground, aux
      (by rwa [multiConn_inter_ground]) (fun i ↦ inter_subset_right), ← iUnion_inter]
    simp
  rw [← he.eRk_eq, multiConn_project_eq_multiConn_add_iff _ hXfin hXE (by simp [he.eRk_eq])
    (by simpa using he.mem_ground), singleton_subset_iff]
  simp_rw [he.skew_right_iff (hXE _)]

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
  nth_rw 1 [← U.extendBy_contractElem he,  ← U.extendBy_deleteElem he,
    multiConn_delete_of_disjoint _ (fun i ↦ disjoint_singleton_right.2 (notMem_subset (hXE i) he)),
    ← multiConn_project_eq_multiConn_contract, ENat.encard_eq_tsum_ite, eq_comm]
  simp only [mem_setOf_eq]
  convert (M.extendBy e U).multiConn_project_aux_indep (C := {e}) (X := X)
    (by rwa [indep_singleton, extendBy_isNonloop_iff]) with i
  · simp [nullity_singleton_eq_ite, IsLoop, mem_closure_extendBy_iff U he,
      or_iff_right (notMem_subset (hXE i) he)]
  rw [nullity_singleton_eq_ite, IsLoop, project_loops, mem_closure_extendBy_iff U he,
    or_iff_right heX]
  congr

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
  convert (M.extendBy e U)✶.multiConn_project_aux_indep (C := {e}) (X := X) hni with i <;>
  rw [nullity_singleton_eq_ite, isLoop_iff, project_loops]

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
