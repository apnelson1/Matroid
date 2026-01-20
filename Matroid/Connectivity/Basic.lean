import Matroid.Rank.Skew
import Matroid.ForMathlib.Matroid.Map
import Matroid.ForMathlib.ENat
import Matroid.Uniform

open Set Function

lemma disjoint_map_prod_right {α ι : Type*} {f : ι → Set α} :
    Pairwise (Disjoint on fun i ↦ (·, i) '' f i) := by
  simp +contextual [Pairwise, disjoint_right]

lemma disjoint_map_prod_left {α ι : Type*} {f : ι → Set α} :
    Pairwise (Disjoint on fun i ↦ (i, ·) '' f i) := by
  simp +contextual [Pairwise, disjoint_right]

-- TODO : `Prod.snd` version.
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

section Multi

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
If the union of the `X i` has finite rank, then this is equal to `∑' i, r (X i) - r (⋃ i, X i)`.
If the `X i` are not disjoint, and the rank of their union is infinite,
then there is no simple formula in general, but for pairs,
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

lemma multiConn_eq_nullity_iUnion (hdj : Pairwise (Disjoint on I))
    (hIX : ∀ i, M.IsBasis (I i) (X i)) : M.multiConn X = M.nullity (⋃ i, I i) := by
  rw [multiConn_eq_nullity_iUnion' hdj (fun i ↦ (hIX i).isBasis')]

lemma multiConn_eq_nullity_iUnion'' (hdj : Pairwise (Disjoint on X))
    (hIX : ∀ i, M.IsBasis' (I i) (X i)) : M.multiConn X = M.nullity (⋃ i, I i) :=
  multiConn_eq_nullity_iUnion' (hdj.mono fun i j ↦ Disjoint.mono (hIX i).subset (hIX j).subset) hIX

@[simp]
lemma multiConn_subsingleton [Subsingleton ι] (M : Matroid α) (X : ι → Set α) :
    M.multiConn X = 0 := by
  choose I hI using fun i ↦ M.exists_isBasis' (X i)
  rw [multiConn_eq_nullity_iUnion'' Subsingleton.pairwise hI, nullity_eq_zero]
  obtain hι | ⟨⟨i⟩⟩ := isEmpty_or_nonempty ι
  · simp
  exact (hI i).indep.subset <| iUnion_subset_iff.2 fun j ↦ by rw [Subsingleton.elim i j]

@[simp]
lemma multiConn_const (M : Matroid α) (X : Set α) :
    M.multiConn (fun (_ : ι) ↦ X) = (ENat.card ι - 1) * M.eRk X := by
  obtain hι | ⟨⟨i⟩⟩ := isEmpty_or_nonempty ι
  · simp [tsub_eq_zero_iff_le]
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [M.multiConn_eq_comap_nullity (fun _ ↦ hI), ← biUnion_univ]
  simp_rw [← union_compl_self {i}, biUnion_union]
  rw [nullity_union_eq_nullity_add_encard_diff, sdiff_eq_left.2]
  · simp only [mem_singleton_iff]
    rw [Indep.nullity_eq, zero_add]
    · rw [← ENat.tsum_encard_eq_encard_biUnion, tsum_congr (fun _ ↦ InjOn.encard_image (by simp)),
        ENat.tsum_const, mul_comm, ← ENat.card_coe_setOf_ne i, hI.encard_eq_eRk]
      · rfl
      intro p (hp : p ≠ i) q (hq : q ≠ i) hpq
      simp [disjoint_left, hpq.symm]
    simp only [iUnion_iUnion_eq_left, comap_indep_iff, image_image, image_id', hI.indep, true_and]
    exact LeftInvOn.injOn_image fun ⦃x⦄ ↦ congrFun rfl
  · simp only [mem_compl_iff, mem_singleton_iff, iUnion_iUnion_eq_left, disjoint_iUnion_left]
    intro j hji
    simp [disjoint_left, Ne.symm hji]
  simp [image_image, preimage_preimage, M.subset_closure _ hI.indep.subset_ground]

lemma multiconn_eq_comap_prod_multiConn (X : ι → Set α) :
    M.multiConn X = (M.comap Prod.fst).multiConn (fun i ↦ (· , i) '' X i) := by
  choose I hI using fun i ↦ M.exists_isBasis' (X i)
  rwa [multiConn_eq_nullity_iUnion'' (M := M.comap Prod.fst)
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

@[simp]
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

lemma multiConn_closure (M : Matroid α) (X : ι → Set α) :
    M.multiConn (fun i ↦ M.closure (X i)) = M.multiConn X := by
  choose I hI using fun i ↦ M.exists_isBasis' (X i)
  rw [multiConn_eq_comap_nullity (I := I), multiConn_eq_comap_nullity (I := I) hI]
  exact fun i ↦ (hI i).isBasis_closure_right.isBasis'

lemma multiConn_closure_congr {X Y : ι → Set α} (hXY : ∀ i, M.closure (X i) = M.closure (Y i)) :
    M.multiConn X = M.multiConn Y := by
  rw [← M.multiConn_closure X, ← M.multiConn_closure Y]
  simp [hXY]

@[simp]
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

lemma tsum_eRk_eq_eRk_iUnion_add_multiConn :
    ∑' i, M.eRk (X i) = M.eRk (⋃ i, X i) + M.multiConn X := by
  wlog hX : ∀ i, M.Indep (X i) generalizing X with aux
  · choose I hI using fun i ↦ M.exists_isBasis' (X i)
    rw [← tsum_congr (fun i ↦ (hI i).eRk_eq_eRk), ← eRk_closure_eq,
      closure_iUnion_congr _ _ (fun i ↦ (hI i).closure_eq_closure.symm), eRk_closure_eq,
      ← multiConn_closure_congr (fun i ↦ (hI i).closure_eq_closure), aux (fun i ↦ (hI i).indep)]
  rw [tsum_congr (fun i ↦ (hX i).eRk_eq_encard),
    multiConn_eq_comap_nullity (fun i ↦ (hX i).isBasis_self.isBasis')]
  have hrw := M.eRk_comap (α := α × ι) (f := Prod.fst) (⋃ i, (·,i) '' X i)
  simp_rw [image_iUnion, image_image, image_id'] at hrw
  rw [← hrw, eRk_add_nullity_eq_encard, ← ENat.tsum_encard_eq_encard_iUnion
    disjoint_map_prod_right, tsum_congr (fun i ↦ InjOn.encard_image (by simp))]



  -- obtain h_eq | hne := eq_or_ne (M.eRk X) ⊤
  -- · grw [h_eq, ENat.mul_eq_top_iff.2 (by simp [tsub_eq_zero_iff_le])]
  -- obtain ⟨I, hI⟩ := M.exists_isBasis' X
  -- rw [IsBasis'.multiConn_eq_nullity_iUnion]

section Minor

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

lemma IsRestriction.multiConn {N : Matroid α} (hNM : N ≤r M) :
    N.multiConn X = M.multiConn fun i ↦ (X i ∩ N.E) := by
  obtain ⟨R, hRE, rfl⟩ := hNM
  rw [multiConn_restrict, restrict_ground_eq]

lemma IsRestriction.multiConn_of_subset {N : Matroid α} (hNM : N ≤r M) (hX : ∀ i, X i ⊆ N.E) :
    N.multiConn X = M.multiConn X := by
  rw [hNM.multiConn]
  simp [fun i ↦ inter_eq_self_of_subset_left (hX i)]

lemma multiConn_delete_of_disjoint (M : Matroid α) {D : Set α} (hXD : ∀ i, Disjoint (X i) D) :
    (M ＼ D).multiConn X = M.multiConn X := by
  simp_rw [multiConn_delete, (hXD _).sdiff_eq_left]

@[simp]
lemma multiConn_loopyOn (E : Set α) (X : ι → Set α) : (loopyOn E).multiConn X = 0 := by
  have h (i) : (loopyOn E).IsBasis' ∅ (X i) := by simp [isBasis'_iff_isBasis_closure]
  simp [multiConn_eq_comap_nullity h]

end Minor

end Multi

section Local

variable {X Y I J : Set α}

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

/-- The `ℕ∞`-valued local connectivity between two sets `X` and `Y`, often written `⊓ (X,Y)`.
Defined to correctly describe the connectivity even when one or both sets has infinite rank.
For a `ℕ`-valued version, see `Matroid.localConn`. -/
noncomputable def eLocalConn (M : Matroid α) (X Y : Set α) : ℕ∞ :=
  M.multiConn (fun b ↦ bif b then X else Y)

lemma IsBasis'.eLocalConn_eq {I J X Y : Set α} (hI : M.IsBasis' I X) (hJ : M.IsBasis' J Y) :
    M.eLocalConn X Y = (I ∩ J).encard + M.nullity (I ∪ J) := by
  rw [eLocalConn, M.multiConn_cond hI hJ, union_comm, add_comm]

lemma IsBasis.eLocalConn_eq {I J X Y : Set α}  (hI : M.IsBasis I X) (hJ : M.IsBasis J Y) :
    M.eLocalConn X Y = (I ∩ J).encard + M.nullity (I ∪ J) :=
  hI.isBasis'.eLocalConn_eq hJ.isBasis'

lemma eLocalConn_comm (M : Matroid α) (X Y : Set α) : M.eLocalConn X Y = M.eLocalConn Y X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  obtain ⟨J, hJ⟩ := M.exists_isBasis' Y
  rw [hI.eLocalConn_eq hJ, hJ.eLocalConn_eq hI, inter_comm, union_comm]

lemma eLocalConn_eq_multiConn (M : Matroid α) (X Y : Set α) :
    M.eLocalConn X Y = M.multiConn (fun b ↦ bif b then X else Y) := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  obtain ⟨J, hJ⟩ := M.exists_isBasis' Y
  rw [M.multiConn_cond hI hJ, hI.eLocalConn_eq hJ, add_comm]

lemma IsBasis'.eLocalConn_eq_nullity_project_right (hI : M.IsBasis' I X) (Y : Set α) :
    M.eLocalConn X Y = (M.project Y).nullity I := by
  obtain ⟨J, hJ⟩ := M.exists_isBasis' Y
  rw [hI.eLocalConn_eq hJ, add_comm, ← nullity_project_add_nullity_eq,
    ← hJ.project_eq_project, hJ.indep.nullity_eq, add_zero]

lemma IsBasis.eLocalConn_eq_nullity_project_right (hI : M.IsBasis I X) (Y : Set α) :
    M.eLocalConn X Y = (M.project Y).nullity I :=
  hI.isBasis'.eLocalConn_eq_nullity_project_right Y

lemma IsBasis'.eLocalConn_eq_nullity_project_left (hI : M.IsBasis' I Y) (X : Set α) :
    M.eLocalConn X Y = (M.project X).nullity I := by
  rw [eLocalConn_comm, hI.eLocalConn_eq_nullity_project_right]

lemma IsBasis.eLocalConn_eq_nullity_project_left (hI : M.IsBasis I Y) (X : Set α) :
    M.eLocalConn X Y = (M.project X).nullity I := by
  rw [eLocalConn_comm, hI.eLocalConn_eq_nullity_project_right]

lemma Indep.eLocalConn_eq_nullity_project_left (hI : M.Indep I) (X : Set α) :
    M.eLocalConn I X = (M.project X).nullity I :=
  hI.isBasis_self.eLocalConn_eq_nullity_project_right ..

lemma Indep.eLocalConn_eq_nullity_project_right (hI : M.Indep I) (X : Set α) :
    M.eLocalConn X I = (M.project X).nullity I :=
  hI.isBasis_self.eLocalConn_eq_nullity_project_left ..

lemma Indep.eLocalConn_eq (hI : M.Indep I) (hJ : M.Indep J) :
    M.eLocalConn I J = (I ∩ J).encard + M.nullity (I ∪ J) :=
  hI.isBasis_self.eLocalConn_eq hJ.isBasis_self

lemma IsBasis'.eLocalConn_eq_of_disjoint' (hI : M.IsBasis' I X) (hJ : M.IsBasis' J Y)
    (hIJ : Disjoint I J) : M.eLocalConn X Y = M.nullity (I ∪ J) := by
  rw [hI.eLocalConn_eq hJ, hIJ.inter_eq, encard_empty, zero_add]

lemma IsBasis.eLocalConn_eq_of_disjoint' (hI : M.IsBasis I X) (hJ : M.IsBasis J Y)
    (hIJ : Disjoint I J) : M.eLocalConn X Y = M.nullity (I ∪ J) := by
  rw [hI.eLocalConn_eq hJ, hIJ.inter_eq, encard_empty, zero_add]

lemma IsBasis'.eLocalConn_eq_of_disjoint (hI : M.IsBasis' I X) (hJ : M.IsBasis' J Y)
    (hXY : Disjoint X Y) : M.eLocalConn X Y = M.nullity (I ∪ J) := by
  rw [hI.eLocalConn_eq hJ, (hXY.mono hI.subset hJ.subset).inter_eq, encard_empty, zero_add]

lemma IsBasis.eLocalConn_eq_of_disjoint (hI : M.IsBasis I X) (hJ : M.IsBasis J Y)
    (hXY : Disjoint X Y) : M.eLocalConn X Y = M.nullity (I ∪ J) := by
  rw [hI.eLocalConn_eq hJ, (hXY.mono hI.subset hJ.subset).inter_eq, encard_empty, zero_add]

lemma eLocalConn_eq_encard_of_diff {F : Set α} (hXY : Disjoint X Y) (hI : M.IsBasis' I X)
    (hJ : M.IsBasis' J Y) (hFIJ : F ⊆ I ∪ J)  (hF : M.IsBasis' ((I ∪ J) \ F) (X ∪ Y)) :
    M.eLocalConn X Y = F.encard := by
  have hF' : M.IsBasis ((I ∪ J) \ F) (I ∪ J) := by
    refine hF.isBasis_inter_ground.isBasis_subset diff_subset
      (subset_inter (union_subset_union hI.subset hJ.subset)
      (union_subset hI.indep.subset_ground hJ.indep.subset_ground))
  rw [hI.eLocalConn_eq hJ, hF'.nullity_eq, diff_diff_cancel_left hFIJ,
    (hXY.mono hI.subset hJ.subset).inter_eq, encard_empty, zero_add]

lemma eLocalConn_eq_encard_of_diff' {F : Set α} (hXY : Disjoint X Y) (hI : M.IsBasis' I X)
    (hJ : M.IsBasis' J Y) (hFI : F ⊆ I)  (hF : M.IsBasis' ((I \ F) ∪ J) (X ∪ Y)) :
    M.eLocalConn X Y = F.encard := by
  apply eLocalConn_eq_encard_of_diff hXY hI hJ (hFI.trans subset_union_left)
  rwa [union_diff_distrib, (sdiff_eq_left (x := J)).2 ]
  exact (hXY.symm.mono hJ.subset (hFI.trans hI.subset))

@[simp] lemma eLocalConn_closure_right (M : Matroid α) (X Y : Set α) :
    M.eLocalConn X (M.closure Y) = M.eLocalConn X Y := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [hI.eLocalConn_eq_nullity_project_right, project_closure_eq,
    ← hI.eLocalConn_eq_nullity_project_right]

@[simp] lemma eLocalConn_closure_left (M : Matroid α) (X Y : Set α) :
    M.eLocalConn (M.closure X) Y = M.eLocalConn X Y := by
  rw [eLocalConn_comm, eLocalConn_closure_right, eLocalConn_comm]

@[simp] lemma eLocalConn_closure_closure (M : Matroid α) (X Y : Set α) :
    M.eLocalConn (M.closure X) (M.closure Y) = M.eLocalConn X Y := by
  rw [eLocalConn_closure_left, eLocalConn_closure_right]

lemma eLocalConn_inter_ground (M : Matroid α) (X Y : Set α) :
    M.eLocalConn (X ∩ M.E) (Y ∩ M.E) = M.eLocalConn X Y := by
  rw [← eLocalConn_closure_closure, closure_inter_ground, closure_inter_ground _ Y,
    eLocalConn_closure_closure]

@[simp] lemma eLocalConn_inter_ground_left (M : Matroid α) (X Y : Set α) :
    M.eLocalConn (X ∩ M.E) Y = M.eLocalConn X Y := by
  rw [← eLocalConn_closure_left, closure_inter_ground, eLocalConn_closure_left]

@[simp] lemma eLocalConn_inter_ground_right (M : Matroid α) (X Y : Set α) :
    M.eLocalConn X (Y ∩ M.E) = M.eLocalConn X Y := by
  rw [← eLocalConn_closure_right, closure_inter_ground, eLocalConn_closure_right]

@[simp]
lemma eLocalConn_self (M : Matroid α) (X : Set α) : M.eLocalConn X X = M.eRk X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [hI.eLocalConn_eq_nullity_project_left, hI.project_eq_project, hI.eRk_eq_encard,
    nullity_eq_encard]
  simp [M.subset_closure I hI.indep.subset_ground]

lemma eLocalConn_of_subset_coloops (M : Matroid α) (X : Set α) (hY : Y ⊆ M.coloops) :
    M.eLocalConn X Y = (X ∩ Y).encard := by
  nth_rw 1 [(M.coloops_indep.subset hY).isBasis_self.eLocalConn_eq_nullity_project_left X,
    ← diff_union_inter Y X, nullity_union_eq_nullity_add_encard_diff,
    disjoint_sdiff_inter.symm.sdiff_eq_left, inter_comm, Indep.nullity_eq, zero_add]
  · rw [project_indep_iff]
    exact (M ／ X).coloops_indep.subset <| by grw [contract_coloops_eq, hY]
  grw [project_closure, diff_union_self, M.subset_closure (Y ∩ X) _, inter_comm,
    inter_subset_left, ← subset_union_right]
  grw [inter_subset_left, hY, coloops_subset_ground]

@[simp] lemma eLocalConn_restrict_eq (M : Matroid α) (X Y R : Set α) :
    (M ↾ R).eLocalConn X Y = M.eLocalConn (X ∩ R) (Y ∩ R) := by
  obtain ⟨I, hI⟩ := (M ↾ R).exists_isBasis' X
  obtain ⟨J, hJ⟩ := (M ↾ R).exists_isBasis' Y
  have ⟨hI', hI'R⟩ := isBasis'_restrict_iff.1 hI
  have ⟨hJ', hJ'R⟩ := isBasis'_restrict_iff.1 hJ
  rw [hI.eLocalConn_eq hJ, hI'.eLocalConn_eq hJ',
    nullity_restrict_of_subset _ (union_subset hI'R hJ'R)]

lemma eLocalConn_restrict_univ (M : Matroid α) (X Y : Set α) :
    (M ↾ univ).eLocalConn X Y = M.eLocalConn X Y := by
  simp

lemma eLocalConn_union_left_of_subset_loops {L : Set α} (hL : L ⊆ M.loops) :
    M.eLocalConn (X ∪ L) Y = M.eLocalConn X Y := by
  rw [← eLocalConn_closure_left, closure_union_congr_right (closure_eq_loops_of_subset hL),
    union_empty, eLocalConn_closure_left]

lemma eLocalConn_union_right_of_subset_loops {L : Set α} (hL : L ⊆ M.loops) :
    M.eLocalConn X (Y ∪ L) = M.eLocalConn X Y := by
  rw [eLocalConn_comm, eLocalConn_union_left_of_subset_loops hL, eLocalConn_comm]

lemma eLocalConn_diff_left_of_subset_loops {L : Set α} (hL : L ⊆ M.loops) :
    M.eLocalConn (X \ L) Y = M.eLocalConn X Y := by
  rw [← eLocalConn_union_left_of_subset_loops hL, diff_union_self,
    eLocalConn_union_left_of_subset_loops hL]

lemma eLocalConn_diff_right_of_subset_loops {L : Set α} (hL : L ⊆ M.loops) :
    M.eLocalConn X (Y \ L) = M.eLocalConn X Y := by
  rw [eLocalConn_comm, eLocalConn_diff_left_of_subset_loops hL, eLocalConn_comm]

lemma IsRestriction.eLocalConn_eq {N : Matroid α} (hNM : N ≤r M) (X Y : Set α) :
    N.eLocalConn X Y = M.eLocalConn (X ∩ N.E) (Y ∩ N.E) := by
  rw [eLocalConn, hNM.multiConn, eLocalConn]
  simp_rw [Bool.apply_cond (f := fun X ↦ X ∩ N.E)]

lemma IsRestriction.eLocalConn_eq_of_subset {N : Matroid α} (hNM : N ≤r M)
    (hXE : X ⊆ N.E := by aesop_mat) (hYE : Y ⊆ N.E := by aesop_mat) :
    N.eLocalConn X Y = M.eLocalConn X Y := by
  rw [eLocalConn, hNM.multiConn_of_subset (by simp [hXE, hYE]), eLocalConn]

lemma eRk_add_eRk_eq_eRk_union_add_eLocalConn (M : Matroid α) (X Y : Set α) :
    M.eRk X + M.eRk Y = M.eRk (X ∪ Y) + M.eLocalConn X Y := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  obtain ⟨J, hJ⟩ := M.exists_isBasis' Y
  rw [hI.eLocalConn_eq hJ, ← hI.encard_eq_eRk, ← hJ.encard_eq_eRk, ← eRk_closure_eq,
    ← closure_union_congr_left hI.closure_eq_closure,
    ← closure_union_congr_right hJ.closure_eq_closure, eRk_closure_eq, add_comm (I ∩ J).encard,
    ← add_assoc, eRk_add_nullity_eq_encard, encard_union_add_encard_inter]

lemma eRk_inter_le_eLocalConn (M : Matroid α) (X Y : Set α) : M.eRk (X ∩ Y) ≤ M.eLocalConn X Y := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' (X ∩ Y)
  obtain ⟨IX, hIX⟩ := hI.indep.subset_isBasis'_of_subset (hI.subset.trans inter_subset_left)
  obtain ⟨IY, hIY⟩ := hI.indep.subset_isBasis'_of_subset (hI.subset.trans inter_subset_right)
  rw [← hI.encard_eq_eRk, hIX.1.eLocalConn_eq hIY.1]
  exact (encard_le_encard (subset_inter hIX.2 hIY.2)).trans le_self_add

lemma eLocalConn_mono_left {X' : Set α} (M : Matroid α) (hX : X' ⊆ X) (Y : Set α) :
    M.eLocalConn X' Y ≤ M.eLocalConn X Y := by
  obtain ⟨J, hJ⟩ := M.exists_isBasis' Y
  rw [hJ.eLocalConn_eq_nullity_project_left, hJ.eLocalConn_eq_nullity_project_left]
  apply nullity_project_mono _ hX

lemma eLocalConn_mono_right {Y' : Set α} (M : Matroid α) (X : Set α) (hY : Y' ⊆ Y) :
    M.eLocalConn X Y' ≤ M.eLocalConn X Y := by
  grw [eLocalConn_comm, eLocalConn_mono_left M hY, eLocalConn_comm]

lemma eLocalConn_mono {X' Y' : Set α} (M : Matroid α) (hX : X' ⊆ X) (hY : Y' ⊆ Y) :
    M.eLocalConn X' Y' ≤ M.eLocalConn X Y :=
  ((M.eLocalConn_mono_left hX Y').trans (M.eLocalConn_mono_right _ hY))

@[simp] lemma empty_eLocalConn (M : Matroid α) (X : Set α) : M.eLocalConn ∅ X = 0 := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [(M.empty_indep.isBasis_self.isBasis').eLocalConn_eq hI]
  simp [hI.indep]

@[simp] lemma eLocalConn_empty (M : Matroid α) (X : Set α) : M.eLocalConn X ∅ = 0 := by
  rw [eLocalConn_comm, empty_eLocalConn]

lemma eLocalConn_subset (M : Matroid α) (hXY : X ⊆ Y) : M.eLocalConn X Y = M.eRk X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [hI.eLocalConn_eq_nullity_project_right, hI.eRk_eq_encard, nullity_eq_encard]
  grw [hI.isBasis_closure_right.subset, project_loops]
  exact M.closure_mono hXY

lemma eLocalConn_eq_zero (hX : X ⊆ M.E := by aesop_mat) (hY : Y ⊆ M.E := by aesop_mat) :
    M.eLocalConn X Y = 0 ↔ M.Skew X Y := by
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  obtain ⟨J, hJ⟩ := M.exists_isBasis Y
  rw [skew_iff_closure_skew, ← eLocalConn_closure_closure, ← hI.closure_eq_closure,
    ← hJ.closure_eq_closure, ← skew_iff_closure_skew, eLocalConn_closure_closure,
    hI.indep.eLocalConn_eq hJ.indep]
  simp [hI.indep.skew_iff_disjoint_union_indep hJ.indep, disjoint_iff_inter_eq_empty]

lemma Skew.eLocalConn (hXY : M.Skew X Y) : M.eLocalConn X Y = 0 := by
  rwa [eLocalConn_eq_zero]

lemma eLocalConn_restrict_of_subset (M : Matroid α) {R : Set α} (hXR : X ⊆ R) (hYR : Y ⊆ R) :
    (M ↾ R).eLocalConn X Y = M.eLocalConn X Y := by
  rw [eLocalConn_restrict_eq, inter_eq_self_of_subset_left hXR, inter_eq_self_of_subset_left hYR]

lemma eLocalConn_delete_eq (M : Matroid α) (X Y D : Set α) :
    (M ＼ D).eLocalConn X Y = M.eLocalConn (X \ D) (Y \ D) := by
  rw [delete_eq_restrict, eLocalConn_restrict_eq, ← inter_diff_assoc, inter_diff_right_comm,
    ← inter_diff_assoc, inter_diff_right_comm, eLocalConn_inter_ground]

lemma eLocalConn_delete_eq_of_disjoint (M : Matroid α) {D : Set α} (hXD : Disjoint X D)
    (hYD : Disjoint Y D) : (M ＼ D).eLocalConn X Y = M.eLocalConn X Y := by
  rw [eLocalConn_delete_eq, hXD.sdiff_eq_left, hYD.sdiff_eq_left]

lemma eLocalConn_delete_eq_of_subset_loops {L : Set α} (hL : L ⊆ M.loops) :
    (M ＼ L).eLocalConn X Y = M.eLocalConn X Y := by
  rw [eLocalConn_delete_eq, eLocalConn_diff_left_of_subset_loops hL,
    eLocalConn_diff_right_of_subset_loops hL]

@[simp]
lemma eLocalConn_map {β : Type*} (M : Matroid α) (f : α → β) (hf) (X Y : Set β) :
    (M.map f hf).eLocalConn X Y = M.eLocalConn (f ⁻¹' X) (f ⁻¹' Y) := by
  simp [eLocalConn, multiConn_map, Bool.apply_cond]

@[simp]
lemma eLocalConn_comap {β : Type*} (M : Matroid β) (f : α → β) (X Y : Set α) :
    (M.comap f).eLocalConn X Y = M.eLocalConn (f '' X) (f '' Y) := by
  simp [eLocalConn, multiConn_comap, Bool.apply_cond]

@[simp] lemma eLocalConn_ground_eq (M : Matroid α) (X : Set α) : M.eLocalConn X M.E = M.eRk X := by
  wlog hX : X ⊆ M.E generalizing X with aux
  · rw [← eLocalConn_inter_ground_left, aux _ inter_subset_right, eRk_inter_ground]
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  obtain ⟨B, hB, hIB⟩ := hI.indep.exists_isBase_superset
  rw [hI.eLocalConn_eq hB.isBasis_ground, hI.eRk_eq_encard, inter_eq_self_of_subset_left hIB,
    union_eq_self_of_subset_left hIB, hB.indep.nullity_eq, add_zero]

@[simp] lemma ground_eLocalConn_eq (M : Matroid α) (X : Set α) : M.eLocalConn M.E X = M.eRk X := by
  rw [eLocalConn_comm, eLocalConn_ground_eq]

lemma eLocalConn_le_eRk_left (M : Matroid α) (X Y : Set α) : M.eLocalConn X Y ≤ M.eRk X := by
  grw [← eLocalConn_inter_ground_right, M.eLocalConn_mono_right X inter_subset_right,
    eLocalConn_ground_eq]

lemma eLocalConn_le_eRk_right (M : Matroid α) (X Y : Set α) : M.eLocalConn X Y ≤ M.eRk Y := by
  rw [eLocalConn_comm]
  apply eLocalConn_le_eRk_left

@[simp]
lemma eLocalConn_lt_top (M : Matroid α) [RankFinite M] (X Y : Set α) :
    M.eLocalConn X Y < ⊤ := by
  grw [eLocalConn_le_eRk_left]
  simp

@[simp]
lemma eLocalConn_ne_top (M : Matroid α) [RankFinite M] (X Y : Set α) :
    M.eLocalConn X Y ≠ ⊤ :=
  (eLocalConn_lt_top ..).ne

lemma IsLoop.eLocalConn {e : α} (he : M.IsLoop e) (X : Set α) : M.eLocalConn {e} X = 0 := by
  rw [← eLocalConn_closure_left, he.closure, loops, eLocalConn_closure_left]
  simp

@[simp]
lemma loopyOn_eLocalConn {E X Y : Set α} : (loopyOn E).eLocalConn X Y = 0 := by
  simp [eLocalConn]

lemma Indep.encard_inter_add_nullity_le_eLocalConn (hI : M.Indep I) (hIX : I ⊆ X) (hJ : M.Indep J)
    (hJY : J ⊆ Y) : (I ∩ J).encard + M.nullity (I ∪ J) ≤ M.eLocalConn X Y := by
  obtain ⟨I', hI', hII'⟩ := hI.subset_isBasis'_of_subset hIX
  obtain ⟨J', hJ', hJJ'⟩ := hJ.subset_isBasis'_of_subset hJY
  rw [hI'.eLocalConn_eq hJ']
  exact add_le_add (encard_le_encard (inter_subset_inter hII' hJJ')) <|
    M.nullity_le_of_subset <| union_subset_union hII' hJJ'

lemma IsModularPair.eLocalConn_eq_eRk_inter (h : M.IsModularPair X Y) :
    M.eLocalConn X Y = M.eRk (X ∩ Y) := by
  obtain ⟨I, hIu, hIX, hIY, hIi⟩ := h.exists_common_isBasis
  rw [hIX.eLocalConn_eq hIY, ← hIi.encard_eq_eRk, ← inter_inter_distrib_left,
    ← inter_union_distrib_left, inter_eq_self_of_subset_left hIu.subset, hIu.indep.nullity_eq,
    add_zero, inter_assoc]

lemma eLocalConn_insert_left_eq_add_one {e : α} (heX : e ∉ M.closure X)
    (heXY : e ∈ M.closure (X ∪ Y)) : M.eLocalConn (insert e X) Y = M.eLocalConn X Y + 1 := by
  have heE : e ∈ M.E := mem_ground_of_mem_closure heXY
  wlog hX : X ⊆ M.E generalizing X with aux
  · rw [← eLocalConn_inter_ground_left, insert_inter_of_mem heE,
      aux (by simpa) _ inter_subset_right, eLocalConn_inter_ground_left]
    rwa [← closure_inter_ground, union_inter_distrib_right, inter_assoc, inter_self,
      ← union_inter_distrib_right, closure_inter_ground]
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  obtain ⟨J, hJ⟩ := M.exists_isBasis' Y
  have hIe : M.IsBasis (insert e I) (insert e X) := by
    refine hI.insert_isBasis_insert ?_
    rw [hI.indep.insert_indep_iff, hI.closure_eq_closure]
    exact .inl ⟨heE, heX⟩

  rw [hI.isBasis'.eLocalConn_eq hJ, hIe.isBasis'.eLocalConn_eq hJ, insert_union]
  have heI : e ∉ I := notMem_subset (hI.subset.trans (M.subset_closure X)) heX
  by_cases heJ : e ∈ J
  · rw [insert_inter_of_mem heJ, insert_eq_of_mem (mem_union_right _ heJ),
      encard_insert_of_notMem (by simp [heI]), add_right_comm]

  rw [insert_inter_of_notMem heJ, nullity_insert_eq_add_one
    (by rwa [closure_union_congr_left hI.closure_eq_closure,
      closure_union_congr_right hJ.closure_eq_closure]) (by simp [heI, heJ]), add_assoc]

lemma eLocalConn_insert_right_eq_add_one {e : α} (heY : e ∉ M.closure Y)
    (heXY : e ∈ M.closure (X ∪ Y)) : M.eLocalConn X (insert e Y) = M.eLocalConn X Y + 1 := by
  rw [eLocalConn_comm, eLocalConn_insert_left_eq_add_one heY (by rwa [union_comm]),
    eLocalConn_comm]

lemma IsNonloop.eLocalConn_eq_zero_iff {e : α} (he : M.IsNonloop e) :
    M.eLocalConn {e} X = 0 ↔ e ∉ M.closure X := by
  rw [← M.closure_inter_ground, ← he.skew_left_iff, ← eLocalConn_inter_ground_right,
    eLocalConn_eq_zero]

lemma IsNonloop.eLocalConn_eq_one_iff {e : α} (he : M.IsNonloop e) :
    M.eLocalConn {e} X = 1 ↔ e ∈ M.closure X := by
  have h_eq (x : ℕ∞) (hx : x ≤ 1) : x = 1 ↔ x ≠ 0 := by
    induction x with
    | top => simp at hx
    | coe a =>
      simp only [Nat.cast_le_one, Nat.cast_eq_one, ne_eq, Nat.cast_eq_zero] at hx ⊢
      omega
  rw [h_eq _ (by simpa using (M.eLocalConn_le_eRk_left {e} (X ∩ M.E)).trans (M.eRk_le_encard {e})),
    not_iff_comm, he.eLocalConn_eq_zero_iff]

lemma IsNonloop.eLocalConn_eq_ite {e : α} (he : M.IsNonloop e) (X : Set α)
    [Decidable (e ∈ M.closure X)] :
    M.eLocalConn {e} X = if e ∈ M.closure X then 1 else 0 := by
  split_ifs <;>
  simpa [he.eLocalConn_eq_one_iff, he.eLocalConn_eq_zero_iff]

lemma IsCircuit.eLocalConn_subset_compl {C : Set α} (hC : M.IsCircuit C) (hI : I.Nonempty)
    (hIC : I ⊂ C) : M.eLocalConn I (C \ I) = 1 := by
  obtain ⟨e, heC, heI⟩ := exists_of_ssubset hIC
  have hi' : C \ I ⊂ C := by simpa [inter_eq_self_of_subset_right hIC.subset]
  rw [(hC.ssubset_indep hIC).isBasis_self.eLocalConn_eq (hC.ssubset_indep hi').isBasis_self,
    disjoint_sdiff_right.inter_eq, encard_empty, zero_add, union_diff_cancel hIC.subset,
    hC.nullity_eq]

lemma IsRkFinite.isModularPair_iff_eLocalConn_eq_eRk_inter (hX : M.IsRkFinite X) (Y : Set α)
    (hXE : X ⊆ M.E := by aesop_mat) (hYE : Y ⊆ M.E := by aesop_mat) :
    M.IsModularPair X Y ↔ M.eLocalConn X Y = M.eRk (X ∩ Y) := by
  refine ⟨fun h ↦ h.eLocalConn_eq_eRk_inter, fun h ↦ ?_⟩
  obtain ⟨Ii, hIi⟩ := M.exists_isBasis (X ∩ Y)
  obtain ⟨IX, hIX, hIX'⟩ := hIi.exists_isBasis_inter_eq_of_superset inter_subset_left
  obtain ⟨IY, hIY, hIY'⟩ := hIi.exists_isBasis_inter_eq_of_superset inter_subset_right

  have h_inter : Ii = IX ∩ IY
  · exact hIi.eq_of_subset_indep (hIX.indep.inter_right _)
      (subset_inter (by simp [← hIX']) (by simp [← hIY']))
      (inter_subset_inter hIX.subset hIY.subset)

  rw [hIX.eLocalConn_eq hIY, ← h_inter, hIi.encard_eq_eRk, ← add_zero (a := M.eRk _), add_assoc,
    zero_add, WithTop.add_left_inj hX.inter_right.eRk_lt_top.ne, nullity_eq_zero] at h

  exact h.isModularPair_of_union.of_isBasis_of_isBasis hIX hIY

/-- For finite matroids, this is another rearrangement of the formula in
`Matroid.eRk_add_eRk_eq_eRk_union_add_eLocalConn`.
For infinite matroids it needs a separate proof. -/
lemma eLocalConn_add_eRelRk_union_eq_eRk (M : Matroid α) (X Y : Set α) :
    M.eLocalConn X Y + M.eRelRk Y (X ∪ Y) = M.eRk X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  have hcl : (M.project Y).closure X = (M.project Y).closure I := by
    simp [closure_union_congr_left hI.closure_eq_closure]
  rw [hI.eLocalConn_eq_nullity_project_right, hI.eRk_eq_encard, ← eRelRk_eq_union_right,
    eRelRk_eq_eRk_project, ← eRk_closure_eq, hcl, eRk_closure_eq, add_comm,
    eRk_add_nullity_eq_encard]

lemma IsHyperplane.eLocalConn_add_one_eq {H X : Set α} (hH : M.IsHyperplane H) (hXH : ¬ (X ⊆ H))
    (hXE : X ⊆ M.E := by aesop_mat) : M.eLocalConn X H + 1 = M.eRk X := by
  rw [← M.eLocalConn_add_eRelRk_union_eq_eRk X H, ← eRelRk_closure_right,
    (hH.spanning_of_ssuperset (show H ⊂ X ∪ H by simpa)).closure_eq, hH.eRelRk_eq_one]

lemma eLocalConn_le_add_eRelRk_left (M : Matroid α) (hXY : X ⊆ Y) (Z : Set α) :
    M.eLocalConn Y Z ≤ M.eLocalConn X Z + M.eRelRk X Y := by
  obtain ⟨IX, hIX⟩ := M.exists_isBasis' X
  obtain ⟨J, hJ, rfl⟩ := hIX.exists_isBasis'_inter_eq_of_superset hXY
  rw [hJ.eLocalConn_eq_nullity_project_right, hIX.eLocalConn_eq_nullity_project_right,
    hJ.eRelRk_eq_encard_diff_of_subset hXY hIX]
  nth_grw 1 [← inter_union_diff J X, nullity_union_le_nullity_add_encard_diff,
    sdiff_eq_left.2 disjoint_sdiff_inter]

lemma eLocalConn_le_add_eRelRk_right (M : Matroid α) (hXY : X ⊆ Y) (Z : Set α) :
    M.eLocalConn Z Y ≤ M.eLocalConn Z X + M.eRelRk X Y := by
  grw [eLocalConn_comm, eLocalConn_le_add_eRelRk_left _ hXY, eLocalConn_comm]

lemma eLocalConn_union_left_le (M : Matroid α) (X Y A : Set α) :
    M.eLocalConn (X ∪ A) Y ≤ M.eLocalConn X Y + M.eRk A := by
  grw [M.eLocalConn_le_add_eRelRk_left subset_union_left, union_comm, ← eRelRk_eq_union_right,
    eRelRk_le_eRk]

lemma eLocalConn_union_right_le (M : Matroid α) (X Y A : Set α) :
    M.eLocalConn X (Y ∪ A) ≤ M.eLocalConn X Y + M.eRk A := by
  grw [eLocalConn_comm, eLocalConn_union_left_le, eLocalConn_comm]

lemma eLocalConn_insert_left_le (M : Matroid α) (X Y : Set α) (e : α) :
    M.eLocalConn (insert e X) Y ≤ M.eLocalConn X Y + 1 := by
  grw [← union_singleton, eLocalConn_union_left_le, eRk_le_encard, encard_singleton]

lemma eLocalConn_insert_right_le (M : Matroid α) (X Y : Set α) (e : α) :
    M.eLocalConn X (insert e Y) ≤ M.eLocalConn X Y + 1 := by
  grw [← union_singleton, eLocalConn_union_right_le, eRk_le_encard, encard_singleton]

@[simp]
lemma removeLoops_eLocalConn (M : Matroid α) : M.removeLoops.eLocalConn = M.eLocalConn := by
  ext _ _
  rw [removeLoops_eq_restrict, eLocalConn_restrict_eq, ← eLocalConn_closure_closure]
  simp

/-- A submodularity-like equality with an explicit slack term in the form of local connectivity. -/
lemma eRk_union_right_add_eRk_union_right_eq (M : Matroid α) (X Y C : Set α) :
    M.eRk (X ∪ C) + M.eRk (Y ∪ C) = M.eRk (X ∪ Y ∪ C) + M.eRk C + (M.project C).eLocalConn X Y := by
  wlog hC : M.Indep C generalizing C with aux
  · obtain ⟨I, hI⟩ := M.exists_isBasis' C
    rw [← eRk_closure_eq (X := _ ∪ C), ← eRk_closure_eq (X := _ ∪ C), ← eRk_closure_eq (X := _ ∪ C)]
    simp_rw [← closure_union_congr_right hI.closure_eq_closure, hI.project_eq_project,
      eRk_closure_eq, ← hI.eRk_eq_eRk]
    exact aux _ hI.indep
  obtain ⟨I, hI⟩ := (M.project C).exists_isBasis' X
  obtain ⟨J, hJ⟩ := (M.project C).exists_isBasis' Y
  rw [hI.eLocalConn_eq hJ, hC.eRk_eq_encard]
  simp_rw [hC.project_isBasis'_iff, union_comm C] at hI hJ
  have hdj := (hI.2.union_right hJ.2)
  rw [hC.nullity_project_of_disjoint hdj, union_comm C]
  rw [hI.1.eRk_eq_encard, hJ.1.eRk_eq_encard, ← eRk_closure_eq, union_union_distrib_right,
    ← closure_union_congr_left hI.1.closure_eq_closure,
    ← closure_union_congr_right hJ.1.closure_eq_closure, ← union_union_distrib_right,
    eRk_closure_eq, ← encard_union_add_encard_inter, ← union_union_distrib_right,
    ← inter_union_distrib_right,
    encard_union_eq (hdj.symm.mono_left (show I ∩ J ⊆ I ∪ J by tauto_set))]
  simp_rw [← add_assoc, add_comm _ (nullity _ _), ← add_assoc, add_comm (nullity ..) (eRk ..),
    eRk_add_nullity_eq_encard, add_assoc, add_comm _ C.encard]

/-- A version of submodularity with an explicit slack term. -/
lemma eRk_add_eRk_eq_eRk_union_add_eRk_inter_add_eLocalConn (M : Matroid α) (X Y : Set α) :
    M.eRk X + M.eRk Y = M.eRk (X ∪ Y) + M.eRk (X ∩ Y) + (M.project (X ∩ Y)).eLocalConn X Y := by
  convert M.eRk_union_right_add_eRk_union_right_eq X Y (X ∩ Y) using 4 <;> tauto_set

end Local


section Global

variable {I X : Set α}

/-- The `ℕ∞`-valued connectivity of a set `X` to its complement, traditionally written as `λ (X)`.
For a `ℕ`-valued version, see `Matroid.conn`. -/
noncomputable def eConn (M : Matroid α) (X : Set α) : ℕ∞ := M.eLocalConn X (M.E \ X)

lemma eConn_eq_eLocalConn (M : Matroid α) (X : Set α) : M.eConn X = M.eLocalConn X (M.E \ X) := rfl

@[simp] lemma eConn_inter_ground (M : Matroid α) (X : Set α) :  M.eConn (X ∩ M.E) = M.eConn X := by
  rw [eConn, eLocalConn_inter_ground_left, eConn, diff_inter_self_eq_diff]

@[simp]
lemma eConn_empty (M : Matroid α) : M.eConn ∅ = 0 := by
  simp [eConn]

@[simp]
lemma loopyOn_eConn (E X : Set α) : (loopyOn E).eConn X = 0 := by
  simp [eConn]

@[simp]
lemma eConn_ground (M : Matroid α) : M.eConn M.E = 0 := by
  simp [eConn]

lemma IsBasis'.eConn_eq (hIX : M.IsBasis' I X) (hJX : M.IsBasis' J (M.E \ X)) :
    M.eConn X = M.nullity (I ∪ J) := by
  rw [eConn_eq_eLocalConn, hIX.eLocalConn_eq_of_disjoint hJX disjoint_sdiff_right]

lemma IsBasis.eConn_eq (hIX : M.IsBasis I X) (hJX : M.IsBasis J (M.E \ X)) :
    M.eConn X = M.nullity (I ∪ J) :=
  hIX.isBasis'.eConn_eq hJX.isBasis'

lemma IsBasis.eConn_eq' (hIX : M.IsBasis I X) (hJX : M.IsBasis J Xᶜ) :
    M.eConn X = M.nullity (I ∪ J) := by
  rw [hIX.eConn_eq (hJX.isBasis_subset ?_ (diff_subset_compl ..))]
  rw [subset_diff, ← subset_compl_iff_disjoint_right]
  exact ⟨hJX.indep.subset_ground, hJX.subset⟩

lemma eConn_eq_eLocalConn' (M : Matroid α) (X : Set α) :
    M.eConn X = M.eLocalConn (X ∩ M.E) (M.E \ X) := by
  rw [← eConn_inter_ground, eConn_eq_eLocalConn, diff_inter_self_eq_diff, inter_comm]

@[simp]
lemma removeLoops_eConn (M : Matroid α) : M.removeLoops.eConn = M.eConn := by
  ext X
  rw [eConn, removeLoops_eLocalConn, eConn, ← eLocalConn_closure_right, removeLoops_ground_eq,
    diff_eq_compl_inter, closure_inter_setOf_isNonloop_eq, ← closure_inter_ground,
    ← diff_eq_compl_inter, eLocalConn_closure_right]

lemma eConn_union_of_subset_loops {L : Set α} (hL : L ⊆ M.loops) :
    M.eConn (X ∪ L) = M.eConn X := by
  rw [← removeLoops_eConn, ← eConn_inter_ground, removeLoops_ground_eq, setOf_isNonloop_eq,
    show (X ∪ L) ∩ (M.E \ M.loops) = X ∩ (M.E \ M.loops) by tauto_set,
    ← setOf_isNonloop_eq, ← removeLoops_ground_eq, eConn_inter_ground]

lemma eConn_diff_of_subset_loops {L : Set α} (hL : L ⊆ M.loops) :
    M.eConn (X \ L) = M.eConn X := by
  rw [← eConn_union_of_subset_loops hL, diff_union_self, eConn_union_of_subset_loops hL]

lemma Indep.nullity_union_le_eConn (hI : M.Indep I) (hJ : M.Indep J) (hIX : I ⊆ X)
    (hJX : Disjoint J X) : M.nullity (I ∪ J) ≤ M.eConn X := by
  rw [eConn_eq_eLocalConn]
  refine le_trans ?_ <| hI.encard_inter_add_nullity_le_eLocalConn hIX hJ (Y := M.E \ X) ?_
  · simp [(hJX.symm.mono_left hIX).inter_eq]
  rwa [subset_diff, and_iff_right hJ.subset_ground]

@[simp]
lemma eConn_restrict_univ_eq (M : Matroid α) (X : Set α) : (M ↾ univ).eConn X = M.eConn X := by
  rw [← removeLoops_eConn, ← M.removeLoops_eConn, restrict_univ_removeLoops_eq]

@[simp]
lemma eConn_corestrict_univ_eq (M : Matroid α) (X : Set α) : (M✶ ↾ univ)✶.eConn X = M.eConn X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  obtain ⟨J, hJ⟩ := M.exists_isBasis (M.E \ X)
  have hJ' : (M✶ ↾ univ)✶.IsBasis (J ∪ (Xᶜ \ M.E)) ((M✶ ↾ univ)✶.E \ X) := by
    rwa [dual_ground, restrict_ground_eq, ← compl_eq_univ_diff, corestrict_univ_isBasis_iff,
      union_subset_iff, and_iff_left subset_union_right, and_iff_left diff_subset,
      and_iff_left <| hJ.subset.trans <| diff_subset_compl .., ← diff_eq_compl_inter,
      union_inter_distrib_right, disjoint_sdiff_left.inter_eq, union_empty,
      inter_eq_self_of_subset_left hJ.indep.subset_ground]
  rw [hI.corestrict_univ_isBasis.isBasis'.eConn_eq hJ'.isBasis', hI.eConn_eq hJ.isBasis',
    nullity_corestrict_univ_eq_nullity_inter, union_right_comm, union_assoc, union_assoc,
    ← union_diff_distrib, ← union_assoc, union_inter_distrib_right, disjoint_sdiff_left.inter_eq,
    union_empty,
    inter_eq_self_of_subset_left (union_subset hI.indep.subset_ground hJ.indep.subset_ground)]

@[simp]
lemma eConn_compl (M : Matroid α) (X : Set α) : M.eConn (M.E \ X) = M.eConn X := by
  rw [eq_comm, ← eConn_inter_ground, eConn, diff_inter_self_eq_diff, eConn, eLocalConn_comm,
    inter_comm]
  simp

/-- A version of `eConn_compl` where `compl` really means complementation in the universe. -/
@[simp]
lemma eConn_compl' (M : Matroid α) (X : Set α) : M.eConn Xᶜ = M.eConn X := by
  rw [← eConn_restrict_univ_eq, compl_eq_univ_diff, ← M.eConn_restrict_univ_eq,
    eq_comm, ← eConn_compl, restrict_ground_eq]

lemma IsBasis'.eConn_eq_nullity_contract (hI : M.IsBasis' I X) : M.eConn X =
    (M ／ (M.E \ X)).nullity I := by
  rw [eConn_eq_eLocalConn, hI.eLocalConn_eq_nullity_project_right,
    nullity_project_eq_nullity_contract]

lemma IsBasis.eConn_eq_nullity_contract (hI : M.IsBasis I X) : M.eConn X =
    (M ／ (M.E \ X)).nullity I :=
  hI.isBasis'.eConn_eq_nullity_contract

/-- Connectivity is self-dual. -/
@[simp]
lemma eConn_dual (M : Matroid α) (X : Set α) : M✶.eConn X = M.eConn X := by
  wlog h : OnUniv M with aux
  · rw [← eConn_corestrict_univ_eq, dual_dual, eq_comm, ← eConn_restrict_univ_eq, aux _ _ ⟨rfl⟩]
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  obtain ⟨J, hJ⟩ := M.exists_isBasis (M.E \ X)
  obtain ⟨B, hB, rfl⟩ := hI.exists_isBasis_inter_eq_of_superset <| subset_union_left (t := J)
  have hsp : M.Spanning (X ∪ J) := by
    simp [spanning_iff_closure_eq, closure_union_congr_right hJ.closure_eq_closure]
  have hBdual := (hB.isBase_of_spanning hsp).compl_inter_isBasis_of_inter_isBasis hI
  rw [diff_inter_diff, union_comm, ← diff_diff] at hBdual
  obtain ⟨B', hB', rfl⟩ := hJ.exists_isBase
  have hB'dual : M✶.IsBasis (B'ᶜ ∩ X) X := by
    simpa [← compl_eq_univ_diff] using hB'.compl_inter_isBasis_of_inter_isBasis hJ
  have hBss := hB.subset
  have hgd := OnUniv.ground_diff_eq M X
  rw [ hB'dual.eConn_eq hBdual, hI.eConn_eq hJ, OnUniv.ground_diff_eq,
    (hB.isBasis_subset (by tauto_set) (by tauto_set)).nullity_eq,
    (hB'.compl_isBase_dual.isBasis_ground.isBasis_subset (by tauto_set) (by simp)).nullity_eq,
    OnUniv.ground_diff_eq]
  exact congr_arg _ <| by tauto_set

lemma eConn_union_of_subset_coloops {L : Set α} (hL : L ⊆ M.coloops) :
    M.eConn (X ∪ L) = M.eConn X := by
  rw [← eConn_dual, eConn_union_of_subset_loops hL, eConn_dual]

lemma eConn_diff_of_subset_coloops {L : Set α} (hL : L ⊆ M.coloops) :
    M.eConn (X \ L) = M.eConn X := by
  rw [← eConn_dual, eConn_diff_of_subset_loops hL, eConn_dual]

lemma eConn_delete_eq_of_subset_loops {L : Set α} (hL : L ⊆ M.loops) :
    (M ＼ L).eConn X = M.eConn X := by
  rw [eConn_eq_eLocalConn, eLocalConn_delete_eq_of_subset_loops hL, delete_ground, diff_diff_comm,
    eLocalConn_diff_right_of_subset_loops hL, eConn_eq_eLocalConn]

lemma eConn_delete_eq_diff_of_subset_loops {L : Set α} (hL : L ⊆ M.loops) :
    (M ＼ L).eConn X = M.eConn (X \ L) := by
  rw [eConn_delete_eq_of_subset_loops hL, eConn_diff_of_subset_loops hL]

lemma eConn_contract_of_subset_coloops {L : Set α} (hL : L ⊆ M.coloops) :
    (M ／ L).eConn X = M.eConn X := by
  rw [← eConn_dual, dual_contract, eConn_delete_eq_of_subset_loops hL, eConn_dual]

lemma eConn_contract_eq_diff_of_subset_coloops {L : Set α} (hL : L ⊆ M.coloops) :
    (M ／ L).eConn X = M.eConn (X \ L) := by
  rw [← eConn_dual, dual_contract, eConn_delete_eq_diff_of_subset_loops hL, eConn_dual]

@[simp]
lemma eConn_loops (M : Matroid α) : M.eConn M.loops = 0 := by
  rw [← eConn_diff_of_subset_loops rfl.subset]
  simp

@[simp]
lemma eConn_coloops (M : Matroid α) : M.eConn M.coloops = 0 := by
  rw [← eConn_dual, ← dual_loops, eConn_loops]

@[simp]
lemma eConn_union_loops (M : Matroid α) (X : Set α) : M.eConn (X ∪ M.loops) = M.eConn X :=
  eConn_union_of_subset_loops rfl.subset

@[simp]
lemma eConn_union_coloops (M : Matroid α) (X : Set α) : M.eConn (X ∪ M.coloops) = M.eConn X :=
  eConn_union_of_subset_coloops rfl.subset

lemma eConn_subset_loops (h : X ⊆ M.loops) : M.eConn X = 0 := by
  rw [← empty_union X, eConn_union_of_subset_loops h, eConn_empty]

lemma eConn_subset_coloops (h : X ⊆ M.coloops) : M.eConn X = 0 := by
  rw [← empty_union X, eConn_union_of_subset_coloops h, eConn_empty]

lemma eConn_of_subset_loops_union_coloops (h : X ⊆ M.loops ∪ M.coloops) :
    M.eConn X = 0 := by
  rw [← diff_union_inter X M.coloops, eConn_union_of_subset_coloops inter_subset_right,
    eConn_subset_loops]
  rwa [diff_subset_iff, union_comm]

@[simp]
lemma uniqueBaseon_eConn (E B X : Set α) : (uniqueBaseOn B E).eConn X = 0 := by
  have hrw : X ∩ (uniqueBaseOn B E).E =
    ((X ∩ (uniqueBaseOn B E).loops) ∪ (X ∩ (uniqueBaseOn B E).coloops)) := by
    simp only [uniqueBaseOn_ground, uniqueBaseOn_loops_eq, uniqueBaseOn_coloops_eq']
    tauto_set
  rw [← eConn_inter_ground, hrw, eConn_union_of_subset_coloops inter_subset_right,
    eConn_subset_loops inter_subset_right]

lemma eRk_add_eRk_compl_eq (M : Matroid α) (X : Set α) :
    M.eRk X + M.eRk (M.E \ X) = M.eRank + M.eConn X := by
  rw [eConn_eq_eLocalConn, eRk_add_eRk_eq_eRk_union_add_eLocalConn, union_diff_self,
    ← eRk_inter_ground, inter_eq_self_of_subset_right subset_union_right, eRank_def]

lemma eConn_le_eRk (M : Matroid α) (X : Set α) : M.eConn X ≤ M.eRk X :=
  eLocalConn_le_eRk_left ..

lemma eConn_le_eRk_dual (M : Matroid α) (X : Set α) : M.eConn X ≤ M✶.eRk X :=
  by grw [← eConn_dual, eConn_le_eRk]

lemma eConn_le_encard (M : Matroid α) (X : Set α) : M.eConn X ≤ X.encard :=
  (eConn_le_eRk ..).trans (eRk_le_encard ..)

@[simp]
lemma freeOn_eConn (E X : Set α) : (freeOn E).eConn X = 0 := by
  rw [← eConn_dual, freeOn_dual_eq, loopyOn_eConn]

/-- The slack term in the inequality `λ(X) ≤ r(X)` is co-nullity -/
lemma eConn_add_nullity_dual_eq_eRk (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    M.eConn X + M✶.nullity X = M.eRk X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  rw [eConn_eq_eLocalConn, hI.eLocalConn_eq_nullity_project_right, ← hI.encard_eq_eRk,
    M✶.nullity_eq_eRank_restrict_dual, ← delete_compl, dual_delete_dual, dual_ground,
    ← eRk_ground, contract_ground, diff_diff_cancel_left hX, ← eRk_closure_eq,
    ← contract_closure_congr hI.closure_eq_closure, eRk_closure_eq,
    nullity_project_eq_nullity_contract, add_comm, eRk_add_nullity_eq_encard]

lemma eConn_add_nullity_dual_eq_eRk' (M : Matroid α) (X : Set α) :
    M.eConn X + M✶.nullity X = M.eRk X + (X \ M.E).encard := by
  rw [← eRk_inter_ground, ← M.eConn_add_nullity_dual_eq_eRk (X ∩ M.E), eConn_inter_ground,
    nullity_eq_nullity_inter_ground_add_encard_diff, dual_ground, add_assoc]

/-- The slack term in the inequality `λ(X) ≤ r✶(X)` is nullity -/
lemma eConn_add_nullity_eq_eRk_dual (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    M.eConn X + M.nullity X = M✶.eRk X := by
  simp [← M✶.eConn_add_nullity_dual_eq_eRk X hX]

lemma Indep.eConn_eq_eRk_dual (hI : M.Indep I) : M.eConn I = M✶.eRk I := by
  rw [← eConn_add_nullity_eq_eRk_dual _ I hI.subset_ground, hI.nullity_eq, add_zero]

lemma eConn_add_eRank_eq (M : Matroid α) : M.eConn X + M.eRank = M.eRk X + M.eRk (M.E \ X) := by
  wlog hXE : X ⊆ M.E generalizing X with aux
  · rw [← eConn_inter_ground, aux inter_subset_right, eRk_inter_ground, diff_inter_self_eq_diff]
  rw [M.eRk_add_eRk_eq_eRk_union_add_eLocalConn, ← eConn_eq_eLocalConn, union_diff_cancel hXE,
    eRk_ground, add_comm]

lemma Indep.eConn_eq_of_compl_indep (hI : M.Indep I) (hI' : M.Indep (M.E \ I)) :
    M.eConn I = M✶.eRank := by
  rw [hI.eConn_eq_eRk_dual, ← hI'.coindep.compl_spanning.eRk_eq, dual_ground,
    diff_diff_cancel_left hI.subset_ground]

lemma eConn_union_eq_of_subset_loops {Y : Set α} (X : Set α) (hY : Y ⊆ M.loops) :
    M.eConn (X ∪ Y) = M.eConn X := by
  rw [eConn_eq_eLocalConn, ← diff_diff, ← eLocalConn_closure_closure, ← union_empty (a := _ \ _),
    ← closure_union_congr_right (closure_eq_loops_of_subset hY), diff_union_self,
    closure_union_congr_right (closure_eq_loops_of_subset hY),
    closure_union_congr_right (closure_eq_loops_of_subset hY), union_empty, union_empty,
    eLocalConn_closure_closure, ← eConn_eq_eLocalConn]

lemma eConn_union_eq_of_subset_coloops {Y : Set α} (X : Set α) (hY : Y ⊆ M.coloops) :
    M.eConn (X ∪ Y) = M.eConn X := by
  rw [← eConn_dual, eConn_union_eq_of_subset_loops _ (by simpa), eConn_dual]

/-- The slack term in the inequality `λ(X) ≤ |X|` is the sum of the nullity and conullity of `X`.
This needs `X ⊆ M.E`, for instance in the case where `X` is a single non-element. -/
lemma eConn_add_nullity_add_nullity_dual (M : Matroid α) (X : Set α)
  (hX : X ⊆ M.E := by aesop_mat) :
    M.eConn X + M.nullity X + M✶.nullity X = X.encard := by
  rw [eConn_add_nullity_eq_eRk_dual _ _ hX, eRk_add_nullity_eq_encard]

lemma eConn_add_nullity_add_nullity_dual' (M : Matroid α) (X : Set α) :
    M.eConn X + M.nullity X + M✶.nullity X = X.encard + (X \ M.E).encard := by
  rw [add_right_comm, eConn_add_nullity_dual_eq_eRk', add_right_comm, eRk_add_nullity_eq_encard]

lemma eConn_eq_eRk_iff (hX : M.eConn X ≠ ⊤) (hXE : X ⊆ M.E := by aesop_mat) :
    M.eConn X = M.eRk X ↔ M✶.Indep X := by
  rw [← eConn_add_nullity_dual_eq_eRk _ _ hXE, eq_comm, ENat.add_eq_left_iff, or_iff_right hX,
    nullity_eq_zero]

lemma IsRkFinite.eConn_eq_eRk_iff (h : M.IsRkFinite X) (hXE : X ⊆ M.E := by aesop_mat) :
    M.eConn X = M.eRk X ↔ M✶.Indep X :=
  Matroid.eConn_eq_eRk_iff (fun h' ↦ (h.eRk_lt_top.trans_eq h'.symm).not_ge (M.eConn_le_eRk X)) hXE

lemma eConn_eq_encard_iff' (hX : M.eConn X ≠ ⊤) :
    M.eConn X = X.encard ↔ M.Indep X ∧ M.Coindep X := by
  wlog hXE : X ⊆ M.E generalizing X with aux
  · refine iff_of_false (fun h_eq ↦ hXE ?_) fun h ↦ hXE h.1.subset_ground
    have hle := h_eq.symm.le
    grw [← eConn_inter_ground, ← encard_diff_add_encard_inter X M.E, eConn_le_encard,
      ENat.add_le_right_iff, encard_eq_zero, diff_eq_empty, or_iff_right hXE,
      ← top_le_iff, encard_le_encard inter_subset_left, ← h_eq, top_le_iff] at hle
    contradiction
  simp [← M.eConn_add_nullity_add_nullity_dual X, add_assoc, hX]

lemma eConn_eq_encard_iff (hX : X.Finite) : M.eConn X = X.encard ↔ M.Indep X ∧ M.Coindep X := by
  apply eConn_eq_encard_iff'
  grw [← lt_top_iff_ne_top, eConn_le_encard]
  exact hX.encard_lt_top

lemma eRk_add_eRk_dual_eq (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    M.eRk X + M✶.eRk X = M.eConn X + X.encard := by
  rw [← M.eRk_add_nullity_eq_encard X, add_comm _ (nullity ..), ← add_assoc,
    M.eConn_add_nullity_eq_eRk_dual X, add_comm]

lemma Indep.eConn_eq (hI : M.Indep I) : M.eConn I = M✶.eRk I := by
  rw [← M✶.eConn_add_nullity_dual_eq_eRk _ hI.subset_ground, dual_dual, hI.nullity_eq, add_zero,
    eConn_dual]

lemma Indep.eConn_eq_zero_iff (hI : M.Indep I) : M.eConn I = 0 ↔ I ⊆ M.coloops := by
  rw [coloops, ← eRk_eq_zero_iff, hI.eConn_eq]

lemma Coindep.eConn_eq_zero_iff (hI : M.Coindep I) : M.eConn I = 0 ↔ I ⊆ M.loops := by
  rw [← eConn_dual, Indep.eConn_eq_zero_iff hI, dual_coloops]

lemma Coindep.eConn_eq (hI : M.Coindep I) : M.eConn I = M.eRk I := by
  simpa using Indep.eConn_eq hI

lemma Spanning.eConn_eq (h : M.Spanning X) : M.eConn X = M.eRk (M.E \ X) := by
  rw [← h.compl_coindep.eConn_eq, eConn_compl]

lemma IsHyperplane.eConn_add_one_eq {H : Set α} (hH : M.IsHyperplane H) :
    M.eConn H + 1 = M.eRk (M.E \ H) := by
  rw [← eConn_compl, ← M.eConn_add_nullity_dual_eq_eRk (M.E \ H), nullity_compl_dual_eq,
    hH.eRelRk_eq_one]

lemma IsCocircuit.eConn_add_one_eq {C : Set α} (hC : M.IsCocircuit C) :
    M.eConn C + 1 = M.eRk C := by
  rw [← eConn_compl, hC.compl_isHyperplane.eConn_add_one_eq, diff_diff_cancel_left hC.subset_ground]

lemma IsCircuit.eConn_add_one_eq {C : Set α} (hC : M.IsCircuit C) :
    M.eConn C + 1 = M✶.eRk C := by
  rw [← hC.isCocircuit.eConn_add_one_eq, eConn_dual]

lemma eConn_eq_eRk_compl_iff (hX : M.eConn X ≠ ⊤) (hXE : X ⊆ M.E := by aesop_mat) :
    M.eConn X = M.eRk (M.E \ X) ↔ M.Spanning X := by
  rw [← eConn_compl, eConn_eq_eRk_iff (by simpa), ← coindep_def, ← spanning_iff_compl_coindep]

lemma Indep.eConn_eq_encard_of_coindep (hI : M.Indep I) (hI' : M.Coindep I) :
    M.eConn I = I.encard := by
  rw [hI.eConn_eq, hI'.indep.eRk_eq_encard]

lemma eConn_lt_encard_iff' (hX : M.eConn X ≠ ⊤) :
    M.eConn X < X.encard ↔ ¬ M.Indep X ∨ ¬ M.Coindep X := by
  rw [lt_iff_le_and_ne, and_iff_right (eConn_le_encard ..), Ne, eConn_eq_encard_iff' hX,
    Classical.not_and_iff_not_or_not]

lemma eConn_lt_encard_iff (hX : M.eConn X ≠ ⊤) (hXE : X ⊆ M.E := by aesop_mat) :
    M.eConn X < X.encard ↔ M.Dep X ∨ M✶.Dep X := by
  rw [eConn_lt_encard_iff' hX, coindep_def, not_indep_iff, not_indep_iff]

lemma eConn_lt_encard_compl_iff (hX : M.eConn X ≠ ⊤) (hXE : X ⊆ M.E := by aesop_mat) :
    M.eConn X < (M.E \ X).encard ↔ ¬ M✶.Spanning X ∨ ¬ M.Spanning X := by
  rw [← eConn_compl, eConn_lt_encard_iff' (by simpa), coindep_iff_compl_spanning,
    diff_diff_cancel_left hXE, ← dual_coindep_iff, ← dual_ground, ← spanning_iff_compl_coindep]

lemma eConn_lt_eRk_iff (hX : M.eConn X ≠ ⊤) (hXE : X ⊆ M.E := by aesop_mat) :
    M.eConn X < M.eRk X ↔ ¬ M.Spanning (M.E \ X) := by
  rw [lt_iff_le_and_ne, and_iff_right (eConn_le_eRk ..), Ne, eConn_eq_eRk_iff hX, ← coindep_def,
    coindep_iff_compl_spanning]

lemma eConn_lt_eRk_compl_iff (hX : M.eConn X ≠ ⊤) (hXE : X ⊆ M.E := by aesop_mat) :
    M.eConn X < M.eRk (M.E \ X) ↔ ¬ M.Spanning X := by
  rw [← eConn_compl, eConn_lt_eRk_iff (by simpa), diff_diff_cancel_left hXE]

@[simp]
lemma eConn_lt_top (M : Matroid α) [RankFinite M] (X : Set α) : M.eConn X < ⊤ :=
  eLocalConn_lt_top ..

@[simp]
lemma eConn_ne_top (M : Matroid α) [RankFinite M] (X : Set α) : M.eConn X ≠ ⊤ :=
  (eLocalConn_lt_top ..).ne

@[simp]
lemma eConn_lt_top' (M : Matroid α) [RankFinite M✶] (X : Set α) : M.eConn X < ⊤ := by
  rw [← eConn_dual]
  apply eConn_lt_top

@[simp]
lemma eConn_ne_top' (M : Matroid α) [RankFinite M✶] (X : Set α) : M.eConn X ≠ ⊤ :=
  (eConn_lt_top' ..).ne

lemma eConn_le_of_subset_of_subset_closure {Y : Set α} (M : Matroid α)
    (hXY : X ⊆ Y) (hYX : Y ⊆ M.closure X) : M.eConn Y ≤ M.eConn X := by
  grw [eConn_eq_eLocalConn, eLocalConn_mono_left _ hYX, eLocalConn_closure_left,
    eLocalConn_mono_right _ _ (diff_subset_diff_right hXY), eConn_eq_eLocalConn]

lemma eConn_closure_le (M : Matroid α) (X : Set α) : M.eConn (M.closure X) ≤ M.eConn X := by
  wlog hX : X ⊆ M.E generalizing X with aux
  · grw [← M.closure_inter_ground X, aux _ inter_subset_right, eConn_inter_ground]
  grw [eConn_eq_eLocalConn, eLocalConn_closure_left, eConn_eq_eLocalConn,
    M.eLocalConn_mono_right X (diff_subset_diff_right (M.subset_closure X))]

@[simp]
lemma eConn_disjointSum_left_eq {M₁ M₂ : Matroid α} (hdj : Disjoint M₁.E M₂.E) :
    (M₁.disjointSum M₂ hdj).eConn M₁.E = 0 := by
  rw [eConn, eLocalConn_eq_zero (by simp) (by tauto_set)]
  simp [hdj.sdiff_eq_right, skew_disjointSum]

@[simp]
lemma eConn_disjointSum_right_eq {M₁ M₂ : Matroid α} (hdj : Disjoint M₁.E M₂.E) :
    (M₁.disjointSum M₂ hdj).eConn M₂.E = 0 := by
  rw [disjointSum_comm]
  simp

lemma eConn_eq_zero_of_subset_loops {L : Set α} (hL : L ⊆ M.loops) : M.eConn L = 0 := by
  rw [eConn_eq_eLocalConn, ← eLocalConn_diff_left_of_subset_loops hL]
  simp

lemma eConn_eq_zero_of_subset_coloops {L : Set α} (hL : L ⊆ M.coloops) : M.eConn L = 0 := by
  rw [← eConn_dual]
  exact eConn_eq_zero_of_subset_loops <| by simpa

lemma IsLoop.eConn_eq_zero {e : α} (he : M.IsLoop e) : M.eConn {e} = 0 :=
  eConn_eq_zero_of_subset_loops <| by simpa

lemma IsColoop.eConn_eq_zero {e : α} (he : M.IsColoop e) : M.eConn {e} = 0 :=
  eConn_eq_zero_of_subset_coloops <| by simpa

lemma eConn_singleton_eq_zero_iff {e : α} (heM : e ∈ M.E) :
    M.eConn {e} = 0 ↔ M.IsLoop e ∨ M.IsColoop e := by
  rw [iff_def, or_imp, and_iff_right IsLoop.eConn_eq_zero, and_iff_left IsColoop.eConn_eq_zero]
  intro h
  obtain he | he := M.isLoop_or_isNonloop e
  · exact .inl he
  rw [he.indep.eConn_eq_zero_iff, singleton_subset_iff] at h
  exact .inr h

-- the next four lemmas can't go in `Minor`, since they are needed in `Finitize`.
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
  obtain ⟨C, D, rfl⟩ := hNM
  exact ((M ／ C).eConn_delete_le X D).trans <| M.eConn_contract_le X C

end Global
