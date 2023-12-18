import Matroid.Constructions.Basic
import Matroid.ForMathlib.Other
import Matroid.Equiv

open Set Function


namespace Matroid
variable {α β : Type*} {f : α → β} {E I s : Set α}

def preimage_indepMatroid (M : Matroid β) (f : α → β) : IndepMatroid α where
  E := f ⁻¹' M.E
  Indep I := M.Indep (f '' I) ∧ InjOn f I
  indep_empty := by simp
  indep_subset I J h hIJ := ⟨h.1.subset (image_subset _ hIJ), InjOn.mono hIJ h.2⟩
  indep_aug := by
    rintro I B ⟨hI, hIinj⟩ hImax hBmax
    simp only [mem_maximals_iff, mem_setOf_eq, hI, hIinj, and_self, and_imp,
      true_and, not_forall, exists_prop, exists_and_left] at hImax hBmax

    obtain ⟨I', hI', hI'inj, hII', hne⟩ := hImax

    have h₁ : ¬(M ↾ range f).Base (f '' I)
    · refine fun hB ↦ hne ?_
      have h_im := hB.eq_of_subset_indep (by simpa) (image_subset _ hII')
      rwa [hI'inj.image_eq_image_iff_of_subset hII' Subset.rfl] at h_im

    have h₂ : (M ↾ range f).Base (f '' B)
    · refine Indep.base_of_maximal (by simpa using hBmax.1.1) (fun J hJi hBJ ↦ ?_)
      simp only [restrict_indep_iff] at hJi
      obtain ⟨J₀, hBJ₀, hJ₀⟩ := hBmax.1.2.bijOn_image.extend hBJ hJi.2
      obtain rfl := hJ₀.image_eq
      rw [hBmax.2 hJi.1 hJ₀.injOn hBJ₀]

    obtain ⟨_, ⟨⟨e, he, rfl⟩, he'⟩, hei⟩ := Indep.exists_insert_of_not_base (by simpa) h₁ h₂
    have heI : e ∉ I := fun heI ↦ he' (mem_image_of_mem f heI)
    rw [← image_insert_eq, restrict_indep_iff] at hei
    exact ⟨e, ⟨he, heI⟩, hei.1, (injOn_insert heI).2 ⟨hIinj, he'⟩⟩
  indep_maximal := by
    rintro X - I ⟨hI, hIinj⟩ hIX
    obtain ⟨J, hJ⟩ := (M ↾ range f).existsMaximalSubsetProperty_indep (f '' X) (by simp)
      (f '' I) (by simpa) (image_subset _ hIX)
    simp only [restrict_indep_iff, image_subset_iff, mem_maximals_iff, mem_setOf_eq, and_imp] at hJ

    obtain ⟨J₀, hIJ₀, hJ₀X, hbj⟩ := hIinj.bijOn_image.extend_of_subset hIX
      (image_subset f hJ.1.2.1) (image_subset_iff.2 <| preimage_mono hJ.1.2.2)

    have him := hbj.image_eq; rw [image_preimage_eq_of_subset hJ.1.1.2] at him; subst him
    use J₀
    simp only [mem_maximals_iff, mem_setOf_eq, hJ.1.1.1, hbj.injOn, and_self, hIJ₀,
      hJ₀X, and_imp, true_and]
    intro K hK hinj hIK hKX hJ₀K
    rw [← hinj.image_eq_image_iff_of_subset hJ₀K Subset.rfl,
       hJ.2 hK (image_subset_range _ _) (fun e he ↦ ⟨e, hIK he, rfl⟩)
       (image_subset _ hKX) (image_subset _ hJ₀K)]
  subset_ground I hI e heI := hI.1.subset_ground ⟨e, heI, rfl⟩

/-- The pullback of a matroid on `β` by a function `f : α → β` to a matroid on `α`.
  Elements with the same image are parallel and the ground set is `f ⁻¹' M.E`. -/
def preimage (M : Matroid β) (f : α → β) : Matroid α := (preimage_indepMatroid M f).matroid

@[simp] theorem preimage_indep_iff {M : Matroid β} :
    (M.preimage f).Indep I ↔ M.Indep (f '' I) ∧ InjOn f I := by
  simp [preimage, preimage_indepMatroid]

@[simp] theorem preimage_ground_eq (M : Matroid β) (f : α → β) :
    (M.preimage f).E = f ⁻¹' M.E := rfl

@[simp] theorem preimage_dep_iff {M : Matroid β} :
    (M.preimage f).Dep I ↔ M.Dep (f '' I) ∨ (M.Indep (f '' I) ∧ ¬ InjOn f I) := by
  rw [Dep, preimage_indep_iff, not_and, preimage_ground_eq, Dep, image_subset_iff]
  refine ⟨fun ⟨hi, h⟩ ↦ ?_, ?_⟩
  · rw [and_iff_left h, ← imp_iff_not_or]
    exact fun hI ↦ ⟨hI, hi hI⟩
  rintro (⟨hI, hIE⟩ | hI)
  · exact ⟨fun h ↦ (hI h).elim, hIE⟩
  rw [iff_true_intro hI.1, iff_true_intro hI.2, implies_true, true_and]
  simpa using hI.1.subset_ground

@[simp] theorem preimage_id (M : Matroid β) : M.preimage id = M :=
  eq_of_indep_iff_indep_forall (by simp) (by simp [injective_id.injOn _])

theorem preimage_indep_off_of_injective (M : Matroid β) (hf : f.Injective) :
    (M.preimage f).Indep I ↔ M.Indep (f '' I) := by
  rw [preimage_indep_iff, and_iff_left (hf.injOn I)]

noncomputable def preimage_iso [Nonempty α] {M : Matroid β} (hf : f.Injective)
    (hfE : range f = M.E) : Iso (M.preimage f) M :=
    Iso.of_forall_indep
      (hf.injOn univ).toPartialEquiv (by simp [← hfE]) (by simpa)
      ( by simp [← hfE, hf.injOn _] )

@[simp] theorem preimage_iso_coeFun [Nonempty α] {M : Matroid β} (hf : f.Injective)
    (hfE : range f = M.E) : (preimage_iso hf hfE : α → β) = fun x ↦ f x := rfl

/-- The pullback of a matroid on `β` by a function `f : α → β` to a matroid on `α`, restricted
  to a ground set `E`. Elements with the same image are parallel. -/
def preimageOn (M : Matroid β) (E : Set α) (f : α → β) : Matroid α := (M.preimage f) ↾ E

@[simp] theorem preimageOn_indep_iff {M : Matroid β} :
    (M.preimageOn E f).Indep I ↔ (M.Indep (f '' I) ∧ InjOn f I ∧ I ⊆ E) := by
  simp [preimageOn, and_assoc]

@[simp] theorem preimageOn_ground_eq {M : Matroid β} :
    (M.preimageOn E f).E = E := rfl

/-- If `f` is locally a bijection, then `M` is isomorphic to its preimage. -/
noncomputable def iso_preimageOn [_root_.Nonempty α] (M : Matroid β) {f : α → β} {E : Set α}
    (hf : BijOn f E M.E) : Iso (M.preimageOn E f) M :=
  Iso.of_forall_indep
  hf.toPartialEquiv
  ( by rw [BijOn.toPartialEquiv_source, preimageOn_ground_eq] )
  hf.toPartialEquiv_target
  ( by
    simp only [preimageOn_ground_eq, preimageOn_indep_iff, BijOn.toPartialEquiv_apply,
      and_iff_left_iff_imp]
    exact fun I hIE _ ↦ ⟨hf.injOn.mono hIE, hIE⟩ )

theorem Iso.eq_preimage {M : Matroid α} {N : Matroid β} (e : Iso M N) : M = N.preimageOn M.E e := by
  simp only [eq_iff_indep_iff_indep_forall, preimageOn_ground_eq, preimageOn_indep_iff, true_and]
  intro I hIE
  rw [and_iff_left hIE, ← e.on_indep_iff, iff_self_and]
  exact fun _ ↦ e.toPartialEquiv.bijOn.injOn.mono (by simpa)

section Image

/-- Given an injective function `f` on `M.E`, the `IndepMatroid` whose independent sets
  are the images of those in `M`. -/
def image_indepMatroid (M : Matroid α) (f : α → β) (hf : InjOn f M.E) : IndepMatroid β where
  E := f '' M.E
  Indep I := ∃ I₀, M.Indep I₀ ∧ I = f '' I₀
  indep_empty := ⟨∅, by simp⟩
  indep_subset := by
    rintro I _ ⟨J, hJ, rfl⟩ hIJ
    refine ⟨f ⁻¹' I ∩ M.E, hJ.subset ?_, ?_⟩
    · refine (inter_subset_inter_left M.E (preimage_mono hIJ)).trans ?_
      rw [hf.preimage_image_inter hJ.subset_ground]
    simp only [subset_antisymm_iff, image_subset_iff, inter_subset_left, and_true]
    rintro x hx
    obtain ⟨y, hy, rfl⟩ := hIJ hx
    exact ⟨_, ⟨hx, hJ.subset_ground hy⟩, rfl⟩
  indep_aug := by
    rintro _ B ⟨I, hI, rfl⟩ hImax hBmax
    simp only [mem_maximals_iff, mem_setOf_eq, forall_exists_index, and_imp, image_subset_iff,
      not_and, not_forall, exists_prop, exists_and_left] at hBmax hImax
    obtain ⟨⟨B, hB, rfl⟩, hmax⟩ := hBmax
    obtain ⟨_, I', hI', rfl, hII', hne⟩ := hImax _ hI rfl

    have hIb : ¬ M.Base I
    · refine fun hIb ↦ hne ?_
      rw [hIb.eq_of_subset_indep ?_ (subset_inter hII' hI.subset_ground),
        hf.preimage_image_inter hI'.subset_ground]
      rwa [hf.preimage_image_inter hI'.subset_ground]

    have hB : M.Base B
    · refine hB.base_of_maximal (fun J hJ hBJ ↦ ?_)
      have h_image := hmax  _ hJ rfl (image_subset _ hBJ)
      rwa [hf.image_eq_image_iff_of_subset hB.subset_ground hJ.subset_ground] at h_image

    obtain ⟨e, he, hi⟩ := hI.exists_insert_of_not_base hIb hB
    refine ⟨f e, ⟨mem_image_of_mem f he.1, fun h ↦ he.2 ?_⟩, ⟨_, hi, by rw [image_insert_eq]⟩⟩
    rwa [hf.mem_image_iff hI.subset_ground (hB.subset_ground he.1)] at h
  indep_maximal := by
    rintro X hX I ⟨I, hI, rfl⟩ hIX
    obtain ⟨X, hXE, rfl⟩ := exists_eq_image_subset_of_subset_image hX
    rw [hf.image_subset_image_iff_of_subset hI.subset_ground hXE] at hIX

    obtain ⟨B, hB, hIB⟩ := hI.subset_basis_of_subset hIX
    refine ⟨f '' B, ?_⟩
    simp only [image_subset_iff, mem_maximals_iff, mem_setOf_eq, and_imp, forall_exists_index]
    refine ⟨⟨⟨B, hB.indep, rfl⟩, hIB.trans <| subset_preimage_image _ _,
      hB.subset.trans <| subset_preimage_image _ _⟩, ?_⟩
    rintro _ K hK rfl - hKX hBK

    rw [hB.eq_of_subset_indep hK]
    · have hss := subset_inter hBK hB.left_subset_ground
      rwa [hf.preimage_image_inter hK.subset_ground] at hss
    rwa [hf.image_subset_image_iff_of_subset hK.subset_ground hXE] at hKX
  subset_ground := by
    rintro _ ⟨I, hI, rfl⟩; exact image_subset _ hI.subset_ground

/-- Map a matroid `M` on `α` to a copy in `β` using a function `f` that is injective on `M.E` -/
def image (M : Matroid α) (f : α → β) (hf : InjOn f M.E) : Matroid β :=
  (image_indepMatroid M f hf).matroid

@[simp] theorem image_ground (M : Matroid α) (f : α → β) (hf : InjOn f M.E) :
    (M.image f hf).E = f '' M.E := rfl

@[simp] theorem image_indep_iff (M : Matroid α) (f : α → β) (hf : InjOn f M.E) (I : Set β) :
    (M.image f hf).Indep I ↔ ∃ I₀, M.Indep I₀ ∧ I = f '' I₀ :=
  by simp [image, image_indepMatroid]

/-- `M` is isomorphic to its image -/
noncomputable def iso_image [Nonempty α] (M : Matroid α) (f : α → β) (hf : InjOn f M.E) :
    Iso M (M.image f hf)  :=
  Iso.of_forall_indep hf.toPartialEquiv ( by simp ) ( by simp )
  ( by
    simp only [InjOn.toPartialEquiv, BijOn.toPartialEquiv_apply, image_indep_iff]
    refine fun I hIE ↦ ⟨fun hI ↦ ⟨I, hI, rfl⟩, fun ⟨I₀, hI₀, (h_eq : f '' _ = _)⟩ ↦ ?_⟩
    rw [hf.image_eq_image_iff_of_subset hIE hI₀.subset_ground] at h_eq
    rwa [h_eq] )

end Image

section OnUniv

variable {E X : Set α} {M N : Matroid α}

/-- Given `M : Matroid α` and `X : Set α`, the natural matroid on type `X` with ground set `univ`.
  If `X ⊆ M.E`, then isomorphic to `M ↾ X`. -/
def onGround (M : Matroid α) (X : Set α) : Matroid X := M.preimage (↑)

theorem onGround_ground (hX : X ⊆ M.E) : (M.onGround X).E = univ := by
  rw [onGround, preimage_ground_eq, eq_univ_iff_forall]; simpa

noncomputable def iso_onGround' (hX : X ⊆ M.E) (hne : X.Nonempty) : Iso (M.onGround X) (M ↾ X) :=
  have _ := nonempty_coe_sort.2 hne
  Iso.of_forall_indep (Subtype.coe_injective.injOn univ).toPartialEquiv
    (by simp [onGround_ground hX]) (by simp)
  ( by
    simp only [onGround_ground hX, subset_univ, InjOn.toPartialEquiv, image_univ,
      Subtype.range_coe_subtype, setOf_mem_eq, BijOn.toPartialEquiv_apply, restrict_indep_iff,
      image_subset_iff, Subtype.coe_preimage_self, and_true, forall_true_left]
    simp only [onGround._eq_1, preimage_indep_iff, and_iff_left_iff_imp]
    intro I
    simp [Subtype.val_injective.injOn I] )

noncomputable def iso_onGround [M.Nonempty] (hE : M.E = E) : Iso M (M.onGround E) := by
  have hne : Nonempty E := by subst hE; exact nonempty_coe_sort.mpr M.ground_nonempty
  exact (preimage_iso Subtype.val_injective (by rw [Subtype.range_val, ← hE])).symm

theorem isIso_onGround (M : Matroid α) (hE : M.E = E) : M ≅ M.onGround E := by
  obtain (rfl | hM) := M.eq_emptyOn_or_nonempty
  · simp only [emptyOn_ground] at hE; subst hE; simp
  exact (iso_onGround hE).isIso

theorem eq_of_onGround_eq (hM : M.E = E) (hN : N.E = E) (h : M.onGround E = N.onGround E) :
    M = N := by
  obtain (rfl | hMn) := M.eq_emptyOn_or_nonempty
  · rw [eq_comm, ← ground_eq_empty_iff, hN, ← hM, emptyOn_ground]
  have hNn : N.Nonempty
  · rwa [← ground_nonempty_iff, hN, ← hM, ground_nonempty_iff]
  rw [eq_iff_indep_iff_indep_forall] at h ⊢
  rw [hM, hN, and_iff_right rfl]
  intro I hIE
  simp only [onGround_ground hM.symm.subset, subset_univ, forall_true_left] at h
  rw [(iso_onGround hM).on_indep_iff, (iso_onGround hN).on_indep_iff]
  convert h.2 _ using 1

@[simp] theorem onGround_dual (hM : M.E = E) : (M.onGround E)﹡ = M﹡.onGround E := by
  obtain (rfl | hne) := eq_emptyOn_or_nonempty M
  · simp only [emptyOn_ground] at hM; subst hM; simp
  set e := iso_onGround hM
  set e' := iso_onGround (show M﹡.E = E from hM)
  have hu1 := onGround_ground hM.symm.subset
  have hu2 := onGround_ground (M := M﹡) hM.symm.subset
  subst hM

  apply eq_of_base_iff_base_forall
  · rw [dual_ground, hu1, hu2]

  intro B _

  rw [e'.symm.on_base_iff, dual_base_iff', dual_base_iff', e.symm.on_base_iff, and_iff_left,
    and_iff_left, e.symm.injOn_ground.image_diff, e.symm.image_ground]
  · rfl
  · rw [hu1]; exact subset_univ _
  · apply e'.symm.image_subset_ground
  rw [hu1]; exact subset_univ _

end OnUniv
