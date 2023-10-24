import Matroid.Constructions.Basic
import Matroid.ForMathlib.Other

open Set Function

variable {α β : Type _} {f : α → β} {E I s : Set α}

namespace Matroid

/-- The pullback of a matroid on `β` by a function `f : α → β` to a matroid on `α`.
  Elements with the same image are parallel and the ground set is `f ⁻¹' M.E`. -/
def preimage (M : Matroid β) (f : α → β) : Matroid α := matroid_of_indep
  (f ⁻¹' M.E) (fun I ↦ M.Indep (f '' I) ∧ InjOn f I) ( by simp )
  ( fun I J ⟨h, h'⟩ hIJ ↦ ⟨h.subset (image_subset _ hIJ), InjOn.mono hIJ h'⟩ )
  ( by
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
    exact ⟨e, ⟨he, heI⟩, hei.1, (injOn_insert heI).2 ⟨hIinj, he'⟩⟩ )
  ( by
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
    rw [←hinj.image_eq_image_iff_of_subset hJ₀K Subset.rfl,
       hJ.2 hK (image_subset_range _ _) (fun e he ↦ ⟨e, hIK he, rfl⟩)
       (image_subset _ hKX) (image_subset _ hJ₀K)] )
  ( fun I hI e heI ↦ hI.1.subset_ground ⟨e, heI, rfl⟩ )

@[simp] theorem preimage_indep_iff {M : Matroid β} :
    (M.preimage f).Indep I ↔ M.Indep (f '' I) ∧ InjOn f I := by
  simp [preimage]

@[simp] theorem preimage_ground_eq {M : Matroid β} :
    (M.preimage f).E = f ⁻¹' M.E := rfl

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
  hf.toLocalEquiv
  ( by rw [BijOn.toLocalEquiv_source, preimageOn_ground_eq] )
  hf.toLocalEquiv_target
  ( by
    simp only [preimageOn_ground_eq, preimageOn_indep_iff, BijOn.toLocalEquiv_apply,
      and_iff_left_iff_imp]
    exact fun I hIE _ ↦ ⟨hf.injOn.mono hIE, hIE⟩ )

theorem Iso.eq_preimage {M : Matroid α} {N : Matroid β} (e : Iso M N) : M = N.preimageOn M.E e := by
  simp only [eq_iff_indep_iff_indep_forall, preimageOn_ground_eq, preimageOn_indep_iff, true_and]
  intro I hIE
  rw [and_iff_left hIE, ←e.on_indep_iff, iff_self_and]
  exact fun _ ↦ e.toLocalEquiv.bijOn.injOn.mono (by simpa)

section Image

/-- Map a matroid `M` on `α` to a copy in `β` using a function `f` that is injective on `M.E` -/
def image (M : Matroid α) (f : α → β) (hf : InjOn f M.E) : Matroid β := matroid_of_indep
  ( f '' M.E )
  ( fun I ↦ ∃ I₀, M.Indep I₀ ∧ I = f '' I₀)
  ⟨ ∅, by simp ⟩
  ( by
    rintro I _ ⟨J, hJ, rfl⟩ hIJ
    refine ⟨f ⁻¹' I ∩ M.E, hJ.subset ?_, ?_⟩
    · refine (inter_subset_inter_left M.E (preimage_mono hIJ)).trans ?_
      rw [hf.preimage_image_inter hJ.subset_ground]
    simp only [subset_antisymm_iff, image_subset_iff, inter_subset_left, and_true]
    rintro x hx
    obtain ⟨y, hy, rfl⟩ := hIJ hx
    exact ⟨_, ⟨hx, hJ.subset_ground hy⟩, rfl⟩ )
  ( by
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
    rwa [hf.mem_image_iff hI.subset_ground (hB.subset_ground he.1)] at h )
  ( by
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
    rwa [hf.image_subset_image_iff_of_subset hK.subset_ground hXE] at hKX )
  ( by rintro _ ⟨I, hI, rfl⟩; exact image_subset _ hI.subset_ground )

@[simp] theorem image_ground (M : Matroid α) (f : α → β) (hf : InjOn f M.E) :
    (M.image f hf).E = f '' M.E := rfl

@[simp] theorem image_indep_iff (M : Matroid α) (f : α → β) (hf : InjOn f M.E) (I : Set β) :
    (M.image f hf).Indep I ↔ ∃ I₀, M.Indep I₀ ∧ I = f '' I₀ :=
  by simp [image]

/-- `M` is isomorphic to its image -/
noncomputable def iso_image [_root_.Nonempty α] (M : Matroid α) (f : α → β) (hf : InjOn f M.E) :
    Iso M (M.image f hf)  :=
  Iso.of_forall_indep hf.toLocalEquiv ( by simp ) ( by simp )
  ( by
    simp only [InjOn.toLocalEquiv, BijOn.toLocalEquiv_apply, image_indep_iff]
    refine fun I hIE ↦ ⟨fun hI ↦ ⟨I, hI, rfl⟩, fun ⟨I₀, hI₀, (h_eq : f '' _ = _)⟩ ↦ ?_⟩
    rw [hf.image_eq_image_iff_of_subset hIE hI₀.subset_ground] at h_eq
    rwa [h_eq] )


end Image
