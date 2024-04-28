import Matroid.Constructions.Basic
import Matroid.ForMathlib.Other
import Mathlib.Data.Set.Subset

open Set.Notation
-- import Matroid.Equiv

open Set Function

namespace Matroid
variable {α β : Type*} {f : α → β} {E I s : Set α}

private def comapIndepMatroid (M : Matroid β) (f : α → β) : IndepMatroid α where
  E := f ⁻¹' M.E
  Indep I := M.Indep (f '' I) ∧ InjOn f I
  indep_empty := by simp
  indep_subset I J h hIJ := ⟨h.1.subset (image_subset _ hIJ), InjOn.mono hIJ h.2⟩
  indep_aug := by
    rintro I B ⟨hI, hIinj⟩ hImax hBmax
    simp only [mem_maximals_iff, mem_setOf_eq, hI, hIinj, and_self, and_imp,
      true_and, not_forall, exists_prop, exists_and_left] at hImax hBmax

    obtain ⟨I', hI', hI'inj, hII', hne⟩ := hImax

    have h₁ : ¬(M ↾ range f).Base (f '' I) := by
      refine fun hB ↦ hne ?_
      have h_im := hB.eq_of_subset_indep (by simpa) (image_subset _ hII')
      rwa [hI'inj.image_eq_image_iff_of_subset hII' Subset.rfl] at h_im

    have h₂ : (M ↾ range f).Base (f '' B) := by
      refine Indep.base_of_maximal (by simpa using hBmax.1.1) (fun J hJi hBJ ↦ ?_)
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
def comap (M : Matroid β) (f : α → β) : Matroid α := (comapIndepMatroid M f).matroid

@[simp] theorem comap_indep_iff {M : Matroid β} :
    (M.comap f).Indep I ↔ M.Indep (f '' I) ∧ InjOn f I := by
  simp [comap, comapIndepMatroid]

@[simp] theorem comap_ground_eq (M : Matroid β) (f : α → β) :
    (M.comap f).E = f ⁻¹' M.E := rfl

@[simp] theorem comap_dep_iff {M : Matroid β} :
    (M.comap f).Dep I ↔ M.Dep (f '' I) ∨ (M.Indep (f '' I) ∧ ¬ InjOn f I) := by
  rw [Dep, comap_indep_iff, not_and, comap_ground_eq, Dep, image_subset_iff]
  refine ⟨fun ⟨hi, h⟩ ↦ ?_, ?_⟩
  · rw [and_iff_left h, ← imp_iff_not_or]
    exact fun hI ↦ ⟨hI, hi hI⟩
  rintro (⟨hI, hIE⟩ | hI)
  · exact ⟨fun h ↦ (hI h).elim, hIE⟩
  rw [iff_true_intro hI.1, iff_true_intro hI.2, implies_true, true_and]
  simpa using hI.1.subset_ground

@[simp] theorem comap_id (M : Matroid β) : M.comap id = M :=
  eq_of_indep_iff_indep_forall (by simp) (by simp [injective_id.injOn _])

theorem comap_indep_iff_of_injOn {M : Matroid β} (hf : InjOn f (f ⁻¹' M.E)) :
    (M.comap f).Indep I ↔ M.Indep (f '' I) := by
  rw [comap_indep_iff, and_iff_left_iff_imp]
  refine fun hi ↦ hf.mono <| subset_trans ?_ (preimage_mono hi.subset_ground)
  apply subset_preimage_image

theorem comap_indep_iff_of_embedding (M : Matroid β) (f : α ↪ β) :
    (M.comap f).Indep I ↔ M.Indep (f '' I) :=
  comap_indep_iff_of_injOn (f.injective.injOn _)

@[simp] theorem comap_emptyOn (f : α → β) : comap (emptyOn β) f = emptyOn α := by
  simp [← ground_eq_empty_iff]

@[simp] theorem comap_loopyOn (f : α → β) (E : Set β) :
    comap (loopyOn E) f = loopyOn (f ⁻¹' E) := by
  rw [eq_loopyOn_iff]; aesop

/-- The pullback of a matroid on `β` by a function `f : α → β` to a matroid on `α`,
restricted to a ground set `E`. Elements with the same image are parallel. -/
def comapOn (M : Matroid β) (E : Set α) (f : α → β) : Matroid α := (M.comap f) ↾ E

theorem comapOn_preimage_eq (M : Matroid β) (f : α → β) : M.comapOn (f ⁻¹' M.E) f = M.comap f := by
  rw [comapOn, restrict_eq_self_iff]; rfl

@[simp] theorem comapOn_indep_iff {M : Matroid β} :
    (M.comapOn E f).Indep I ↔ (M.Indep (f '' I) ∧ InjOn f I ∧ I ⊆ E) := by
  simp [comapOn, and_assoc]

@[simp] theorem comapOn_ground_eq {M : Matroid β} :
    (M.comapOn E f).E = E := rfl

theorem comapOn_base_iff_of_surjOn {M : Matroid β} {E : Set α} (h : SurjOn f E M.E) {B : Set α} :
    (M.comapOn E f).Base B ↔ (M.Base (f '' B) ∧ InjOn f B ∧ B ⊆ E) := by
  simp only [base_iff_maximal_indep, comapOn_indep_iff, and_imp, image_subset_iff]
  rw [and_assoc, and_assoc, and_assoc, (show (∀ _, _) ∧ _ ↔ _ ∧ (∀ _, _) by rw [and_comm]),
    and_assoc, and_congr_right_iff, and_congr_right_iff, and_congr_right_iff]
  refine fun _ hinj hBE ↦ ⟨fun h' J hJ hBJ ↦ ?_, fun h' I hI hfI _ hBI ↦ ?_⟩
  · rw [subset_antisymm_iff, image_subset_iff, and_iff_right hBJ]
    refine fun x hxJ ↦ by_contra fun hcon ↦ ?_
    obtain ⟨x, hx, rfl⟩ := h (hJ.subset_ground hxJ)
    rw [h' (insert x B) (hJ.subset ?_) ?_ (insert_subset hx hBE) (subset_insert _ _)] at hcon
    · simp at hcon
    · exact image_subset_iff.2 <| insert_subset hxJ hBJ
    rwa [injOn_insert (fun hxB ↦ hcon (mem_image_of_mem _ hxB)), and_iff_right hinj]
  specialize h' _ hI (hBI.trans (subset_preimage_image _ _))
  rwa [hfI.image_eq_image_iff_of_subset hBI Subset.rfl] at h'

theorem comapOn_base_iff_of_bijOn {M : Matroid β} {E : Set α} (h : BijOn f E M.E) {B : Set α} :
    (M.comapOn E f).Base B ↔ M.Base (f '' B) ∧ B ⊆ E := by
  rw [comapOn_base_iff_of_surjOn h.surjOn, and_congr_right_iff, and_iff_right_iff_imp]
  exact fun _ ↦ h.injOn.mono

theorem comapOn_dual_eq_of_bijOn {M : Matroid β} {E : Set α} (h : BijOn f E M.E) :
    (M.comapOn E f)✶ = M✶.comapOn E f := by
  refine eq_of_base_iff_base_forall (by simp) (fun B hB ↦ ?_)
  rw [comapOn_base_iff_of_bijOn (by simpa), dual_base_iff, comapOn_base_iff_of_bijOn h,
    dual_base_iff _, comapOn_ground_eq, and_iff_left (diff_subset _ _), and_iff_left (by simpa),
    h.injOn.image_diff (by simpa), h.image_eq]
  exact (h.mapsTo.mono_left (show B ⊆ E by simpa)).image_subset

section Image

/-- Given an injective function `f` on `M.E`, the `IndepMatroid` whose independent sets
are the images of those in `M`. -/
private def mapIndepMatroid (M : Matroid α) (f : α → β) (hf : InjOn f M.E) : IndepMatroid β where
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

    have hIb : ¬ M.Base I := by
      refine fun hIb ↦ hne ?_
      rw [hIb.eq_of_subset_indep ?_ (subset_inter hII' hI.subset_ground),
        hf.preimage_image_inter hI'.subset_ground]
      rwa [hf.preimage_image_inter hI'.subset_ground]

    have hB : M.Base B := by
      refine hB.base_of_maximal (fun J hJ hBJ ↦ ?_)
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
def map (M : Matroid α) (f : α → β) (hf : InjOn f M.E) : Matroid β :=
  (mapIndepMatroid M f hf).matroid

/-- Map a matroid `M` across an embedding. -/
def mapEmbedding (M : Matroid α) (f : α ↪ β) : Matroid β := M.map f <| f.injective.injOn _

def mapEquiv (M : Matroid α) (f : α ≃ β) : Matroid β := M.mapEmbedding f.toEmbedding

@[simp] theorem map_ground (M : Matroid α) (f : α → β) (hf : InjOn f M.E) :
    (M.map f hf).E = f '' M.E := rfl

@[simp] theorem map_indep_iff {M : Matroid α} {f : α → β} {hf : InjOn f M.E} {I : Set β} :
    (M.map f hf).Indep I ↔ ∃ I₀, M.Indep I₀ ∧ I = f '' I₀ :=
  by simp [map, mapIndepMatroid]

theorem map_image_indep_iff {M : Matroid α} {f : α → β} {hf : InjOn f M.E} {I : Set α}
    (hI : I ⊆ M.E) : (M.map f hf).Indep (f '' I) ↔ M.Indep I := by
  rw [map_indep_iff]
  refine ⟨fun ⟨J, hJ, hIJ⟩ ↦ ?_, fun h ↦ ⟨I, h, rfl⟩ ⟩
  rw [hf.image_eq_image_iff_of_subset hI hJ.subset_ground] at hIJ; rwa [hIJ]

@[simp] theorem mapEmbedding_indep_iff {M : Matroid α} {f : α ↪ β} {I : Set β} :
    (M.mapEmbedding f).Indep I ↔ M.Indep (f ⁻¹' I) ∧ I ⊆ range f := by
  rw [mapEmbedding, map_indep_iff]
  refine ⟨?_, fun ⟨h,h'⟩ ↦ ⟨f ⁻¹' I, h, by rwa [eq_comm, image_preimage_eq_iff]⟩⟩
  rintro ⟨I, hI, rfl⟩
  rw [preimage_image_eq _ f.injective]
  exact ⟨hI, image_subset_range _ _⟩

@[simp] theorem mapEquiv_indep_iff {M : Matroid α} {f : α ≃ β} {I : Set β} :
    (M.mapEquiv f).Indep I ↔ M.Indep (f.symm '' I) := by
  rw [mapEquiv, mapEmbedding, map_indep_iff, Equiv.coe_toEmbedding]
  refine ⟨?_, fun h ↦ ⟨_, h, by simp⟩ ⟩
  rintro ⟨I, hI, rfl⟩
  rwa [f.symm_image_image]

@[simp] theorem map_base_iff (M : Matroid α) (f : α → β) (hf : InjOn f M.E) {B : Set β} :
    (M.map f hf).Base B ↔ ∃ B₀, M.Base B₀ ∧ B = f '' B₀ := by
  rw [base_iff_maximal_indep, map_indep_iff]
  refine ⟨fun ⟨h, hB⟩ ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨B₀, hB₀, rfl⟩ := h
    refine ⟨_, hB₀.base_of_maximal fun J hJ hB₀J ↦ ?_, rfl⟩
    specialize hB (f '' J) ((map_image_indep_iff hJ.subset_ground).2 hJ) (image_subset _ hB₀J)
    rwa [hf.image_eq_image_iff_of_subset hB₀.subset_ground hJ.subset_ground] at hB
  obtain ⟨B₀, hB, rfl⟩ := h
  refine ⟨⟨B₀, hB.indep, rfl⟩, fun I hI hB₀I ↦ ?_⟩
  obtain ⟨I, hI', rfl⟩ := map_indep_iff.1 hI
  rw [hf.image_subset_image_iff_of_subset hB.subset_ground hI'.subset_ground] at hB₀I
  rw [hB.eq_of_subset_indep hI' hB₀I]

theorem map_image_base_iff {M : Matroid α} {f : α → β} {hf : InjOn f M.E} {B : Set α}
    (hB : B ⊆ M.E) : (M.map f hf).Base (f '' B) ↔ M.Base B := by
  rw [map_base_iff]
  refine ⟨fun ⟨J, hJ, hIJ⟩ ↦ ?_, fun h ↦ ⟨B, h, rfl⟩⟩
  rw [hf.image_eq_image_iff_of_subset hB hJ.subset_ground] at hIJ; rwa [hIJ]

@[simp] theorem map_dual {M : Matroid α} {f : α → β} {hf : InjOn f M.E} :
    (M.map f hf)✶ = M✶.map f hf := by
  apply eq_of_base_iff_base_forall (by simp)
  simp only [dual_ground, map_ground, subset_image_iff, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, dual_base_iff']
  intro B hB
  simp_rw [← hf.image_diff hB, map_image_base_iff (diff_subset _ _),
    map_image_base_iff (show B ⊆ M✶.E from hB), dual_base_iff hB, and_iff_left_iff_imp]
  exact fun _ ↦ ⟨B, hB, rfl⟩

@[simp] theorem map_emptyOn (f : α → β) : (emptyOn α).map f (by simp) = emptyOn β := by
  simp [← ground_eq_empty_iff]

@[simp] theorem map_loopyOn (f : α → β) (hf : InjOn f E) :
    (loopyOn E).map f hf = loopyOn (f '' E) := by
  simp [eq_loopyOn_iff]

@[simp] theorem map_freeOn (f : α → β) (hf : InjOn f E) :
    (freeOn E).map f hf = freeOn (f '' E) := by
  rw [← dual_inj]; simp

end Image

section OnSubtype

variable {E X : Set α} {M N : Matroid α}

/-- Given `M : Matroid α` and `X : Set α`, the natural matroid on type `X` with ground set `univ`.
  If `X ⊆ M.E`, then isomorphic to `M ↾ X`. If `X = M.E`, then isomorphic to `M`. -/
def onSubtype (M : Matroid α) (X : Set α) : Matroid X := M.comap (↑)

theorem onSubtype_ground (hX : X ⊆ M.E) : (M.onSubtype X).E = univ := by
  rw [onSubtype, comap_ground_eq, eq_univ_iff_forall]; simpa

@[simp] theorem onSubtype_indep_iff {X : Set α} {I : Set X} :
    (M.onSubtype X).Indep I ↔ M.Indep ((↑) '' I) := by
  simp [onSubtype, Subtype.val_injective.injOn I]

theorem onSubtype_indep_iff_of_subset {X I : Set α} (hIX : I ⊆ X) :
    (M.onSubtype X).Indep (X ↓∩ I) ↔ M.Indep I := by
  rw [onSubtype_indep_iff, image_preimage_eq_iff.2]; simpa

theorem onSubtype_inter_indep_iff {X I : Set α} :
    (M.onSubtype X).Indep (X ↓∩ I) ↔ M.Indep (X ∩ I) := by
  simp only [onSubtype, comap_indep_iff, Subtype.image_preimage_coe, and_iff_left_iff_imp]
  exact fun _ ↦ injOn_subtype_val

theorem eq_of_onSubtype_eq (hM : M.E = E) (hN : N.E = E) (h : M.onSubtype E = N.onSubtype E) :
    M = N := by
  subst hM
  refine eq_of_indep_iff_indep_forall (by rw [hN]) (fun I hI ↦ ?_)
  rwa [← onSubtype_indep_iff_of_subset hI, h, onSubtype_indep_iff_of_subset]

theorem onSubtype_dual' (hM : M.E = E) : (M.onSubtype E)✶ = M✶.onSubtype E := by
  rw [onSubtype, ← comapOn_preimage_eq, comapOn_dual_eq_of_bijOn, ← dual_ground,
    comapOn_preimage_eq, onSubtype]
  subst hM
  exact ⟨by simp [MapsTo], Subtype.val_injective.injOn _, by simp [SurjOn, Subset.rfl]⟩

@[simp] theorem onSubtype_dual : (M.onSubtype M.E)✶ = M✶.onSubtype M.E :=
  onSubtype_dual' rfl

end OnSubtype
section Iso



end Iso
