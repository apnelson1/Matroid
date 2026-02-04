import Mathlib.Combinatorics.Matroid.Map -- inefficient import
import Matroid.ForMathlib.Matroid.Basic
import Matroid.ForMathlib.Function

open Set Function

namespace Matroid

variable {α β : Type*} {M : Matroid α} {X : Set α}

lemma map_restrict (M : Matroid α) (f : α → β) (hf : M.E.InjOn f) (R : Set α)
    (hR : R ⊆ M.E := by aesop_mat) : (M ↾ R).map f (hf.mono hR) = (M.map f hf) ↾ f '' R := by
  refine ext_indep rfl fun I (hI : I ⊆ f '' R) ↦ ?_
  simp only [map_indep_iff, restrict_indep_iff, hI, and_true]
  constructor
  · rintro ⟨I₀, hI₀, -, rfl⟩
    exact ⟨_, hI₀.1, rfl⟩
  rintro ⟨I₀, hI₀, rfl⟩
  exact ⟨_, ⟨hI₀, (hf.image_subset_image_iff hI₀.subset_ground hR).1 hI⟩, rfl⟩

lemma comap_restrict (M : Matroid β) (f : α → β) (R : Set β) :
    (M ↾ R).comap f = (M.comap f ↾ (f ⁻¹' R)) :=
  ext_indep rfl fun I _ ↦ by simp [and_assoc, and_comm (a := I ⊆ _)]

lemma comap_restrict_univ (M : Matroid β) (f : α → β) :
    (M ↾ univ).comap f = (M.comap f ↾ univ) := by
  simp [comap_restrict]

lemma comap_restrict_range_inter (M : Matroid β) (f : α → β) :
    (M ↾ (range f) ∩ M.E).comap f = M.comap f := by
  simp [comap_restrict]

@[simp] lemma comapOn_ground_map {M : Matroid α} (f : α → β) (hf : InjOn f M.E) :
    (M.map f hf).comapOn M.E f = M := by
  refine ext_indep rfl fun I _ ↦ ?_
  simp only [comapOn_indep_iff, map_indep_iff]
  refine ⟨fun ⟨⟨I₀, hI₀, hII₀⟩, hinj, hIE⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [hf.image_eq_image_iff hIE hI₀.subset_ground] at hII₀
    rwa [hII₀]
  exact ⟨⟨I, h, rfl⟩, hf.mono h.subset_ground, h.subset_ground⟩

@[simp] lemma comapOn_map (M : Matroid β) {R : Set α} {f : α → β} (hf : InjOn f R) :
    (M.comapOn R f).map f hf = M ↾ (f '' R) := by
  refine ext_indep rfl fun I hI ↦ ?_
  simp only [map_indep_iff, comapOn_indep_iff, restrict_indep_iff]
  refine ⟨?_, fun ⟨hI, hIR⟩ ↦ ?_⟩
  · rintro ⟨I, ⟨hind,-,hss⟩, rfl⟩
    exact ⟨hind, image_mono hss⟩
  obtain ⟨I₀, hI₀R, hbij⟩ := SurjOn.exists_bijOn_subset hIR
  exact ⟨I₀, ⟨by rwa [hbij.image_eq], hbij.injOn, hI₀R⟩, hbij.image_eq.symm⟩

-- lemma map_eq_comap (M : Matroid α) {f : α → β} {g : β → α} (hfg :  g f M.E)
--     (hEg : range g ⊆ M.E) : M.map f hfg.injOn = M.comap g := by
--   refine ext_indep ?_ fun I hIi ↦ ?_
--   · sorry
--     -- rw [map_ground, comap_ground_eq]
--     -- nth_rw 2 [← hfg.image_image]
--     -- rw [InjOn.preimage_image_inter]
--   simp
--   refine ⟨?_, fun h ↦ ?_⟩
--   · rintro ⟨I, hI, rfl⟩
--     rw [hfg.image_image]

lemma IsBasis'.comap {f : β → α} {g : α → β} {I X : Set α} (h : M.IsBasis' I X)
    (hinv : LeftInvOn f g X) : (M.comap f).IsBasis' (g '' I) (g '' X) := by
  rwa [comap_isBasis'_iff, and_iff_left (image_mono h.subset),
    and_iff_left (hinv.mono h.subset).injOn_image, hinv.image_image,
    (hinv.mono h.subset).image_image]

lemma IsBasis.comap {f : β → α} {g : α → β} {I X : Set α} (h : M.IsBasis I X)
    (hinv : LeftInvOn f g X) : (M.comap f).IsBasis (g '' I) (g '' X) := by
  rwa [comap_isBasis_iff, and_iff_left (image_mono h.subset),
    and_iff_left (hinv.mono h.subset).injOn_image, hinv.image_image,
    (hinv.mono h.subset).image_image]

lemma Indep.comap {f : β → α} {g : α → β} {I : Set α} (hI : M.Indep I) (hinv : LeftInvOn f g I) :
    (M.comap f).Indep (g '' I) := by
  rwa [comap_indep_iff, and_iff_left hinv.injOn_image, hinv.image_image]

@[simp]
lemma mapEmbedding_image_closure_eq (M : Matroid α) (f : α ↪ β) (X : Set α) :
    (M.mapEmbedding f).closure (f '' X) = f '' M.closure X := by
  rw [mapEmbedding, map_closure_eq, f.injective.preimage_image]

/-- This needs `mapEmbedding` rather than just `map`, since otherwise `X` could contain
an element outside `M.E` that collides with something in `M.E`-/
lemma IsBasis'.mapEmbedding {I : Set α} {f : α ↪ β} (h : M.IsBasis' I X)  :
    (M.mapEmbedding f).IsBasis' (f '' I) (f '' X) := by
  rw [isBasis'_iff_isBasis_closure, mapEmbedding_image_closure_eq,
    and_iff_left (image_mono h.subset)]
  apply h.isBasis_closure_right.map

@[simp]
lemma isBasis'_mapEmbedding_image_iff {I : Set α} {f : α ↪ β} :
    (M.mapEmbedding f).IsBasis' (f '' I) (f '' X) ↔ M.IsBasis' I X := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.mapEmbedding ..⟩
  rw [isBasis'_iff_isBasis_inter_ground, isBasis_iff_indep_subset_closure] at h ⊢
  simp only [mapEmbedding_indep_iff, f.injective.preimage_image, image_subset_iff, preimage_range,
    subset_univ, and_true, mapEmbedding_ground_eq, subset_inter_iff,
    mapEmbedding_image_closure_eq] at h
  rwa [← image_inter f.injective, image_subset_image_iff f.injective, ← subset_inter_iff] at h

@[simp]
lemma isBasis_mapEmbedding_image_iff {I : Set α} {f : α ↪ β} :
    (M.mapEmbedding f).IsBasis (f '' I) (f '' X) ↔ M.IsBasis I X := by
  simp [f.injective.preimage_image]
  exact IsBasis.subset

lemma map_map {α β γ : Type*} (M : Matroid α) {f : α → β} {g : β → γ} (hf) (hg) :
    (M.map f hf).map g hg = M.map (g ∘ f) (by rwa [hf.comp_iff]) :=
  ext_indep (by simp [image_image]) fun I hI ↦ by aesop

lemma comap_comap {α β γ : Type*} (M : Matroid γ) (f : α → β) (g : β → γ) :
    (M.comap g).comap f = M.comap (g ∘ f) := by
  refine ext_indep rfl fun I hI ↦ ?_
  simp only [comap_indep_iff, image_image, comp_apply]
  exact ⟨fun ⟨⟨h,h'⟩,h''⟩ ↦ ⟨h, by rwa [h''.comp_iff]⟩,
    fun h ↦ ⟨⟨h.1, h.2.image_of_comp⟩, h.2.of_comp⟩⟩

protected lemma map_inj {M N : Matroid α} (f : α → β) (hf : InjOn f (M.E ∪ N.E))
    (hMN : M.map f (hf.mono subset_union_left) = N.map f (hf.mono subset_union_right)) : M = N := by
  simp only [ext_iff_indep, map_ground, map_indep_iff, forall_subset_image_iff] at hMN
  rw [hf.image_eq_image_iff subset_union_left subset_union_right] at hMN
  refine ext_indep hMN.1 fun I hIE ↦ ⟨fun hI ↦ ?_, fun hI ↦ ?_⟩
  · obtain ⟨J, hJ, hIJ⟩ := (hMN.2 I hIE).1 ⟨I, hI, rfl⟩
    rwa [(hf.image_eq_image_iff ?_ ?_).1 hIJ]
    · exact hIE.trans subset_union_left
    exact hJ.subset_ground.trans subset_union_right
  obtain ⟨J, hJ, hIJ⟩ := (hMN.2 _ hIE).2 ⟨I, hI, rfl⟩
  rwa [(hf.image_eq_image_iff ?_ ?_).1 hIJ]
  · exact hIE.trans subset_union_left
  exact hJ.subset_ground.trans subset_union_left

protected lemma comap_inj {M N : Matroid β} {f : α → β} (hfM : M.E ⊆ range f) (hfN : N.E ⊆ range f)
    (hMN : M.comap f = N.comap f) : M = N := by
  refine ext_indep ?_ fun I hI ↦ ?_
  · apply_fun Matroid.E at hMN
    rwa [comap_ground_eq, comap_ground_eq, preimage_eq_preimage' hfM hfN] at hMN
  obtain ⟨I, rfl, hinj⟩ := exists_image_eq_injOn_of_subset_range (hI.trans hfM)
  have hMI := M.comap_indep_iff (f := f) (I := I)
  have hNI := N.comap_indep_iff (f := f) (I := I)
  rw [and_iff_left hinj] at hNI hMI
  rw [← hNI, ← hMI, hMN]

theorem map_comapOn {N : Matroid β} {f : α → β} {X : Set α}
    (h_bij : BijOn f X N.E) : (N.comapOn X f).map f h_bij.injOn = N := by
  refine ext_indep h_bij.image_eq fun I hI ↦ ?_
  simp only [comapOn_map, restrict_indep_iff, and_iff_left_iff_imp]
  rw [h_bij.image_eq]
  exact Indep.subset_ground

lemma comapOn_dual {f : α → β} {X : Set α} {N : Matroid β} (h_bij : BijOn f X N.E) :
    (N.comapOn X f)✶ = N✶.comapOn X f := by
  refine ext_isBase rfl fun B (hB : B ⊆ X) ↦ ?_
  rw [dual_isBase_iff, comapOn_isBase_iff_of_bijOn (by simpa), comapOn_ground_eq,
    comapOn_isBase_iff_of_bijOn (by simpa), and_iff_left diff_subset, and_iff_left hB,
    dual_isBase_iff', ← h_bij.image_eq, image_diff_of_injOn h_bij.injOn hB,
    and_iff_left (image_mono hB)]

lemma comap_dual {f : α → β} {N : Matroid β} (h_bij : BijOn f (f ⁻¹' N.E) N.E) :
    (N.comap f)✶ = N✶.comap f := by
  convert comapOn_dual h_bij using 1
  · rw [← (N.comap f).restrict_ground_eq_self, comapOn, comap_ground_eq]
  rw [← (N✶.comap f).restrict_ground_eq_self, comapOn, comap_ground_eq, dual_ground]

lemma restrictSubtype_closure (M : Matroid α) (X : Set α) (Y : Set X)
    (hX : X ⊆ M.E := by aesop_mat) :
    (M.restrictSubtype X).closure Y = M.closure ((↑) '' Y) ∩ X := by
  rw [restrictSubtype, comap_closure_eq, restrict_closure_eq _ _ hX, image_preimage_eq_inter_range,
    Subtype.range_coe, inter_assoc, inter_self]
  grw [image_subset_range, Subtype.range_coe]

@[simp]
lemma restrictSubtype_ground_closure (M : Matroid α) (Y : Set M.E) :
    (M.restrictSubtype M.E).closure Y = M.closure ((↑) '' Y) := by
  rw [M.restrictSubtype_closure M.E, inter_eq_self_of_subset_left <| M.closure_subset_ground ..]


end Matroid
