import Mathlib.Data.Matroid.Map
import Matroid.ForMathlib.Matroid.Basic
import Matroid.ForMathlib.Function

open Set

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
    exact ⟨hind, image_subset f hss⟩
  obtain ⟨I₀, hI₀R, hbij⟩ := SurjOn.exists_bijOn_subset hIR
  exact ⟨I₀, ⟨by rwa [hbij.image_eq], hbij.injOn, hI₀R⟩, hbij.image_eq.symm⟩

lemma IsBasis'.comap {f : β → α} {g : α → β} {I X : Set α} (h : M.IsBasis' I X)
    (hinv : RightInvOn g f X) : (M.comap f).IsBasis' (g '' I) (g '' X) := by
  rwa [comap_isBasis'_iff, and_iff_left (image_subset _ h.subset),
    and_iff_left (hinv.mono h.subset).injOn_image, hinv.image_image,
    (hinv.mono h.subset).image_image]

lemma IsBasis.comap {f : β → α} {g : α → β} {I X : Set α} (h : M.IsBasis I X)
    (hinv : RightInvOn g f X) : (M.comap f).IsBasis (g '' I) (g '' X) := by
  rwa [comap_isBasis_iff, and_iff_left (image_subset _ h.subset),
    and_iff_left (hinv.mono h.subset).injOn_image, hinv.image_image,
    (hinv.mono h.subset).image_image]

lemma Indep.comap {f : β → α} {g : α → β} {I : Set α} (hI : M.Indep I) (hinv : RightInvOn g f I) :
    (M.comap f).Indep (g '' I) := by
  rwa [comap_indep_iff, and_iff_left hinv.injOn_image, hinv.image_image]

end Matroid
