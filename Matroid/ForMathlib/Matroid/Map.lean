import Mathlib.Data.Matroid.Map

open Set

namespace Matroid

variable {α β : Type*} {M : Matroid α} {X : Set α}

lemma map_restrict (M : Matroid α) (f : α → β) (hf : M.E.InjOn f) (R : Set α)
    (hR : R ⊆ M.E := by aesop_mat) : (M ↾ R).map f (hf.mono hR) = (M.map f hf) ↾ f '' R := by
  refine eq_of_indep_iff_indep_forall rfl fun I (hI : I ⊆ f '' R) ↦ ?_
  simp only [map_indep_iff, restrict_indep_iff, hI, and_true]
  constructor
  · rintro ⟨I₀, hI₀, -, rfl⟩
    exact ⟨_, hI₀.1, rfl⟩
  rintro ⟨I₀, hI₀, rfl⟩
  exact ⟨_, ⟨hI₀, (hf.image_subset_image_iff hI₀.subset_ground hR).1 hI⟩, rfl⟩

lemma comap_restrict (M : Matroid β) (f : α → β) (R : Set β) :
    (M ↾ R).comap f = (M.comap f ↾ (f ⁻¹' R)) :=
  eq_of_indep_iff_indep_forall rfl fun I _ ↦ by simp [and_assoc, and_comm (a := I ⊆ _)]

lemma comap_restrict_univ (M : Matroid β) (f : α → β) :
    (M ↾ univ).comap f = (M.comap f ↾ univ) := by
  simp [comap_restrict]

lemma comap_restrict_range_inter (M : Matroid β) (f : α → β) :
    (M ↾ (range f) ∩ M.E).comap f = M.comap f := by
  simp [comap_restrict]

@[simp] lemma comapOn_ground_map {M : Matroid α} (f : α → β) (hf : InjOn f M.E) :
    (M.map f hf).comapOn M.E f = M := by
  refine eq_of_indep_iff_indep_forall rfl fun I _ ↦ ?_
  simp only [comapOn_indep_iff, map_indep_iff]
  refine ⟨fun ⟨⟨I₀, hI₀, hII₀⟩, hinj, hIE⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [hf.image_eq_image_iff hIE hI₀.subset_ground] at hII₀
    rwa [hII₀]
  exact ⟨⟨I, h, rfl⟩, hf.mono h.subset_ground, h.subset_ground⟩

@[simp] lemma comapOn_map (M : Matroid β) {R : Set α} {f : α → β} (hf : InjOn f R) :
    (M.comapOn R f).map f hf = M ↾ (f '' R) := by
  refine eq_of_indep_iff_indep_forall rfl fun I hI ↦ ?_
  simp only [map_indep_iff, comapOn_indep_iff, restrict_indep_iff]
  refine ⟨?_, fun ⟨hI, hIR⟩ ↦ ?_⟩
  · rintro ⟨I, ⟨hind,-,hss⟩, rfl⟩
    exact ⟨hind, image_subset f hss⟩
  obtain ⟨I₀, hI₀R, hbij⟩ := SurjOn.exists_bijOn_subset hIR
  exact ⟨I₀, ⟨by rwa [hbij.image_eq], hbij.injOn, hI₀R⟩, hbij.image_eq.symm⟩

end Matroid
