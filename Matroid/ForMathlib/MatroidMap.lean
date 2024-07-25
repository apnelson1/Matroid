import Mathlib.Data.Matroid.Map

open Set

namespace Matroid

variable {α β : Type*} {M : Matroid α} {X : Set α}

@[simp] lemma mapEmbedding_base_iff {f : α ↪ β} {B : Set β} :
    (M.mapEmbedding f).Base B ↔ M.Base (f ⁻¹' B) ∧ B ⊆ range f := by
  rw [mapEmbedding, map_base_iff]
  refine ⟨?_, fun ⟨h,h'⟩ ↦ ⟨f ⁻¹' B, h, by rwa [eq_comm, image_preimage_eq_iff]⟩⟩
  rintro ⟨B, hB, rfl⟩
  rw [preimage_image_eq _ f.injective]
  exact ⟨hB, image_subset_range _ _⟩

@[simp] lemma mapEmbedding_basis_iff {f : α ↪ β} {I X : Set β} :
    (M.mapEmbedding f).Basis I X ↔ M.Basis (f ⁻¹' I) (f ⁻¹' X) ∧ I ⊆ X ∧ X ⊆ range f := by
  rw [mapEmbedding, map_basis_iff']
  refine ⟨?_, fun ⟨hb, hIX, hX⟩ ↦ ?_⟩
  · rintro ⟨I, X, hIX, rfl, rfl⟩
    simp [preimage_image_eq _ f.injective, image_subset f hIX.subset, hIX]
  obtain ⟨X, rfl⟩ := subset_range_iff_exists_image_eq.1 hX
  obtain ⟨I, -, rfl⟩ := subset_image_iff.1 hIX
  exact ⟨I, X, by simpa [preimage_image_eq _ f.injective] using hb⟩

lemma restrictSubtype_basis_iff {Y : Set α} {I X : Set Y} :
    (M.restrictSubtype Y).Basis I X ↔ M.Basis' I X := by
  rw [restrictSubtype, comap_basis_iff, and_iff_right Subtype.val_injective.injOn,
    and_iff_left_of_imp, basis_restrict_iff', basis'_iff_basis_inter_ground]
  · simp
  exact fun h ↦ (image_subset_image_iff Subtype.val_injective).1 h.subset

lemma restrictSubtype_base_iff {B : Set X} : (M.restrictSubtype X).Base B ↔ M.Basis' B X := by
  rw [restrictSubtype, comap_base_iff]
  simp [Subtype.val_injective.injOn, Subset.rfl, basis_restrict_iff', basis'_iff_basis_inter_ground]

@[simp] lemma restrictSubtype_ground_base_iff {B : Set M.E} :
    (M.restrictSubtype M.E).Base B ↔ M.Base B := by
  rw [restrictSubtype_base_iff, basis'_iff_basis, basis_ground_iff]

@[simp] lemma restrictSubtype_ground_basis_iff {I X : Set M.E} :
    (M.restrictSubtype M.E).Basis I X ↔ M.Basis I X := by
  rw [restrictSubtype_basis_iff, basis'_iff_basis]

@[simp] lemma mapEquiv_basis_iff {α β : Type*} {M : Matroid α} (f : α ≃ β) {I X : Set β} :
    (M.mapEquiv f).Basis I X ↔ M.Basis (f.symm '' I) (f.symm '' X) := by
  rw [mapEquiv_eq_map, map_basis_iff']
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨_, _, h, by simp, by simp⟩⟩
  obtain ⟨I, X, hIX, rfl, rfl⟩ := h
  simpa

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

end Matroid
