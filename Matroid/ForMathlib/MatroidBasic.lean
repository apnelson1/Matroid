import Mathlib.Data.Matroid.Restrict

namespace Matroid

@[simp] theorem ofExistsMatroid_indep_eq {α : Type*} (E : Set α) (Indep) (hM) :
    (Matroid.ofExistsMatroid E Indep hM).Indep = Indep := rfl

@[simp] theorem ofExistsMatroid_ground_eq {α : Type*} (E : Set α) (Indep) (hM) :
    (Matroid.ofExistsMatroid E Indep hM).E = E := rfl

theorem Restriction.indep_iff {α : Type*} {M N : Matroid α} (hMN : N ≤r M) {I : Set α} :
    N.Indep I ↔ M.Indep I ∧ I ⊆ N.E :=
  ⟨fun h ↦ ⟨h.of_restriction hMN, h.subset_ground⟩, fun h ↦ h.1.indep_restriction hMN h.2⟩
