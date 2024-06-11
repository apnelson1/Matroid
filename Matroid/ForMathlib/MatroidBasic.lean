import Mathlib.Data.Matroid.Restrict

open Set

variable {α : Type*}
namespace Matroid

lemma nonempty_type (M : Matroid α) [h : M.Nonempty] : Nonempty α :=
  let ⟨⟨e,_⟩⟩ := h
  ⟨e⟩

@[simp] theorem ofExistsMatroid_indep_eq {α : Type*} (E : Set α) (Indep) (hM) :
    (Matroid.ofExistsMatroid E Indep hM).Indep = Indep := rfl

@[simp] theorem ofExistsMatroid_ground_eq {α : Type*} (E : Set α) (Indep) (hM) :
    (Matroid.ofExistsMatroid E Indep hM).E = E := rfl

theorem Restriction.indep_iff {α : Type*} {M N : Matroid α} (hMN : N ≤r M) {I : Set α} :
    N.Indep I ↔ M.Indep I ∧ I ⊆ N.E :=
  ⟨fun h ↦ ⟨h.of_restriction hMN, h.subset_ground⟩, fun h ↦ h.1.indep_restriction hMN h.2⟩

lemma insert_base_of_insert_indep {M : Matroid α} {I : Set α} {e f : α}
    (he : e ∉ I) (hf : f ∉ I) (heI : M.Base (insert e I)) (hfI : M.Indep (insert f I)) :
    M.Base (insert f I) := by
  obtain (rfl | hef) := eq_or_ne e f; assumption
  simpa [diff_singleton_eq_self he, hfI]
    using heI.exchange_base_of_indep (e := e) (f := f) (by simp [hef.symm, hf])

lemma Indep.base_of_forall_insert {M : Matroid α} {B : Set α} (hB : M.Indep B)
    (hBmax : ∀ e ∈ M.E \ B, ¬ M.Indep (insert e B)) : M.Base B := by
  refine by_contra fun hnb ↦ ?_
  obtain ⟨B', hB'⟩ := M.exists_base
  obtain ⟨e, he, h⟩ := hB.exists_insert_of_not_base hnb hB'
  exact hBmax e ⟨hB'.subset_ground he.1, he.2⟩ h
