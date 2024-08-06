import Mathlib.Data.Matroid.Restrict
import Mathlib.Tactic

open Set

variable {α : Type*} {M : Matroid α}
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

lemma Indep.augment_finset [DecidableEq α] {I J : Finset α} (hI : M.Indep I) (hJ : M.Indep J)
    (hIJ : I.card < J.card) : ∃ e ∈ J, e ∉ I ∧ M.Indep (insert e I) := by
  obtain ⟨x, hx, hxI⟩ := hI.augment hJ (by simpa [encard_eq_coe_toFinset_card] )
  simp only [mem_diff, Finset.mem_coe] at hx
  exact ⟨x, hx.1, hx.2, hxI⟩

lemma basis_restrict_univ_iff {I X : Set α} : (M ↾ univ).Basis I X ↔ M.Basis' I X := by
  rw [basis_restrict_iff', basis'_iff_basis_inter_ground, and_iff_left (subset_univ _)]
