import Mathlib.Data.Matroid.Closure
import Mathlib.Data.Matroid.Constructions
import Mathlib.Tactic

open Set

variable {α : Type*} {M : Matroid α}
namespace Matroid

lemma nonempty_type (M : Matroid α) [h : M.Nonempty] : Nonempty α :=
  ⟨M.ground_nonempty.some⟩

@[simp] theorem ofExistsMatroid_indep_eq {α : Type*} (E : Set α) (Indep) (hM) :
    (Matroid.ofExistsMatroid E Indep hM).Indep = Indep := rfl

@[simp] theorem ofExistsMatroid_ground_eq {α : Type*} (E : Set α) (Indep) (hM) :
    (Matroid.ofExistsMatroid E Indep hM).E = E := rfl

theorem Restriction.indep_iff {α : Type*} {M N : Matroid α} (hMN : N ≤r M) {I : Set α} :
    N.Indep I ↔ M.Indep I ∧ I ⊆ N.E :=
  ⟨fun h ↦ ⟨h.of_restriction hMN, h.subset_ground⟩, fun h ↦ h.1.indep_restriction hMN h.2⟩

lemma Basis'.base_restrict {I X : Set α} (hIX : M.Basis' I X) : (M ↾ X).Base I :=
  hIX

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

lemma Indep.basis_iff_eq {I J : Set α} (hI : M.Indep I) : M.Basis J I ↔ J = I := by
  refine ⟨fun h ↦ h.eq_of_subset_indep hI h.subset rfl.subset, ?_⟩
  rintro rfl
  exact hI.basis_self

theorem ext_indep {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
    (h : ∀ ⦃I⦄, I ⊆ M₁.E → (M₁.Indep I ↔ M₂.Indep I)) : M₁ = M₂ := eq_of_indep_iff_indep_forall hE h

theorem ext_base {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
    (h : ∀ ⦃B⦄, B ⊆ M₁.E → (M₁.Base B ↔ M₂.Base B)) : M₁ = M₂ := eq_of_base_iff_base_forall hE h

lemma ext_iff_base {M₁ M₂ : Matroid α} :
    M₁ = M₂ ↔ M₁.E = M₂.E ∧ ∀ ⦃B⦄, B ⊆ M₁.E → (M₁.Base B ↔ M₂.Base B) :=
  ⟨fun h ↦ by simp [h], fun ⟨hE, h⟩ ↦ ext_base hE h⟩

lemma ext_iff_indep {M₁ M₂ : Matroid α} :
    M₁ = M₂ ↔ M₁.E = M₂.E ∧ ∀ ⦃I⦄, I ⊆ M₁.E → (M₁.Indep I ↔ M₂.Indep I) :=
  ⟨fun h ↦ by simp [h], fun ⟨hE, h⟩ ↦ ext_indep hE h⟩

/-- If every base of `M₁` is independent in `M₂` and vice versa, then `M₁ = M₂`. -/
lemma ext_base_indep {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E) (h₁ : ∀ ⦃B⦄, M₁.Base B → M₂.Indep B)
    (h₂ : ∀ ⦃B⦄, M₂.Base B → M₁.Indep B) : M₁ = M₂ := by
  refine ext_indep hE fun I hIE ↦ ⟨fun hI ↦ ?_, fun hI ↦ ?_⟩
  · obtain ⟨B, hB, hIB⟩ := hI.exists_base_superset
    exact (h₁ hB).subset hIB
  obtain ⟨B, hB, hIB⟩ := hI.exists_base_superset
  exact (h₂ hB).subset hIB

lemma eq_loopyOn_or_rkPos' (M : Matroid α) : (∃ E, M = loopyOn E) ∨ M.RkPos := by
  obtain h | h := M.eq_loopyOn_or_rkPos
  · exact .inl ⟨M.E, h⟩
  exact .inr h

lemma rkPos_iff_empty_not_spanning : M.RkPos ↔ ¬ M.Spanning ∅ := by
  rw [rkPos_iff_empty_not_base, not_iff_not]
  exact ⟨fun h ↦ h.spanning, fun h ↦ h.base_of_indep M.empty_indep⟩
