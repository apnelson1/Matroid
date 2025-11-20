import Mathlib.Combinatorics.Matroid.Circuit
import Matroid.ForMathlib.Matroid.Closure

namespace Matroid

open Set

variable {α : Type*} {M : Matroid α} {D C X : Set α} {e : α}

lemma Codep.exists_isCocircuit_subset (h : M.Codep D) : ∃ C ⊆ D, M.IsCocircuit C :=
  h.dep_dual.exists_isCircuit_subset

lemma IsCocircuit.codep (h : M.IsCocircuit C) : M.Codep C :=
  h.dep

lemma isCocircuit_iff_minimal_codep : M.IsCocircuit C ↔ Minimal M.Codep C := Iff.rfl

lemma codep_iff_exists_isCocircuit_subset (hDE : D ⊆ M.E := by aesop_mat) :
    M.Codep D ↔ ∃ C ⊆ D, M.IsCocircuit C :=
  dep_iff_superset_isCircuit

-- TODO : rename `dep_iff_superset_isCircuit` to `dep_iff_exists ...`

lemma exists_isCircuit_or_exists_eq_freeOn (M : Matroid α) :
    (∃ C, M.IsCircuit C) ∨ ∃ E, M = freeOn E := by
  rw [← dual_rankPos_iff_exists_isCircuit, or_iff_not_imp_left, not_rankPos_iff]
  intro hM
  refine ⟨M.E, by rw [← dual_inj, hM, freeOn_dual_eq, dual_ground]⟩

lemma exists_isCocircuit_or_exists_eq_loopyOn (M : Matroid α) :
    (∃ C, M.IsCocircuit C) ∨ ∃ E, M = loopyOn E := by
  obtain h | ⟨E, h_eq⟩ := M✶.exists_isCircuit_or_exists_eq_freeOn
  · exact .inl h
  exact .inr ⟨E, by rwa [← dual_inj, freeOn_dual_eq, dual_dual] at h_eq⟩
