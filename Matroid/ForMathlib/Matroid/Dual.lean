import Mathlib.Combinatorics.Matroid.Closure

variable {α : Type*} {X Y D : Set α} {M : Matroid α}

open Set

lemma Set.diff_diff_invOn_Iic (s : Set α) : InvOn (s \ ·) (s \ ·) (Iic s) (Iic s) :=
  ⟨fun t ht ↦ by simpa, fun t ht ↦ by simpa⟩

lemma Set.diff_bijOn_subset (s : Set α) : BijOn (s \ ·) (Iic s) (Iic s) :=
  s.diff_diff_invOn_Iic.bijOn (fun _ _ ↦ diff_subset) fun _ _ ↦ diff_subset

namespace Matroid


/-- `M.Codep D` means that `D` is a subset of `M.E` that is dependent in `M✶`. -/
@[mk_iff]
structure Codep (M : Matroid α) (D : Set α) : Prop where
  not_coindep : ¬ M.Coindep D
  subset_ground : D ⊆ M.E

attribute [aesop unsafe 20% (rule_sets := [Matroid])] Codep.subset_ground

lemma Codep.dep_dual (h : M.Codep D) : M✶.Dep D :=
  ⟨h.not_coindep, h.subset_ground⟩

@[simp]
lemma codep_dual_iff : M✶.Codep D ↔ M.Dep D := by
  simp [codep_iff, dep_iff]

lemma Codep.not_indep (h : M.Codep D) : ¬ M✶.Indep D :=
  h.not_coindep

@[simp]
lemma dep_dual_iff : M✶.Dep D ↔ M.Codep D := by
  rw [dep_iff, codep_iff, dual_ground]

lemma codep_def : M.Codep D ↔ M✶.Dep D :=
  dep_dual_iff.symm

lemma coindep_or_codep (M : Matroid α) (X : Set α) (hXE : X ⊆ M.E := by aesop_mat) :
    M.Coindep X ∨ M.Codep X := by
  rw [codep_def, coindep_def]
  exact M✶.indep_or_dep
