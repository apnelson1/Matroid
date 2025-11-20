import Mathlib.Combinatorics.Matroid.Closure

variable {α : Type*} {X Y D : Set α} {M : Matroid α}

open Set

lemma Set.diff_diff_invOn_Iic (s : Set α) : InvOn (s \ ·) (s \ ·) (Iic s) (Iic s) :=
  ⟨fun t ht ↦ by simpa, fun t ht ↦ by simpa⟩

lemma Set.diff_bijOn_subset (s : Set α) : BijOn (s \ ·) (Iic s) (Iic s) :=
  s.diff_diff_invOn_Iic.bijOn (fun _ _ ↦ diff_subset) fun _ _ ↦ diff_subset

namespace Matroid

lemma Coindep.subset {I J : Set α} (h : M.Coindep I) (hJI : J ⊆ I) : M.Coindep J :=
  Indep.subset h hJI

/-- `M.Codep D` means that `D` is a subset of `M.E` that is dependent in `M✶`. -/
def Codep (M : Matroid α) (D : Set α) : Prop := M✶.Dep D

lemma Coindep.not_codep (hD : M.Coindep D) : ¬ M.Codep D :=
  Indep.not_dep hD

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma Codep.subset_ground (h : M.Codep D) : D ⊆ M.E :=
  Dep.subset_ground (M := M✶) h

lemma Codep.dep_dual (h : M.Codep D) : M✶.Dep D := h

lemma Codep.not_coindep (h : M.Codep D) : ¬ M.Coindep D :=
  h.dep_dual.not_indep

lemma codep_iff : M.Codep D ↔ ¬ M.Coindep D ∧ D ⊆ M.E := by
  rw [Codep, dep_iff]
  rfl

-- If this lemma is good, it belongs earlier.
@[simp]
lemma not_indep_compl_iff : ¬ M.Indep (M.E \ X) ↔ M.Dep (M.E \ X) := by
  rw [not_indep_iff]

@[simp]
lemma not_dep_compl_iff : ¬ M.Dep (M.E \ X) ↔ M.Indep (M.E \ X) := by
  rw [not_dep_iff]

@[simp]
lemma dep_dual_iff : M✶.Dep D ↔ M.Codep D := Iff.rfl

lemma codep_def : M.Codep D ↔ M✶.Dep D :=
  dep_dual_iff.symm

lemma not_coindep_iff (hDE : D ⊆ M.E := by aesop_mat) :
    ¬ M.Coindep D ↔ M.Codep D := by
  rw [codep_iff, and_iff_left hDE]

lemma not_codep_iff (hDE : D ⊆ M.E := by aesop_mat) :
    ¬ M.Codep D ↔ M.Coindep D := by
  rw [← not_coindep_iff, not_not]

@[simp]
lemma not_coindep_compl_iff : ¬ M.Coindep (M.E \ X) ↔ M.Codep (M.E \ X) := by
  rw [not_coindep_iff]

@[simp]
lemma not_codep_compl_iff : ¬ M.Codep (M.E \ X) ↔ M.Coindep (M.E \ X) := by
  rw [not_codep_iff]

@[simp]
lemma codep_dual_iff : M✶.Codep D ↔ M.Dep D := by
  simp [codep_iff, dep_iff]

lemma Codep.not_indep (h : M.Codep D) : ¬ M✶.Indep D :=
  h.not_coindep

lemma coindep_or_codep (M : Matroid α) (X : Set α) (hXE : X ⊆ M.E := by aesop_mat) :
    M.Coindep X ∨ M.Codep X := by
  rw [codep_def, coindep_def]
  exact M✶.indep_or_dep

lemma Codep.superset (h : M.Codep D) (hDX : D ⊆ X) (hXE : X ⊆ M.E := by aesop_mat) :
    M.Codep X :=
  ⟨fun hX ↦ h.not_coindep (hX.subset hDX), hXE⟩
