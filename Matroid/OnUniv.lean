import Mathlib.Data.Matroid.Circuit

section OnUniv

namespace Matroid

variable {α : Type*} {M : Matroid α}

open Set

@[mk_iff]
class OnUniv (M : Matroid α) : Prop where
  ground_eq : M.E = univ

@[simp]
lemma ground_eq_univ (M : Matroid α) [OnUniv M] : M.E = univ :=
  OnUniv.ground_eq

@[simp, aesop safe (rule_sets := [Matroid])]
lemma OnUniv.subset_ground (M : Matroid α) [M.OnUniv] (X : Set α) : X ⊆ M.E := by
  simp [OnUniv.ground_eq]
