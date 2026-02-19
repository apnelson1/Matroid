import Matroid.Connectivity.ConnSystem.Matroid

open Set Set.Notation Function

set_option linter.style.longLine false

namespace Matroid

variable {α : Type*} {M : Matroid α} {B B' I I' J J' K X Y : Set α}


section core

/-- The core of a set is its intersection with the set of nonloop, noncoloop elements.
This does not change the connectivity of a set, and is stable under duality.
This is mostly an implementation detail, used for relating connectivity to junk elements . -/
protected def core (M : Matroid α) (X : Set α) := ((X \ M.loops) \ M.coloops) ∩ M.E

lemma core_def (M : Matroid α) (X : Set α) : M.core X = ((X \ M.loops) \ M.coloops) ∩ M.E :=
  rfl

@[simp]
lemma core_subset (M : Matroid α) (X : Set α) : M.core X ⊆ X :=
  inter_subset_left.trans <| diff_subset.trans diff_subset

@[simp, aesop safe (rule_sets := [Matroid])]
lemma core_subset_ground (M : Matroid α) (X : Set α) : M.core X ⊆ M.E :=
  inter_subset_right

@[simp]
lemma core_inter_ground (M : Matroid α) (X : Set α) : M.core (X ∩ M.E) = M.core X := by
  simp_rw [core_def]
  tauto_set

@[simp]
lemma core_empty (M : Matroid α) : M.core ∅ = ∅ := by
  simpa using M.core_subset ∅

@[simp]
lemma core_dual (M : Matroid α) (X : Set α) : M✶.core X = M.core X := by
  rw [core_def, coloops, dual_dual, diff_diff_comm, dual_ground]
  rfl

@[simp]
lemma removeLoops_core (M : Matroid α) (X : Set α) : M.removeLoops.core X = M.core X := by
  rw [core_def, removeLoops_ground_eq, setOf_isNonloop_eq, core_def, loops_eq_empty,
    removeLoops_coloops_eq]
  tauto_set

@[simp]
lemma eConn_core (M : Matroid α) : M.eConn (M.core X) = M.eConn X := by
  rw [Matroid.core, eConn_inter_ground, eConn_diff_of_subset_coloops rfl.subset,
    eConn_diff_of_subset_loops rfl.subset]

@[simp]
lemma core_core (M : Matroid α) (X : Set α) : M.core (M.core X) = M.core X := by
  rw [core_def, core_def]
  tauto_set

@[simp]
lemma core_union (M : Matroid α) (X Y : Set α) : M.core (X ∪ Y) = M.core X ∪ M.core Y := by
  simp_rw [core_def]
  tauto_set

@[simp]
lemma core_inter (M : Matroid α) (X Y : Set α) : M.core (X ∩ Y) = M.core X ∩ M.core Y := by
  simp_rw [core_def]
  tauto_set

@[simp]
lemma core_diff (M : Matroid α) (X Y : Set α) : M.core (X \ Y) = M.core X \ M.core Y := by
  simp_rw [core_def]
  tauto_set

lemma core_subset_core (M : Matroid α) (hXY : X ⊆ Y) : M.core X ⊆ M.core Y := by
  rw [← diff_eq_empty, ← core_diff, diff_eq_empty.2 hXY, core_empty]

@[simp]
lemma core_subset_inter_ground (M : Matroid α) (X : Set α) : M.core X ⊆ X ∩ M.E :=
  inter_subset_inter_left _ <| diff_subset.trans diff_subset

@[simp]
lemma core_delete_subset (M : Matroid α) (X D : Set α) : (M ＼ D).core X ⊆ M.core X := by
  simp_rw [core_def, delete_loops_eq, coloops, dual_delete, contract_loops_eq,
    delete_ground]
  have := M✶.closure_subset_closure (empty_subset D)
  tauto_set

@[simp]
lemma core_restrict_subset (M : Matroid α) (X R : Set α) : (M ↾ R).core X ⊆ M.core X := by
  rw [← removeLoops_core, restrict_removeLoops, removeLoops_core, ← delete_compl]
  apply core_delete_subset

@[simp]
lemma core_contract_subset (M : Matroid α) (X C : Set α) : (M ／ C).core X ⊆ M.core X := by
   rw [← core_dual, dual_contract, ← M.core_dual]
   apply core_delete_subset

end core
