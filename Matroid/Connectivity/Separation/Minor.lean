import Matroid.Connectivity.Separation.Basic
import Matroid.Bool

open Set Function

variable {α : Type*} {M N : Matroid α} {k : ℕ∞} {e f : α} {A B C D C' D' X X' Y Y' : Set α}
    {i j b : Bool} {P : M.Separation} {C D : Set α} {e f : α}

namespace Matroid.Separation

@[simp, aesop unsafe 10% (rule_sets := [Matroid])]
lemma subset_ground_of_delete (P : (M ＼ D).Separation) (i : Bool) : P i ⊆ M.E :=
  P.subset_ground.trans diff_subset

@[simp, aesop unsafe 10% (rule_sets := [Matroid])]
lemma left_subset_ground_of_contract (P : (M ／ C).Separation) (i : Bool) : P i ⊆ M.E :=
  P.subset_ground.trans diff_subset

@[simp]
lemma disjoint_contract (P : (M ／ C).Separation) (i : Bool) : Disjoint (P i) C := by
  grw [P.subset_ground]
  exact disjoint_sdiff_left

@[simp]
lemma disjoint_delete (P : (M ＼ D).Separation) (i : Bool) : Disjoint (P i) D := by
  grw [P.subset_ground]
  exact disjoint_sdiff_left

lemma compl_remove {b} (P : (M.remove b X).Separation) (hX : X ⊆ M.E := by aesop_mat) (i : Bool) :
    M.E \ P i = P (!i) ∪ X := by
  grw [← P.compl_eq, remove_ground, diff_diff_comm, diff_union_self, eq_comm, union_eq_left,
    subset_diff, and_iff_right hX, P.subset_ground]
  exact disjoint_sdiff_right.mono_right <| (remove_ground ..).subset

lemma compl_delete (P : (M ＼ D).Separation) (hD : D ⊆ M.E := by aesop_mat) (i : Bool) :
    M.E \ P i = P (!i) ∪ D :=
  P.compl_remove (b := false) hD i

lemma compl_delete_not (P : (M ＼ D).Separation) (hD : D ⊆ M.E := by aesop_mat) (i : Bool) :
    M.E \ (P !i) = P i ∪ D := by
  simpa using P.compl_delete hD !i

lemma compl_contract (P : (M ／ C).Separation) (hC : C ⊆ M.E := by aesop_mat) (i : Bool) :
    M.E \ (P i) = P (!i) ∪ C :=
  P.compl_remove (b := true) hC i

lemma compl_contract_not (P : (M ／ C).Separation) (hC : C ⊆ M.E := by aesop_mat) (i : Bool) :
    M.E \ (P !i) = P i ∪ C := by
  simpa using P.compl_contract hC !i

@[simp]
lemma apply_inter_ground_of_delete (P : (M ＼ D).Separation) (i : Bool) : P i ∩ M.E = P i :=
  inter_eq_self_of_subset_left <| P.subset.trans diff_subset

@[simp]
lemma apply_inter_ground_of_contract (P : (M ／ C).Separation) (i : Bool) : P i ∩ M.E = P i :=
  inter_eq_self_of_subset_left <| P.subset.trans diff_subset

@[simp]
lemma apply_inter_ground_of_remove (P : (M.remove b X).Separation) (i : Bool) : P i ∩ M.E = P i :=
  inter_eq_self_of_subset_left <| P.subset.trans <| by simp

@[simp]
lemma compl_union_contract (P : (M ／ C).Separation) (i : Bool) : M.E \ (P i ∪ C) = P !i := by
  rw [← P.compl_eq, Set.union_comm, contract_ground, diff_diff]

@[simp]
lemma compl_union_delete (P : (M ＼ D).Separation) (i : Bool) : M.E \ (P i ∪ D) = P !i := by
  rw [← P.compl_eq, Set.union_comm, delete_ground, diff_diff]

lemma compl_delete_singleton (P : (M ＼ {e}).Separation) (he : e ∈ M.E := by aesop_mat) (i : Bool) :
    M.E \ (P i) = insert e (P (!i)) := by
  rw [compl_delete, union_singleton]

lemma compl_contract_singleton (P : (M ／ {e}).Separation) (he : e ∈ M.E := by aesop_mat)
    (i : Bool) : M.E \ (P i) = insert e (P !i) := by
  rw [compl_contract, union_singleton]

set_option backward.isDefEq.respectTransparency false in
/-- The generalized Bixby-Coullard inequality for pairs of separations. -/
lemma eConn_inter_add_eConn_inter_le_add (P : (M ／ X).Separation) (Q : (M ＼ X).Separation)
    (i : Bool) :
    M.eConn (P i ∩ Q i) + M.eConn (P (!i) ∩ Q (!i)) ≤ P.eConn + Q.eConn + M.eConn X := by
  wlog hX : X ⊆ M.E generalizing X P Q with aux
  · simpa using aux (X := X ∩ M.E) (P.copy (by simp)) (Q.copy (by simp)) inter_subset_right
  convert M.eConn_inter_add_eConn_union_union_le (C := P i) (D := Q i) (X := X) (by simp) (by simp)
    using 2
  · rw [union_assoc, X.union_comm, union_union_distrib_right, ← Q.compl_contract_not,
      ← P.compl_delete_not, dual_ground, ← diff_inter, eConn_compl]
  simp

/-- The Bixby-Coullard inequality for pairs of separations. -/
lemma eConn_inter_add_eConn_inter_le_add_of_singleton
    (P : (M ／ {e}).Separation) (Q : (M ＼ {e}).Separation) (i : Bool) :
    M.eConn (P i ∩ Q i) + M.eConn (P (!i) ∩ Q (!i)) ≤ P.eConn + Q.eConn + 1 := by
  grw [P.eConn_inter_add_eConn_inter_le_add, eConn_le_encard, encard_singleton]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma induce_apply_remove (P : M.Separation) (X : Set α) (b i j : Bool) :
    P.induce (M.remove b X) i j = P j \ X := by
  grw [induce_apply_subset _ (by simp), remove_ground, ← inter_diff_assoc,
    P.inter_ground_left]

lemma induce_apply_remove_of_remove (P : (M.remove b X).Separation) (hXY : X ⊆ Y) (i j : Bool) :
    P.induce (M.remove b Y) i j = P j \ Y := by
  rw [induce_apply_subset _ (by grind), remove_ground, ← inter_diff_assoc,
    inter_eq_self_of_subset_left]
  grw [P.subset, remove_ground, diff_subset]

@[simp]
lemma induce_apply_delete (P : M.Separation) (D : Set α) (i j : Bool) :
    P.induce (M ＼ D) i j = P j \ D :=
  P.induce_apply_remove D false i j

lemma induce_apply_delete_of_delete (P : (M ＼ X).Separation) (hXY : X ⊆ Y) (i j : Bool) :
    P.induce (M ＼ Y) i j = P j \ Y :=
  induce_apply_remove_of_remove (b := false) P hXY i j

@[simp]
lemma induce_apply_contract (P : M.Separation) (C : Set α) (i j : Bool) :
    P.induce (M ／ C) i j = P j \ C :=
  P.induce_apply_remove C true i j

lemma induce_apply_contract_of_contract (P : (M ／ X).Separation) (hXY : X ⊆ Y) (i j : Bool) :
    P.induce (M ／ Y) i j = P j \ Y :=
  induce_apply_remove_of_remove (b := true) P hXY i j

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma induce_apply_contract_delete (P : M.Separation) (C D : Set α) (i j : Bool) :
    P.induce (M ／ C ＼ D) i j = P j \ (C ∪ D) := by
  rw [induce_apply_subset _ (by grind), delete_ground, contract_ground, ← inter_diff_assoc,
    ← inter_diff_assoc, P.inter_ground_left, diff_diff]

lemma induce_apply_of_remove_eq_cond {b} (P : (M.remove b X).Separation) (i j : Bool)
    (hX : X ⊆ M.E := by aesop_mat) :
    P.induce M i j = bif j == i then P j ∪ X else P j := by
  rw [induce_apply_eq_cond, remove_ground, diff_diff_cancel_left hX, inter_eq_self_of_subset_left]
  grw [P.subset, remove_ground, diff_subset]

@[simp]
lemma induce_apply_of_remove_self {b} (P : (M.remove b X).Separation) (i : Bool)
    (hX : X ⊆ M.E := by aesop_mat) : P.induce M i i = P i ∪ X := by
  simp [induce_apply_of_remove_eq_cond P _ _ hX]

lemma induce_apply_of_delete_eq_cond {D} (P : (M ＼ D).Separation) (i : Bool)
    (hD : D ⊆ M.E := by aesop_mat) :
    P.induce M i j = bif j == i then P j ∪ D else P j :=
  P.induce_apply_of_remove_eq_cond (b := false) i j hD

@[simp]
lemma induce_apply_of_delete_self (P : (M ＼ X).Separation) (i : Bool)
    (hX : X ⊆ M.E := by aesop_mat) : P.induce M i i = P i ∪ X :=
  P.induce_apply_of_remove_self (b := false) i hX

lemma induce_apply_of_contract_eq_cond (P : (M ／ X).Separation) (i : Bool)
    (hX : X ⊆ M.E := by aesop_mat) :
    P.induce M i j = bif j == i then P j ∪ X else P j :=
  P.induce_apply_of_remove_eq_cond (b := true) i j hX

@[simp]
lemma induce_apply_of_contract_self (P : (M ／ X).Separation) (i : Bool)
    (hX : X ⊆ M.E := by aesop_mat) : P.induce M i i = P i ∪ X :=
  P.induce_apply_of_remove_self (b := true) i hX

lemma induce_remove_congr (P : M.Separation) {b : Bool} (hXY : X ∩ M.E = Y ∩ M.E) :
    P.induce (M.remove b X) = (P.induce (M.remove b Y)).copy
      (by rw [← remove_inter_ground, ← hXY, remove_inter_ground]) := by
  refine Separation.ext_bool true ?_
  simp only [induce_apply_remove, copy_apply]
  have : P true ⊆ M.E := P.subset
  tauto_set

lemma induce_remove_eq_inter_ground (P : M.Separation) (b X) :
    P.induce (M.remove b X) = (P.induce (M.remove b (X ∩ M.E))).copy (by simp) :=
  P.induce_remove_congr <| by simp

lemma induce_remove_inter_ground_eq (P : M.Separation) (b X) :
    P.induce (M.remove b (X ∩ M.E)) = (P.induce (M.remove b X)).copy (by simp) :=
  P.induce_remove_congr <| by simp

@[simp]
lemma induce_induce_remove_eq_self {b X i} (P : (M.remove b X).Separation) :
    (P.induce M i).induce (M.remove b X) = P :=
  induce_induce_eq_self _ (by simp) i

lemma induce_induce_remove_of_subset {b X i} (P : M.Separation) (hX : X ⊆ P i) :
    (P.induce (M.remove b X)).induce M i = P :=
  induce_induce_eq_self_of_subset_union _ (by simp) <| by
    grw [remove_ground, hX, P.compl_eq]

lemma induce_remove_union (P : M.Separation) (X Y : Set α) (b : Bool):
    P.induce (M.remove b (X ∪ Y)) = ((P.induce (M.remove b X)).induce
      ((M.remove b X).remove b Y)).copy (by simp) :=
  Separation.ext <| by grind [induce_false_true, copy_apply]

@[simp]
lemma induce_union_remove (P : M.Separation) (X Y : Set α) (b : Bool) :
    ((P.induce (M.remove b X)).induce ((M.remove b X).remove b Y)) =
      (P.induce (M.remove b (X ∪ Y))).copy (by simp) :=
  Separation.ext <| by grind [induce_false_true, copy_apply]

@[simp]
lemma induce_induce_remove (P : M.Separation) (X : Set α) (i b : Bool) :
    (P.induce N i).induce (N.remove b X) = P.induce (N.remove b X) i :=
  Separation.ext_bool (!i) <| by simp [inter_diff_assoc]

lemma induce_contract_congr (P : M.Separation) (hC : C ∩ M.E = C' ∩ M.E) :
    P.induce (M ／ C) = (P.induce (M ／ C')).copy
      (by rwa [eq_comm, contract_eq_contract_iff]) := by
  simp_rw [← M.remove_true C, induce_remove_congr P hC]
  simp

lemma induce_contract_eq_inter_ground (P : M.Separation) (C) :
    P.induce (M ／ C) = (P.induce (M ／ (C ∩ M.E))).copy (by simp) :=
  P.induce_remove_eq_inter_ground true C

lemma induce_contract_inter_ground_eq (P : M.Separation) (C) :
    P.induce (M ／ (C ∩ M.E)) = (P.induce (M ／ C)).copy (by simp) :=
  P.induce_remove_inter_ground_eq true C

lemma induce_contract_union (P : M.Separation) (C C' : Set α) :
    P.induce (M ／ (C ∪ C')) = ((P.induce (M ／ C)).induce (M ／ C ／ C')).copy (by simp) :=
  induce_remove_union P C C' true

@[simp]
lemma induce_union_contract (P : M.Separation) (C C' : Set α) :
    (P.induce (M ／ C)).induce (M ／ C ／ C') = (P.induce (M ／ (C ∪ C'))).copy (by simp) :=
  induce_union_remove (b := true) P C C'

@[simp]
lemma induce_induce_contract_eq_self {X i} (P : (M ／ X).Separation) :
    (P.induce M i).induce (M ／ X) = P :=
  induce_induce_remove_eq_self (b := true) P

@[simp]
lemma induce_induce_contract (P : M.Separation) (X : Set α) (i : Bool) :
    (P.induce N i).induce (N ／ X) = P.induce (N ／ X) i :=
  induce_induce_remove P X i true

lemma induce_induce_contract_of_subset {X i} (P : M.Separation) (hX : X ⊆ P i) :
    (P.induce (M ／ X)).induce M i = P :=
  P.induce_induce_remove_of_subset (b := true) hX

lemma induce_delete_eq_inter_ground (P : M.Separation) (D) :
    P.induce (M ＼ D) = (P.induce (M ＼ (D ∩ M.E))).copy (by simp) :=
  P.induce_remove_eq_inter_ground false D

lemma induce_delete_inter_ground_eq (P : M.Separation) (D) :
    P.induce (M ＼ (D ∩ M.E)) = (P.induce (M ＼ D)).copy (by simp) :=
  P.induce_remove_inter_ground_eq false D

lemma induce_delete_union (P : M.Separation) (D D' : Set α) :
    P.induce (M ／ (D ∪ D')) = ((P.induce (M ／ D)).induce (M ／ D ／ D')).copy (by simp) :=
  induce_remove_union P D D' false

@[simp]
lemma induce_union_delete (P : M.Separation) (D D' : Set α) :
    (P.induce (M ＼ D)).induce (M ＼ D ＼ D') = (P.induce (M ＼ (D ∪ D'))).copy (by simp) :=
  induce_union_remove (b := false) P D D'

@[simp]
lemma induce_induce_delete (P : M.Separation) (X : Set α) (i : Bool) :
    (P.induce N i).induce (N ＼ X) = P.induce (N ＼ X) i :=
  P.induce_induce_remove X i false

lemma induce_delete_congr (P : M.Separation) {D D' : Set α} (hD : D ∩ M.E = D' ∩ M.E) :
    P.induce (M ＼ D) = (P.induce (M ＼ D')).copy (by rwa [eq_comm, delete_eq_delete_iff]) := by
  simp_rw [← M.remove_false D, induce_remove_congr P hD]
  simp

@[simp]
lemma induce_induce_delete_eq_self {X i} (P : (M ＼ X).Separation) :
    (P.induce M i).induce (M ＼ X) = P :=
  induce_induce_remove_eq_self (b := true) P

lemma induce_induce_delete_of_subset {X i} (P : M.Separation) (hX : X ⊆ P i) :
    (P.induce (M ＼ X)).induce M i = P :=
  P.induce_induce_remove_of_subset (b := false) hX

@[simp]
lemma restrict_eq_delete (P : M.Separation) (i : Bool) : M ↾ (P !i) = M ＼ P i := by
  rw [← delete_compl, P.compl_not_eq]

@[simp]
lemma delete_eq_restrict (P : M.Separation) (i : Bool) : M ＼ (P !i) = M ↾ P i := by
  rw [← delete_compl, P.compl_eq]

lemma contract_eq_delete_of_eConn_eq_zero (hP : P.eConn = 0) (i : Bool) :
    M ／ P i = M ＼ P i := by
 rwa [contract_eq_delete_iff_skew_compl, P.compl_eq, ← eConn_eq_zero_iff_skew]

lemma contract_eq_restrict_of_eConn_eq_zero (hP : P.eConn = 0) (i : Bool) :
    M ／ P i = M ↾ P (!i) := by
  simp [contract_eq_delete_of_eConn_eq_zero hP]

@[simp]
lemma eConn_induce_dual_contract (P : M.Separation) (X : Set α) :
    (P.induce (M✶ ／ X)).eConn = (P.induce (M ＼ X)).eConn := by
  rw [← induce_dual_eConn]
  convert rfl
  simp

@[simp]
lemma eConn_induce_dual_delete (P : M.Separation) (X : Set α) :
    (P.induce (M✶ ＼ X)).eConn = (P.induce (M ／ X)).eConn := by
  rw [← induce_dual_eConn]
  convert rfl

lemma induce_contract_delete (P : M.Separation) (C D : Set α) :
    P.induce (M ／ C ＼ D) = (P.induce (M ／ C)).induce (M ／ C ＼ D) :=
  Eq.symm <| P.induce_induce <| by simp

lemma eConn_eq_eConn_induce_contract_add (P : M.Separation) (hC : C ⊆ P i) :
    P.eConn = (P.induce (M ／ C)).eConn + M.eLocalConn (P (!i)) C := by
  have hdj : Disjoint (P (!i)) C := ((P.disjoint_bool i).mono_left hC).symm
  rw [← eConn_eq _ (!i), ← eConn_eq _ (!i), induce_apply_contract,
    eConn_eq_eConn_contract_disjoint_add (C := C) _ hdj, hdj.sdiff_eq_left]

lemma eConn_eq_eConn_induce_remove_add (P : M.Separation) (hX : X ⊆ P i) (b : Bool) :
    P.eConn = (P.induce (M.remove b X)).eConn + (M.bDual (!b)).eLocalConn (P (!i)) X := by
  cases b
  · rw [← P.eConn_induce_dual, eConn_eq_eConn_induce_contract_add (P.induce M✶) (by simpa),
      induce_dual_induce, ← induce_dual_eConn, dual_contract_dual, remove_false, Bool.not_false,
      bDual_true, induce_dual_apply]
  exact P.eConn_eq_eConn_induce_contract_add hX

lemma eConn_eq_eConn_induce_delete_add (P : M.Separation) (hD : D ⊆ P i) :
    P.eConn = (P.induce (M ＼ D)).eConn + M✶.eLocalConn (P (!i)) D :=
  P.eConn_eq_eConn_induce_remove_add hD false

lemma eConn_induce_of_remove (P : (M.remove b X).Separation) (i : Bool) :
    (P.induce M i).eConn = P.eConn + (M.bDual (!b)).eLocalConn (P !i) X := by
  rw [eConn_eq_eConn_induce_remove_add (X := X ∩ M.E) (b := b) (i := i),
    induce_remove_inter_ground_eq, induce_induce_remove_eq_self, eConn_copy, induce_apply_not,
    ← M.bDual_ground (!b), eLocalConn_inter_ground]
  grind [induce_apply_eq_cond]

lemma eConn_induce_of_contract (P : (M ／ C).Separation) (i : Bool) :
    (P.induce M i).eConn = P.eConn + M.eLocalConn (P !i) C :=
  eConn_induce_of_remove (b := true) P i

lemma eConn_induce_of_delete (P : (M ＼ D).Separation) (i : Bool) :
    (P.induce M i).eConn = P.eConn + M✶.eLocalConn (P !i) D :=
  eConn_induce_of_remove (b := false) P i

lemma eConn_induce_project_eq (P : M.Separation) (C : Set α) :
    (P.induce (M.project C)).eConn = (P.induce (M ／ C)).eConn := by
  rw [eConn_eq_eLocalConn _ true, eConn_eq_eLocalConn _ true]
  -- simp [eLocalConn_project_eq_eLocalConn_contract]
  rw [induce_apply_subset _ (by simp), induce_apply_subset _ (by simp),
    eLocalConn_inter_ground, eLocalConn_project_eq_eLocalConn_contract,
    induce_apply_subset _ (by simp), induce_apply_subset _ (by simp), eLocalConn_inter_ground]

lemma eConn_induce_contract_le (P : M.Separation) (C : Set α) :
    (P.induce (M ／ C)).eConn ≤ P.eConn := by
  grw [← Separation.eConn_eq _ false, ← P.eConn_eq false, induce_apply_contract,
    eConn_contract_diff_le]

lemma eConn_induce_remove_le (P : M.Separation) (b : Bool) (X : Set α) :
    (P.induce (M.remove b X)).eConn ≤ P.eConn := by
  cases b
  · grw [← P.eConn_induce_dual, ← (P.induce M✶).eConn_induce_contract_le X, induce_dual_induce,
       ← P.induce_dual_eConn, remove_false, dual_delete]
  exact P.eConn_induce_contract_le X

lemma eConn_induce_delete_le (P : M.Separation) (D : Set α) :
    (P.induce (M ＼ D)).eConn ≤ P.eConn :=
  P.eConn_induce_remove_le false D

lemma eConn_induce_le_eConn_induce_of_isMinor {N'} (P : M.Separation) (hNN' : N ≤m N') :
    (P.induce N).eConn ≤ (P.induce N').eConn := by
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := hNN'.exists_contract_indep_delete_coindep
  grw [← (P.induce N').eConn_induce_contract_le C,
    ← eConn_induce_delete_le ((P.induce _).induce _) D, induce_induce, induce_induce] <;>
  grind

lemma eConn_induce_delete_le_of_subset (P : M.Separation) (hDD : D ⊆ D') :
    (P.induce (M ＼ D')).eConn ≤ (P.induce (M ＼ D)).eConn :=
  eConn_induce_le_eConn_induce_of_isMinor _ (delete_isRestriction_of_subset _ hDD).isMinor

lemma eConn_induce_contract_le_of_subset (P : M.Separation) (hCC' : C ⊆ C') :
    (P.induce (M ／ C')).eConn ≤ (P.induce (M ／ C)).eConn :=
  eConn_induce_le_eConn_induce_of_isMinor _ <| contract_isMinor_of_subset _ hCC'

lemma eConn_induce_le_of_isMinor (P : M.Separation) (hNM : N ≤m M) :
    (P.induce N).eConn ≤ P.eConn := by
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := hNM.exists_contract_indep_delete_coindep
  grw [induce_contract_delete, eConn_induce_delete_le, eConn_induce_contract_le]

lemma eConn_induce_of_delete_le_eConn_add_eRelRk (P : (M ＼ D).Separation) (i : Bool) :
    (P.induce M i).eConn ≤ P.eConn + M.eRelRk (P i) (P i ∪ D) := by
  wlog hD : D ⊆ M.E generalizing D with aux
  · rw [← eRelRk_inter_ground_right, union_inter_distrib_right,
      inter_eq_self_of_subset_left (P.subset.trans diff_subset)]
    simpa using aux (D := D ∩ M.E) (P.copy (by simp)) inter_subset_right
  grw [eConn_induce_of_delete, eRelRk_eq_eRk_diff_contract,
    union_diff_cancel_left (P.disjoint_delete i).inter_eq.subset,
    ← eRelRk_eq_eRk_contract, eRelRk_eq_union_right, eLocalConn_comm,
    eLocalConn_le_dual_eRelRk _ (disjoint_delete P !i).symm, Matroid.dual_dual, dual_ground,
    union_comm, P.compl_union_delete, P.compl_delete_not, Bool.not_not, union_comm]

lemma eConn_le_eConn_induce_contract_add_eRk (P : M.Separation) (C : Set α) :
    P.eConn ≤ (P.induce (M ／ C)).eConn + M.eRk C := by
  grw [P.eConn_eq_eConn_induce_contract_add (C := C ∩ P false) inter_subset_right,
    eLocalConn_le_eRk_right,
    Separation.eConn_eq_eConn_induce_contract_add _ (i := true) (C := C ∩ _) inter_subset_right,
    induce_apply_contract, sdiff_eq_left.2 (P.disjoint_true_false.mono_right inter_subset_right),
    induce_union_contract, eConn_copy, eLocalConn_le_eRk_right, ← eRelRk_eq_eRk_contract,
    add_assoc, eRelRk_add_eRk_eq, union_comm, ← inter_union_distrib_left, P.union_eq,
    contract_inter_ground_eq, eRk_inter_ground]

lemma eConn_le_eConn_induce_delete_add (P : M.Separation) (D : Set α) :
    P.eConn ≤ (P.induce (M ＼ D)).eConn + M✶.eRk D := by
  grw [← P.eConn_induce_dual, eConn_le_eConn_induce_contract_add_eRk _ D, induce_dual_induce,
    ← induce_dual_eConn, dual_contract_dual]

lemma eConn_induce_le_eConn_add_of_contract (P : (M ／ C).Separation) (i : Bool) :
    (P.induce M i).eConn ≤ P.eConn + M.eRk C := by
  grw [eConn_le_eConn_induce_contract_add_eRk _ C, induce_induce_contract_eq_self]

lemma eConn_induce_le_eConn_add_of_delete (P : (M ＼ D).Separation) (i : Bool) :
    (P.induce M i).eConn ≤ P.eConn + M✶.eRk D := by
  grw [eConn_le_eConn_induce_delete_add _ D, induce_induce_delete_eq_self]

lemma eConn_induce_le_eConn_add_one_of_contractElem (P : (M ／ {e}).Separation) (i : Bool) :
    (P.induce M i).eConn ≤ P.eConn + 1 := by
  grw [eConn_induce_of_contract, eLocalConn_le_eRk_right, eRk_singleton_le]

lemma eConn_induce_le_eConn_add_one_of_deleteElem (P : (M ＼ {e}).Separation) (i : Bool) :
    (P.induce M i).eConn ≤ P.eConn + 1 := by
  grw [eConn_induce_of_delete, eLocalConn_le_eRk_right, eRk_singleton_le]

/-- If `P` is a separation of a restriction of `M`, and each element of `M` is spanned by
one side of `P`, then `P` extends to a separation of `M` with the same connectivity. -/
lemma exists_of_isRestriction_of_forall_mem_closure (P : N.Separation) (hNM : N ≤r M)
    (h : ∀ e, M.IsNonloop e → ∃ i, e ∈ M.closure (P i)) : ∃ (Q : M.Separation),
    (∀ i, (P i ⊆ Q i ∧ M.closure (Q i) = M.closure (P i))) ∧ Q.eConn = P.eConn := by
  have h' (e : α) (he : e ∈ M.E) : ∃ i, e ∈ M.closure (P i) ∧ (e ∈ N.E → e ∈ P i) := by
    by_cases heN : e ∈ N.E
    · obtain ⟨i, hi⟩ := IndexedPartition.exists_mem P heN
      exact ⟨i, mem_closure_of_mem' _ hi he, fun _ ↦ hi⟩
    obtain hel | henl := M.isLoop_or_isNonloop e
    · exact ⟨true, hel.mem_closure (P true), by simp [heN]⟩
    simpa [heN] using h e henl
  choose! φ hφ using h'
  have aux {i} : P i ⊆ φ ⁻¹' {i} := fun e he ↦
    P.eq_of_mem_of_mem ((hφ _ (hNM.subset (P.subset_ground he))).2 (P.subset_ground he)) he
  have auxcl {i} : M.closure (φ ⁻¹' {i}) = M.closure (P i) := by
    refine (M.closure_subset_closure aux).antisymm' ?_
    rw [← M.closure_inter_ground, M.closure_subset_closure_iff_subset_closure]
    rintro x ⟨rfl, hxE⟩
    exact (hφ x hxE).1
  refine ⟨Separation.mk (fun i ↦ φ ⁻¹' {i} ∩ M.E) ?_ ?_, ?_⟩
  · simp +contextual [Pairwise, disjoint_left]
  · simp [← union_inter_distrib_right, ← preimage_union, subset_def, iUnion_bool]
  simp only [↓mk_apply, subset_inter_iff, aux, P.subset_ground.trans hNM.subset, and_self,
    closure_inter_ground, true_and]
  refine ⟨fun _ ↦ auxcl, ?_⟩
  simp only [eConn_eq_eLocalConn_true_false, ↓mk_apply, eLocalConn_inter_ground_right,
    eLocalConn_inter_ground_left]
  rw [hNM.eLocalConn_eq_of_subset, ← M.eLocalConn_closure_closure, auxcl, auxcl,
    eLocalConn_closure_closure]

/-- If `N` simplifies `M`, then each separation of `N` extends naturally to one of `M`. -/
lemma exists_of_simplifies (P : N.Separation) (hNM : N ≤si M) : ∃ (Q : M.Separation),
    (∀ i, (P i ⊆ Q i ∧ M.closure (Q i) = M.closure (P i))) ∧ Q.eConn = P.eConn := by
  refine P.exists_of_isRestriction_of_forall_mem_closure hNM.isRestriction fun e he ↦ ?_
  obtain ⟨f, hfN, hef⟩ := hNM.exists_of_isNonloop he
  obtain ⟨i, hi⟩ := P.exists_mem hfN
  use i
  refine mem_of_mem_of_subset ?_ <| M.closure_subset_closure <| singleton_subset_iff.2 hi
  exact hef.mem_closure

lemma indep_of_contract {I} (hI : I ⊆ M.E) (hi : M.Indep (I ∩ P i))
    (hic : (M ／ P i).Indep (I ∩ P (!i))) : M.Indep I := by
  replace hic := hic.of_isMinor <|
    contract_isMinor_of_subset _ (show I ∩ P i ⊆ P i from inter_subset_right)
  rw [hi.contract_indep_iff, union_comm, P.union_inter_left _] at hic
  exact hic.2

/-- The guts of a separation comprises the points spanned by both sides. -/
def guts (P : M.Separation) : Set α := ⋂ i, M.closure (P i)

lemma guts_eq_inter_bool (P : M.Separation) (i : Bool) :
    P.guts = M.closure (P i) ∩ M.closure (P !i) := by
  rw [Separation.guts, iInter_bool' _ i]

@[simp, grind =]
lemma guts_symm (P : M.Separation) : P.symm.guts = P.guts := by
  rw [guts_eq_inter_bool _ true, P.symm_apply, P.symm_apply, ← guts_eq_inter_bool]

lemma guts_isFlat (P : M.Separation) : M.IsFlat P.guts := by
  rw [guts_eq_inter_bool _ true]
  exact (M.closure_isFlat ..).inter (M.closure_isFlat ..)

@[simp, grind! .,  aesop unsafe 10% (rule_sets := [Matroid])]
lemma guts_subset_ground : P.guts ⊆ M.E :=
  P.guts_isFlat.subset_ground

lemma closure_inter_subset_guts (P : M.Separation) (i : Bool) :
    M.closure (P i) ∩ P (!i) ⊆ P.guts := by
  grw [M.subset_closure (P !i), guts_eq_inter_bool]

@[simp, grind! .]
lemma guts_subset_closure (P : M.Separation) (i : Bool) : P.guts ⊆ M.closure (P i) := by
  grw [guts_eq_inter_bool P i, inter_subset_left]

lemma eRk_guts_le : M.eRk P.guts ≤ P.eConn := by
  nth_grw 1 [eConn_eq_eLocalConn _ true, ← M.eRk_project_add_eLocalConn_eq _ (P false),
    guts_subset_closure P false, (eRk_eq_zero_iff).2 (by simp), zero_add,
    guts_subset_closure P true, eLocalConn_closure_left, Bool.not_true]

lemma guts_induce_contract_of_subset_guts (hX : X ⊆ P.guts) :
    (P.induce (M ／ X)).guts = P.guts \ X := by
  rw [guts_eq_inter_bool _ true, contract_closure_eq,
    contract_closure_eq, induce_apply_contract, induce_apply_contract, ← diff_inter_distrib_right,
    diff_union_self, diff_union_self, ← closure_union_closure_left_eq,
    union_eq_self_of_subset_right (by grind), ← closure_union_closure_left_eq,
    union_eq_self_of_subset_right (by grind), closure_closure, closure_closure,
    ← guts_eq_inter_bool]

/-- Contracting a subset `X` of the guts of `P` reduces connectivity by the rank of `X`. -/
lemma eConn_induce_contract_add_of_subset_guts (hX : X ⊆ P.guts) :
    (P.induce (M ／ X)).eConn + M.eRk X = P.eConn := by
  wlog hXP : X ⊆ P true generalizing X P M with aux
  · rw [← aux (M := M) (P := P) (X := X ∩ P true) (by grind) (by grind), eq_comm,
      ← eConn_symm, ← aux (M := M ／ (X ∩ P true)) (X := X ∩ P false)]
    · rw [induce_symm_of_subset _ (by simp), induce_induce _ (by grind),
        contract_contract, add_assoc, eRk_contract_add_eRk, union_comm (X ∩ P false),
        ← inter_union_distrib_left, P.union_eq, contract_inter_ground_eq,
        eRk_inter_ground, ← induce_symm_of_subset _ (by simp), eConn_symm]
    · rw [guts_symm, guts_induce_contract_of_subset_guts (by grind), subset_diff]
      grind
    grind [Separation.symm_apply, induce_apply_contract]
  rw [eConn_eq_eConn_induce_contract_add _ hXP, ← eLocalConn_closure_left,
    eLocalConn_comm, M.eLocalConn_subset (by grind)]

/-- The intersection of the coclosures of the two sides of a separation. -/
def coguts (P : M.Separation) := (P.induce M✶).guts

lemma coguts_eq_inter_bool (P : M.Separation) (i : Bool) :
    P.coguts = M✶.closure (P i) ∩ M✶.closure (P !i) := by
  rw [Separation.coguts, guts_eq_inter_bool _ i, induce_dual_apply, induce_dual_apply]

@[simp, grind =]
lemma coguts_symm (P : M.Separation) : P.symm.coguts = P.coguts := by
  rw [coguts, ← induce_symm_of_subset _ (by simp), guts_symm, coguts]

lemma coguts_isFlat_dual (P : M.Separation) : M✶.IsFlat P.coguts :=
  guts_isFlat (P.induce M✶)

@[simp, grind! .,  aesop unsafe 10% (rule_sets := [Matroid])]
lemma coguts_subset_ground : P.coguts ⊆ M.E :=
  P.coguts_isFlat_dual.subset_ground

lemma closure_inter_subset_coguts (P : M.Separation) (i : Bool) :
    M✶.closure (P i) ∩ P (!i) ⊆ P.coguts := by
  grw [M✶.subset_closure (P !i), coguts_eq_inter_bool _ i]

@[simp, grind! .]
lemma coguts_subset_closure (P : M.Separation) (i : Bool) : P.coguts ⊆ M✶.closure (P i) := by
  grw [coguts, guts_subset_closure _ i, induce_dual_apply]

@[simp]
lemma guts_induce_dual : (P.induce M✶).guts = P.coguts := rfl

@[simp]
lemma coguts_induce_dual : (P.induce M✶).coguts = P.guts := by
  rw [coguts, guts_eq_inter_bool _ true, induce_dual_apply, induce_dual_apply,
    induce_dual_apply, induce_dual_apply, dual_dual, guts_eq_inter_bool]

lemma eConn_toggle_le_of_subset_guts (hX : X ⊆ P.guts) : (P.toggle X).eConn ≤ P.eConn := by
  nth_grw 1 [P.eConn_eq_eLocalConn true, ← eLocalConn_closure_closure, eConn_eq_eLocalConn _ true,
    toggle_apply, symmDiff_subset_union, toggle_apply, symmDiff_subset_union, hX, hX,
    union_subset (M.subset_closure (P true)) (guts_subset_closure P true),
    union_subset (M.subset_closure (P !true)) (guts_subset_closure P !true)]

/-- Move all the elements of `P !i` spanned by `P i` to side `i`. -/
def closureShift (P : M.Separation) (i : Bool) : M.Separation := M.ofSetSep (M.closure (P i)) i

@[simp]
lemma closureShift_apply_self (P : M.Separation) (i : Bool) :
    (P.closureShift i) i = M.closure (P i) := by
  rw [closureShift, ofSetSep_apply_self]

@[simp]
lemma closureShift_apply_not (P : M.Separation) (i : Bool) :
    (P.closureShift i) (!i) = P (!i) \ M.closure (P i) := by
  rw [closureShift, ofSetSep_apply_not, ← P.union_bool_eq i, union_diff_distrib,
    diff_eq_empty.2 (M.subset_closure ..), empty_union]

@[simp]
lemma closureShift_not_apply (P : M.Separation) (i : Bool) :
    (P.closureShift (!i)) i = P i \ M.closure (P (!i)) := by
  simpa using P.closureShift_apply_not !i

lemma closureShift_eConn_le (P : M.Separation) (i : Bool) :
    (P.closureShift i).eConn ≤ P.eConn := by
  grw [eConn_eq_eLocalConn _ i, closureShift_apply_not, closureShift_apply_self,
    eLocalConn_closure_left, diff_subset, ← eConn_eq_eLocalConn]
