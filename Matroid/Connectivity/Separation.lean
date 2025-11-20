import Matroid.Connectivity.Core
import Matroid.Connectivity.Nat
import Matroid.Connectivity.Connected
import Matroid.Connectivity.Minor
import Matroid.ForMathlib.Finset
import Matroid.ForMathlib.Matroid.Sum

set_option linter.style.longLine false
open Set

namespace Matroid

section separation

variable {α : Type*} {M : Matroid α} {j k : ℕ∞} {a b : α} {A B X X' Y Y' : Set α}

/-- A partition of the ground set of a matroid into two parts.
Used for reasoning about connectivity. -/
protected structure Partition (M : Matroid α) where
  left : Set α
  right : Set α
  disjoint : Disjoint left right
  union_eq : left ∪ right = M.E

variable {P : M.Partition}

namespace Partition

protected lemma ext {P P' : M.Partition} (h_left : P.left = P'.left)
    (h_right : P.right = P'.right) : P = P' := by
  cases P
  cases P'
  simp_all

-- protected lemma ext_subset {P P' : M.Partition} (h_left : P.left ⊆ P'.left)
--     (h_right : P.right ⊆ P'.right) : P = P' := by
--   have := P.left
--   refine Partition.ext ?_ ?_
@[simp] lemma P.union : P.left ∪ P.right = M.E :=
  P.union_eq

@[simps]
protected def symm (P : M.Partition) : M.Partition where
  left := P.2
  right := P.1
  disjoint := P.disjoint.symm
  union_eq := by rw [← P.union_eq, union_comm]

@[simp]
lemma symm_symm (P : M.Partition) : P.symm.symm = P := rfl

@[simps]
protected def dual (P : M.Partition) : M✶.Partition where
  left := P.1
  right := P.2
  disjoint := P.disjoint
  union_eq := P.union_eq

@[simps]
protected def ofDual (P : M✶.Partition) : M.Partition where
  left := P.1
  right := P.2
  disjoint := P.disjoint
  union_eq := P.union_eq

@[simp] lemma dual_ofDual (P : M.Partition) : P.dual.ofDual = P := rfl

@[simp] lemma ofDual_dual (P : M✶.Partition) : P.ofDual.dual = P := rfl

@[simps] def dualEquiv (M : Matroid α) : M.Partition ≃ M✶.Partition where
  toFun := Partition.dual
  invFun := Partition.ofDual
  left_inv P := by simp
  right_inv P := by simp

@[simp, aesop unsafe 10% (rule_sets := [Matroid])]
protected lemma left_subset_ground (P : M.Partition) : P.1 ⊆ M.E := by
  rw [← P.union_eq]; apply subset_union_left

@[simp, aesop unsafe 10% (rule_sets := [Matroid])]
protected lemma right_subset_ground (P : M.Partition) : P.2 ⊆ M.E := by
  rw [← P.union_eq]; apply subset_union_right

noncomputable abbrev eConn (P : M.Partition) : ℕ∞ := M.eLocalConn P.1 P.2

@[simp]
lemma eConn_symm (P : M.Partition) : P.symm.eConn = P.eConn :=
  M.eLocalConn_comm _ _

@[simp]
lemma compl_left (P : M.Partition) : M.E \ P.1 = P.2 := by
  rw [← P.union_eq, union_diff_left, sdiff_eq_left]
  exact P.symm.disjoint

@[simp]
lemma compl_right (P : M.Partition) : M.E \ P.2 = P.1 := by
  rw [← symm_left, compl_left, symm_right]

lemma eConn_eq_left (P : M.Partition) : P.eConn = M.eConn P.1 := by
  rw [eConn, ← compl_left]
  rfl

lemma eConn_eq_right (P : M.Partition) : P.eConn = M.eConn P.2 := by
  rw [← P.eConn_symm, P.symm.eConn_eq_left, symm_left]

@[simp]
lemma eConn_left (P : M.Partition) : M.eConn P.1 = P.eConn := by
  rw [eConn, ← compl_left]
  rfl

@[simp]
lemma eConn_right (P : M.Partition) : M.eConn P.2 = P.eConn := by
  rw [← P.eConn_symm, ← eConn_left, symm_left]

@[simp]
lemma dual_eConn (P : M.Partition) : P.dual.eConn = P.eConn := by
  rw [← P.dual.eConn_left, M.eConn_dual, P.dual_left, P.eConn_left]

@[simp]
lemma ofDual_eConn (P : M✶.Partition) : P.ofDual.eConn = P.eConn := by
  rw [← P.dual_ofDual, ← dual_eConn]
  simp

@[simp]
lemma not_indep_left_iff : ¬ M.Indep P.left ↔ M.Dep P.left := by
  rw [not_indep_iff]

@[simp]
lemma not_indep_right_iff : ¬ M.Indep P.right ↔ M.Dep P.right := by
  rw [not_indep_iff]

@[simp]
lemma not_dep_left_iff : ¬ M.Dep P.left ↔ M.Indep P.left := by
  rw [not_dep_iff]

@[simp]
lemma not_dep_right_iff : ¬ M.Dep P.right ↔ M.Indep P.right := by
  rw [not_dep_iff]

@[simp]
lemma not_coindep_left_iff : ¬ M.Coindep P.left ↔ M.Codep P.left := by
  rw [not_coindep_iff]

@[simp]
lemma not_coindep_right_iff : ¬ M.Coindep P.right ↔ M.Codep P.right := by
  rw [not_coindep_iff]

@[simp]
lemma not_indep_dual_left_iff : ¬ M✶.Indep P.left ↔ M.Codep P.left := by
  rw [not_coindep_iff]

@[simp]
lemma not_indep_dual_right_iff : ¬ M✶.Indep P.right ↔ M.Codep P.right := by
  rw [not_coindep_iff]

@[simp]
lemma not_spanning_left_iff : ¬ M.Spanning P.left ↔ M.Nonspanning P.left := by
  rw [not_spanning_iff]

@[simp]
lemma not_spanning_right_iff : ¬ M.Spanning P.right ↔ M.Nonspanning P.right := by
  rw [not_spanning_iff]

@[simp]
lemma not_nonspanning_left_iff : ¬ M.Nonspanning P.left ↔ M.Spanning P.left := by
  rw [not_nonspanning_iff]

@[simp]
lemma not_nonspanning_right_iff : ¬ M.Nonspanning P.right ↔ M.Spanning P.right := by
  rw [not_nonspanning_iff]

lemma coindep_left_iff : M.Coindep P.left ↔ M.Spanning P.right := by
  rw [← compl_right, ← spanning_iff_compl_coindep]

lemma coindep_right_iff : M.Coindep P.right ↔ M.Spanning P.left := by
  rw [← compl_left, ← spanning_iff_compl_coindep]

lemma codep_left_iff : M.Codep P.left ↔ M.Nonspanning P.right := by
  rw [← not_coindep_left_iff, coindep_left_iff, not_spanning_right_iff]

lemma codep_right_iff : M.Codep P.right ↔ M.Nonspanning P.left := by
  rw [← symm_right, ← codep_left_iff, symm_left]

lemma isCocircuit_left_iff : M.IsCocircuit P.left ↔ M.IsHyperplane P.right := by
  rw [← isHyperplane_compl_iff_isCocircuit, P.compl_left]

lemma isCocircuit_right_iff : M.IsCocircuit P.right ↔ M.IsHyperplane P.left := by
  rw [← isHyperplane_compl_iff_isCocircuit, P.compl_right]

@[simp]
lemma spanning_dual_left_iff : M✶.Spanning P.left ↔ M.Indep P.right := by
  simp [spanning_dual_iff]

@[simp]
lemma spanning_dual_right_iff : M✶.Spanning P.right ↔ M.Indep P.left := by
  simp [spanning_dual_iff]

@[simp]
lemma nonspanning_dual_left_iff : M✶.Nonspanning P.left ↔ M.Dep P.right := by
  rw [← not_spanning_iff, spanning_dual_left_iff, not_indep_iff]

@[simp]
lemma nonspanning_dual_right_iff : M✶.Nonspanning P.right ↔ M.Dep P.left :=
  nonspanning_dual_left_iff (P := P.symm)

/-- The connectivity of a partition as a natural number. Takes a value of `0` if infinite. -/
noncomputable def conn (P : M.Partition) : ℕ := M.localConn P.1 P.2

@[simp]
lemma conn_symm (P : M.Partition) : P.symm.conn = P.conn := by
  simp [conn, localConn_comm]

lemma conn_eq_left (P : M.Partition) : P.conn = M.conn P.left := by
  simp [conn, conn_eq_localConn, P.compl_left]

lemma conn_eq_right (P : M.Partition) : P.conn = M.conn P.right := by
  simp [conn, conn_eq_localConn, P.compl_right, localConn_comm]

@[simps] protected def setCompl (M : Matroid α) [OnUniv M] (X : Set α) : M.Partition where
  left := X
  right := Xᶜ
  disjoint := disjoint_compl_right
  union_eq := by simp

/-- Restrict a partition to a set. The junk elements go on the right. -/
@[simps] protected def restrict (P : M.Partition) (R : Set α) : (M ↾ R).Partition where
  left := P.left ∩ R
  right := (P.right ∩ R) ∪ (R \ M.E)
  disjoint := by
    refine disjoint_union_right.2 ⟨(P.disjoint.mono inter_subset_left inter_subset_left),
      disjoint_sdiff_right.mono_left (inter_subset_left.trans P.left_subset_ground)⟩
  union_eq := by rw [← union_assoc, ← union_inter_distrib_right, P.union_eq, inter_comm,
    inter_union_diff, restrict_ground_eq]

lemma eConn_restrict_eq (P : M.Partition) (R : Set α) :
    (P.restrict R).eConn = M.eLocalConn (P.left ∩ R) (P.right ∩ R) := by
  simp only [eConn, Partition.restrict, eLocalConn_restrict_eq]
  rw [union_inter_distrib_right, inter_assoc, inter_assoc, inter_self,
    inter_eq_self_of_subset_left diff_subset, ← eLocalConn_inter_ground_right,
    union_inter_distrib_right, disjoint_sdiff_left.inter_eq, union_empty,
    eLocalConn_inter_ground_right]

@[simps] protected def copy {M' : Matroid α} (P : M.Partition) (h_eq : M.E = M'.E) :
    M'.Partition where
  left := P.left
  right := P.right
  disjoint := P.disjoint
  union_eq := P.union_eq.trans (by simp [h_eq])

@[simp] lemma copy_eConn {M' : Matroid α} (P : M.Partition) (h_eq : M = M') :
    (P.copy (congr_arg Matroid.E h_eq)).eConn = P.eConn := by
  obtain rfl := h_eq
  rfl

/-- The partition of `M` given by a subset of `M.E` and its complement.  -/
@[simps]
protected def _root_.Matroid.partition (M : Matroid α) (A : Set α) (hA : A ⊆ M.E := by aesop_mat) :
    M.Partition where
  left := A
  right := M.E \ A
  disjoint :=  disjoint_sdiff_right
  union_eq := by rwa [union_diff_cancel]

@[simp]
lemma _root_.Matroid.eConn_partition (hA : A ⊆ M.E) : (M.partition A).eConn = M.eConn A := by
  simp [eConn, Matroid.eConn]

@[simp]
lemma _root_.Matroid.partition_dual (hA : A ⊆ M.E) : M✶.partition A hA = (M.partition A).dual := rfl

/-- Intersect a partition with the ground set of a smaller matroid -/
@[simps]
def induce {N : Matroid α} (P : M.Partition) (hN : N.E ⊆ M.E) : N.Partition where
  left := P.left ∩ N.E
  right := P.right ∩ N.E
  disjoint := P.disjoint.mono inter_subset_left inter_subset_left
  union_eq := by rw [← union_inter_distrib_right, P.union_eq, inter_eq_self_of_subset_right hN]

def contract (P : M.Partition) (C : Set α) : (M ／ C).Partition := P.induce diff_subset

@[simp]
lemma contract_left (P : M.Partition) (C : Set α) : (P.contract C).left = P.left \ C := by
  simp only [contract, induce, contract_ground]
  rw [← inter_diff_assoc, inter_eq_self_of_subset_left P.left_subset_ground]

@[simp]
lemma contract_symm (P : M.Partition) (C : Set α) : (P.contract C).symm = P.symm.contract C := rfl

@[simp]
lemma contract_right (P : M.Partition) (C : Set α) : (P.contract C).right = P.right \ C := by
  rw [← symm_left, contract_symm, contract_left, symm_left]

def delete (P : M.Partition) (D : Set α) : (M ＼ D).Partition := P.induce diff_subset

@[simp]
lemma delete_left (P : M.Partition) (D : Set α) : (P.delete D).left = P.left \ D := by
  simp only [delete, induce, delete_ground]
  rw [← inter_diff_assoc, inter_eq_self_of_subset_left P.left_subset_ground]

@[simp]
lemma delete_symm (P : M.Partition) (D : Set α) : (P.delete D).symm = P.symm.delete D := rfl

@[simp]
lemma delete_right (P : M.Partition) (D : Set α) : (P.delete D).right = P.right \ D := by
  rw [← symm_left, delete_symm, delete_left, symm_left]

section Cross

/-- Cross two partitions by intersecting the left sets. -/
@[simps]
def inter (P Q : M.Partition) : M.Partition where
  left := P.left ∩ Q.left
  right := P.right ∪ Q.right
  disjoint := by
    nth_grw 1 [disjoint_union_right, inter_subset_left, inter_subset_right]
    exact ⟨P.disjoint, Q.disjoint⟩
  union_eq := by
    rw [← P.compl_right, ← Q.compl_right, ← inter_diff_right_comm, union_comm P.right,
      inter_eq_self_of_subset_right diff_subset, diff_diff, diff_union_self,
      union_eq_self_of_subset_right (union_subset Q.right_subset_ground P.right_subset_ground)]

/-- Cross two partitions by intersecting the right sets. -/
def union (P Q : M.Partition) : M.Partition := (P.symm.inter Q.symm).symm

@[simp]
lemma union_left (P Q : M.Partition) : (P.union Q).left = P.left ∪ Q.left := rfl

@[simp]
lemma union_right (P Q : M.Partition) : (P.union Q).right = P.right ∩ Q.right := rfl

@[simp]
lemma inter_symm (P Q : M.Partition) : (P.inter Q).symm = P.symm.union Q.symm := rfl

@[simp]
lemma union_symm (P Q : M.Partition) : (P.union Q).symm = P.symm.inter Q.symm := rfl

end Cross

section Minor

variable {C D : Set α} {e f : α}

@[simp]
lemma disjoint_left_contract (P : (M ／ C).Partition) : Disjoint P.left C := by
  grw [P.left_subset_ground]
  exact disjoint_sdiff_left

@[simp]
lemma disjoint_right_contract (P : (M ／ C).Partition) : Disjoint P.right C :=
  P.symm.disjoint_left_contract

@[simp]
lemma disjoint_left_delete (P : (M ＼ D).Partition) : Disjoint P.left D := by
  grw [P.left_subset_ground]
  exact disjoint_sdiff_left

@[simp]
lemma disjoint_right_delete (P : (M ＼ D).Partition) : Disjoint P.right D :=
  P.symm.disjoint_left_delete

@[simps!]
def contractDual (P : (M ／ C).Partition) : (M✶ ＼ C).Partition := P.dual.copy rfl

@[simps!]
def deleteDual (P : (M ＼ D).Partition) : (M✶ ／ D).Partition := P.dual.copy rfl

/-- Extend a partition of `M ／ C` to a partition of `M` by adding `C` to the left side. -/
@[simps]
def ofContractLeft (P : (M ／ C).Partition) (hC : C ⊆ M.E := by aesop_mat) : M.Partition where
  left := P.left ∪ C
  right := P.right
  disjoint := by simp [P.disjoint_right_contract.symm, P.disjoint]
  union_eq := by rw [union_right_comm, P.union_eq, contract_ground, diff_union_of_subset hC]

/-- Extend a partition of `M ／ C` to a partition of `M` by adding `C` to the right side. -/
@[simps!]
def ofContractRight (P : (M ／ C).Partition) (hC : C ⊆ M.E := by aesop_mat) :=
  P.symm.ofContractLeft.symm

/-- Extend a partition of `M ＼ D` to a partition of `M` by adding `D` to the left side. -/
@[simps]
def ofDeleteLeft (P : (M ＼ D).Partition) (hC : D ⊆ M.E := by aesop_mat) : M.Partition where
  left := P.left ∪ D
  right := P.right
  disjoint := by simp [P.disjoint_right_delete.symm, P.disjoint]
  union_eq := by rw [union_right_comm, P.union_eq, delete_ground, diff_union_of_subset hC]

/-- Extend a partition of `M ＼ D` to a partition of `M` by adding `D` to the right side. -/
@[simps!]
def ofDeleteRight (P : (M ＼ D).Partition) (hD : D ⊆ M.E := by aesop_mat) :=
  P.symm.ofDeleteLeft.symm

@[simp]
lemma ofDeleteLeft_symm (P : (M ＼ D).Partition) (hD : D ⊆ M.E := by aesop_mat) :
    P.ofDeleteLeft.symm = P.symm.ofDeleteRight := rfl

@[simp]
lemma ofDeleteRight_symm (P : (M ＼ D).Partition) (hD : D ⊆ M.E := by aesop_mat) :
    P.ofDeleteRight.symm = P.symm.ofDeleteLeft := rfl

@[simp]
lemma ofContractLeft_symm (P : (M ／ C).Partition) (hC : C ⊆ M.E := by aesop_mat) :
    P.ofContractLeft.symm = P.symm.ofContractRight := rfl

@[simp]
lemma ofContractRight_symm (P : (M ／ C).Partition) (hC : C ⊆ M.E := by aesop_mat) :
    P.ofContractRight.symm = P.symm.ofContractLeft := rfl

@[simp]
lemma ofDeleteLeft_dual (P : (M ＼ D).Partition) (hD : D ⊆ M.E := by aesop_mat) :
    P.ofDeleteLeft.dual = P.deleteDual.ofContractLeft := rfl

@[simp]
lemma ofDeleteRight_dual (P : (M ＼ D).Partition) (hD : D ⊆ M.E := by aesop_mat) :
    P.ofDeleteRight.dual = P.deleteDual.ofContractRight := rfl

@[simp]
lemma ofContractLeft_dual (P : (M ／ C).Partition) (hC : C ⊆ M.E := by aesop_mat) :
    P.ofContractLeft.dual = P.contractDual.ofDeleteLeft := rfl

@[simp]
lemma ofContractRight_dual (P : (M ／ C).Partition) (hC : C ⊆ M.E := by aesop_mat) :
    P.ofContractRight.dual = P.contractDual.ofDeleteRight := rfl

lemma compl_left_delete (P : (M ＼ D).Partition) (hD : D ⊆ M.E := by aesop_mat) :
    M.E \ P.left = P.right ∪ D := by
  grw [← P.compl_left, delete_ground, diff_diff_comm, diff_union_self, eq_comm, union_eq_left,
    subset_diff, and_iff_right hD, P.left_subset_ground]
  exact disjoint_sdiff_right

lemma compl_right_delete (P : (M ＼ D).Partition) (hD : D ⊆ M.E := by aesop_mat) :
    M.E \ P.right = P.left ∪ D :=
  P.symm.compl_left_delete

lemma compl_left_contract (P : (M ／ C).Partition) (hD : C ⊆ M.E := by aesop_mat) :
    M.E \ P.left = P.right ∪ C :=  by
  simpa using (P.dual.copy (show (M ／ C)✶.E = (M✶ ＼ C).E by simp)).compl_left_delete

lemma compl_right_contract (P : (M ／ C).Partition) (hD : C ⊆ M.E := by aesop_mat) :
    M.E \ P.right = P.left ∪ C :=
  P.symm.compl_left_contract

lemma compl_left_delete_singleton (P : (M ＼ {e}).Partition) (he : e ∈ M.E := by aesop_mat) :
    M.E \ P.left = insert e P.right := by
  simp [P.compl_left_delete]

lemma compl_right_delete_singleton (P : (M ＼ {e}).Partition) (he : e ∈ M.E := by aesop_mat) :
    M.E \ P.right = insert e P.left :=
  P.symm.compl_left_delete_singleton

lemma compl_left_contract_singleton (P : (M ／ {e}).Partition) (he : e ∈ M.E := by aesop_mat) :
    M.E \ P.left = insert e P.right := by
  simp [P.compl_left_contract]

@[simp]
lemma compl_right_contract_singleton (P : (M ／ {e}).Partition) (he : e ∈ M.E := by aesop_mat) :
    M.E \ P.right = insert e P.left :=
  P.symm.compl_left_contract_singleton

lemma ofContractLeft_eConn (P : (M ／ C).Partition) (hC : C ⊆ M.E := by aesop_mat) :
    P.ofContractLeft.eConn = P.eConn + M.eLocalConn P.right C := by
  simp only [← eConn_left, ofContractLeft_left]
  rw [eConn_union_eq_eConn_contract_add _ P.disjoint_left_contract, ← P.compl_right_contract,
    diff_diff_cancel_left]
  grw [P.right_subset_ground, contract_ground, diff_subset]

lemma ofContractRight_eConn (P : (M ／ C).Partition) (hC : C ⊆ M.E := by aesop_mat) :
    P.ofContractRight.eConn = P.eConn + M.eLocalConn P.left C := by
  rw [← eConn_symm, P.ofContractRight_symm, ofContractLeft_eConn, eConn_symm, symm_right]





end Minor


lemma eConn_eq_zero_iff_skew {P : M.Partition} : P.eConn = 0 ↔ M.Skew P.1 P.2 :=
  M.eLocalConn_eq_zero P.left_subset_ground P.right_subset_ground

lemma eConn_eq_zero_iff_eq_disjointSum {P : M.Partition} :
    P.eConn = 0 ↔ M = (M ↾ P.1).disjointSum (M ↾ P.2) P.disjoint := by
  rw [eConn_eq_zero_iff_skew,
    skew_iff_restrict_union_eq P.left_subset_ground P.right_subset_ground P.disjoint,
    P.union_eq, restrict_ground_eq_self]

lemma exists_partition_of_not_connected [M.Nonempty] (h : ¬ M.Connected) :
    ∃ P : M.Partition, P.left.Nonempty ∧ P.right.Nonempty ∧ P.eConn = 0 := by
  obtain ⟨M₁, M₂, hdj, hM₁, hM₂, rfl⟩ := eq_disjointSum_of_not_connected h
  exact ⟨Matroid.partition _ M₁.E,
    by simp [hM₁.ground_nonempty, hdj.sdiff_eq_right, hM₂.ground_nonempty]⟩

lemma exists_partition_iff_not_connected [M.Nonempty] :
    ¬ M.Connected ↔ ∃ P : M.Partition, P.left.Nonempty ∧ P.right.Nonempty ∧ P.eConn = 0 := by
  refine ⟨exists_partition_of_not_connected, fun ⟨P, hPleft, hPright, hP⟩ ↦ ?_⟩
  rw [eConn_eq_zero_iff_eq_disjointSum] at hP
  rw [hP]
  apply disjointSum_not_connected <;>
  simpa [← ground_nonempty_iff]

section wlog


protected lemma wlog_symm (motive : {N : Matroid α} → (P : N.Partition) → Prop)
    (property : Matroid α → Set α → Prop)
    (h_symm : ∀ ⦃N⦄ ⦃P : Matroid.Partition N⦄, motive P.symm → motive P)
    (h_some : ∀ ⦃N⦄ ⦃P : Matroid.Partition N⦄, property N P.left → motive P)
    (h_not : ∀ ⦃N⦄ ⦃P : Matroid.Partition N⦄, ¬ property N P.left → ¬ property N P.right → motive P)
    (P₀ : M.Partition) : motive P₀ := by
  by_cases h1 : property M P₀.left
  · exact h_some h1
  by_cases h2 : property M P₀.right
  · exact h_symm <| h_some (P := P₀.symm) (by simpa)
  exact h_not h1 h2

protected lemma wlog_symm_dual (motive : {N : Matroid α} → (P : N.Partition) → Prop)
    (property : Matroid α → Set α → Prop)
    (h_symm : ∀ ⦃N⦄ ⦃P : Matroid.Partition N⦄, motive P.symm → motive P)
    (h_dual : ∀ ⦃N⦄ ⦃P : Matroid.Partition N⦄, motive P.dual → motive P)
    (h_some : ∀ ⦃N⦄ ⦃P : Matroid.Partition N⦄, property N P.left → motive P)
    (h_not : ∀ ⦃N⦄ ⦃P : Matroid.Partition N⦄, ¬ property N P.left → ¬ property N P.right →
      ¬ property N✶ P.left → ¬ property N✶ P.right → motive P) (P₀ : M.Partition) : motive P₀ := by
  by_cases h1 : property M P₀.left
  · exact h_some h1
  by_cases h2 : property M P₀.right
  · exact h_symm <| h_some (P := P₀.symm) (by simpa)
  by_cases h1' : property M✶ P₀.left
  · exact h_dual <| h_some (N := M✶) (P := P₀.dual) (by simpa)
  by_cases h2' : property M✶ P₀.right
  · exact h_symm <| h_dual <| h_some (N := M✶) (P := P₀.symm.dual) (by simpa)
  exact h_not h1 h2 h1' h2'

end wlog

end Partition
