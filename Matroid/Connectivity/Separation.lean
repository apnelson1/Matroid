import Matroid.Connectivity.Core
import Matroid.Connectivity.Nat
import Matroid.Connectivity.Connected
import Matroid.Connectivity.Minor
import Matroid.ForMathlib.Finset
import Matroid.ForMathlib.Matroid.Sum

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

attribute [simp] Partition.disjoint Partition.union_eq

@[simps] def dualEquiv (M : Matroid α) : M.Partition ≃ M✶.Partition where
  toFun := Partition.dual
  invFun := Partition.ofDual
  left_inv P := by simp
  right_inv P := by simp

@[simp]
lemma compl_left (P : M.Partition) : M.E \ P.1 = P.2 := by
  rw [← P.union_eq, union_diff_left, sdiff_eq_left]
  exact P.symm.disjoint

@[simp]
lemma compl_right (P : M.Partition) : M.E \ P.2 = P.1 := by
  rw [← symm_left, compl_left, symm_right]

@[simp, aesop unsafe 10% (rule_sets := [Matroid])]
protected lemma left_subset_ground (P : M.Partition) : P.1 ⊆ M.E := by
  rw [← P.union_eq]; apply subset_union_left

@[simp, aesop unsafe 10% (rule_sets := [Matroid])]
protected lemma right_subset_ground (P : M.Partition) : P.2 ⊆ M.E := by
  rw [← P.union_eq]; apply subset_union_right

/-- A partition is trivial if one side is empty. -/
protected def Trivial (P : M.Partition) : Prop := P.left = ∅ ∨ P.right = ∅

lemma trivial_of_left_eq_empty (h : P.left = ∅) : P.Trivial := .inl h

lemma trivial_of_right_eq_empty (h : P.right = ∅) : P.Trivial := .inr h

lemma trivial_of_left_eq_ground (h : P.left = M.E) : P.Trivial :=
  .inr <| by simp [← P.compl_left, h]

lemma trivial_of_right_eq_ground (h : P.right = M.E) : P.Trivial :=
  .inl <| by simp [← P.compl_right, h]

protected lemma trivial_def : P.Trivial ↔ P.left = ∅ ∨ P.right = ∅ := Iff.rfl

protected lemma trivial_def' : P.Trivial ↔ P.left = M.E ∨ P.right = M.E := by
  rw [← P.compl_left, sdiff_eq_left, ← P.compl_right, sdiff_eq_left, P.compl_right,
    disjoint_iff_inter_eq_empty, inter_eq_self_of_subset_right P.right_subset_ground,
    disjoint_iff_inter_eq_empty, inter_eq_self_of_subset_right P.left_subset_ground, or_comm,
    P.trivial_def]

lemma Trivial.eq_ground_or_eq_ground (h : P.Trivial) : P.left = M.E ∨ P.right = M.E := by
  rwa [← P.trivial_def']

lemma trivial_of_ground_subsingleton (P : M.Partition) (h : M.E.Subsingleton) : P.Trivial :=
  (h.eq_or_eq_of_subset P.left_subset_ground).elim trivial_of_left_eq_empty
    trivial_of_left_eq_ground

noncomputable abbrev eConn (P : M.Partition) : ℕ∞ := M.eLocalConn P.1 P.2

@[simp]
lemma eConn_symm (P : M.Partition) : P.symm.eConn = P.eConn :=
  M.eLocalConn_comm _ _


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

lemma eConn_eq_eLocalConn (P : M.Partition) : P.eConn = M.eLocalConn P.1 P.2 := by
  rw [← eConn_left, Matroid.eConn_eq_eLocalConn, P.compl_left]

@[simp]
lemma eConn_dual (P : M.Partition) : P.dual.eConn = P.eConn := by
  rw [← P.dual.eConn_left, M.eConn_dual, P.dual_left, P.eConn_left]

@[simp]
lemma eConn_ofDual (P : M✶.Partition) : P.ofDual.eConn = P.eConn := by
  rw [← P.dual_ofDual, ← eConn_dual]
  simp

lemma Trivial.eConn (h : P.Trivial) : P.eConn = 0 := by
  obtain h | h := h
  · simp [← P.eConn_left, h]
  simp [← P.eConn_right, h]

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
lemma not_codep_left_iff : ¬ M.Codep P.left ↔ M.Coindep P.left := by
  rw [← not_coindep_iff, not_not]

@[simp]
lemma not_codep_right_iff : ¬ M.Codep P.right ↔ M.Coindep P.right := by
  rw [← not_coindep_iff, not_not]

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

/-- Transfer a partition across a matroid equality. -/
@[simps]
protected def copy {M' : Matroid α} (P : M.Partition) (h_eq : M = M') :
    M'.Partition where
  left := P.left
  right := P.right
  disjoint := P.disjoint
  union_eq := P.union_eq.trans (by simp [h_eq])

/-- A version of `copy` where the ground sets are equal, but the matroids need not be.
`copy` is preferred where possible, so that lemmas like `eConn_copy` can be `@[simp]`. -/
@[simps] protected def copy' {M' : Matroid α} (P : M.Partition) (h_eq : M.E = M'.E) :
    M'.Partition where
  left := P.left
  right := P.right
  disjoint := P.disjoint
  union_eq := P.union_eq.trans (by simp [h_eq])

@[simp]
lemma eConn_copy {M' : Matroid α} (P : M.Partition) (h_eq : M = M') :
    (P.copy h_eq).eConn = P.eConn := by
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

lemma Trivial.eq_or_eq (h : P.Trivial) : P = M.partition ∅ ∨ P = M.partition M.E := by
  obtain h | h := h
  · exact .inl <| Partition.ext h (by simp [← P.compl_left, h])
  exact .inr <| Partition.ext (by simp [← P.compl_right, h]) (by simpa)

/-- Intersect a partition with the ground set of a smaller matroid -/
@[simps]
def induce {N : Matroid α} (P : M.Partition) (hN : N.E ⊆ M.E) : N.Partition where
  left := P.left ∩ N.E
  right := P.right ∩ N.E
  disjoint := P.disjoint.mono inter_subset_left inter_subset_left
  union_eq := by rw [← union_inter_distrib_right, P.union_eq, inter_eq_self_of_subset_right hN]

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

@[simp]
lemma disjoint_inter_right (P : M.Partition) {X Y : Set α} : Disjoint (P.1 ∩ X) (P.2 ∩ Y) :=
  P.disjoint.mono inter_subset_left inter_subset_left

@[simp]
lemma disjoint_inter_left (P : M.Partition) {X Y : Set α} : Disjoint (X ∩ P.1) (Y ∩ P.2) :=
  P.disjoint.mono inter_subset_right inter_subset_right

@[simp]
lemma inter_ground_right (P : M.Partition) : P.right ∩ M.E = P.right :=
  inter_eq_self_of_subset_left P.right_subset_ground

@[simp]
lemma inter_ground_left (P : M.Partition) : P.left ∩ M.E = P.left :=
  inter_eq_self_of_subset_left P.left_subset_ground

lemma union_inter_right' (P : M.Partition) (X : Set α) : (P.1 ∩ X) ∪ (P.2 ∩ X) = X ∩ M.E := by
  rw [← union_inter_distrib_right, P.union_eq, inter_comm]

lemma union_inter_left' (P : M.Partition) (X : Set α) : (X ∩ P.1) ∪ (X ∩ P.2) = X ∩ M.E := by
  rw [← inter_union_distrib_left, P.union_eq, inter_comm]

@[simp]
lemma union_inter_right (P : M.Partition) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    (P.1 ∩ X) ∪ (P.2 ∩ X) = X := by
  rw [union_inter_right', inter_eq_self_of_subset_left hX]

@[simp]
lemma union_inter_left (P : M.Partition) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    (X ∩ P.1) ∪ (X ∩ P.2) = X := by
  rw [union_inter_left', inter_eq_self_of_subset_left hX]

protected lemma eConn_inter_add_eConn_union_le (P Q : M.Partition) :
    (P.inter Q).eConn + (P.union Q).eConn ≤ P.eConn + Q.eConn := by
  simp_rw [← Partition.eConn_left, union_left, inter_left]
  exact M.eConn_inter_add_eConn_union_le P.left Q.left

end Cross

section Minor

variable {C D : Set α} {e f : α}

@[simp, aesop unsafe 10% (rule_sets := [Matroid])]
lemma left_subset_ground_of_delete (P : (M ＼ D).Partition) : P.left ⊆ M.E :=
  P.left_subset_ground.trans diff_subset

@[simp, aesop unsafe 10% (rule_sets := [Matroid])]
lemma right_subset_ground_of_delete (P : (M ＼ D).Partition) : P.right ⊆ M.E :=
  P.right_subset_ground.trans diff_subset

@[simp, aesop unsafe 10% (rule_sets := [Matroid])]
lemma left_subset_ground_of_contract (P : (M ／ C).Partition) : P.left ⊆ M.E :=
  P.left_subset_ground.trans diff_subset

@[simp, aesop unsafe 10% (rule_sets := [Matroid])]
lemma right_subset_ground_of_contract (P : (M ／ C).Partition) : P.right ⊆ M.E :=
  P.right_subset_ground.trans diff_subset

/-- Contract the elements of `C` to take a partition of `M` to a partition of `M ／ C`. -/
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

lemma contract_contract (P : M.Partition) (C₁ C₂ : Set α) :
    (P.contract C₁).contract C₂ = (P.contract (C₁ ∪ C₂)).copy (by simp) := by
  apply Partition.ext <;> simp [diff_diff]

lemma contract_congr (P : M.Partition) {C₁ C₂ : Set α} (h : C₁ ∩ M.E = C₂ ∩ M.E) :
    P.contract C₁ = (P.contract C₂).copy
      (by rw [← contract_inter_ground_eq, ← h, contract_inter_ground_eq]) := by
  have h1 := P.left_subset_ground
  have h2 := P.right_subset_ground
  refine Partition.ext ?_ ?_ <;>
  · simp only [contract_left, copy_left, contract_right, copy_right]
    tauto_set

lemma contract_inter_ground (P : M.Partition) (C : Set α) :
    (P.contract (C ∩ M.E)) = (P.contract C).copy (by simp) :=
  P.contract_congr <| by simp [inter_assoc]

/-- Delete the elements of `D` to take a partition of `M` to a partition of `M ＼ D`. -/
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

lemma delete_delete (P : M.Partition) (D₁ D₂ : Set α) :
    (P.delete D₁).delete D₂ = (P.delete (D₁ ∪ D₂)).copy (by simp) := by
  apply Partition.ext <;> simp [diff_diff]

@[simp]
lemma contract_dual (P : M.Partition) (C : Set α) :
    (P.contract C).dual = (P.dual.delete C).copy (by simp) :=
  Partition.ext rfl rfl

lemma dual_contract (P : M.Partition) (C : Set α) :
    P.dual.contract C = (P.delete C).dual.copy (by simp) :=
  Partition.ext rfl rfl

@[simp]
lemma delete_dual (P : M.Partition) (D : Set α) :
    (P.delete D).dual = (P.dual.contract D).copy (by simp) :=
  Partition.ext rfl rfl

lemma dual_delete (P : M.Partition) (D : Set α) :
    (P.delete D).dual = (P.dual.contract D).copy (by simp) :=
  Partition.ext rfl rfl

lemma delete_congr (P : M.Partition) {D₁ D₂ : Set α} (h : D₁ ∩ M.E = D₂ ∩ M.E) :
    P.delete D₁ = (P.delete D₂).copy
      (by rw [← delete_inter_ground_eq, ← h, delete_inter_ground_eq]) := by
  have h1 := P.left_subset_ground
  have h2 := P.right_subset_ground
  refine Partition.ext ?_ ?_ <;>
  · simp only [delete_left, copy_left, delete_right, copy_right]
    tauto_set

lemma delete_inter_ground (P : M.Partition) (D : Set α) :
    (P.delete (D ∩ M.E)) = (P.delete D).copy (by rw [delete_inter_ground_eq]) :=
  P.delete_congr <| by simp [inter_assoc]

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
abbrev contractDual (P : (M ／ C).Partition) : (M✶ ＼ C).Partition := P.dual.copy (by simp)

@[simps!]
abbrev deleteDual (P : (M ＼ D).Partition) : (M✶ ／ D).Partition := P.dual.copy (by simp)

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

@[simp]
lemma ofContractLeft_contract (P : (M ／ C).Partition) (hC : C ⊆ M.E := by aesop_mat) :
    P.ofContractLeft.contract C = P := by
  apply Partition.ext <;> simp

@[simp]
lemma ofContractRight_contract (P : (M ／ C).Partition) (hC : C ⊆ M.E := by aesop_mat) :
    P.ofContractRight.contract C = P := by
  apply Partition.ext <;> simp

lemma contract_ofContractLeft (P : M.Partition) (hC : C ⊆ P.left) :
    (P.contract C).ofContractLeft = P :=
  Partition.ext (by simpa) <| by simp [P.disjoint.symm.mono_right hC]

lemma contract_ofContractRight (P : M.Partition) (hC : C ⊆ P.right) :
    (P.contract C).ofContractRight = P :=
  Partition.ext (by simp [P.disjoint.mono_right hC]) <| by simpa

lemma delete_ofDeleteLeft (P : M.Partition) (hD : D ⊆ P.left) :
    (P.delete D).ofDeleteLeft = P :=
  Partition.ext (by simpa) <| by simp [P.disjoint.symm.mono_right hD]

lemma delete_ofDeleteRight (P : M.Partition) (hD : D ⊆ P.right) :
    (P.delete D).ofDeleteRight = P :=
  Partition.ext (by simp [P.disjoint.mono_right hD]) <| by simpa

@[simp]
lemma ofDeleteLeft_delete (P : (M ＼ D).Partition) (hD : D ⊆ M.E := by aesop_mat) :
    P.ofDeleteLeft.delete D = P := by
  apply Partition.ext <;> simp

@[simp]
lemma ofDeleteRight_delete (P : (M ＼ D).Partition) (hD : D ⊆ M.E := by aesop_mat) :
    P.ofDeleteRight.delete D = P := by
  apply Partition.ext <;> simp

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
  simpa using (P.dual.copy (M.dual_contract C)).compl_left_delete

lemma compl_right_contract (P : (M ／ C).Partition) (hD : C ⊆ M.E := by aesop_mat) :
    M.E \ P.right = P.left ∪ C :=
  P.symm.compl_left_contract

@[simp]
lemma compl_union_contract_left (P : (M ／ C).Partition) : M.E \ (P.left ∪ C) = P.right := by
  rw [← P.compl_left, union_comm, contract_ground, diff_diff]

@[simp]
lemma compl_union_contract_right (P : (M ／ C).Partition) : M.E \ (P.right ∪ C) = P.left :=
  P.symm.compl_union_contract_left

@[simp]
lemma compl_union_delete_left (P : (M ＼ D).Partition) : M.E \ (P.left ∪ D) = P.right := by
  rw [← P.compl_left, union_comm, delete_ground, diff_diff]

@[simp]
lemma compl_union_delete_right (P : (M ＼ D).Partition) : M.E \ (P.right ∪ D) = P.left :=
  P.symm.compl_union_delete_left

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

lemma eConn_ofContractLeft (P : (M ／ C).Partition) (hC : C ⊆ M.E := by aesop_mat) :
    P.ofContractLeft.eConn = P.eConn + M.eLocalConn P.right C := by
  simp only [← eConn_left, ofContractLeft_left]
  rw [eConn_union_eq_eConn_contract_add _ P.disjoint_left_contract, ← P.compl_right_contract,
    diff_diff_cancel_left]
  grw [P.right_subset_ground, contract_ground, diff_subset]

lemma eConn_ofContractRight (P : (M ／ C).Partition) (hC : C ⊆ M.E := by aesop_mat) :
    P.ofContractRight.eConn = P.eConn + M.eLocalConn P.left C := by
  rw [← eConn_symm, P.ofContractRight_symm, eConn_ofContractLeft, eConn_symm, symm_right]

lemma eConn_ofDeleteLeft (P : (M ＼ D).Partition) (hD : D ⊆ M.E := by aesop_mat) :
    P.ofDeleteLeft.eConn = P.eConn + M✶.eLocalConn P.right D := by
  rw [← eConn_dual, ofDeleteLeft_dual, eConn_ofContractLeft]
  simp

lemma eConn_ofDeleteRight (P : (M ＼ D).Partition) (hD : D ⊆ M.E := by aesop_mat) :
    P.ofDeleteRight.eConn = P.eConn + M✶.eLocalConn P.left D := by
  rw [← eConn_symm, P.ofDeleteRight_symm, eConn_ofDeleteLeft, eConn_symm, symm_right]

lemma eConn_induce_le_of_isMinor {N : Matroid α} (P : M.Partition) (hNM : N ≤m M) :
    (P.induce hNM.subset).eConn ≤ P.eConn := by
  rw [← eConn_left, induce_left, ← eConn_left, eConn_inter_ground]
  exact hNM.eConn_le _

lemma eConn_contract_le (P : M.Partition) (C : Set α) : (P.contract C).eConn ≤ P.eConn :=
  eConn_induce_le_of_isMinor P <| contract_isMinor ..

lemma eConn_delete_le (P : M.Partition) (D : Set α) : (P.delete D).eConn ≤ P.eConn :=
  eConn_induce_le_of_isMinor P <| delete_isMinor ..

lemma eConn_eq_eConn_contract_add_left (P : M.Partition) (hC : C ⊆ P.left) :
    P.eConn = (P.contract C).eConn + M.eLocalConn P.right C := by
  rw [← P.contract_ofContractLeft hC, eConn_ofContractLeft]
  simp

lemma eConn_eq_eConn_contract_add_right (P : M.Partition) (hC : C ⊆ P.right) :
    P.eConn = (P.contract C).eConn + M.eLocalConn P.left C := by
  rw [← P.contract_ofContractRight hC, eConn_ofContractRight]
  simp

lemma eConn_le_eConn_contract_add (P : M.Partition) (C : Set α) :
    P.eConn ≤ (P.contract C).eConn + M.eRk C := by
  have hrw : (C ∩ P.left ∪ C ∩ P.right) ∩ M.E = C ∩ M.E := by
    rw [← inter_union_distrib_left, P.union_eq, inter_assoc, inter_self]
  grw [eConn_eq_eConn_contract_add_left (C := C ∩ P.left) _ inter_subset_right,
    eConn_eq_eConn_contract_add_right (C := C ∩ P.right), eLocalConn_le_eRk_right,
    eLocalConn_le_eRk_right, add_assoc, ← eRelRk_eq_eRk_contract, eRelRk_add_eRk_eq, union_comm,
    contract_contract, P.contract_congr hrw, ← eRk_inter_ground]
  · simp [hrw]
  have := P.disjoint
  rw [contract_right]
  tauto_set

lemma eConn_le_eConn_delete_add (P : M.Partition) (D : Set α) :
    P.eConn ≤ (P.delete D).eConn + M✶.eRk D := by
  grw [← eConn_dual, eConn_le_eConn_contract_add _ D, dual_contract, eConn_copy, eConn_dual]

lemma eConn_ofContractLeft_singleton_le_eConn_add_one (P : (M ／ {e}).Partition)
    (he : e ∈ M.E := by aesop_mat) :
    P.ofContractLeft.eConn ≤ P.eConn + 1 := by
  grw [eConn_ofContractLeft, eLocalConn_le_eRk_right, eRk_singleton_le]

lemma eConn_ofContractRight_singleton_le_eConn_add_one (P : (M ／ {e}).Partition)
    (he : e ∈ M.E := by aesop_mat) :
    P.ofContractRight.eConn ≤ P.eConn + 1 := by
  grw [eConn_ofContractRight, eLocalConn_le_eRk_right, eRk_singleton_le]

lemma eConn_ofDeleteLeft_singleton_le_eConn_add_one (P : (M ＼ {e}).Partition)
    (he : e ∈ M.E := by aesop_mat) :
    P.ofDeleteLeft.eConn ≤ P.eConn + 1 := by
  grw [eConn_ofDeleteLeft, eLocalConn_le_eRk_right, eRk_singleton_le]

lemma eConn_ofDeleteRight_singleton_le_eConn_add_one (P : (M ＼ {e}).Partition)
    (he : e ∈ M.E := by aesop_mat) :
    P.ofDeleteRight.eConn ≤ P.eConn + 1 := by
  grw [eConn_ofDeleteRight, eLocalConn_le_eRk_right, eRk_singleton_le]

lemma eConn_eq_of_subset_closure_of_isRestriction {N : Matroid α} {Q : N.Partition}
    {P : M.Partition} (hNM : N ≤r M) (subset_left : Q.1 ⊆ P.1) (subset_right : Q.2 ⊆ P.2)
    (subset_closure_left : P.1 ⊆ M.closure Q.1) (subset_closure_right : P.2 ⊆ M.closure Q.2) :
    P.eConn = Q.eConn := by
  simp_rw [eConn_eq_left, Matroid.eConn_eq_eLocalConn, Partition.compl_left]
  rw [hNM.eLocalConn_eq_of_subset Q.left_subset_ground Q.right_subset_ground]
  refine le_antisymm ?_ ?_
  · rw [← eLocalConn_closure_closure (X := Q.left)]
    exact eLocalConn_mono _ subset_closure_left subset_closure_right
  exact eLocalConn_mono _ subset_left subset_right




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
