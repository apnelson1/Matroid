import Matroid.Connectivity.Core
import Matroid.Connectivity.Nat
import Matroid.Connectivity.Connected
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

@[mk_iff]
structure Partition.SepOf (P : M.Partition) (X Y : Set α) : Prop where
  subset_left : X ⊆ P.left
  subset_right : Y ⊆ P.right

lemma Partition.sepOf_iff_left (P : M.Partition) (hY : Y ⊆ M.E) :
    P.SepOf X Y ↔ X ⊆ P.left ∧ Disjoint P.left Y := by
  rw [sepOf_iff, ← P.compl_left, subset_diff, and_iff_right hY, disjoint_comm]

lemma Partition.sepOf_iff_right (P : M.Partition) (hX : X ⊆ M.E) :
    P.SepOf X Y ↔ Disjoint X P.right ∧ Y ⊆ P.right := by
  rw [sepOf_iff, ← P.compl_right, subset_diff, and_iff_right hX]

lemma Partition.SepOf.symm (hP : P.SepOf X Y) : P.symm.SepOf Y X :=
  ⟨hP.2, hP.1⟩

lemma Partition.SepOf.disjoint (hP : P.SepOf X Y) : Disjoint X Y :=
  P.disjoint.mono hP.1 hP.2

lemma Partition.SepOf.mono_left (hP : P.SepOf X Y) (hX'X : X' ⊆ X) : P.SepOf X' Y :=
  ⟨hX'X.trans hP.1, hP.2⟩

lemma Partition.SepOf.mono_right (hP : P.SepOf X Y) (hY'Y : Y' ⊆ Y) : P.SepOf X Y' :=
  ⟨hP.1, hY'Y.trans hP.2⟩

lemma Partition.SepOf.disjoint_left (hP : P.SepOf X Y) : Disjoint P.left Y :=
  (subset_diff.1 <| hP.subset_right.trans_eq P.compl_left.symm).2.symm

lemma Partition.SepOf.disjoint_right (hP : P.SepOf X Y) : Disjoint X P.right :=
  (subset_diff.1 <| hP.subset_left.trans_eq P.compl_right.symm).2

lemma Partition.SepOf.mono (hP : P.SepOf X Y) (hX'X : X' ⊆ X) (hY'Y : Y' ⊆ Y) : P.SepOf X' Y' :=
  ⟨hX'X.trans hP.1, hY'Y.trans hP.2⟩

@[simp]
lemma Partition.symm_sepOf_iff : P.symm.SepOf X Y ↔ P.SepOf Y X :=
  ⟨fun h ↦ h.symm, fun h ↦ h.symm⟩

lemma partition_sepOf (hXY : Disjoint X Y) (hXE : X ⊆ M.E) (hYE : Y ⊆ M.E) :
    (M.partition X).SepOf X Y := by
  rw [Partition.sepOf_iff_left _ hYE, partition_left _ _ hXE, and_iff_left hXY]


-- lemma Partition.restrict_sepOf_iff (R : Set α) :
--     (P.restrict R).SepOf X Y ↔ P.SepOf X Y ∧ X ⊆ R ∧ Y ⊆ R := by
--   simp only [SepOf, restrict_left, subset_inter_iff, restrict_right]
--   refine ⟨fun ⟨⟨h1, h2⟩, h3⟩ ↦ ?_, fun h ↦ ?_⟩
--   · refine ⟨⟨h1, ?_⟩, ?_⟩

lemma Partition.SepOf.left_subset_ground (h : P.SepOf X Y) : X ⊆ M.E :=
  h.1.trans P.left_subset_ground

lemma Partition.SepOf.right_subset_ground (h : P.SepOf X Y) : Y ⊆ M.E :=
  h.2.trans P.right_subset_ground

lemma Partition.sepOf_self_compl_iff (hX : X ⊆ M.E) :
    P.SepOf X (M.E \ X) ↔ P = M.partition X hX := by
  rw [sepOf_iff, diff_subset_comm, P.compl_right, ← subset_antisymm_iff]
  refine ⟨?_, by simp +contextual⟩
  rintro rfl
  exact Partition.ext rfl <| by simp [P.compl_left]

lemma Partition.sepOf_compl_self_iff (hX : X ⊆ M.E) :
    P.SepOf (M.E \ X) X ↔ P = M.partition (M.E \ X) diff_subset := by
  rw [← sepOf_self_compl_iff]
  simp [inter_eq_self_of_subset_right hX]

/-- The minimum order of a separation of `M` with `X` and `Y` contained in different sides.
The 'well-defined' inputs are where `X` and `Y` are disjoint subsets of `M.E`,
but we give a more complicated definition (in terms of `Matroid.core`)
that ignores junk elements, loops and coloops in `X` and `Y`.
This definition is the simplest definition that is unconditionally monotone under restrictions,
and preserved by intersections with the ground set, duality and adding/removing loops.
`Matroid.eConnBetween_eq_iInf` shows that the definition behaves correctly for sensible inputs. -/
noncomputable def eConnBetween (M : Matroid α) (X Y : Set α) : ℕ∞ :=
  ⨅ P : {P : M.Partition // P.SepOf (M.core X) (M.core Y)}, P.1.eConn

lemma Partition.SepOf.eConnBetween_le_of_core (hP : P.SepOf (M.core X) (M.core Y)) :
    M.eConnBetween X Y ≤ P.eConn :=
  iInf_le_of_le ⟨P, hP⟩ rfl.le

lemma Partition.SepOf.eConnBetween_le (hP : P.SepOf X Y) :
    M.eConnBetween X Y ≤ P.eConn :=
  (hP.mono (M.core_subset X) (M.core_subset Y)).eConnBetween_le_of_core

lemma eConnBetween_symm (M : Matroid α) : M.eConnBetween X Y = M.eConnBetween Y X := by
  apply le_antisymm <;>
  exact le_iInf fun ⟨P, hP⟩ ↦ iInf_le_of_le ⟨P.symm, by simpa⟩ (by simp)

lemma eConnBetween_le_eConn_left (M : Matroid α) (hdj : Disjoint X Y) :
    M.eConnBetween X Y ≤ M.eConn X := by
  have h : (M.partition (M.core X)).SepOf (M.core X) (M.core Y) := by
    simpa [Partition.sepOf_iff, subset_diff] using hdj.symm.mono (core_subset ..) (core_subset ..)
  exact h.eConnBetween_le_of_core.trans <| by simp

lemma eConnBetween_le_eConn_right (M : Matroid α) (hdj : Disjoint X Y) :
    M.eConnBetween X Y ≤ M.eConn Y := by
  rw [eConnBetween_symm]
  exact M.eConnBetween_le_eConn_left hdj.symm

lemma le_eConnBetween_iff_forall_sepOf_core {k : ℕ∞} : k ≤ M.eConnBetween X Y ↔
    ∀ (P : M.Partition), P.SepOf (M.core X) (M.core Y) → k ≤ P.eConn := by
  simp [eConnBetween, le_iInf_iff, Subtype.forall]

lemma eConnBetween_eq_iInf (hXY : Disjoint X Y) (hX : X ⊆ M.E) (hY : Y ⊆ M.E) :
    M.eConnBetween X Y = ⨅ P : {P : M.Partition // P.SepOf X Y}, P.1.eConn := by
  simp only [eConnBetween, le_antisymm_iff, le_iInf_iff, Subtype.forall]
  refine ⟨fun P hP ↦ ?_, fun P hP ↦ ?_⟩
  · exact iInf_le_of_le ⟨P, hP.mono (M.core_subset X) (M.core_subset Y)⟩ rfl.le
  refine iInf_le_of_le ⟨M.partition ((P.left ∪ X) \ Y), ?_⟩ ?_
  · simpa [Partition.sepOf_iff_left _ hY, disjoint_sdiff_left, subset_diff]
  rw [eConn_partition, ← eConn_core, core_diff, core_union, ← M.core_core X,
    union_eq_self_of_subset_right (M.core_subset_core hP.1), sdiff_eq_left.2, eConn_core,
    P.eConn_left]
  exact hP.disjoint_left.mono_left (M.core_subset ..)

lemma le_eConnBetween_iff_forall_sepOf {k : ℕ∞} (hdj : Disjoint X Y) (hX : X ⊆ M.E) (hY : Y ⊆ M.E) :
    k ≤ M.eConnBetween X Y ↔ ∀ (P : M.Partition), P.SepOf X Y → k ≤ P.eConn := by
  simp [eConnBetween_eq_iInf hdj hX hY]

lemma exists_partition_eConn_eq_eConnBetween_core (hXY : Disjoint (M.core X) (M.core Y)) :
    ∃ P : M.Partition, P.SepOf (M.core X) (M.core Y) ∧ P.eConn = M.eConnBetween X Y := by
  set α := {P : M.Partition // P.SepOf (M.core X) (M.core Y)}
  have hne : Nonempty α := ⟨_, partition_sepOf hXY (core_subset_ground ..) (core_subset_ground ..)⟩
  obtain ⟨⟨P,h⟩, hP⟩ := ENat.exists_eq_iInf (f := fun i : α ↦ i.1.eConn)
  exact ⟨P, h, hP⟩

lemma exists_partition_eConn_eq_eConnBetween (hXY : Disjoint X Y) (hXE : X ⊆ M.E) (hYE : Y ⊆ M.E) :
    ∃ P : M.Partition, P.SepOf X Y ∧ P.eConn = M.eConnBetween X Y := by
  simp_rw [eConnBetween_eq_iInf hXY hXE hYE]
  set α := {P : M.Partition // P.SepOf X Y}
  have hne : Nonempty α := ⟨_, partition_sepOf hXY hXE hYE⟩
  obtain ⟨⟨P,h⟩, hP⟩ := ENat.exists_eq_iInf (f := fun i : α ↦ i.1.eConn)
  exact ⟨P, h, hP⟩

lemma eConnBetween_of_not_disjoint (M : Matroid α) (hXY : ¬ Disjoint (M.core X) (M.core Y)) :
    M.eConnBetween X Y = ⊤ := by
  simp [eConnBetween, iInf_subtype, show ∀ P : M.Partition, ¬ P.SepOf (M.core X) (M.core Y) from
    fun P hP ↦ hXY <| P.disjoint.mono hP.1 hP.2]

lemma eConnBetween_mono_left (M : Matroid α) (hX : X' ⊆ X) (Y : Set α) :
    M.eConnBetween X' Y ≤ M.eConnBetween X Y :=
  le_iInf fun ⟨P, hP⟩ ↦ iInf_le_of_le ⟨P, hP.mono_left (M.core_subset_core hX)⟩ rfl.le

lemma eConnBetween_mono_right (M : Matroid α) (X : Set α) (hY : Y' ⊆ Y) :
    M.eConnBetween X Y' ≤ M.eConnBetween X Y :=
  le_iInf fun ⟨P, hP⟩ ↦ iInf_le_of_le ⟨P, hP.mono_right (M.core_subset_core hY)⟩ rfl.le

lemma eConnBetween_mono (M : Matroid α) (hX : X' ⊆ X) (hY : Y' ⊆ Y) :
    M.eConnBetween X' Y' ≤ M.eConnBetween X Y :=
  (M.eConnBetween_mono_left hX _).trans <| M.eConnBetween_mono_right _ hY

@[simp]
lemma eConnBetween_core_left (M : Matroid α) (X Y : Set α) :
    M.eConnBetween (M.core X) Y = M.eConnBetween X Y := by
  simp [eConnBetween, iInf_subtype]

@[simp]
lemma eConnBetween_core_right (M : Matroid α) (X Y : Set α) :
    M.eConnBetween X (M.core Y) = M.eConnBetween X Y := by
  simp [eConnBetween, iInf_subtype]

@[simp]
lemma eConnBetween_inter_ground_left (M : Matroid α) (X Y : Set α) :
    M.eConnBetween (X ∩ M.E) Y = M.eConnBetween X Y := by
  refine (M.eConnBetween_mono_left inter_subset_left _).antisymm ?_
  rw [← eConnBetween_core_left]
  exact M.eConnBetween_mono_left (by simp) _

@[simp]
lemma eConnBetween_inter_ground_right (M : Matroid α) (X Y : Set α) :
    M.eConnBetween X (Y ∩ M.E) = M.eConnBetween X Y := by
  rw [eConnBetween_symm, eConnBetween_inter_ground_left, eConnBetween_symm]

@[simp]
lemma eConnBetween_self_compl (M : Matroid α) (X : Set α) :
    M.eConnBetween X (M.E \ X) = M.eConn X := by
  wlog hXE : X ⊆ M.E generalizing X with aux
  · rw [← eConnBetween_inter_ground_left, ← diff_inter_self_eq_diff, aux _ inter_subset_right,
      eConn_inter_ground]
  obtain ⟨P, hP, hP'⟩ := exists_partition_eConn_eq_eConnBetween disjoint_sdiff_right hXE diff_subset
  rw [Partition.sepOf_self_compl_iff hXE] at hP
  rw [← hP', hP, eConn_partition]

@[simp]
lemma eConnBetween_compl_self (M : Matroid α) (X : Set α) :
    M.eConnBetween (M.E \ X) X = M.eConn X := by
  rw [eConnBetween_symm, M.eConnBetween_self_compl]

@[simp]
lemma eConnBetween_dual_eq (M : Matroid α) (X Y : Set α) :
    M✶.eConnBetween X Y = M.eConnBetween X Y := by
  simp only [eConnBetween, iInf_subtype, core_dual]
  apply (Partition.dualEquiv M).symm.iInf_congr
  intro P
  convert rfl using 2 <;>
  simp [Partition.sepOf_iff]

@[simp]
lemma eConnBetween_removeLoops_eq (M : Matroid α) :
    M.removeLoops.eConnBetween = M.eConnBetween := by
  ext X Y
  obtain hndj | hdj := em' <| Disjoint (M.core X) (M.core Y)
  · rw [eConnBetween_of_not_disjoint _ (by simpa), eConnBetween_of_not_disjoint _ hndj]
  refine le_antisymm ?_ ?_
  · obtain ⟨P, hP, hP_eq⟩ := M.exists_partition_eConn_eq_eConnBetween_core hdj
    refine iInf_le_of_le ⟨M.removeLoops.partition (P.left ∩ _) inter_subset_right, ?_⟩ ?_
    · rw [Partition.sepOf_iff_left _ (core_subset_ground ..)]
      simp only [removeLoops_core, partition_left, subset_inter_iff, hP.1, true_and]
      rw [← removeLoops_core, and_iff_right (core_subset_ground ..)]
      exact P.disjoint.mono inter_subset_left hP.2
    simp only [eConn_partition, removeLoops_eConn, ← hP_eq, ← P.eConn_left]
    rw [← removeLoops_eConn, eConn_inter_ground]
  obtain ⟨P, hP, hP_eq⟩ := M.removeLoops.exists_partition_eConn_eq_eConnBetween_core (by simpa)
  refine iInf_le_of_le ⟨M.partition P.left ?_, ?_⟩ ?_
  · exact P.left_subset_ground.trans M.removeLoops_isRestriction.subset
  · rw [Partition.sepOf_iff_left _ (by simp)]
    simp only [partition_left]
    simp only [removeLoops_core] at hP
    exact ⟨hP.1, hP.disjoint_left⟩
  simp only [eConn_partition, hP_eq.symm, ← P.eConn_left, removeLoops_eConn]
  exact rfl.le

lemma eConnBetween_restrict_le (M : Matroid α) (X Y R : Set α) :
    (M ↾ R).eConnBetween X Y ≤ M.eConnBetween X Y := by
  wlog hRE : R ⊆ M.E with aux
  · rw [← eConnBetween_removeLoops_eq, restrict_removeLoops, eConnBetween_removeLoops_eq]
    exact aux M X Y (R ∩ M.E) inter_subset_right
  rw [le_eConnBetween_iff_forall_sepOf_core]
  intro P hP
  refine iInf_le_of_le ⟨P.restrict R, ?_⟩ ?_
  · rw [Partition.sepOf_iff_left _ (core_subset_ground ..)]
    simp only [Partition.restrict_left, subset_inter_iff]
    exact ⟨⟨(core_restrict_subset ..).trans hP.1, core_subset_ground ..⟩,
      P.disjoint.mono inter_subset_left ((core_restrict_subset ..).trans hP.2)⟩
  simp only [eLocalConn_restrict_eq, Partition.restrict_left, inter_assoc, inter_self,
    Partition.restrict_right, diff_eq_empty.2 hRE, union_empty, Partition.eConn]
  exact M.eLocalConn_mono inter_subset_left inter_subset_left

lemma eConnBetween_delete_le (M : Matroid α) (X Y D : Set α) :
    (M ＼ D).eConnBetween X Y ≤ M.eConnBetween X Y := by
  apply eConnBetween_restrict_le

lemma eConnBetween_contract_le (M : Matroid α) (X Y C : Set α) :
    (M ／ C).eConnBetween X Y ≤ M.eConnBetween X Y := by
  rw [← eConnBetween_dual_eq, dual_contract, ← M.eConnBetween_dual_eq]
  apply eConnBetween_delete_le

lemma IsMinor.eConnBetween_le {N : Matroid α} (hNM : N ≤m M) :
    N.eConnBetween X Y ≤ M.eConnBetween X Y := by
  obtain ⟨C, D, h, -, -, rfl⟩ := hNM
  exact le_trans ((M ／ C).eConnBetween_delete_le X Y D) <| (M.eConnBetween_contract_le X Y C)
