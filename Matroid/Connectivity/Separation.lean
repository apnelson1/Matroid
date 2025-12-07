import Matroid.Connectivity.Core
import Matroid.Connectivity.Nat
import Matroid.Connectivity.Connected
import Matroid.Connectivity.Minor
import Matroid.ForMathlib.Finset
import Matroid.ForMathlib.Matroid.Sum

open Set Function

lemma pairwise_on_bool' {α : Type*} {r : α → α → Prop} {f : Bool → α} (b : Bool) :
    Pairwise (r on f) ↔ r (f b) (f !b) ∧ r (f !b) (f b) := by
  simp_rw [Pairwise, b.forall_bool']
  simp
lemma pairwise_disjoint_on_bool' {α : Type*} {f : Bool → Set α} (b : Bool) :
    Pairwise (Disjoint on f) ↔ Disjoint (f b) (f !b) := by
  rw [pairwise_on_bool', disjoint_comm, and_self]

abbrev left : Bool := true
abbrev right : Bool := false

@[simp]
lemma not_left : (!left) = right := rfl

@[simp]
lemma not_right : (!right) = left := rfl

def Bool.recLeftRight {motive : Bool → Sort*} (left : motive left) (right : motive right)
    (b : Bool) :
    motive b := match b with
  | false => right
  | true => left

namespace Matroid

section separation

variable {α : Type*} {M N : Matroid α} {j k : ℕ∞} {e f : α} {A B X X' Y Y' : Set α} {b : Bool}

/-- A partition of the ground set of a matroid into two parts.
Used for reasoning about connectivity. -/
protected structure Partition' (M : Matroid α) where
  left : Set α
  right : Set α
  disjoint : Disjoint left right
  union_eq : left ∪ right = M.E

protected structure Partition (M : Matroid α) where
  toFun : Bool → Set α
  pairwise_disjoint' : Pairwise (Disjoint on toFun)
  iUnion_eq' : ⋃ i, toFun i = M.E

instance : FunLike M.Partition Bool (Set α) where
  coe := Partition.toFun
  coe_injective' := by rintro ⟨f,h⟩ ⟨f', h'⟩; simp

variable {P : M.Partition}

namespace Partition

@[simp]
protected lemma toFun_eq_coe (P : M.Partition) : P.toFun = P := rfl

@[simp]
protected lemma mk_apply (f : Bool → Set α) (dj) (hu : ⋃ i, f i = M.E) (b : Bool) :
    Partition.mk f dj hu b = f b := rfl

protected lemma pairwise_disjoint (P : M.Partition) : Pairwise (Disjoint on P) :=
  P.pairwise_disjoint'

protected lemma iUnion_eq (P : M.Partition) : ⋃ i, P i = M.E :=
  P.iUnion_eq'

@[simp]
protected lemma union_eq : P left ∪ P right = M.E := by
  simp [← P.iUnion_eq]

@[simp]
protected lemma union_eq' : P right ∪ P left = M.E := by
  simp [← P.iUnion_eq, union_comm]

@[simp]
protected lemma union_bool_eq (b : Bool) : P b ∪ P (!b) = M.E := by
  cases b <;> simp

@[simp]
protected lemma union_bool_eq' (b : Bool) : P (!b) ∪ P b = M.E := by
  cases b <;> simp

@[simp]
protected lemma disjoint : Disjoint (P left) (P right) := by
  rw [← pairwise_disjoint_on_bool]
  convert P.pairwise_disjoint with b
  cases b <;> rfl

@[simp]
protected lemma disjoint' : Disjoint (P right) (P left) :=
  P.disjoint.symm

@[simp]
protected lemma disjoint_bool (b : Bool) : Disjoint (P b) (P (!b)) := by
  cases b
  · exact P.disjoint.symm
  exact P.disjoint

@[simp]
protected lemma compl_eq (P : M.Partition) (b : Bool) : M.E \ (P b) = P (!b) := by
  rw [← P.union_bool_eq b, union_diff_cancel_left (P.disjoint_bool b).inter_eq.subset]

protected lemma compl_not_eq (P : M.Partition) (b : Bool) : M.E \ (P (!b)) = P b := by
  rw [P.compl_eq, Bool.not_not]

protected def mk' (A B : Set α) (disjoint : Disjoint A B) (union_eq : A ∪ B = M.E) :
    M.Partition where
  toFun b := bif b then A else B
  pairwise_disjoint' := by rwa [pairwise_disjoint_on_bool]
  iUnion_eq' := by simpa

@[simp]
protected lemma mk'_left {A B : Set α} {hdj} {hu : A ∪ B = M.E} :
    Partition.mk' A B hdj hu left = A := rfl

@[simp]
protected lemma mk'_right {A B : Set α} {hdj} {hu : A ∪ B = M.E} :
    Partition.mk' A B hdj hu right = B := rfl

protected lemma ext_bool {P P' : M.Partition} (h : P b = P' b) : P = P' := by
  have h' (i) : P i = P' i := by
    obtain rfl | rfl := b.eq_or_eq_not i
    · assumption
    rw [← P.compl_not_eq, h, P'.compl_not_eq]
  cases P; cases P'; simpa [funext_iff] using h'

protected lemma ext {P P' : M.Partition} (h_left : P left = P' left) : P = P' :=
  P.ext_bool h_left

protected lemma ext_iff {P P' : M.Partition} (b : Bool) : P = P' ↔ P b = P' b :=
  ⟨fun h ↦ by simp [h], fun h ↦ P.ext_bool h⟩

@[simps]
protected def symm (P : M.Partition) : M.Partition where
  toFun b := P.toFun !b
  pairwise_disjoint' := P.pairwise_disjoint.comp_of_injective <| by trivial
  iUnion_eq' := by
    rw [← P.iUnion_eq]
    simp [union_comm]

protected lemma symm_left (P : M.Partition) : P.symm left = P right := rfl

protected lemma symm_right (P : M.Partition) : P.symm right = P left := rfl

@[simp]
protected lemma symm_apply (P : M.Partition) (b : Bool) : P.symm b = P !b := rfl

@[simp]
protected lemma symm_symm (P : M.Partition) : P.symm.symm = P := Partition.ext rfl

@[simps]
protected def dual (P : M.Partition) : M✶.Partition where
  toFun := P.toFun
  pairwise_disjoint' := P.pairwise_disjoint
  iUnion_eq' := P.iUnion_eq

@[simps]
protected def ofDual (P : M✶.Partition) : M.Partition where
  toFun := P.toFun
  pairwise_disjoint' := P.pairwise_disjoint
  iUnion_eq' := P.iUnion_eq

@[simp]
protected lemma dual_apply (P : M.Partition) (b : Bool) : P.dual b = P b := rfl


@[simp]
protected lemma ofDual_apply (P : M✶.Partition) (b : Bool) : P.ofDual b = P b := rfl

@[simp] lemma dual_ofDual (P : M.Partition) : P.dual.ofDual = P := rfl

@[simp] lemma ofDual_dual (P : M✶.Partition) : P.ofDual.dual = P := rfl

attribute [simp] Partition.disjoint Partition.union_eq

@[simps] def dualEquiv (M : Matroid α) : M.Partition ≃ M✶.Partition where
  toFun := Partition.dual
  invFun := Partition.ofDual
  left_inv P := by simp
  right_inv P := by simp



protected lemma compl_left (P : M.Partition) : M.E \ (P left) = P right := by
  rw [← P.union_eq, union_diff_left, sdiff_eq_left]
  exact P.symm.disjoint

@[simp]
protected lemma compl_right (P : M.Partition) : M.E \ (P right) = P left := by
  rw [← P.symm_right, ← P.symm.compl_left, P.symm_left]

@[simp, aesop unsafe 10% (rule_sets := [Matroid])]
protected lemma subset_ground (P : M.Partition) (b : Bool) : P b ⊆ M.E := by
  rw [← P.iUnion_eq]
  exact subset_iUnion ..

/-- A partition is trivial if one side is empty. -/
protected def Trivial (P : M.Partition) : Prop := ∃ b, P b = ∅

lemma trivial_of_eq_empty (h : P b = ∅) : P.Trivial := ⟨_, h⟩

lemma trivial_of_eq_ground (h : P b = M.E) : P.Trivial := ⟨!b, by rw [← P.compl_eq, h, diff_self]⟩

protected lemma trivial_def : P.Trivial ↔ P left = ∅ ∨ P right = ∅ := by
  simp [Partition.Trivial, or_comm]

lemma not_trivial_iff : ¬ P.Trivial ↔ ∀ b, (P b).Nonempty := by
  simp [nonempty_iff_ne_empty, P.trivial_def, and_comm]

protected lemma trivial_def' : P.Trivial ↔ P left = M.E ∨ P right = M.E := by
  rw [or_comm, ← Bool.exists_bool (p := fun i ↦ P i = M.E)]
  exact ⟨fun ⟨b, hb⟩ ↦ ⟨!b, by rw [← P.compl_eq, hb, diff_empty]⟩,
    fun ⟨b, hb⟩ ↦ trivial_of_eq_ground hb⟩

lemma Trivial.exists_eq_ground (h : P.Trivial) : ∃ b, P b = M.E := by
  obtain ⟨b, hb⟩ := h
  refine ⟨!b, by rw [← P.compl_eq, hb, diff_empty]⟩

lemma trivial_of_ground_subsingleton (P : M.Partition) (h : M.E.Subsingleton) : P.Trivial :=
  (h.eq_or_eq_of_subset (P.subset_ground left)).elim trivial_of_eq_empty trivial_of_eq_ground

noncomputable abbrev eConn (P : M.Partition) : ℕ∞ := M.eLocalConn (P left) (P right)

@[simp]
lemma eConn_symm (P : M.Partition) : P.symm.eConn = P.eConn :=
  M.eLocalConn_comm _ _

@[simp]
lemma eConn_eq (P : M.Partition) (b : Bool) : M.eConn (P b) = P.eConn := by
  rw [Partition.eConn, eConn_eq_eLocalConn]
  simp only [Partition.compl_eq]
  cases b with
  | false => exact eLocalConn_comm ..
  | true => rfl

lemma eConn_eq_eLocalConn (P : M.Partition) : P.eConn = M.eLocalConn (P left) (P right) := rfl

@[simp]
lemma eConn_dual (P : M.Partition) : P.dual.eConn = P.eConn := by
  rw [← P.dual.eConn_eq left, M.eConn_dual, P.dual_apply, P.eConn_eq]

@[simp]
lemma eConn_ofDual (P : M✶.Partition) : P.ofDual.eConn = P.eConn := by
  rw [← P.dual_ofDual, ← eConn_dual]
  simp

lemma Trivial.eConn (h : P.Trivial) : P.eConn = 0 := by
  obtain ⟨b, hb⟩ := h
  simp [← P.eConn_eq b, hb]

@[simp]
protected lemma not_indep_iff : ¬ M.Indep (P b) ↔ M.Dep (P b) := by
  rw [not_indep_iff]

@[simp]
protected lemma not_dep_iff : ¬ M.Dep (P b) ↔ M.Indep (P b) := by
  rw [not_dep_iff]

@[simp]
protected lemma not_coindep_iff : ¬ M.Coindep (P b) ↔ M.Codep (P b) := by
  rw [not_coindep_iff]

@[simp]
protected lemma not_codep_iff : ¬ M.Codep (P b) ↔ M.Coindep (P b) := by
  rw [← not_coindep_iff, not_not]

@[simp]
protected lemma not_indep_dual_iff : ¬ M✶.Indep (P b) ↔ M.Codep (P b) := by
  rw [not_coindep_iff]

@[simp]
protected lemma not_spanning_iff : ¬ M.Spanning (P b) ↔ M.Nonspanning (P b) := by
  rw [not_spanning_iff]

@[simp]
protected lemma not_nonspanning_iff : ¬ M.Nonspanning (P b) ↔ M.Spanning (P b) := by
  rw [not_nonspanning_iff]

lemma coindep_not_iff : M.Coindep (P !b) ↔ M.Spanning (P b) := by
  rw [← P.compl_eq, spanning_iff_compl_coindep]

lemma codep_not_iff : M.Codep (P !b) ↔ M.Nonspanning (P b) := by
  rw [← not_coindep_iff, coindep_not_iff, not_spanning_iff]

lemma nonspanning_not_iff : M.Nonspanning (P !b) ↔ M.Codep (P b) := by
  rw [← codep_not_iff, Bool.not_not]

lemma spanning_not_iff : M.Spanning (P !b) ↔ M.Coindep (P b) := by
  rw [← not_nonspanning_iff, nonspanning_not_iff, not_codep_iff]

lemma isCocircuit_not_iff : M.IsCocircuit (P !b) ↔ M.IsHyperplane (P b) := by
  rw [← isHyperplane_compl_iff_isCocircuit, P.compl_not_eq]

lemma isHyperplane_not_iff : M.IsHyperplane (P !b) ↔ M.IsCocircuit (P b) := by
  rw [← isCocircuit_not_iff, Bool.not_not]

protected lemma spanning_dual_iff : M✶.Spanning (P b) ↔ M.Indep (P !b) := by
  simp [spanning_dual_iff]

protected lemma nonspanning_dual_iff : M✶.Nonspanning (P b) ↔ M.Dep (P !b) := by
  rw [← not_spanning_iff, spanning_dual_iff, not_indep_iff, P.compl_eq]


/-- The connectivity of a partition as a natural number. Takes a value of `0` if infinite. -/
noncomputable def conn (P : M.Partition) : ℕ := M.localConn (P left) (P right)

@[simp]
lemma conn_symm (P : M.Partition) : P.symm.conn = P.conn := by
  simp [conn, localConn_comm]

lemma conn_eq_left (P : M.Partition) : P.conn = M.conn (P left) := by
  simp [conn, conn_eq_localConn, P.compl_left]

lemma conn_eq_right (P : M.Partition) : P.conn = M.conn (P right) := by
  simp [conn, conn_eq_localConn, P.compl_right, localConn_comm]

@[simps!]
protected def setCompl (M : Matroid α) [OnUniv M] (X : Set α) : M.Partition :=
  Matroid.Partition.mk' X Xᶜ disjoint_compl_right (by simp)

-- /-- Restrict a partition to a set. The junk elements go on the right. -/
-- @[simps!] protected def restrict (P : M.Partition) (R : Set α) : (M ↾ R).Partition :=
-- Partition.mk'
--   (P.left ∩ R) ((P.right ∩ R) ∪ (R \ M.E))
--   (disjoint_union_right.2 ⟨(P.disjoint.mono inter_subset_left inter_subset_left),
--       disjoint_sdiff_right.mono_left (inter_subset_left.trans P.left_subset_ground)⟩)
--   (by rw [← union_assoc, ← union_inter_distrib_right, P.union_eq, inter_comm, inter_union_diff,
--     restrict_ground_eq])

-- lemma eConn_restrict_eq (P : M.Partition) (R : Set α) :
--     (P.restrict R).eConn = M.eLocalConn (P.left ∩ R) (P.right ∩ R) := by
--   simp only [eConn, Partition.restrict, eLocalConn_restrict_eq, Partition.mk'_left,
--     Partition.mk'_right]
--   rw [union_inter_distrib_right, inter_assoc, inter_assoc, inter_self,
--     inter_eq_self_of_subset_left diff_subset, ← eLocalConn_inter_ground_right,
--     union_inter_distrib_right, disjoint_sdiff_left.inter_eq, union_empty,
--     eLocalConn_inter_ground_right]

/-- Transfer a partition across a matroid equality. -/
protected def copy {M' : Matroid α} (P : M.Partition) (h_eq : M = M') : M'.Partition where
  toFun := P.toFun
  pairwise_disjoint' := P.pairwise_disjoint
  iUnion_eq' := h_eq ▸ P.iUnion_eq

@[simp]
lemma copy_apply (P : M.Partition) (h_eq : M = N) (b : Bool) : P.copy h_eq b = P b := rfl

/-- A version of `copy` where the ground sets are equal, but the matroids need not be.
`copy` is preferred where possible, so that lemmas like `eConn_copy` can be `@[simp]`. -/
@[simps] protected def copy' {M' : Matroid α} (P : M.Partition) (h_eq : M.E = M'.E) :
    M'.Partition where
  toFun := P.toFun
  pairwise_disjoint' := P.pairwise_disjoint
  iUnion_eq' := h_eq ▸ P.iUnion_eq

@[simp]
lemma copy'_apply (P : M.Partition) (h_eq : M.E = N.E) (b : Bool) : P.copy' h_eq b = P b := rfl

@[simp]
lemma eConn_copy {M' : Matroid α} (P : M.Partition) (h_eq : M = M') :
    (P.copy h_eq).eConn = P.eConn := by
  obtain rfl := h_eq
  rfl

/-- The partition of `M` given by a subset of `M.E` and its complement. The elements of the set
go on side `b`.   -/
@[simps!]
protected def _root_.Matroid.partition (M : Matroid α) (A : Set α) (b : Bool)
    (hA : A ⊆ M.E := by aesop_mat) : M.Partition where
  toFun i := bif (i == b) then A else M.E \ A
  pairwise_disjoint' := by
    rw [pairwise_disjoint_on_bool' b]
    cases b <;> simp [disjoint_sdiff_right]
  iUnion_eq' := by cases b <;> simpa


lemma _root_.Matroid.partition_apply (hA : A ⊆ M.E) : (M.partition A b hA) b = A := by
  simp

lemma _root_.Matroid.partition_apply_not (hA : A ⊆ M.E) : (M.partition A b hA !b) = M.E \ A := by
  simp

@[simp]
lemma _root_.Matroid.eConn_partition (hA : A ⊆ M.E) : (M.partition A b hA).eConn = M.eConn A := by
  rw [← Partition.eConn_eq _ b, partition_apply]

@[simp]
lemma _root_.Matroid.partition_dual (hA : A ⊆ M.E) :
  M✶.partition A b hA = (M.partition A b hA).dual := rfl

lemma Trivial.exists_eq (h : P.Trivial) : ∃ b, P = M.partition ∅ b := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, Partition.ext_bool (b := b) (by simpa)⟩

/-- Intersect a partition with the ground set of a smaller matroid -/
def induce (P : M.Partition) (hN : N.E ⊆ M.E) : N.Partition where
  toFun b := P b ∩ N.E
  pairwise_disjoint' := P.pairwise_disjoint.mono <| by grind
  iUnion_eq' := by rw [← iUnion_inter, P.iUnion_eq, inter_eq_self_of_subset_right hN]

@[simp]
lemma induce_apply (P : M.Partition) (hN : N.E ⊆ M.E) (b) : P.induce hN b = (P b) ∩ N.E := rfl

@[simp]
lemma induce_symm (P : M.Partition) (hN : N.E ⊆ M.E) : (P.induce hN).symm = P.symm.induce hN :=
  Partition.ext rfl

section Cross

/-- Cross two partitions by intersecting the left sets. -/
def inter (P Q : M.Partition) : M.Partition := Partition.mk'
  (A := P left ∩ Q left)
  (B := P right ∪ Q right)
  (disjoint := by
    nth_grw 1 [disjoint_union_right, inter_subset_left, inter_subset_right]
    exact ⟨P.disjoint, Q.disjoint⟩)
  (union_eq := by
    rw [← P.compl_right, ← Q.compl_right, ← inter_diff_right_comm, union_comm (P right),
      inter_eq_self_of_subset_right diff_subset, diff_diff, diff_union_self,
      union_eq_self_of_subset_right (union_subset (Q.subset_ground _) (P.subset_ground _))])

@[simp]
lemma inter_left (P Q : M.Partition) : (P.inter Q) left = P left ∩ Q left := rfl

@[simp]
lemma inter_right (P Q : M.Partition) : (P.inter Q) right = P right ∪ Q right := rfl

/-- Cross two partitions by intersecting the right sets. -/
def union (P Q : M.Partition) : M.Partition := (P.symm.inter Q.symm).symm

@[simp]
lemma union_left (P Q : M.Partition) : (P.union Q) left = P left ∪ Q left := rfl

@[simp]
lemma union_right (P Q : M.Partition) : (P.union Q) right = P right ∩ Q right := rfl

@[simp]
lemma inter_symm (P Q : M.Partition) : (P.inter Q).symm = P.symm.union Q.symm := rfl

@[simp]
lemma union_symm (P Q : M.Partition) : (P.union Q).symm = P.symm.inter Q.symm :=
  Partition.ext rfl

@[simp]
lemma disjoint_inter_right (P : M.Partition) {X Y : Set α} : Disjoint (P left ∩ X) (P right ∩ Y) :=
  P.disjoint.mono inter_subset_left inter_subset_left

@[simp]
lemma disjoint_inter_left (P : M.Partition) {X Y : Set α} : Disjoint (X ∩ P left) (Y ∩ P right) :=
  P.disjoint.mono inter_subset_right inter_subset_right

@[simp]
lemma inter_ground_eq (P : M.Partition) (b) : P b ∩ M.E = P b :=
  inter_eq_self_of_subset_left <| P.subset_ground b

lemma union_inter_right' (P : M.Partition) (X : Set α) (b : Bool) :
    (P b ∩ X) ∪ (P (!b) ∩ X) = X ∩ M.E := by
  rw [← union_inter_distrib_right, P.union_bool_eq, inter_comm]

lemma union_inter_left' (P : M.Partition) (X : Set α) (b : Bool) :
    (X ∩ (P b)) ∪ (X ∩ (P !b)) = X ∩ M.E := by
  rw [← inter_union_distrib_left, P.union_bool_eq, inter_comm]

@[simp]
lemma union_inter_right (P : M.Partition) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) (b : Bool) :
    (P b ∩ X) ∪ ((P !b) ∩ X) = X := by
  rw [union_inter_right', inter_eq_self_of_subset_left hX]

@[simp]
lemma union_inter_left (P : M.Partition) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) (b : Bool):
    (X ∩ (P b)) ∪ (X ∩ (P !b)) = X := by
  rw [union_inter_left', inter_eq_self_of_subset_left hX]

protected lemma eConn_inter_add_eConn_union_le (P Q : M.Partition) :
    (P.inter Q).eConn + (P.union Q).eConn ≤ P.eConn + Q.eConn := by
  simp_rw [← Partition.eConn_eq _ left, union_left, inter_left]
  exact M.eConn_inter_add_eConn_union_le ..

end Cross

section Minor

variable {C D : Set α} {e f : α}

@[simp, aesop unsafe 10% (rule_sets := [Matroid])]
lemma subset_ground_of_delete (P : (M ＼ D).Partition) (b : Bool) : P b ⊆ M.E :=
  (P.subset_ground b).trans diff_subset

@[simp, aesop unsafe 10% (rule_sets := [Matroid])]
lemma left_subset_ground_of_contract (P : (M ／ C).Partition) (b : Bool) : P b ⊆ M.E :=
  (P.subset_ground b).trans diff_subset

/-- Contract the elements of `C` to take a partition of `M` to a partition of `M ／ C`. -/
def contract (P : M.Partition) (C : Set α) : (M ／ C).Partition := P.induce diff_subset

@[simp]
lemma contract_apply (P : M.Partition) (C : Set α) : (P.contract C) b = P b \ C := by
  simp only [contract, induce_apply, contract_ground]
  rw [← inter_diff_assoc, inter_eq_self_of_subset_left (P.subset_ground b)]

@[simp]
lemma contract_symm (P : M.Partition) (C : Set α) : (P.contract C).symm = P.symm.contract C := by
  simp [contract]

lemma contract_contract (P : M.Partition) (C₁ C₂ : Set α) :
    (P.contract C₁).contract C₂ = (P.contract (C₁ ∪ C₂)).copy (by simp) := by
  apply Partition.ext; simp [diff_diff]

lemma contract_congr (P : M.Partition) {C₁ C₂ : Set α} (h : C₁ ∩ M.E = C₂ ∩ M.E) :
    P.contract C₁ = (P.contract C₂).copy
      (by rw [← contract_inter_ground_eq, ← h, contract_inter_ground_eq]) := by
  have h1 := P.subset_ground left
  refine Partition.ext ?_;
  simp only [contract_apply, copy_apply]
  tauto_set

lemma contract_inter_ground (P : M.Partition) (C : Set α) :
    (P.contract (C ∩ M.E)) = (P.contract C).copy (by simp) :=
  P.contract_congr <| by simp [inter_assoc]

/-- Delete the elements of `D` to take a partition of `M` to a partition of `M ＼ D`. -/
def delete (P : M.Partition) (D : Set α) : (M ＼ D).Partition := P.induce diff_subset

@[simp]
lemma delete_apply (P : M.Partition) (D : Set α) (b : Bool) : (P.delete D) b = P b \ D := by
  simp only [delete, induce_apply, delete_ground]
  rw [← inter_diff_assoc, inter_eq_self_of_subset_left (P.subset_ground _)]

@[simp]
lemma delete_symm (P : M.Partition) (D : Set α) : (P.delete D).symm = P.symm.delete D := by
  simp [delete]

lemma delete_delete (P : M.Partition) (D₁ D₂ : Set α) :
    (P.delete D₁).delete D₂ = (P.delete (D₁ ∪ D₂)).copy (by simp) := by
  apply Partition.ext; simp [diff_diff]

@[simp]
lemma contract_dual (P : M.Partition) (C : Set α) :
    (P.contract C).dual = (P.dual.delete C).copy (by simp) :=
  Partition.ext rfl

lemma dual_contract (P : M.Partition) (C : Set α) :
    P.dual.contract C = (P.delete C).dual.copy (by simp) :=
  Partition.ext rfl

@[simp]
lemma delete_dual (P : M.Partition) (D : Set α) :
    (P.delete D).dual = (P.dual.contract D).copy (by simp) :=
  Partition.ext rfl

lemma dual_delete (P : M.Partition) (D : Set α) :
    (P.delete D).dual = (P.dual.contract D).copy (by simp) :=
  Partition.ext rfl

lemma delete_congr (P : M.Partition) {D₁ D₂ : Set α} (h : D₁ ∩ M.E = D₂ ∩ M.E) :
    P.delete D₁ = (P.delete D₂).copy
      (by rw [← delete_inter_ground_eq, ← h, delete_inter_ground_eq]) := by
  have h2 := P.subset_ground left
  refine Partition.ext ?_
  simp only [delete_apply, copy_apply]
  tauto_set

lemma delete_inter_ground (P : M.Partition) (D : Set α) :
    (P.delete (D ∩ M.E)) = (P.delete D).copy (by rw [delete_inter_ground_eq]) :=
  P.delete_congr <| by simp [inter_assoc]

@[simp]
lemma disjoint_contract (P : (M ／ C).Partition) (b : Bool) : Disjoint (P b) C := by
  grw [P.subset_ground]
  exact disjoint_sdiff_left

@[simp]
lemma disjoint_delete (P : (M ＼ D).Partition) (b : Bool) : Disjoint (P b) D := by
  grw [P.subset_ground]
  exact disjoint_sdiff_left

@[simps!]
abbrev contractDual (P : (M ／ C).Partition) : (M✶ ＼ C).Partition := P.dual.copy (by simp)

@[simps!]
abbrev deleteDual (P : (M ＼ D).Partition) : (M✶ ／ D).Partition := P.dual.copy (by simp)

/-- Extend a partition `P` of some matroid `N` to a matroid `M` with larger ground set by
adding the extra elements to side `b` of `P`. `-/
def ofSubset (P : N.Partition) (hNM : N.E ⊆ M.E) (b : Bool) : M.Partition where
  toFun i := bif (i == b) then P i ∪ (M.E \ N.E) else P i
  pairwise_disjoint' := by
    suffices Disjoint (M.E \ N.E) (P !b) by simpa [pairwise_disjoint_on_bool' b]
    exact disjoint_sdiff_left.mono_right <| P.subset_ground _
  iUnion_eq' := by
    cases b
    · simpa [← union_assoc]
    simpa [union_right_comm _ (M.E \ N.E)]

lemma ofSubset_apply (P : N.Partition) (hNM : N.E ⊆ M.E) (b i : Bool) :
    P.ofSubset hNM b i = bif (i == b) then P i ∪ (M.E \ N.E) else P i := rfl

lemma ofSubset_symm (P : N.Partition) (hNM : N.E ⊆ M.E) (b : Bool) :
    (P.ofSubset hNM b).symm = P.symm.ofSubset hNM (!b) :=
  Partition.ext <| by simp [ofSubset_apply]

@[simp]
lemma ofSubset_apply_self (P : N.Partition) (hNM : N.E ⊆ M.E) (b : Bool) :
    P.ofSubset hNM b b = P b ∪ (M.E \ N.E) := by
  simp [ofSubset_apply]

@[simp]
lemma ofSubset_apply_not (P : N.Partition) (hNM : N.E ⊆ M.E) (b : Bool) :
    P.ofSubset hNM b (!b) = P (!b) := by
  simp [ofSubset_apply]

@[simp]
lemma ofSubset_not_apply (P : N.Partition) (hNM : N.E ⊆ M.E) (b : Bool) :
    P.ofSubset hNM (!b) b = P b := by
  simp [ofSubset_apply]

@[simp]
lemma ofSubset_copy {N' : Matroid α} (P : N.Partition) (hN' : N = N') (hN'M : N'.E ⊆ M.E)
    (b : Bool) : (P.copy hN').ofSubset hN'M b = P.ofSubset (hN' ▸ hN'M) b :=
  Partition.ext_bool (b := !b) <| by simp

/-- Extend a partition of `M ／ C` to one of `M` by extending using side `b`. -/
def ofContract (P : (M ／ C).Partition) (b : Bool) : M.Partition := P.ofSubset diff_subset b

lemma ofContract_apply (P : (M ／ C).Partition) (hC : C ⊆ M.E := by aesop_mat) (b i : Bool) :
    P.ofContract b i = bif i == b then P i ∪ C else P i := by
  simp [ofContract, ofSubset_apply, inter_eq_self_of_subset_right hC]

@[simp]
lemma ofContract_apply_self (P : (M ／ C).Partition) (hC : C ⊆ M.E := by aesop_mat) (b : Bool) :
    P.ofContract b b = P b ∪ C := by
  simp [P.ofContract_apply]

@[simp]
lemma ofContract_apply_not (P : (M ／ C).Partition) (b : Bool) : P.ofContract b (!b) = P !b := by
  simp [ofContract, ofSubset_apply]

@[simp]
lemma ofContract_not_apply (P : (M ／ C).Partition) (b : Bool) : P.ofContract (!b) b = P b := by
  simpa using P.ofContract_apply_not (!b)

@[simp]
lemma ofContract_symm (P : (M ／ C).Partition) (b : Bool) :
    (P.ofContract b).symm = P.symm.ofContract (!b) :=
  ofSubset_symm ..

@[simp]
lemma ofContract_copy {C' : Set α} (P : (M ／ C).Partition) (h_eq : M ／ C = M ／ C') (b : Bool) :
    (P.copy h_eq).ofContract b = P.ofContract b :=
  Partition.ext_bool (b := !b) <| by simp

/-- Extend a partition of `M ＼ D` to a partition of `M` by adding `D` to the left side. -/
def ofDelete (P : (M ＼ D).Partition) (b : Bool) : M.Partition := P.ofSubset diff_subset b

lemma ofDelete_apply (P : (M ＼ D).Partition) (hD : D ⊆ M.E := by aesop_mat) (b i : Bool) :
    P.ofDelete b i = bif i == b then P i ∪ D else P i := by
  simp [ofDelete, ofSubset_apply, inter_eq_self_of_subset_right hD]

@[simp]
lemma ofDelete_apply_self (P : (M ＼ D).Partition) (hD : D ⊆ M.E := by aesop_mat) (b : Bool) :
    P.ofDelete b b = P b ∪ D := by
  simp [P.ofDelete_apply]

@[simp]
lemma ofDelete_apply_not (P : (M ＼ D).Partition) (b : Bool) : P.ofDelete b (!b) = P !b := by
  simp [ofDelete]

@[simp]
lemma ofDelete_not_apply (P : (M ＼ D).Partition) (b : Bool) : P.ofDelete (!b) b = P b := by
  simp [ofDelete]

@[simp]
lemma ofDelete_copy {D' : Set α} (P : (M ＼ D).Partition) (h_eq : M ＼ D = M ＼ D') (b : Bool) :
    (P.copy h_eq).ofDelete b = P.ofDelete b :=
  Partition.ext_bool (b := !b) <| by simp

@[simp]
lemma ofDelete_symm (P : (M ＼ D).Partition) (b : Bool):
    (P.ofDelete b).symm = P.symm.ofDelete !b :=
  ofSubset_symm ..

@[simp]
lemma ofDelete_dual (P : (M ＼ D).Partition) (b : Bool) :
    (P.ofDelete b).dual = P.deleteDual.ofContract b := rfl

@[simp]
lemma ofContract_dual (P : (M ／ C).Partition) (b : Bool) :
    (P.ofContract b).dual = P.contractDual.ofDelete b := rfl

@[simp]
lemma ofContract_contract (P : (M ／ C).Partition) (hC : C ⊆ M.E := by aesop_mat) (b : Bool) :
    (P.ofContract b).contract C = P := by
  apply Partition.ext
  obtain rfl | rfl := b.eq_or_eq_not left
  · rw [contract_apply, ofContract_apply_self, union_diff_cancel_right]
    exact (P.disjoint_contract left).inter_eq.subset
  rw [contract_apply, not_left, ← not_right, ofContract_apply_not, sdiff_eq_left]
  simp

lemma contract_ofContract (P : M.Partition) (hC : C ⊆ P b) : (P.contract C).ofContract b = P :=
  Partition.ext_bool (b := b) <| by
    rw [ofContract_apply_self, contract_apply, diff_union_of_subset hC]

lemma delete_ofDelete (P : M.Partition) (hD : D ⊆ P b) :
    (P.delete D).ofDelete b = P :=
  Partition.ext_bool (b := b) <| by rw [ofDelete_apply_self, delete_apply, diff_union_of_subset hD]

@[simp]
lemma ofDelete_delete (P : (M ＼ D).Partition) (hD : D ⊆ M.E := by aesop_mat) :
    (P.ofDelete b).delete D = P :=
  Partition.ext_bool (b := b) <| by simp [ofDelete_apply_self _ hD]

lemma compl_delete (P : (M ＼ D).Partition) (hD : D ⊆ M.E := by aesop_mat) (b : Bool) :
    M.E \ P b = P (!b) ∪ D := by
  grw [← P.compl_eq, delete_ground, diff_diff_comm, diff_union_self, eq_comm, union_eq_left,
    subset_diff, and_iff_right hD, P.subset_ground]
  exact disjoint_sdiff_right

lemma compl_contract (P : (M ／ C).Partition) (hC : C ⊆ M.E := by aesop_mat) (b : Bool) :
    M.E \ (P b) = P (!b) ∪ C :=  by
  simpa using (P.dual.copy (M.dual_contract C)).compl_delete hC b

@[simp]
lemma compl_union_contract (P : (M ／ C).Partition) (b : Bool) : M.E \ (P b ∪ C) = P !b := by
  rw [← P.compl_eq, union_comm, contract_ground, diff_diff]

@[simp]
lemma compl_union_delete (P : (M ＼ D).Partition) (b : Bool) : M.E \ (P b ∪ D) = P !b := by
  rw [← P.compl_eq, union_comm, delete_ground, diff_diff]

lemma compl_delete_singleton (P : (M ＼ {e}).Partition) (he : e ∈ M.E := by aesop_mat) (b : Bool) :
    M.E \ (P b) = insert e (P (!b)) := by
  rw [compl_delete, union_singleton]

lemma compl_contract_singleton (P : (M ／ {e}).Partition) (he : e ∈ M.E := by aesop_mat) (b : Bool) :
    M.E \ (P b) = insert e (P !b) := by
  rw [compl_contract, union_singleton]

lemma eConn_ofContract (P : (M ／ C).Partition) (b : Bool) :
    (P.ofContract b).eConn = P.eConn + M.eLocalConn (P !b) C := by
  wlog hCE : C ⊆ M.E generalizing C P with aux
  · simpa using aux (C := C ∩ M.E) (P.copy (by simp)) inter_subset_right
  rw [← (P.ofContract b).eConn_eq b, ofContract_apply_self,
    eConn_union_eq_eConn_contract_add _ (by simp), P.compl_union_contract, P.eConn_eq b]

lemma eConn_ofDelete (P : (M ＼ D).Partition) (b : Bool) :
    (P.ofDelete b).eConn = P.eConn + M✶.eLocalConn (P !b) D := by
  rw [← eConn_dual, ofDelete_dual, eConn_ofContract]
  simp

lemma eConn_induce_le_of_isMinor (P : M.Partition) (hNM : N ≤m M) :
    (P.induce hNM.subset).eConn ≤ P.eConn := by
  rw [← eConn_eq _ left, induce_apply, ← eConn_eq _ left, eConn_inter_ground]
  exact hNM.eConn_le _

lemma eConn_contract_le (P : M.Partition) (C : Set α) : (P.contract C).eConn ≤ P.eConn :=
  eConn_induce_le_of_isMinor P <| contract_isMinor ..

lemma eConn_delete_le (P : M.Partition) (D : Set α) : (P.delete D).eConn ≤ P.eConn :=
  eConn_induce_le_of_isMinor P <| delete_isMinor ..

lemma eConn_eq_eConn_contract_add (P : M.Partition) (hC : C ⊆ P b) :
    P.eConn = (P.contract C).eConn + M.eLocalConn (P !b) C := by
  rw [← P.contract_ofContract hC, eConn_ofContract]
  rw [contract_apply, ofContract_contract, contract_ofContract _ hC, sdiff_eq_left.2]
  exact (P.disjoint_bool b).symm.mono_right hC

lemma eConn_le_eConn_contract_add (P : M.Partition) (C : Set α) :
    P.eConn ≤ (P.contract C).eConn + M.eRk C := by
  grw [P.eConn_eq_eConn_contract_add (C := C ∩ (P left)) inter_subset_right,
    eConn_eq_eConn_contract_add (C := C ∩ (P right)) (b := right), eLocalConn_le_eRk_right,
    eLocalConn_le_eRk_right, add_assoc, ← eRelRk_eq_eRk_contract, eRelRk_add_eRk_eq,
    ← inter_union_distrib_left, P.union_eq', eRk_inter_ground, contract_contract,
    P.contract_congr (by rw [← inter_union_distrib_left, P.union_eq]),
    P.contract_congr (C₂ := C) (by simp [inter_assoc])]
  · simp
  rw [P.contract_apply, ← P.compl_right]
  tauto_set

lemma eConn_le_eConn_delete_add (P : M.Partition) (D : Set α) :
    P.eConn ≤ (P.delete D).eConn + M✶.eRk D := by
  grw [← eConn_dual, eConn_le_eConn_contract_add _ D, dual_contract, eConn_copy, eConn_dual]

lemma eConn_ofContract_singleton_le_eConn_add_one (P : (M ／ {e}).Partition) (b : Bool) :
    (P.ofContract b).eConn ≤ P.eConn + 1 := by
  grw [eConn_ofContract, eLocalConn_le_eRk_right, eRk_singleton_le]

lemma eConn_ofDelete_singleton_le_eConn_add_one (P : (M ＼ {e}).Partition) (b : Bool) :
    (P.ofDelete b).eConn ≤ P.eConn + 1 := by
  grw [eConn_ofDelete, eLocalConn_le_eRk_right, eRk_singleton_le]

lemma eConn_eq_of_subset_closure_of_isRestriction {N : Matroid α} {Q : N.Partition}
    {P : M.Partition} (hNM : N ≤r M) (forall_subset : ∀ b, Q b ⊆ P b)
    (forall_subset_closure : ∀ b, P b ⊆ M.closure (Q b)) : P.eConn = Q.eConn := by
  rw [Partition.eConn, Partition.eConn,
    hNM.eLocalConn_eq_of_subset (Q.subset_ground left) (Q.subset_ground right)]
  refine le_antisymm ?_ <| M.eLocalConn_mono (forall_subset left) (forall_subset right)
  grw [← eLocalConn_closure_closure (X := Q _),
  M.eLocalConn_mono (forall_subset_closure left) (forall_subset_closure right)]

end Minor

lemma eConn_eq_zero_iff_skew {P : M.Partition} {b : Bool} : P.eConn = 0 ↔ M.Skew (P b) (P !b) := by
  rw [← M.eLocalConn_eq_zero (P.subset_ground b) (P.subset_ground (!b)), Partition.eConn]
  cases b
  · rw [eLocalConn_comm]
    rfl
  rfl

lemma eConn_eq_zero_iff_eq_disjointSum {P : M.Partition} {b : Bool} :
    P.eConn = 0 ↔ M = (M ↾ (P b)).disjointSum (M ↾ (P !b)) (P.disjoint_bool b) := by
  rw [eConn_eq_zero_iff_skew,
    skew_iff_restrict_union_eq (P.subset_ground _) (P.subset_ground _) (P.disjoint_bool b),
    P.union_bool_eq, restrict_ground_eq_self]

lemma exists_partition_of_not_connected [M.Nonempty] (h : ¬ M.Connected) :
    ∃ P : M.Partition, P.eConn = 0 ∧ ¬ P.Trivial := by
  obtain ⟨M₁, M₂, hdj, hM₁, hM₂, rfl⟩ := eq_disjointSum_of_not_connected h
  refine ⟨Matroid.partition _ M₁.E true (by simp), ?_⟩
  simp [Partition.trivial_def, hdj.symm.sdiff_eq_left, hM₁.ground_nonempty.ne_empty,
    hM₂.ground_nonempty.ne_empty]

lemma exists_partition_iff_not_connected [M.Nonempty] :
    ¬ M.Connected ↔ ∃ P : M.Partition, P.eConn = 0 ∧ ¬ P.Trivial := by
  refine ⟨exists_partition_of_not_connected, fun ⟨P, hP, hPnt⟩ ↦ ?_⟩
  rw [eConn_eq_zero_iff_eq_disjointSum (b := left)] at hP
  rw [hP]
  simp only [P.trivial_def, not_or, ← nonempty_iff_ne_empty] at hPnt
  apply disjointSum_not_connected
  · rw [← ground_nonempty_iff]
    exact hPnt.1
  rw [← ground_nonempty_iff]
  exact hPnt.2


-- section wlog


-- -- protected lemma wlog_symm' (motive : {N : Matroid α} → (P : N.Partition) → Prop)
-- --     (property : {N : Matroid α} → N.Partition → Prop)
-- --     (h_symm : ∀ P, property P ∨ property P.symm)
-- --     (h_wlog : ∀ P, property P → motive P) (P₀ : M.Partition) :

-- protected lemma wlog_symm (motive : {N : Matroid α} → (P : N.Partition) → Prop)
--     (property : Matroid α → Set α → Prop)
--     (h_symm : ∀ ⦃N⦄ ⦃P : Matroid.Partition N⦄, motive P.symm → motive P)
--     (h_some : ∀ ⦃N⦄ ⦃P : Matroid.Partition N⦄, property N P.left → motive P)
--     (h_not : ∀ ⦃N⦄ ⦃P : Matroid.Partition N⦄, ¬ property N P.left → ¬ property N P.right →
-- motive P)
--     (P₀ : M.Partition) : motive P₀ := by
--   by_cases h1 : property M P₀.left
--   · exact h_some h1
--   by_cases h2 : property M P₀.right
--   · exact h_symm <| h_some (P := P₀.symm) (by simpa)
--   exact h_not h1 h2

-- protected lemma wlog_symm_dual (motive : {N : Matroid α} → (P : N.Partition) → Prop)
--     (property : Matroid α → Set α → Prop)
--     (h_symm : ∀ ⦃N⦄ ⦃P : Matroid.Partition N⦄, motive P.symm → motive P)
--     (h_dual : ∀ ⦃N⦄ ⦃P : Matroid.Partition N⦄, motive P.dual → motive P)
--     (h_some : ∀ ⦃N⦄ ⦃P : Matroid.Partition N⦄, property N P.left → motive P)
--     (h_not : ∀ ⦃N⦄ ⦃P : Matroid.Partition N⦄, ¬ property N P.left → ¬ property N P.right →
--       ¬ property N✶ P.left → ¬ property N✶ P.right → motive P) (P₀ : M.Partition) :
--  motive P₀ := by
--   by_cases h1 : property M P₀.left
--   · exact h_some h1
--   by_cases h2 : property M P₀.right
--   · exact h_symm <| h_some (P := P₀.symm) (by simpa)
--   by_cases h1' : property M✶ P₀.left
--   · exact h_dual <| h_some (N := M✶) (P := P₀.dual) (by simpa)
--   by_cases h2' : property M✶ P₀.right
--   · exact h_symm <| h_dual <| h_some (N := M✶) (P := P₀.symm.dual) (by simpa)
--   exact h_not h1 h2 h1' h2'

--end wlog

end Partition
