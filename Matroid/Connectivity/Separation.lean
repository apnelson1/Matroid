import Matroid.Connectivity.Core
import Matroid.Connectivity.Nat
import Matroid.Connectivity.Connected
import Matroid.Connectivity.Minor
import Matroid.ForMathlib.Finset
import Matroid.ForMathlib.Matroid.Sum
import Matroid.ForMathlib.Data.Set.Subsingleton
import Matroid.ForMathlib.Set
import Matroid.ForMathlib.Data.Set.IndexedPartition
-- import Matroid.ForMathlib.Data.Set.IndexedPartitiom

open Set Function

lemma pairwise_on_bool' {α : Type*} {r : α → α → Prop} {f : Bool → α} (i : Bool) :
    Pairwise (r on f) ↔ r (f i) (f !i) ∧ r (f !i) (f i) := by
  simp_rw [Pairwise, i.forall_bool']
  simp

lemma pairwise_disjoint_on_bool' {α : Type*} {f : Bool → Set α} (i : Bool) :
    Pairwise (Disjoint on f) ↔ Disjoint (f i) (f !i) := by
  rw [_root_.pairwise_on_bool', disjoint_comm, and_self]

lemma iUnion_bool' {α : Type*} (f : Bool → Set α) (i : Bool) : ⋃ i, f i = f i ∪ f !i := by
  cases i <;> simp [iUnion_bool, union_comm]

namespace Matroid

section separation

variable {α : Type*} {M N : Matroid α} {j k : ℕ∞} {e f : α} {A B X X' Y Y' : Set α} {i : Bool}

/-- A bipartition of the ground set of a matroid,
implicitly including the data of the actual matroid. -/
protected def Separation (M : Matroid α) := M.E.Bipartition

instance : FunLike M.Separation Bool (Set α) where
  coe P i := IndexedPartition.toFun P i
  coe_injective' P Q := by simp

-- protected def Separation.mk ()

variable {P : M.Separation}

namespace Separation

protected def toBipartition (P : M.Separation) : M.E.Bipartition := P
@[simp, simp↓]
protected lemma toBipartition_apply (P : M.Separation) (i : Bool) : P.toBipartition i = P i := rfl

@[simp]
protected lemma toFun_eq_coe (P : M.Separation) : P.toFun = P := rfl

-- @[simp]
-- protected lemma mk_apply (f : Bool → Set α) (dj) (hu : ⋃ i, f i = M.E) (i : Bool) :
--     Separation.mk f dj hu i = f i := rfl

protected lemma pairwise_disjoint (P : M.Separation) : Pairwise (Disjoint on P) :=
  P.pairwise_disjoint'

protected lemma iUnion_eq (P : M.Separation) : ⋃ i, P i = M.E :=
  P.iUnion_eq'

@[simp] protected lemma union_eq : P true ∪ P false = M.E := Bipartition.union_eq
@[simp] protected lemma union_eq' : P false ∪ P true = M.E := Bipartition.union_eq'
@[simp] protected lemma union_bool_eq (i : Bool) : P i ∪ P (!i) = M.E :=
  Bipartition.union_bool_eq i
@[simp] protected lemma union_bool_eq' (i : Bool) : P (!i) ∪ P i = M.E :=
  Bipartition.union_bool_eq' i
@[simp] protected lemma disjoint_true_false : Disjoint (P true) (P false) :=
  Bipartition.disjoint_true_false
@[simp] protected lemma disjoint_false_true : Disjoint (P false) (P true) :=
  Bipartition.disjoint_false_true
@[simp] protected lemma disjoint_bool (i : Bool) : Disjoint (P i) (P (!i)) :=
  Bipartition.disjoint_bool i
@[simp] protected lemma compl_eq (P : M.Separation) (i : Bool) : M.E \ (P i) = P (!i) :=
  Bipartition.compl_eq P i
@[simp] protected lemma compl_not_eq (P : M.Separation) (i : Bool) : M.E \ (P (!i)) = P i :=
  Bipartition.compl_not_eq P i
@[simp] lemma compl_dual_eq (P : M✶.Separation) (i : Bool) : M.E \ P i = P !i :=
  Bipartition.compl_eq P i
@[simp] lemma compl_dual_not_eq (P : M✶.Separation) (i : Bool) : M.E \ P (!i) = P i :=
  Bipartition.compl_not_eq P i

protected def mk (f : Bool → Set α) (dj : Pairwise (Disjoint on f)) (iUnion_eq : ⋃ i, f i = M.E) :
    M.Separation :=
  IndexedPartition.mk f dj iUnion_eq

@[simp, simp↓]
lemma mk_apply (f : Bool → Set α) (dj) (iUnion_eq : ⋃ i, f i = M.E) (i : Bool) :
    Separation.mk f dj iUnion_eq i = f i := rfl

protected def mk' (A B : Set α) (disjoint : Disjoint A B) (union_eq : A ∪ B = M.E) :
    M.Separation where
  toFun i := bif i then A else B
  pairwise_disjoint' := by rwa [pairwise_disjoint_on_bool]
  iUnion_eq' := by simpa

@[simp]
protected lemma mk'_true {A B : Set α} {hdj} {hu : A ∪ B = M.E} :
    Separation.mk' A B hdj hu true = A := rfl

@[simp]
protected lemma mk'_false {A B : Set α} {hdj} {hu : A ∪ B = M.E} :
    Separation.mk' A B hdj hu false = B := rfl

protected lemma ext_bool {P P' : M.Separation} (i : Bool) (h : P i = P' i) : P = P' :=
  Bipartition.ext_bool i h

protected lemma ext {P P' : M.Separation} (h : P true = P' true) : P = P' := P.ext_bool _ h

protected lemma ext_iff_bool {P P' : M.Separation} (i : Bool) : P = P' ↔ P i = P' i :=
  ⟨fun h ↦ by simp [h], fun h ↦ P.ext_bool i h⟩

protected def symm (P : M.Separation) : M.Separation := Bipartition.symm P
protected lemma symm_true (P : M.Separation) : P.symm true = P false := rfl
protected lemma symm_false (P : M.Separation) : P.symm false = P true := rfl
@[simp] protected lemma symm_apply (P : M.Separation) (i : Bool) : P.symm i = P !i := rfl
@[simp] protected lemma symm_symm (P : M.Separation) : P.symm.symm = P := Separation.ext rfl

@[simp] protected lemma compl_true (P : M.Separation) : M.E \ (P true) = P false :=
  Bipartition.compl_true P

@[simp] protected lemma compl_false (P : M.Separation) : M.E \ (P false) = P true :=
  Bipartition.compl_false P

@[simp, aesop unsafe 10% (rule_sets := [Matroid])]
protected lemma subset_ground (P : M.Separation) : P i ⊆ M.E := P.subset

/-- Transfer a partition across a matroid equality. -/
protected def copy {M' : Matroid α} (P : M.Separation) (h_eq : M = M') : M'.Separation where
  toFun := P.toFun
  pairwise_disjoint' := P.pairwise_disjoint
  iUnion_eq' := h_eq ▸ P.iUnion_eq

@[simp]
lemma copy_apply (P : M.Separation) (h_eq : M = N) (i : Bool) : P.copy h_eq i = P i := rfl

/-- A version of `copy` where the ground sets are equal, but the matroids need not be.
`copy` is preferred where possible, so that lemmas depending on matroid structure
like `eConn_copy` can be `@[simp]`. -/
protected def copy' {M' : Matroid α} (P : M.Separation) (h_eq : M.E = M'.E) :=
  Bipartition.copy P h_eq

@[simp]
lemma copy'_apply (P : M.Separation) (h_eq : M.E = N.E) (i : Bool) : P.copy' h_eq i = P i := rfl

protected def dual (P : M.Separation) : M✶.Separation := P.copy' rfl

protected def ofDual (P : M✶.Separation) : M.Separation := P.copy' rfl

@[simp, simp↓]
protected lemma dual_apply (P : M.Separation) (i : Bool) : P.dual i = P i := rfl

@[simp, simp↓]
protected lemma ofDual_apply (P : M✶.Separation) (i : Bool) : P.ofDual i = P i := rfl

@[simp] lemma dual_ofDual (P : M.Separation) : P.dual.ofDual = P := rfl

@[simp] lemma ofDual_dual (P : M✶.Separation) : P.ofDual.dual = P := rfl

@[simps] def dualEquiv (M : Matroid α) : M.Separation ≃ M✶.Separation where
  toFun := Separation.dual
  invFun := Separation.ofDual
  left_inv P := by simp
  right_inv P := by simp

/-- A partition is trivial if one side is empty. -/
protected def Trivial (P : M.Separation) : Prop := Bipartition.Trivial P

protected lemma trivial_of_eq_empty (h : P i = ∅) : P.Trivial := Bipartition.trivial_of_eq_empty h
protected lemma trivial_of_eq_ground (h : P i = M.E) : P.Trivial := Bipartition.trivial_of_eq h
protected lemma trivial_def : P.Trivial ↔ P true = ∅ ∨ P false = ∅ := Bipartition.trivial_def
protected lemma not_trivial_iff : ¬ P.Trivial ↔ ∀ i, (P i).Nonempty := Bipartition.not_trivial_iff
protected lemma trivial_def' : P.Trivial ↔ P true = M.E ∨ P false = M.E := Bipartition.trivial_def'
lemma Trivial.exists_eq_ground (h : P.Trivial) : ∃ i, P i = M.E := Bipartition.Trivial.exists_eq h

lemma trivial_of_ground_subsingleton (P : M.Separation) (h : M.E.Subsingleton) : P.Trivial :=
  Bipartition.trivial_of_subsingleton P h

/-- The connectivity of a separation of `M`. -/
noncomputable abbrev eConn (P : M.Separation) : ℕ∞ := M.eLocalConn (P true) (P false)

@[simp]
lemma eConn_symm (P : M.Separation) : P.symm.eConn = P.eConn :=
  M.eLocalConn_comm ..

@[simp]
lemma eConn_copy {M' : Matroid α} (P : M.Separation) (h_eq : M = M') :
    (P.copy h_eq).eConn = P.eConn := by
  simp [eConn, h_eq]

@[simp]
lemma eConn_eq (P : M.Separation) (i : Bool) : M.eConn (P i) = P.eConn := by
  rw [Separation.eConn, eConn_eq_eLocalConn, Separation.compl_eq]
  cases i
  <;> simp [eLocalConn_comm]

lemma eConn_eq_eLocalConn_true_false (P : M.Separation) :
  P.eConn = M.eLocalConn (P true) (P false) := rfl

lemma eConn_eq_eLocalConn (P : M.Separation) (i : Bool) :
    P.eConn = M.eLocalConn (P i) (P !i) := by
  obtain rfl | rfl := i
  · rw [eLocalConn_comm]
    rfl
  rfl

lemma eConn_eq_eLocalConn_of_isRestriction (P : N.Separation) (hNM : N ≤r M) (i : Bool) :
    P.eConn = M.eLocalConn (P i) (P !i) := by
  rw [eConn_eq_eLocalConn _ i, hNM.eLocalConn_eq_of_subset]

@[simp]
lemma eConn_dual (P : M.Separation) : P.dual.eConn = P.eConn := by
  rw [← P.dual.eConn_eq true, M.eConn_dual, P.dual_apply, P.eConn_eq]

@[simp]
lemma eConn_ofDual (P : M✶.Separation) : P.ofDual.eConn = P.eConn := by
  rw [← P.dual_ofDual, ← eConn_dual]
  simp

lemma Trivial.eConn (h : P.Trivial) : P.eConn = 0 := by
  obtain ⟨i, hb⟩ := h
  simp [← P.eConn_eq i, hb]

@[simp]
protected lemma not_indep_iff : ¬ M.Indep (P i) ↔ M.Dep (P i) := by
  rw [not_indep_iff]

@[simp]
protected lemma not_dep_iff : ¬ M.Dep (P i) ↔ M.Indep (P i) := by
  rw [not_dep_iff]

@[simp]
protected lemma not_coindep_iff : ¬ M.Coindep (P i) ↔ M.Codep (P i) := by
  rw [not_coindep_iff]

@[simp]
protected lemma not_codep_iff : ¬ M.Codep (P i) ↔ M.Coindep (P i) := by
  rw [← not_coindep_iff, not_not]

@[simp]
protected lemma not_indep_dual_iff : ¬ M✶.Indep (P i) ↔ M.Codep (P i) := by
  rw [not_coindep_iff]

@[simp]
protected lemma not_spanning_iff : ¬ M.Spanning (P i) ↔ M.Nonspanning (P i) := by
  rw [not_spanning_iff]

@[simp]
protected lemma not_nonspanning_iff : ¬ M.Nonspanning (P i) ↔ M.Spanning (P i) := by
  rw [not_nonspanning_iff]

lemma coindep_not_iff : M.Coindep (P !i) ↔ M.Spanning (P i) := by
  rw [← P.compl_eq, spanning_iff_compl_coindep]

lemma codep_not_iff : M.Codep (P !i) ↔ M.Nonspanning (P i) := by
  rw [← not_coindep_iff, coindep_not_iff, not_spanning_iff]

lemma nonspanning_not_iff : M.Nonspanning (P !i) ↔ M.Codep (P i) := by
  rw [← codep_not_iff, Bool.not_not]

lemma spanning_not_iff : M.Spanning (P !i) ↔ M.Coindep (P i) := by
  rw [← not_nonspanning_iff, nonspanning_not_iff, not_codep_iff]

lemma isCocircuit_not_iff : M.IsCocircuit (P !i) ↔ M.IsHyperplane (P i) := by
  rw [← isHyperplane_compl_iff_isCocircuit, P.compl_not_eq]

lemma isHyperplane_not_iff : M.IsHyperplane (P !i) ↔ M.IsCocircuit (P i) := by
  rw [← isCocircuit_not_iff, Bool.not_not]

protected lemma spanning_dual_iff : M✶.Spanning (P i) ↔ M.Indep (P !i) := by
  simp [spanning_dual_iff]

protected lemma nonspanning_dual_iff : M✶.Nonspanning (P i) ↔ M.Dep (P !i) := by
  rw [← not_spanning_iff, spanning_dual_iff, not_indep_iff, P.compl_eq]

/-- The connectivity of a partition as a natural number. Takes a value of `0` if infinite. -/
noncomputable def conn (P : M.Separation) : ℕ := M.localConn (P true) (P false)

@[simp]
lemma conn_symm (P : M.Separation) : P.symm.conn = P.conn := by
  simp [conn, localConn_comm]

@[simps!]
protected def setCompl (M : Matroid α) [OnUniv M] (X : Set α) : M.Separation :=
  Matroid.Separation.mk' X Xᶜ disjoint_compl_right (by simp)

end Separation

-- /-- Restrict a partition to a set. The junk elements go on the right. -/
-- @[simps!] protected def restrict (P : M.Separation) (R : Set α) : (M ↾ R).Separation :=
-- Separation.mk'
--   (P.left ∩ R) ((P.right ∩ R) ∪ (R \ M.E))
--   (disjoint_union_right.2 ⟨(P.disjoint.mono inter_subset_left inter_subset_left),
--       disjoint_sdiff_right.mono_left (inter_subset_left.trans P.left_subset_ground)⟩)
--   (by rw [← union_assoc, ← union_inter_distrib_right, P.union_eq, inter_comm, inter_union_diff,
--     restrict_ground_eq])

-- lemma eConn_restrict_eq (P : M.Separation) (R : Set α) :
--     (P.restrict R).eConn = M.eLocalConn (P.left ∩ R) (P.right ∩ R) := by
--   simp only [eConn, Separation.restrict, eLocalConn_restrict_eq, Separation.mk'_left,
--     Separation.mk'_right]
--   rw [union_inter_distrib_right, inter_assoc, inter_assoc, inter_self,
--     inter_eq_self_of_subset_left diff_subset, ← eLocalConn_inter_ground_right,
--     union_inter_distrib_right, disjoint_sdiff_left.inter_eq, union_empty,
--     eLocalConn_inter_ground_right]


/-- The partition of `M` given by a subset of `M.E` and its complement. The elements of the set
go on side `b`.   -/
@[simps!]
def ofSetSep (M : Matroid α) (A : Set α) (i : Bool) (hA : A ⊆ M.E := by aesop_mat) :
    M.Separation :=
  Bipartition.ofSubset hA i

@[simp]
lemma ofSetSep_apply_self (hA : A ⊆ M.E) : (M.ofSetSep A i hA) i = A :=
  Bipartition.ofSubset_apply_self hA _

@[simp]
lemma ofSetSep_apply_not (hA : A ⊆ M.E) : (M.ofSetSep A i hA !i) = M.E \ A :=
  Bipartition.ofSubset_apply_not hA _

@[simp]
lemma ofSetSep_not_apply (hA : A ⊆ M.E) : (M.ofSetSep A (!i) hA i) = M.E \ A :=
  Bipartition.ofSubset_not_apply hA _

@[simp]
lemma ofSetSep_true_false (hA : A ⊆ M.E) : (M.ofSetSep A true hA false) = M.E \ A :=
  Bipartition.ofSubset_true_false hA

@[simp]
lemma ofSetSep_false_true (hA : A ⊆ M.E) : (M.ofSetSep A false hA true) = M.E \ A :=
  Bipartition.ofSubset_false_true hA

@[simp]
lemma eConn_ofSetSep (hA : A ⊆ M.E) : (M.ofSetSep A i hA).eConn = M.eConn A := by
  rw [← Separation.eConn_eq _ i, M.ofSetSep_apply_self]

@[simp]
lemma ofSetSep_dual (hA : A ⊆ M.E) :
  M✶.ofSetSep A i hA = (M.ofSetSep A i hA).dual := rfl

namespace Separation

lemma Trivial.exists_eq (h : P.Trivial) : ∃ i, P = M.ofSetSep ∅ i := by
  obtain ⟨i, hb⟩ := h
  refine ⟨!i, Separation.ext_bool i (by simpa)⟩

/-- Intersect a partition with the ground set of a smaller matroid -/
def induce (P : M.Separation) (hN : N.E ⊆ M.E) : N.Separation := Bipartition.induce P hN

@[simp]
lemma induce_apply (P : M.Separation) (hN : N.E ⊆ M.E) (i) : P.induce hN i = (P i) ∩ N.E := rfl

@[simp]
lemma induce_symm (P : M.Separation) (hN : N.E ⊆ M.E) : (P.induce hN).symm = P.symm.induce hN :=
  Separation.ext rfl

lemma IsMinor.eConn_induce_le (P : M.Separation) (hNM : N ≤m M) :
    (P.induce hNM.subset).eConn ≤ P.eConn := by
  grw [← P.eConn_eq true, ← Separation.eConn_eq _ true, induce_apply, eConn_inter_ground,
    hNM.eConn_le]

/-- Every partition has a larger side for a given numerical notion of 'large' -/
lemma exists_larger_side {β : Type*} [ConditionallyCompleteLinearOrder β] (P : M.Separation)
    (f : Set α → β) : ∃ i, ∀ j, f (P j) ≤ f (P i) := by
  obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := fun i ↦ f (P i))
  refine ⟨j, fun i ↦ ?_⟩
  grw [hj, ← le_ciSup (by simp)]

/-- For any two partitions, one of the four cells obtained by intersecting them is the
smaller one, for a given numerical notion of 'small'. -/
lemma exists_smaller_side {β : Type*} [ConditionallyCompleteLinearOrder β] (P : M.Separation)
    (f : Set α → β) : ∃ i, ∀ j, f (P i) ≤ f (P j) :=
  exists_larger_side (β := βᵒᵈ) P f

/-- For any two partitions, one of the four cells obtained by intersecting them is the
largest one, for a given numerical notion of 'large'. -/
lemma exists_largest_inter {β : Type*} [ConditionallyCompleteLinearOrder β] (P : M.Separation)
    (Q : N.Separation) (f : Set α → β) : ∃ i i', ∀ j j', f (P j ∩ Q j') ≤ f (P i ∩ Q i') := by
  set φ := fun (p : Bool × Bool) ↦ f (P p.1 ∩ Q p.2) with hφ
  obtain ⟨⟨j, j'⟩, hj⟩ := exists_eq_ciSup_of_finite (f := φ)
  refine ⟨j, j', fun i i' ↦ ?_⟩
  simp only [φ] at hj
  grw [hj, ← hφ, ← le_ciSup (c := (i,i')) (finite_range φ).bddAbove]

/-- For any two partitions, one of the four cells obtained by intersecting them is the
smallest one, for a given numerical notion of small'. -/
lemma exists_smallest_inter {β : Type*} [ConditionallyCompleteLinearOrder β] (P : M.Separation)
    (Q : N.Separation) (f : Set α → β) : ∃ i i', ∀ j j', f (P i ∩ Q i') ≤ f (P j ∩ Q j') :=
  exists_largest_inter (β := βᵒᵈ) P Q f

section Cross

variable {Q : M.Separation}

/-- Cross two partitions by intersecting their `i`-sides and unioning their `!i`-sides-/
protected def cross (P Q : M.Separation) (i : Bool) : M.Separation := Bipartition.cross P Q i

@[simp, simp↓]
protected lemma cross_apply (P Q : M.Separation) (i j : Bool) : (P.cross Q i) j =
    bif j == i then P j ∩ Q j else P j ∪ Q j :=
  Bipartition.cross_apply ..

protected lemma cross_apply_not (P Q : M.Separation) (i : Bool) :
    (P.cross Q i) (!i) = P (!i) ∪ Q !i :=
  Bipartition.cross_apply_not ..

protected lemma cross_not_apply (P Q : M.Separation) (i : Bool) : (P.cross Q !i) i = P i ∪ Q i :=
  Bipartition.cross_not_apply ..

protected lemma cross_true_false (P Q : M.Separation) :
    (P.cross Q true) false = P false ∪ Q false :=
  Bipartition.cross_true_false ..

protected lemma cross_false_true (P Q : M.Separation) :
    (P.cross Q false) true = P true ∪ Q true :=
  Bipartition.cross_false_true ..

@[simp, simp↓]
protected lemma cross_symm (P Q : M.Separation) (i : Bool) :
    (P.cross Q i).symm = P.symm.cross Q.symm !i :=
  Bipartition.cross_symm ..

/-- Cross two partitions by intersecting the `true` sets. -/
def inter (P Q : M.Separation) : M.Separation := P.cross Q true

@[simp]
lemma inter_true (P Q : M.Separation) : (P.inter Q) true = P true ∩ Q true := rfl

@[simp]
lemma inter_false (P Q : M.Separation) : (P.inter Q) false = P false ∪ Q false := rfl

/-- Cross two partitions by intersecting the right sets. -/
def union (P Q : M.Separation) : M.Separation := (P.symm.inter Q.symm).symm

@[simp]
lemma union_true (P Q : M.Separation) : (P.union Q) true = P true ∪ Q true := rfl

@[simp]
lemma union_false (P Q : M.Separation) : (P.union Q) false = P false ∩ Q false := rfl

@[simp]
lemma inter_symm (P Q : M.Separation) : (P.inter Q).symm = P.symm.union Q.symm := by
  simp [inter, union]

@[simp]
lemma union_symm (P Q : M.Separation) : (P.union Q).symm = P.symm.inter Q.symm :=
  Separation.ext rfl

@[simp]
lemma disjoint_inter_right (P : M.Separation) : Disjoint (P true ∩ X) (P false ∩ Y) :=
  P.disjoint_true_false.mono inter_subset_left inter_subset_left

@[simp]
lemma disjoint_inter_left (P : M.Separation) : Disjoint (X ∩ P true) (Y ∩ P false) :=
  P.disjoint_true_false.mono inter_subset_right inter_subset_right

@[simp]
lemma disjoint_bool_inter_right (P : M.Separation) (i : Bool) :
    Disjoint (P i ∩ X) (P (!i) ∩ Y) :=
  (P.disjoint_bool i).mono inter_subset_left inter_subset_left

@[simp]
lemma disjoint_bool_inter_left (P : M.Separation) (i : Bool) :
    Disjoint (X ∩ P i) (Y ∩ P (!i)) :=
  (P.disjoint_bool i).mono inter_subset_right inter_subset_right

@[simp]
lemma disjoint_bool_inter_right' (P : M.Separation) (i : Bool) :
    Disjoint (P (!i) ∩ X) (P i ∩ Y) :=
  (P.disjoint_bool i).symm.mono inter_subset_left inter_subset_left

@[simp]
lemma disjoint_bool_inter_left' (P : M.Separation) (i : Bool) :
    Disjoint (X ∩ P (!i)) (Y ∩ P i) :=
  (P.disjoint_bool i).symm.mono inter_subset_right inter_subset_right

@[simp]
lemma inter_ground_eq (P : M.Separation) (i) : P i ∩ M.E = P i :=
  inter_eq_self_of_subset_left P.subset_ground

lemma union_inter_right' (P : M.Separation) (X : Set α) (i : Bool) :
    (P i ∩ X) ∪ (P (!i) ∩ X) = X ∩ M.E := by
  rw [← union_inter_distrib_right, P.union_bool_eq, inter_comm]

lemma union_inter_left' (P : M.Separation) (X : Set α) (i : Bool) :
    (X ∩ (P i)) ∪ (X ∩ (P !i)) = X ∩ M.E := by
  rw [← inter_union_distrib_left, P.union_bool_eq, inter_comm]

@[simp]
lemma union_inter_right (P : M.Separation) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) (i : Bool) :
    (P i ∩ X) ∪ ((P !i) ∩ X) = X := by
  rw [union_inter_right', inter_eq_self_of_subset_left hX]

@[simp]
lemma union_inter_left (P : M.Separation) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) (i : Bool):
    (X ∩ (P i)) ∪ (X ∩ (P !i)) = X := by
  rw [union_inter_left', inter_eq_self_of_subset_left hX]

protected lemma eConn_inter_add_eConn_union_le (P Q : M.Separation) :
    (P.inter Q).eConn + (P.union Q).eConn ≤ P.eConn + Q.eConn := by
  simp_rw [← Separation.eConn_eq _ true, union_true, inter_true]
  exact M.eConn_inter_add_eConn_union_le ..

end Cross

section Minor

variable {C D : Set α} {e f : α}

@[simp, aesop unsafe 10% (rule_sets := [Matroid])]
lemma subset_ground_of_delete (P : (M ＼ D).Separation) (i : Bool) : P i ⊆ M.E :=
  P.subset_ground.trans diff_subset

@[simp, aesop unsafe 10% (rule_sets := [Matroid])]
lemma left_subset_ground_of_contract (P : (M ／ C).Separation) (i : Bool) : P i ⊆ M.E :=
  P.subset_ground.trans diff_subset

/-- Contract the elements of `C` to take a partition of `M` to a partition of `M ／ C`. -/
def contract (P : M.Separation) (C : Set α) : (M ／ C).Separation := P.induce diff_subset

@[simp, simp↓]
lemma contract_apply (P : M.Separation) (C : Set α) : (P.contract C) i = P i \ C := by
  simp only [contract, induce_apply, contract_ground]
  rw [← inter_diff_assoc, inter_eq_self_of_subset_left P.subset_ground]

@[simp, simp↓]
lemma contract_symm (P : M.Separation) (C : Set α) : (P.contract C).symm = P.symm.contract C := by
  simp [contract]

lemma contract_contract (P : M.Separation) (C₁ C₂ : Set α) :
    (P.contract C₁).contract C₂ = (P.contract (C₁ ∪ C₂)).copy (by simp) := by
  apply Separation.ext; simp [diff_diff]

lemma contract_congr (P : M.Separation) {C₁ C₂ : Set α} (h : C₁ ∩ M.E = C₂ ∩ M.E) :
    P.contract C₁ = (P.contract C₂).copy
      (by rw [← contract_inter_ground_eq, ← h, contract_inter_ground_eq]) := by
  have h1 := P.subset_ground (i := true)
  refine Separation.ext ?_;
  simp only [contract_apply, copy_apply]
  tauto_set

lemma contract_inter_ground (P : M.Separation) (C : Set α) :
    (P.contract (C ∩ M.E)) = (P.contract C).copy (by simp) :=
  P.contract_congr <| by simp [inter_assoc]

/-- Delete the elements of `D` to take a partition of `M` to a partition of `M ＼ D`. -/
def delete (P : M.Separation) (D : Set α) : (M ＼ D).Separation := P.induce diff_subset

@[simp, simp↓]
lemma delete_apply (P : M.Separation) (D : Set α) (i : Bool) : (P.delete D) i = P i \ D := by
  simp only [delete, induce_apply, delete_ground]
  rw [← inter_diff_assoc, inter_eq_self_of_subset_left P.subset_ground]

@[simp, simp↓]
lemma delete_symm (P : M.Separation) (D : Set α) : (P.delete D).symm = P.symm.delete D := by
  simp [delete]

lemma delete_delete (P : M.Separation) (D₁ D₂ : Set α) :
    (P.delete D₁).delete D₂ = (P.delete (D₁ ∪ D₂)).copy (by simp) := by
  apply Separation.ext; simp [diff_diff]

@[simp]
lemma contract_dual (P : M.Separation) (C : Set α) :
    (P.contract C).dual = (P.dual.delete C).copy (by simp) :=
  Separation.ext rfl

lemma dual_contract (P : M.Separation) (C : Set α) :
    P.dual.contract C = (P.delete C).dual.copy (by simp) :=
  Separation.ext rfl

@[simp]
lemma delete_dual (P : M.Separation) (D : Set α) :
    (P.delete D).dual = (P.dual.contract D).copy (by simp) :=
  Separation.ext rfl

lemma dual_delete (P : M.Separation) (D : Set α) :
    (P.delete D).dual = (P.dual.contract D).copy (by simp) :=
  Separation.ext rfl

lemma delete_congr (P : M.Separation) {D₁ D₂ : Set α} (h : D₁ ∩ M.E = D₂ ∩ M.E) :
    P.delete D₁ = (P.delete D₂).copy
      (by rw [← delete_inter_ground_eq, ← h, delete_inter_ground_eq]) := by
  have h2 := P.subset_ground (i := true)
  refine Separation.ext ?_
  simp only [delete_apply, copy_apply]
  tauto_set

lemma delete_inter_ground (P : M.Separation) (D : Set α) :
    (P.delete (D ∩ M.E)) = (P.delete D).copy (by rw [delete_inter_ground_eq]) :=
  P.delete_congr <| by simp [inter_assoc]

@[simp]
lemma disjoint_contract (P : (M ／ C).Separation) (i : Bool) : Disjoint (P i) C := by
  grw [P.subset_ground]
  exact disjoint_sdiff_left

@[simp]
lemma disjoint_delete (P : (M ＼ D).Separation) (i : Bool) : Disjoint (P i) D := by
  grw [P.subset_ground]
  exact disjoint_sdiff_left

@[simps!]
abbrev contractDual (P : (M ／ C).Separation) : (M✶ ＼ C).Separation := P.dual.copy (by simp)

@[simps!]
abbrev deleteDual (P : (M ＼ D).Separation) : (M✶ ／ D).Separation := P.dual.copy (by simp)

/-- Extend a partition `P` of some matroid `N` to a matroid `M` with larger ground set by
adding the extra elements to side `b` of `P`. `-/
def ofGroundSubset (P : N.Separation) (hNM : N.E ⊆ M.E) (i : Bool) : M.Separation :=
  Bipartition.expand P hNM i

@[simp, simp↓]
lemma ofGroundSubset_apply (P : N.Separation) (hNM : N.E ⊆ M.E) (i j : Bool) :
    P.ofGroundSubset hNM j i = bif (i == j) then P i ∪ (M.E \ N.E) else P i := by
  simp [ofGroundSubset, Bipartition.expand_apply ..]

lemma ofGroundSubset_symm (P : N.Separation) (hNM : N.E ⊆ M.E) (i : Bool) :
    (P.ofGroundSubset hNM i).symm = P.symm.ofGroundSubset hNM (!i) :=
  Separation.ext <| by simp [ofGroundSubset_apply]

lemma ofSubset_apply_self (P : N.Separation) (hNM : N.E ⊆ M.E) (i : Bool) :
    P.ofGroundSubset hNM i i = P i ∪ (M.E \ N.E) := by
  simp

lemma ofSubset_apply_not (P : N.Separation) (hNM : N.E ⊆ M.E) (i : Bool) :
    P.ofGroundSubset hNM i (!i) = P (!i) := by
  simp

@[simp]
lemma ofSubset_not_apply (P : N.Separation) (hNM : N.E ⊆ M.E) (i : Bool) :
    P.ofGroundSubset hNM (!i) i = P i := by
  simp

@[simp, simp↓]
lemma ofGroundSubset_copy {N' : Matroid α} (P : N.Separation) (hN' : N = N') (hN'M : N'.E ⊆ M.E)
    (i : Bool) : (P.copy hN').ofGroundSubset hN'M i = P.ofGroundSubset (hN' ▸ hN'M) i :=
  Separation.ext_bool (i := !i) <| by simp

/-- Extend a partition of `M ／ C` to one of `M` by extending using side `b`. -/
def ofContract (P : (M ／ C).Separation) (i : Bool) : M.Separation := P.ofGroundSubset diff_subset i

@[simp, simp↓]
lemma ofContract_apply (P : (M ／ C).Separation) (hC : C ⊆ M.E := by aesop_mat) (i j : Bool) :
    P.ofContract i j = bif j == i then P j ∪ C else P j := by
  simp [ofContract, inter_eq_self_of_subset_right hC]

lemma ofContract_apply_self (P : (M ／ C).Separation) (hC : C ⊆ M.E := by aesop_mat) (i : Bool) :
    P.ofContract i i = P i ∪ C := by
  simp [P.ofContract_apply]

@[simp]
lemma ofContract_apply_not (P : (M ／ C).Separation) (i : Bool) : P.ofContract i (!i) = P !i := by
  simp [ofContract]

@[simp]
lemma ofContract_not_apply (P : (M ／ C).Separation) (i : Bool) : P.ofContract (!i) i = P i := by
  simpa using P.ofContract_apply_not (!i)

lemma ofContract_true_false (P : (M ／ C).Separation) : P.ofContract true false = P false :=
  P.ofContract_apply_not true

lemma ofContract_false_true (P : (M ／ C).Separation) : P.ofContract false true = P true :=
  P.ofContract_apply_not false

@[simp, simp↓]
lemma ofContract_symm (P : (M ／ C).Separation) (i : Bool) :
    (P.ofContract i).symm = P.symm.ofContract (!i) :=
  ofGroundSubset_symm ..

@[simp, simp↓]
lemma ofContract_copy {C' : Set α} (P : (M ／ C).Separation) (h_eq : M ／ C = M ／ C') (i : Bool) :
    (P.copy h_eq).ofContract i = P.ofContract i :=
  Separation.ext_bool (i := !i) <| by
    simp

/-- Extend a partition of `M ＼ D` to a partition of `M` by adding `D` to the left side. -/
def ofDelete (P : (M ＼ D).Separation) (i : Bool) : M.Separation := P.ofGroundSubset diff_subset i

lemma ofDelete_apply (P : (M ＼ D).Separation) (hD : D ⊆ M.E := by aesop_mat) (i j : Bool) :
    P.ofDelete i j = bif j == i then P j ∪ D else P j := by
  simp [ofDelete, inter_eq_self_of_subset_right hD]

@[simp]
lemma ofDelete_apply_self (P : (M ＼ D).Separation) (hD : D ⊆ M.E := by aesop_mat) (i : Bool) :
    P.ofDelete i i = P i ∪ D := by
  simp [P.ofDelete_apply]

@[simp]
lemma ofDelete_apply_not (P : (M ＼ D).Separation) (i : Bool) : P.ofDelete i (!i) = P !i := by
  simp [ofDelete]

@[simp]
lemma ofDelete_not_apply (P : (M ＼ D).Separation) (i : Bool) : P.ofDelete (!i) i = P i := by
  simp [ofDelete]

@[simp]
lemma ofDelete_copy {D' : Set α} (P : (M ＼ D).Separation) (h_eq : M ＼ D = M ＼ D') (i : Bool) :
    (P.copy h_eq).ofDelete i = P.ofDelete i :=
  Separation.ext_bool (i := !i) <| by simp

@[simp]
lemma ofDelete_symm (P : (M ＼ D).Separation) (i : Bool):
    (P.ofDelete i).symm = P.symm.ofDelete !i :=
  ofGroundSubset_symm ..

@[simp]
lemma ofDelete_dual (P : (M ＼ D).Separation) (i : Bool) :
    (P.ofDelete i).dual = P.deleteDual.ofContract i := rfl

@[simp]
lemma ofContract_dual (P : (M ／ C).Separation) (i : Bool) :
    (P.ofContract i).dual = P.contractDual.ofDelete i := rfl

@[simp]
lemma ofContract_contract (P : (M ／ C).Separation) (i : Bool) :
    (P.ofContract i).contract C = P :=
  Separation.ext_bool (!i) <| by simp

@[simp]
lemma ofDelete_delete (P : (M ＼ D).Separation) : (P.ofDelete i).delete D = P :=
  Separation.ext_bool (!i) <| by simp

lemma contract_ofContract (P : M.Separation) (hC : C ⊆ P i) : (P.contract C).ofContract i = P :=
  Separation.ext_bool (!i) <| by simp [(P.disjoint_bool i).symm.mono_right hC]

lemma delete_ofDelete (P : M.Separation) (hD : D ⊆ P i) : (P.delete D).ofDelete i = P :=
  Separation.ext_bool (!i) <| by simp [(P.disjoint_bool i).symm.mono_right hD]

lemma compl_delete (P : (M ＼ D).Separation) (hD : D ⊆ M.E := by aesop_mat) (i : Bool) :
    M.E \ P i = P (!i) ∪ D := by
  grw [← P.compl_eq, delete_ground, diff_diff_comm, diff_union_self, eq_comm, union_eq_left,
    subset_diff, and_iff_right hD, P.subset_ground]
  exact disjoint_sdiff_right

lemma compl_delete_not (P : (M ＼ D).Separation) (hD : D ⊆ M.E := by aesop_mat) (i : Bool) :
    M.E \ (P !i) = P i ∪ D := by
  simpa using P.compl_delete hD !i

lemma compl_contract (P : (M ／ C).Separation) (hC : C ⊆ M.E := by aesop_mat) (i : Bool) :
    M.E \ (P i) = P (!i) ∪ C :=  by
  simpa using (P.dual.copy (M.dual_contract C)).compl_delete hC i

lemma compl_contract_not (P : (M ／ C).Separation) (hC : C ⊆ M.E := by aesop_mat) (i : Bool) :
    M.E \ (P !i) = P i ∪ C := by
  simpa using P.compl_contract hC !i

@[simp]
lemma compl_union_contract (P : (M ／ C).Separation) (i : Bool) : M.E \ (P i ∪ C) = P !i := by
  rw [← P.compl_eq, union_comm, contract_ground, diff_diff]

@[simp]
lemma compl_union_delete (P : (M ＼ D).Separation) (i : Bool) : M.E \ (P i ∪ D) = P !i := by
  rw [← P.compl_eq, union_comm, delete_ground, diff_diff]

lemma compl_delete_singleton (P : (M ＼ {e}).Separation) (he : e ∈ M.E := by aesop_mat) (i : Bool) :
    M.E \ (P i) = insert e (P (!i)) := by
  rw [compl_delete, union_singleton]

lemma compl_contract_singleton (P : (M ／ {e}).Separation) (he : e ∈ M.E := by aesop_mat)
    (i : Bool) : M.E \ (P i) = insert e (P !i) := by
  rw [compl_contract, union_singleton]

lemma eConn_ofContract (P : (M ／ C).Separation) (i : Bool) :
    (P.ofContract i).eConn = P.eConn + M.eLocalConn (P !i) C := by
  wlog hCE : C ⊆ M.E generalizing C P with aux
  · simpa using aux (C := C ∩ M.E) (P.copy (by simp)) inter_subset_right
  rw [← (P.ofContract i).eConn_eq i, ofContract_apply_self,
    eConn_union_eq_eConn_contract_add _ (by simp), P.compl_union_contract, P.eConn_eq i]

lemma eConn_ofDelete (P : (M ＼ D).Separation) (i : Bool) :
    (P.ofDelete i).eConn = P.eConn + M✶.eLocalConn (P !i) D := by
  rw [← eConn_dual, ofDelete_dual, eConn_ofContract]
  simp

lemma eConn_induce_le_of_isMinor (P : M.Separation) (hNM : N ≤m M) :
    (P.induce hNM.subset).eConn ≤ P.eConn := by
  rw [← eConn_eq _ true, induce_apply, ← eConn_eq _ true, eConn_inter_ground]
  exact hNM.eConn_le _

lemma eConn_contract_le (P : M.Separation) (C : Set α) : (P.contract C).eConn ≤ P.eConn :=
  eConn_induce_le_of_isMinor P <| contract_isMinor ..

lemma eConn_delete_le (P : M.Separation) (D : Set α) : (P.delete D).eConn ≤ P.eConn :=
  eConn_induce_le_of_isMinor P <| delete_isMinor ..

lemma eConn_eq_eConn_contract_add (P : M.Separation) (hC : C ⊆ P i) :
    P.eConn = (P.contract C).eConn + M.eLocalConn (P !i) C := by
  rw [← P.contract_ofContract hC, eConn_ofContract]
  rw [contract_apply, ofContract_contract, contract_ofContract _ hC, sdiff_eq_left.2]
  exact (P.disjoint_bool i).symm.mono_right hC

lemma eConn_le_eConn_contract_add (P : M.Separation) (C : Set α) :
    P.eConn ≤ (P.contract C).eConn + M.eRk C := by
  grw [P.eConn_eq_eConn_contract_add (C := C ∩ (P true)) inter_subset_right,
    eConn_eq_eConn_contract_add (C := C ∩ (P false)) (i := false), eLocalConn_le_eRk_right,
    eLocalConn_le_eRk_right, add_assoc, ← eRelRk_eq_eRk_contract, eRelRk_add_eRk_eq,
    ← inter_union_distrib_left, P.union_eq', eRk_inter_ground, contract_contract,
    P.contract_congr (by rw [← inter_union_distrib_left, P.union_eq]),
    P.contract_congr (C₂ := C) (by simp [inter_assoc])]
  · simp
  rw [P.contract_apply, ← P.compl_false]
  tauto_set

lemma eConn_le_eConn_delete_add (P : M.Separation) (D : Set α) :
    P.eConn ≤ (P.delete D).eConn + M✶.eRk D := by
  grw [← eConn_dual, eConn_le_eConn_contract_add _ D, dual_contract, eConn_copy, eConn_dual]

lemma eConn_ofContract_singleton_le_eConn_add_one (P : (M ／ {e}).Separation) (i : Bool) :
    (P.ofContract i).eConn ≤ P.eConn + 1 := by
  grw [eConn_ofContract, eLocalConn_le_eRk_right, eRk_singleton_le]

lemma eConn_ofDelete_singleton_le_eConn_add_one (P : (M ＼ {e}).Separation) (i : Bool) :
    (P.ofDelete i).eConn ≤ P.eConn + 1 := by
  grw [eConn_ofDelete, eLocalConn_le_eRk_right, eRk_singleton_le]

lemma eConn_eq_of_subset_closure_of_isRestriction {N : Matroid α} {Q : N.Separation}
    {P : M.Separation} (hNM : N ≤r M) (forall_subset : ∀ i, Q i ⊆ P i)
    (forall_subset_closure : ∀ i, P i ⊆ M.closure (Q i)) : P.eConn = Q.eConn := by
  rw [Separation.eConn, Separation.eConn,
    hNM.eLocalConn_eq_of_subset Q.subset_ground Q.subset_ground]
  refine le_antisymm ?_ <| M.eLocalConn_mono (forall_subset true) (forall_subset false)
  grw [← eLocalConn_closure_closure (X := Q _),
  M.eLocalConn_mono (forall_subset_closure true) (forall_subset_closure false)]

end Minor

lemma eConn_eq_zero_iff_skew {P : M.Separation} {i : Bool} : P.eConn = 0 ↔ M.Skew (P i) (P !i) := by
  rw [← M.eLocalConn_eq_zero P.subset_ground P.subset_ground, Separation.eConn]
  cases i
  · rw [eLocalConn_comm]
    rfl
  rfl

lemma eConn_eq_zero_iff_eq_disjointSum {P : M.Separation} {i : Bool} :
    P.eConn = 0 ↔ M = (M ↾ (P i)).disjointSum (M ↾ (P !i)) (P.disjoint_bool i) := by
  rw [eConn_eq_zero_iff_skew, skew_iff_restrict_union_eq P.subset_ground P.subset_ground
    (P.disjoint_bool i), P.union_bool_eq, restrict_ground_eq_self]

lemma exists_partition_of_not_connected [M.Nonempty] (h : ¬ M.Connected) :
    ∃ P : M.Separation, P.eConn = 0 ∧ ¬ P.Trivial := by
  obtain ⟨M₁, M₂, hdj, hM₁, hM₂, rfl⟩ := eq_disjointSum_of_not_connected h
  refine ⟨ofSetSep _ M₁.E true (by simp), ?_⟩
  simp [Separation.trivial_def, hdj.symm.sdiff_eq_left, hM₁.ground_nonempty.ne_empty,
    hM₂.ground_nonempty.ne_empty]

lemma exists_partition_iff_not_connected [M.Nonempty] :
    ¬ M.Connected ↔ ∃ P : M.Separation, P.eConn = 0 ∧ ¬ P.Trivial := by
  refine ⟨exists_partition_of_not_connected, fun ⟨P, hP, hPnt⟩ ↦ ?_⟩
  rw [eConn_eq_zero_iff_eq_disjointSum (i := true)] at hP
  rw [hP]
  simp only [P.trivial_def, not_or, ← nonempty_iff_ne_empty] at hPnt
  apply disjointSum_not_connected
  · rw [← ground_nonempty_iff]
    exact hPnt.1
  rw [← ground_nonempty_iff]
  exact hPnt.2

/-- The generalized Bixby-Coullard inequality for pairs of separations. -/
lemma eConn_inter_add_eConn_inter_le (P : (M ／ X).Separation) (Q : (M ＼ X).Separation) (i : Bool) :
    M.eConn (P i ∩ Q i) + M.eConn (P (!i) ∩ Q (!i)) ≤ P.eConn + Q.eConn + M.eConn X := by
  wlog hX : X ⊆ M.E generalizing X P Q with aux
  · simpa using aux (X := X ∩ M.E) (P.copy (by simp)) (Q.copy (by simp)) inter_subset_right
  convert M.eConn_inter_add_eConn_union_union_le (C := P i) (D := Q i) (X := X) (by simp) (by simp)
    using 2
  · rw [union_assoc, union_comm X, union_union_distrib_right, ← Q.compl_contract_not,
      ← P.compl_delete_not, dual_ground, ← diff_inter, eConn_compl]
  simp

/-- The Bixby-Coullard inequality for pairs of separations. -/
lemma eConn_inter_add_eConn_inter_le_of_singleton
    (P : (M ／ {e}).Separation) (Q : (M ＼ {e}).Separation) (i : Bool) :
    M.eConn (P i ∩ Q i) + M.eConn (P (!i) ∩ Q (!i)) ≤ P.eConn + Q.eConn + 1 := by
  grw [P.eConn_inter_add_eConn_inter_le, eConn_le_encard, encard_singleton]

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
  · simp [← union_inter_distrib_right, ← preimage_union, subset_def]
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
  grw [← singleton_subset_iff.2 hi]
  exact hef.mem_closure

end Separation
