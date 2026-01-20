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

lemma apply_eq_iff : P i = M.E ↔ P (!i) = ∅ := by
  rw [← P.compl_eq, diff_eq_empty, subset_antisymm_iff, and_iff_right P.subset]

/-- Transfer a separation across a matroid equality. -/
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

lemma dual_dual (P : M.Separation) : P.dual.dual = P.copy M.dual_dual.symm := rfl

@[simps] def dualEquiv (M : Matroid α) : M.Separation ≃ M✶.Separation where
  toFun := Separation.dual
  invFun := Separation.ofDual
  left_inv P := by simp
  right_inv P := by simp

/-- A separation is trivial if one side is empty. -/
protected def Trivial (P : M.Separation) : Prop := Bipartition.Trivial P

protected lemma trivial_of_eq_empty (h : P i = ∅) : P.Trivial := Bipartition.trivial_of_eq_empty h
protected lemma trivial_of_eq_ground (h : P i = M.E) : P.Trivial := Bipartition.trivial_of_eq h
protected lemma trivial_def : P.Trivial ↔ P false = ∅ ∨ P true = ∅ := Bipartition.trivial_def
protected lemma trivial_def' : P.Trivial ↔ P false = M.E ∨ P true = M.E := Bipartition.trivial_def'
lemma Trivial.exists_eq_ground (h : P.Trivial) : ∃ i, P i = M.E := Bipartition.Trivial.exists_eq h

lemma trivial_of_ground_subsingleton (P : M.Separation) (h : M.E.Subsingleton) : P.Trivial :=
  Bipartition.trivial_of_subsingleton P h

@[simp]
lemma trivial_copy_iff {M' : Matroid α} (h : M = M') (P : M.Separation) :
    (P.copy h).Trivial ↔ P.Trivial := by
  simp [Separation.trivial_def]

/-- A separation is nontrivial if both sides are nonempty -/
protected def Nontrivial (P : M.Separation) : Prop := Bipartition.Nontrivial P

lemma Nontrivial.nonempty (h : P.Nontrivial) (i : Bool) : (P i).Nonempty := h i

protected lemma nontrivial_def : P.Nontrivial ↔ (P false).Nonempty ∧ (P true).Nonempty :=
  Bipartition.nontrivial_def

protected lemma nontrivial_iff_forall : P.Nontrivial ↔ ∀ i, (P i).Nonempty := Iff.rfl

protected lemma nontrivial_iff_bool (i : Bool) :
    P.Nontrivial ↔ (P i).Nonempty ∧ (P !i).Nonempty := by
  rw [P.nontrivial_def]
  cases i <;> grind

@[simp]
protected lemma not_trivial_iff : ¬ P.Trivial ↔ P.Nontrivial := Bipartition.not_trivial_iff

@[simp]
protected lemma not_nontrivial_iff : ¬ P.Nontrivial ↔ P.Trivial := Bipartition.not_nontrivial_iff

protected lemma Nontrivial.not_trivial (h : P.Nontrivial) : ¬ P.Trivial := by simpa

protected lemma Trivial.not_nontrivial (h : P.Trivial) : ¬ P.Nontrivial := by simpa

protected lemma trivial_or_nontrivial (P : M.Separation) : P.Trivial ∨ P.Nontrivial := by
  simp [or_iff_not_imp_left]

lemma Nontrivial.ssubset_ground (h : P.Nontrivial) {i : Bool} : P i ⊂ M.E :=
  Bipartition.Nontrivial.ssubset h

@[simp]
lemma nontrivial_copy_iff {M' : Matroid α} (h : M = M') (P : M.Separation) :
    (P.copy h).Nontrivial ↔ P.Nontrivial := by
  simp [Separation.nontrivial_def]

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

/-- The connectivity of a separation as a natural number. Takes a value of `0` if infinite. -/
noncomputable def conn (P : M.Separation) : ℕ := M.localConn (P true) (P false)

@[simp]
lemma conn_symm (P : M.Separation) : P.symm.conn = P.conn := by
  simp [conn, localConn_comm]

@[simps!]
protected def setCompl (M : Matroid α) [OnUniv M] (X : Set α) : M.Separation :=
  Matroid.Separation.mk' X Xᶜ disjoint_compl_right (by simp)

end Separation

-- /-- Restrict a separation to a set. The junk elements go on the right. -/
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


/-- The separation of `M` given by a subset of `M.E` and its complement. The elements of the set
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

/-- Intersect a separation with the ground set of a smaller matroid -/
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

/-- Every separation has a larger side for a given numerical notion of 'large' -/
lemma exists_larger_side {β : Type*} [ConditionallyCompleteLinearOrder β] (P : M.Separation)
    (f : Set α → β) : ∃ i, ∀ j, f (P j) ≤ f (P i) := by
  obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := fun i ↦ f (P i))
  refine ⟨j, fun i ↦ ?_⟩
  grw [hj, ← le_ciSup (by simp)]

/-- For any two separations, one of the four cells obtained by intersecting them is the
smaller one, for a given numerical notion of 'small'. -/
lemma exists_smaller_side {β : Type*} [ConditionallyCompleteLinearOrder β] (P : M.Separation)
    (f : Set α → β) : ∃ i, ∀ j, f (P i) ≤ f (P j) :=
  exists_larger_side (β := βᵒᵈ) P f

/-- For any two separations, one of the four cells obtained by intersecting them is the
largest one, for a given numerical notion of 'large'. -/
lemma exists_largest_inter {β : Type*} [ConditionallyCompleteLinearOrder β] (P : M.Separation)
    (Q : N.Separation) (f : Set α → β) : ∃ i i', ∀ j j', f (P j ∩ Q j') ≤ f (P i ∩ Q i') := by
  set φ := fun (p : Bool × Bool) ↦ f (P p.1 ∩ Q p.2) with hφ
  obtain ⟨⟨j, j'⟩, hj⟩ := exists_eq_ciSup_of_finite (f := φ)
  refine ⟨j, j', fun i i' ↦ ?_⟩
  simp only [φ] at hj
  grw [hj, ← hφ, ← le_ciSup (c := (i,i')) (finite_range φ).bddAbove]

/-- For any two separations, one of the four cells obtained by intersecting them is the
smallest one, for a given numerical notion of small'. -/
lemma exists_smallest_inter {β : Type*} [ConditionallyCompleteLinearOrder β] (P : M.Separation)
    (Q : N.Separation) (f : Set α → β) : ∃ i i', ∀ j j', f (P i ∩ Q i') ≤ f (P j ∩ Q j') :=
  exists_largest_inter (β := βᵒᵈ) P Q f

section Cross

variable {Q : M.Separation} {b c : Bool}

/-- The separation whose `true` side is `P b ∩ Q c` and whose `false` side is `P !b ∪ Q !c`. -/
protected def inter (P Q : M.Separation) (b c : Bool) : M.Separation := Bipartition.inter P Q b c

protected lemma inter_apply (P Q : M.Separation) :
    P.inter Q b c i = bif i then P b ∩ Q c else P (!b) ∪ Q !c := rfl
@[simp]
protected lemma inter_apply_true (P Q : M.Separation) : P.inter Q b c true = P b ∩ Q c := rfl
@[simp]
protected lemma inter_apply_false (P Q : M.Separation) : P.inter Q b c false = P (!b) ∪ Q !c := rfl

protected lemma inter_comm (P Q : M.Separation) (b c : Bool) : P.inter Q b c = Q.inter P c b :=
  Bipartition.inter_comm ..

/-- The bipartition whose `true` side is `P b ∪ Q c` and whose `false` side is `P !b ∩ Q !c`. -/
protected def union (P Q : M.Separation) (b c : Bool) : M.Separation := Bipartition.union P Q b c

protected lemma union_apply (P Q : M.Separation) :
    P.union Q b c i = bif i then P b ∪ Q c else P (!b) ∩ Q !c := Bipartition.union_apply ..

@[simp]
protected lemma union_apply_true (P Q : M.Separation) : P.union Q b c true = P b ∪ Q c :=
  Bipartition.union_apply_true ..

@[simp]
protected lemma union_apply_false (P Q : M.Separation) : P.union Q b c false = P (!b) ∩ Q !c := rfl

lemma inter_symm (P Q : M.Separation) (b c : Bool) : (P.inter Q b c).symm = P.union Q (!b) (!c) :=
  Bipartition.inter_symm ..

lemma union_symm (P Q : M.Separation) (b c : Bool) : (P.union Q b c).symm = P.inter Q (!b) (!c) :=
  Bipartition.union_symm ..

@[simp]
lemma union_not_symm (P Q : M.Separation) (b c : Bool) :
    (P.union Q (!b) (!c)).symm = P.inter Q b c := by
  simp [union_symm]

@[simp]
lemma inter_not_symm (P Q : M.Separation) (b c : Bool) :
    (P.inter Q (!b) (!c)).symm = P.union Q b c := by
  simp [inter_symm]

protected lemma union_comm (P Q : M.Separation) (b c : Bool) : P.union Q b c = Q.union P c b :=
  Bipartition.union_comm ..

lemma Nontrivial.inter_trivial_iff (hP : P.Nontrivial) (b c : Bool) :
    (P.inter Q b c).Trivial ↔ P b ⊆ Q !c ∨ Q c ⊆ P !b :=
  Bipartition.Nontrivial.inter_trivial_iff hP ..

lemma Nontrivial.union_trivial_iff (hP : P.Nontrivial) (b c : Bool) :
    (P.union Q b c).Trivial ↔ P (!b) ⊆ Q c ∨ Q (!c) ⊆ P b :=
  Bipartition.Nontrivial.union_trivial_iff hP ..

lemma inter_trivial_iff (P Q : M.Separation) (b c : Bool) :
    (P.inter Q b c).Trivial ↔ P b ⊆ Q !c ∨ Q c ⊆ P !b ∨ (P b = M.E ∧ Q c = M.E) :=
  Bipartition.inter_trivial_iff ..

lemma union_trivial_iff (P Q : M.Separation) (b c : Bool) :
    (P.union Q b c).Trivial ↔ P (!b) ⊆ Q c ∨ Q (!c) ⊆ P b ∨ (P b = ∅ ∧ Q c = ∅) :=
  Bipartition.union_trivial_iff ..

protected lemma eConn_inter_add_eConn_union_le (P Q : M.Separation) (b c : Bool) :
    (P.inter Q b c).eConn + (P.union Q b c).eConn ≤ P.eConn + Q.eConn := by
  simp_rw [← P.eConn_eq b, ← Q.eConn_eq c, ← Separation.eConn_eq _ true, P.union_apply_true,
    P.inter_apply_true]
  exact M.eConn_inter_add_eConn_union_le ..

protected lemma eConn_union_add_eConn_union_le (P Q : M.Separation) (b c : Bool) :
    (P.union Q b c).eConn + (P.union Q (!b) (!c)).eConn ≤ P.eConn + Q.eConn := by
  grw [← P.eConn_inter_add_eConn_union_le Q (!b) (!c), ← P.union_not_symm, eConn_symm,
    Bool.not_not, Bool.not_not]

protected lemma eConn_inter_add_eConn_inter_le (P Q : M.Separation) (b c : Bool) :
    (P.inter Q b c).eConn + (P.inter Q (!b) (!c)).eConn ≤ P.eConn + Q.eConn := by
  grw [← Separation.union_not_symm, ← Separation.union_not_symm, Bool.not_not, Bool.not_not,
    eConn_symm, eConn_symm, add_comm, P.eConn_union_add_eConn_union_le Q]

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
  rw [← union_inter_distrib_right, P.union_bool_eq, Set.inter_comm]

lemma union_inter_left' (P : M.Separation) (X : Set α) (i : Bool) :
    (X ∩ (P i)) ∪ (X ∩ (P !i)) = X ∩ M.E := by
  rw [← inter_union_distrib_left, P.union_bool_eq, Set.inter_comm]

@[simp]
lemma union_inter_right (P : M.Separation) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) (i : Bool) :
    (P i ∩ X) ∪ ((P !i) ∩ X) = X := by
  rw [union_inter_right', inter_eq_self_of_subset_left hX]

@[simp]
lemma union_inter_left (P : M.Separation) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) (i : Bool) :
    (X ∩ (P i)) ∪ (X ∩ (P !i)) = X := by
  rw [union_inter_left', inter_eq_self_of_subset_left hX]

lemma diff_eq_inter_bool (P : M.Separation) (i : Bool) (hX : X ⊆ M.E := by aesop_mat) :
    X \ P i = X ∩ P !i := by
  rw [← P.compl_eq]
  grind

end Cross

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

lemma _root_.Matroid.exists_separation_of_not_connected [M.Nonempty] (h : ¬ M.Connected) :
    ∃ P : M.Separation, P.eConn = 0 ∧ P.Nontrivial := by
  obtain ⟨M₁, M₂, hdj, hM₁, hM₂, rfl⟩ := eq_disjointSum_of_not_connected h
  refine ⟨ofSetSep _ M₁.E true (by simp), ?_⟩
  simp [Separation.nontrivial_def, hdj.symm.sdiff_eq_left, hM₁.ground_nonempty, hM₂.ground_nonempty]

lemma _root_.Matroid.exists_separation_iff_not_connected [M.Nonempty] :
    ¬ M.Connected ↔ ∃ P : M.Separation, P.eConn = 0 ∧ P.Nontrivial := by
  refine ⟨exists_separation_of_not_connected, fun ⟨P, hP, hPnt⟩ ↦ ?_⟩
  rw [eConn_eq_zero_iff_eq_disjointSum (i := true)] at hP
  rw [hP]
  apply disjointSum_not_connected
  · rw [← ground_nonempty_iff]
    exact hPnt.nonempty (i := true)
  rw [← ground_nonempty_iff]
  exact hPnt.nonempty (i := false)

lemma _root_.Matroid.connected_iff_forall_separation [M.Nonempty] :
    M.Connected ↔ ∀ P : M.Separation, P.eConn = 0 → P.Trivial := by
  rw [← not_iff_not, exists_separation_iff_not_connected]
  simp

lemma _root_.Matroid.Connected.trivial_of_eConn_eq_zero (h : M.Connected) (hP : P.eConn = 0) :
    P.Trivial := by
  have := h.nonempty
  exact connected_iff_forall_separation.1 h P hP

lemma Nontrivial.one_le_eConn_of_connected (hP : P.Nontrivial) (hM : M.Connected) :
    1 ≤ P.eConn := by
  contrapose! hP
  simpa using hM.trivial_of_eConn_eq_zero <| ENat.lt_one_iff_eq_zero.1 hP
