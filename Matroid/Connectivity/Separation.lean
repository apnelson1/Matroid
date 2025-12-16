import Matroid.Init
import Matroid.Connectivity.Core
import Matroid.Connectivity.Nat
import Matroid.Connectivity.Connected
import Matroid.Connectivity.Minor
import Matroid.ForMathlib.Finset
import Matroid.ForMathlib.Matroid.Sum
import Matroid.ForMathlib.Data.Set.Subsingleton
import Matroid.ForMathlib.Data.Set.IndexedPartition

open Set Function

namespace Matroid

variable {α : Type*} {M N : Matroid α} {j k : ℕ∞} {e f : α} {A B X X' Y Y' : Set α} {i j : Bool}
  {P : M.E.Bipartition}

-- @[simp]
-- protected lemma toFun_eq_coe (P : M.E.Bipartition) : P.toFun = P := rfl

-- @[simp]
-- protected lemma mk_apply (f : Bool → Set α) (dj) (hu : ⋃ i, f i = M.E) (i : Bool) :
--     Partition.mk f dj hu b = f b := rfl

-- protected lemma pairwise_disjoint (P : M.E.Bipartition) : Pairwise (Disjoint on P) :=
--   P.pairwise_disjoint'

-- protected lemma iUnion_eq (P : M.E.Bipartition) : ⋃ i, P i = M.E :=
--   P.iUnion_eq'

-- @[simp]
-- protected lemma union_eq' : P false ∪ P true = M.E := by
--   simp [← P.iUnion_eq, union_comm]

-- @[simp]
-- protected lemma union_eq : P true ∪ P false = M.E := by
--   simp [← P.iUnion_eq]

-- @[simp]
-- protected lemma union_bool_eq (i : Bool) : P i ∪ P (!i) = M.E := by
--   cases i <;> simp

-- @[simp]
-- protected lemma union_bool_eq' (i : Bool) : P (!i) ∪ P i = M.E := by
--   cases i <;> simp

-- @[simp]
-- protected lemma disjoint : Disjoint (P true) (P false) := by
--   rw [← pairwise_disjoint_on_bool]
--   convert P.pairwise_disjoint with b
--   cases i <;> rfl

-- @[simp]
-- protected lemma disjoint' : Disjoint (P false) (P true) :=
--   P.disjoint.symm

-- @[simp]
-- protected lemma disjoint_bool (i : Bool) : Disjoint (P i) (P (!i)) := by
--   cases i
--   · exact P.disjoint.symm
--   exact P.disjoint

-- @[simp]
-- protected lemma compl_eq (P : M.E.Bipartition) (i : Bool) : M.E \ (P i) = P (!i) := by
--   rw [← P.union_bool_eq b, union_diff_cancel_left (P.disjoint_bool b).inter_eq.subset]

-- protected lemma compl_not_eq (P : M.E.Bipartition) (i : Bool) : M.E \ (P (!i)) = P i := by
--   rw [P.compl_eq, Bool.not_not]

-- @[simp]
-- lemma compl_dual_eq (P : M✶.Partition) (i : Bool) : M.E \ P i = P !i := by
--   rw [← dual_ground, P.compl_eq]

-- lemma compl_dual_not_eq (P : M✶.Partition) (i : Bool) : M.E \ P (!i) = P i := by
--   rw [← dual_ground, P.compl_eq, b.not_not]

-- protected def mk' (A B : Set α) (disjoint : Disjoint A B) (union_eq : A ∪ B = M.E) :
--     M.E.Bipartition where
--   toFun b := bif b then A else B
--   pairwise_disjoint' := by rwa [pairwise_disjoint_on_bool]
--   iUnion_eq' := by simpa

-- @[simp]
-- protected lemma mk'_left {A B : Set α} {hdj} {hu : A ∪ B = M.E} :
--     Partition.mk' A B hdj hu left = A := rfl

-- @[simp]
-- protected lemma mk'_right {A B : Set α} {hdj} {hu : A ∪ B = M.E} :
--     Partition.mk' A B hdj hu right = B := rfl

-- protected lemma ext_bool {P P' : M.E.Bipartition} (h : P i = P' b) : P = P' := by
--   have h' (i) : P i = P' i := by
--     obtain rfl | rfl := b.eq_or_eq_not i
--     · assumption
--     rw [← P.compl_not_eq, h, P'.compl_not_eq]
--   cases P; cases P'; simpa [funext_iff] using h'

-- protected lemma ext {P P' : M.E.Bipartition} (h_left : P true = P' true) : P = P' :=
--   P.ext_bool h_left

-- protected lemma ext_iff {P P' : M.E.Bipartition} (i : Bool) : P = P' ↔ P i = P' b :=
--   ⟨fun h ↦ by simp [h], fun h ↦ P.ext_bool h⟩

-- @[simps]
-- protected def symm (P : M.E.Bipartition) : M.E.Bipartition where
--   toFun b := P.toFun !i
--   pairwise_disjoint' := P.pairwise_disjoint.comp_of_injective <| by trivial
--   iUnion_eq' := by
--     rw [← P.iUnion_eq]
--     simp [union_comm]

-- protected lemma symm_left (P : M.E.Bipartition) : P.symm left = P false := rfl

-- protected lemma symm_right (P : M.E.Bipartition) : P.symm right = P true := rfl

-- @[simp]
-- protected lemma symm_apply (P : M.E.Bipartition) (i : Bool) : P.symm b = P !i := rfl

-- @[simp]
-- protected lemma symm_symm (P : M.E.Bipartition) : P.symm.symm = P := Partition.ext rfl

-- protected lemma compl_true (P : M.E.Bipartition) : M.E \ (P true) = P false := by
--   rw [← P.union_eq, union_diff_left, sdiff_eq_left]
--   exact P.symm.disjoint

-- @[simp]
-- protected lemma compl_false (P : M.E.Bipartition) : M.E \ (P false) = P true := by
--   rw [← P.symm_right, ← P.symm.compl_true, P.symm_left]


--   rw [← P.iUnion_eq]
--   exact subset_iUnion ..

-- /-- Transfer a partition across a matroid equality. -/
-- protected def copy {M' : Matroid α} (P : M.E.Bipartition) (h_eq : M = M') : M'.Partition where
--   toFun := P.toFun
--   pairwise_disjoint' := P.pairwise_disjoint
--   iUnion_eq' := h_eq ▸ P.iUnion_eq

-- @[simp]
-- lemma copy_apply (P : M.E.Bipartition) (h_eq : M = N) (i : Bool) : P.copy h_eq b = P i := rfl

-- /-- A version of `copy` where the ground sets are equal, but the matroids need not be.
-- `copy` is preferred where possible, so that lemmas depending on matroid structure
-- like `eConn_copy` can be `@[simp]`. -/
-- @[simps] protected def copy' {M' : Matroid α} (P : M.E.Bipartition) (h_eq : M.E = M'.E) :
--     M'.Partition where
--   toFun := P.toFun
--   pairwise_disjoint' := P.pairwise_disjoint
--   iUnion_eq' := h_eq ▸ P.iUnion_eq

-- @[simp]
-- lemma copy'_apply (P : M.E.Bipartition) (h_eq : M.E = N.E) (i : Bool) : P.copy' h_eq b = P i :=
-- rfl

-- protected def dual (P : M.E.Bipartition) : M✶.Partition := P.copy' rfl

-- protected def ofDual (P : M✶.Partition) : M.E.Bipartition := P.copy' rfl

-- @[simp]
-- protected lemma dual_apply (P : M.E.Bipartition) (i : Bool) : P.dual b = P i := rfl

-- @[simp]
-- protected lemma ofDual_apply (P : M✶.Partition) (i : Bool) : P.ofDual b = P i := rfl

-- @[simp] lemma dual_ofDual (P : M.E.Bipartition) : P.dual.ofDual = P := rfl

-- @[simp] lemma ofDual_dual (P : M✶.Partition) : P.ofDual.dual = P := rfl

-- attribute [simp] Partition.disjoint Partition.union_eq

-- @[simps] def dualEquiv (M : Matroid α) : M.E.Bipartition ≃ M✶.Partition where
--   toFun := Partition.dual
--   invFun := Partition.ofDual
--   left_inv P := by simp
--   right_inv P := by simp

-- /-- A partition is trivial if one side is empty. -/
-- protected def Trivial (P : M.E.Bipartition) : Prop := ∃ b, P i = ∅

-- lemma trivial_of_eq_empty (h : P i = ∅) : P.Trivial := ⟨_, h⟩

-- lemma trivial_of_eq_ground (h : P i = M.E) : P.Trivial := ⟨!i, by rw [← P.compl_eq, h,
-- diff_self]⟩

-- protected lemma trivial_def : P.Trivial ↔ P true = ∅ ∨ P false = ∅ := by
--   simp [Partition.Trivial, or_comm]

-- lemma not_trivial_iff : ¬ P.Trivial ↔ ∀ b, (P i).Nonempty := by
--   simp [nonempty_iff_ne_empty, P.trivial_def, and_comm]

-- protected lemma trivial_def' : P.Trivial ↔ P true = M.E ∨ P false = M.E := by
--   rw [or_comm, ← Bool.exists_bool (p := fun i ↦ P i = M.E)]
--   exact ⟨fun ⟨b, hb⟩ ↦ ⟨!i, by rw [← P.compl_eq, hb, diff_empty]⟩,
--     fun ⟨b, hb⟩ ↦ trivial_of_eq_ground hb⟩

-- lemma Trivial.exists_eq_ground (h : P.Trivial) : ∃ b, P i = M.E := by
--   obtain ⟨b, hb⟩ := h
--   refine ⟨!i, by rw [← P.compl_eq, hb, diff_empty]⟩

-- lemma trivial_of_ground_subsingleton (P : M.E.Bipartition) (h : M.E.Subsingleton) : P.Trivial :=
--   (h.eq_or_eq_of_subset (P.subset_ground left)).elim trivial_of_eq_empty trivial_of_eq_ground


/- Simplify without definitionally altering the ground set. -/
macro "conn_simp" : tactic => `(tactic| focus ((try simp [- delete_ground, - contract_ground,
  - dual_ground, - restrict_ground_eq, - Bool.forall_bool, - Bool.exists_bool])))

@[simp, aesop unsafe 10% (rule_sets := [Matroid])]
protected lemma part_subset_ground (P : M.E.Bipartition) (i : Bool) : P i ⊆ M.E :=
  P.subset

noncomputable def biConn (M : Matroid α) (P : X.Bipartition) : ℕ∞ := M.eLocalConn (P true) (P false)

lemma biConn_eq_eLocalConn (P : X.Bipartition) :
  M.biConn P = M.eLocalConn (P true) (P false) := rfl

lemma biConn_eq_eLocalConn_bool (P : X.Bipartition) (i : Bool) :
    M.biConn P = M.eLocalConn (P i) (P (!i)) := by
  cases i
  · rw [biConn_eq_eLocalConn, eLocalConn_comm, Bool.not_false]
  rw [biConn_eq_eLocalConn, Bool.not_true]

@[simp]
lemma biConn_symm {X : Set α} (P : X.Bipartition) : M.biConn P.symm = M.biConn P :=
  M.eLocalConn_comm ..

@[simp]
lemma biConn_copy {hXY : X = Y} (P : X.Bipartition) : M.biConn (P.copy hXY) = M.biConn P := rfl

@[simp]
lemma eConn_eq_biConn (P : M.E.Bipartition) (i : Bool) : M.eConn (P i) = M.biConn P := by
  cases i <;> simp [biConn, eConn_eq_eLocalConn, eLocalConn_comm]

@[simp]
lemma biConn_dual (P : M.E.Bipartition) : M✶.biConn P = M.biConn P := by
  rw [← eConn_eq_biConn _ true, eConn_dual, eConn_eq_biConn]

@[simp]
lemma biConn_dual' (P : M✶.E.Bipartition) : M✶.biConn P = M.biConn P := by
  rw [← biConn_dual, dual_dual]

lemma biConn_of_trivial {P : X.Bipartition} (h : P.Trivial) : M.biConn P = 0 := by
  obtain ⟨rfl | rfl, hb⟩ := h.exists_eq_empty <;>
  simp [biConn_eq_eLocalConn, hb]

@[simp]
protected lemma not_indep_iff₂ : ¬ M.Indep (P i) ↔ M.Dep (P i) := by
  rw [not_indep_iff]

@[simp]
protected lemma not_dep_iff₂ : ¬ M.Dep (P i) ↔ M.Indep (P i) := by
  rw [not_dep_iff]

@[simp]
protected lemma not_coindep_iff₂ : ¬ M.Coindep (P i) ↔ M.Codep (P i) := by
  rw [not_coindep_iff]

@[simp]
protected lemma not_codep_iff₂ : ¬ M.Codep (P i) ↔ M.Coindep (P i) := by
  rw [← not_coindep_iff, not_not]

@[simp]
protected lemma not_indep_dual_iff₂ : ¬ M✶.Indep (P i) ↔ M.Codep (P i) := by
  rw [not_coindep_iff]

@[simp]
protected lemma not_spanning_iff₂ : ¬ M.Spanning (P i) ↔ M.Nonspanning (P i) := by
  rw [not_spanning_iff]

@[simp]
protected lemma not_nonspanning_iff₂ : ¬ M.Nonspanning (P i) ↔ M.Spanning (P i) := by
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

protected lemma spanning_dual_iff₂ : M✶.Spanning (P i) ↔ M.Indep (P !i) := by
  simp [spanning_dual_iff]

protected lemma nonspanning_dual_iff₂ : M✶.Nonspanning (P i) ↔ M.Dep (P !i) := by
  rw [← not_spanning_iff, spanning_dual_iff, not_indep_iff, P.compl_eq]

/-- The connectivity of a partition as a natural number. Takes a value of `0` if infinite. -/
noncomputable def nbiConn (M : Matroid α) (P : X.Bipartition) : ℕ := M.localConn (P true) (P false)

@[simp]
lemma conn_symm (P : M.E.Bipartition) : M.nbiConn P.symm = M.nbiConn P := by
  simp [nbiConn, localConn_comm]



-- /-- Restrict a partition to a set. The junk elements go on the right. -/
-- @[simps!] protected def restrict (P : M.E.Bipartition) (R : Set α) : (M ↾ R).Partition :=
-- Partition.mk'
--   (P.left ∩ R) ((P.right ∩ R) ∪ (R \ M.E))
--   (disjoint_union_right.2 ⟨(P.disjoint.mono inter_subset_left inter_subset_left),
--       disjoint_sdiff_right.mono_left (inter_subset_left.trans P.left_subset_ground)⟩)
--   (by rw [← union_assoc, ← union_inter_distrib_right, P.union_eq, inter_comm, inter_union_diff,
--     restrict_ground_eq])

-- lemma eConn_restrict_eq (P : M.E.Bipartition) (R : Set α) :
--     (P.restrict R).eConn = M.eLocalConn (P.left ∩ R) (P.right ∩ R) := by
--   simp only [eConn, Partition.restrict, eLocalConn_restrict_eq, Partition.mk'_left,
--     Partition.mk'_right]
--   rw [union_inter_distrib_right, inter_assoc, inter_assoc, inter_self,
--     inter_eq_self_of_subset_left diff_subset, ← eLocalConn_inter_ground_right,
--     union_inter_distrib_right, disjoint_sdiff_left.inter_eq, union_empty,
--     eLocalConn_inter_ground_right]


protected def dualSep (P : M.E.Bipartition) : M✶.E.Bipartition := P.copy rfl

protected def ofDualSep (P : M✶.E.Bipartition) : M.E.Bipartition := P.copy rfl

@[simp]
lemma dualSep_apply (P : M.E.Bipartition) : M.dualSep P i = P i := rfl

/-- An ugly version of `dualSep_apply` needed for simp confluence. -/
@[simp]
lemma dualSep_apply' {M : Matroid α} (P : M.E.Bipartition) (i : Bool) :
  DFunLike.coe (F := M.E.Bipartition) (Matroid.dualSep P) i = P i := rfl

/-- An ugly version of `ofDualSep_apply` needed for simp confluence. -/
@[simp]
lemma ofDualSep_apply' {M : Matroid α} (P : M✶.E.Bipartition) (i : Bool) :
    DFunLike.coe (F := M.E.Bipartition) (Matroid.ofDualSep P) i = P i := rfl

@[simp]
lemma ofDualSep_apply (P : M✶.E.Bipartition) : M.ofDualSep P i = P i := rfl

@[simp]
lemma dualSep_ofDualSep {P : M.E.Bipartition} : M.ofDualSep (M.dualSep P) = P := rfl

@[simp]
lemma ofDualSep_dualSep {P : M✶.E.Bipartition} : M.dualSep (M.ofDualSep P) = P := rfl

/-- The partition of `M` given by a subset of `M.E` and its complement. The elements of the set
go on side `b`.   -/
@[simps!]
protected def toBipartition (M : Matroid α) (A : Set α) (i : Bool)
    (hA : A ⊆ M.E := by aesop_mat) : M.E.Bipartition where
  toFun j := bif (j == i) then A else M.E \ A
  pairwise_disjoint' := by
    rw [pairwise_disjoint_on_bool'' i]
    simp [disjoint_sdiff_right]
  iUnion_eq' := by cases i <;> simpa

@[simp]
lemma toBipartition_apply (hA : A ⊆ M.E) : (M.toBipartition A i hA) i = A := by
  simp [Matroid.toBipartition]
  rw [Bipartition.mk_apply ..]
  simp

lemma toBipartition_apply_not (hA : A ⊆ M.E) :
    (M.toBipartition A i hA !i) = M.E \ A := by
  simp [Matroid.toBipartition]
  rw [Bipartition.mk_apply ..]
  simp

@[simp]
lemma toBipartition_true_false (hA : A ⊆ M.E) :
    (M.toBipartition A true hA false) = M.E \ A := toBipartition_apply_not hA

@[simp]
lemma toBipartition_false_true (hA : A ⊆ M.E) :
    (M.toBipartition A false hA true) = M.E \ A := toBipartition_apply_not hA

@[simp]
lemma biConn_toBipartition (hA : A ⊆ M.E) :
    M.biConn (M.toBipartition A i hA) = M.eConn A := by
  simp [← eConn_eq_biConn _ i]

@[simp]
lemma toBipartition_dual (hA : A ⊆ M.E) :
  M✶.toBipartition A i hA = (M.toBipartition A i hA).copy rfl := rfl

/-- Every partition has a larger side for a given numerical notion of 'large' -/
lemma exists_larger_side {β : Type*} [ConditionallyCompleteLinearOrder β] (P : X.Bipartition)
    (f : Set α → β) : ∃ i, ∀ j, f (P j) ≤ f (P i) := by
  obtain ⟨b, hb⟩ := exists_eq_ciSup_of_finite (f := fun i ↦ f (P i))
  refine ⟨b, fun i ↦ ?_⟩
  grw [hb, ← le_ciSup (by simp)]

/-- For any two partitions, one of the four cells obtained by intersecting them is the
smaller one, for a given numerical notion of 'small'. -/
lemma exists_smaller_side {β : Type*} [ConditionallyCompleteLinearOrder β] (P : X.Bipartition)
    (f : Set α → β) : ∃ j, ∀ i, f (P j) ≤ f (P i) :=
  exists_larger_side (β := βᵒᵈ) P f

/-- For any two partitions, one of the four cells obtained by intersecting them is the
largest one, for a given numerical notion of 'large'. -/
lemma exists_largest_inter {β : Type*} [ConditionallyCompleteLinearOrder β] (P : X.Bipartition)
    (Q : Y.Bipartition) (f : Set α → β) : ∃ j j', ∀ i i', f (P i ∩ Q i') ≤ f (P j ∩ Q j') := by
  set φ := fun (p : Bool × Bool) ↦ f (P p.1 ∩ Q p.2) with hφ
  obtain ⟨⟨b, b'⟩, hb⟩ := exists_eq_ciSup_of_finite (f := φ)
  refine ⟨b, b', fun i j ↦ ?_⟩
  simp only [φ] at hb
  grw [hb, ← hφ, ← le_ciSup (c := (i,j)) (finite_range φ).bddAbove]

/-- For any two partitions, one of the four cells obtained by intersecting them is the
smallest one, for a given numerical notion of small'. -/
lemma exists_smallest_inter {β : Type*} [ConditionallyCompleteLinearOrder β] (P : X.Bipartition)
    (Q : Y.Bipartition) (f : Set α → β) : ∃ j j', ∀ i i', f (P j ∩ Q j') ≤ f (P i ∩ Q i') :=
  exists_largest_inter (β := βᵒᵈ) P Q f

section Cross

variable {Q : M.E.Bipartition}

lemma biConn_cross (P Q : M.E.Bipartition) :
    M.biConn (P.cross Q i) + M.biConn (P.cross Q !i) ≤ M.biConn P + M.biConn Q := by
  grw [← eConn_eq_biConn _ i, Bipartition.cross_apply, ← eConn_eq_biConn _ i,
    Bipartition.cross_not_apply, ← eConn_eq_biConn _ i, ← eConn_eq_biConn _ i,
    eConn_inter_add_eConn_union_le]

end Cross

section Minor

variable {C D : Set α} {e f : α}

@[simp, aesop unsafe 10% (rule_sets := [Matroid])]
lemma subset_ground_of_delete (P : (M ＼ D).E.Bipartition) (i : Bool) : P i ⊆ M.E :=
  P.subset.trans diff_subset

@[simp, aesop unsafe 10% (rule_sets := [Matroid])]
lemma left_subset_ground_of_contract (P : (M ／ C).E.Bipartition) (i : Bool) : P i ⊆ M.E :=
  P.subset.trans diff_subset

/-- Contract the elements of `C` to take a partition of `M` to a partition of `M ／ C`. -/
def contractSep (M : Matroid α) (P : M.E.Bipartition) (C : Set α) :
  (M ／ C).E.Bipartition := P.induce diff_subset

@[simp]
lemma contractSep_apply (P : M.E.Bipartition) (C : Set α) : M.contractSep P C i = P i \ C := by
  simp only [contractSep, Bipartition.induce_apply, contract_ground]
  rw [← inter_diff_assoc, inter_eq_self_of_subset_left P.subset]

/-- An ugly version of `contractSep_apply` needed for simp confluence. -/
-- @[simp]
-- lemma contractSep_apply' {M : Matroid α} (P : M.E.Bipartition) (C : Set α) (i : Bool) :
--     DFunLike.coe (F := (M.E \ C).Bipartition) (contractSep P C) i = P i \ C :=
--   contractSep_apply ..

@[simp]
lemma contractSep_symm (P : M.E.Bipartition) (C : Set α) :
    (M.contractSep P C).symm = M.contractSep P.symm C := by
  simp [contractSep]

lemma contractSep_contractSep (P : M.E.Bipartition) (C₁ C₂ : Set α) :
    (M ／ C₁).contractSep (M.contractSep P C₁) C₂ = (M.contractSep P (C₁ ∪ C₂)).copy (by simp) :=
  Bipartition.ext <| by simp [-contract_ground, diff_diff]

lemma contractSep_congr (M : Matroid α) (P : M.E.Bipartition) {C₁ C₂ : Set α}
    (h : C₁ ∩ M.E = C₂ ∩ M.E) : M.contractSep P C₁ = (M.contractSep P C₂).copy
      (by rw [← contract_inter_ground_eq, ← h, contract_inter_ground_eq]) := by
  have h1 : P true ⊆ M.E := P.subset
  apply Bipartition.ext
  simp only [contractSep_apply, Bipartition.copy_apply]
  tauto_set

lemma contractSep_inter_ground (M : Matroid α) (P : M.E.Bipartition) (C : Set α) :
    (M.contractSep P (C ∩ M.E)) = (M.contractSep P C).copy (by simp) :=
  M.contractSep_congr P <| by simp [inter_assoc]

/-- Delete the elements of `D` to take a partition of `M` to a partition of `M ＼ D`. -/
def deleteSep (M : Matroid α) (P : M.E.Bipartition) (D : Set α) :
  (M ＼ D).E.Bipartition := P.induce diff_subset

@[simp]
lemma deleteSep_apply {M : Matroid α} (P : M.E.Bipartition) (D : Set α) (i : Bool) :
    (M.deleteSep P D) i = P i \ D := by
  simp only [deleteSep, P.induce_apply, delete_ground]
  rw [← inter_diff_assoc, inter_eq_self_of_subset_left P.subset]


@[simp]
lemma deleteSep_symm (P : M.E.Bipartition) (D : Set α) :
    (M.deleteSep P D).symm = M.deleteSep P.symm D := by
  simp [deleteSep]

@[simp]
lemma deleteSep_deleteSep (P : M.E.Bipartition) (D₁ D₂ : Set α) :
    (M ＼ D₁).deleteSep (M.deleteSep P D₁) D₂ = (M.deleteSep P (D₁ ∪ D₂)).copy (by simp) :=
  Bipartition.ext <| by simp [(M ＼ D₁).deleteSep_apply, M.deleteSep_apply, diff_diff]

lemma deleteSep_congr (M : Matroid α) (P : M.E.Bipartition) {D₁ D₂ : Set α}
    (h : D₁ ∩ M.E = D₂ ∩ M.E) : M.deleteSep P D₁ = (M.deleteSep P D₂).copy
      (by rw [← delete_inter_ground_eq, ← h, delete_inter_ground_eq]) :=
  M.contractSep_congr P h

lemma deleteSep_inter_ground (M : Matroid α) (P : M.E.Bipartition) (D : Set α) :
    (M.deleteSep P (D ∩ M.E)) = (M.deleteSep P D).copy (by rw [delete_inter_ground_eq]) :=
  contractSep_inter_ground ..

@[simp]
lemma disjoint_left_of_sep_contract {P : (M ／ C).E.Bipartition} : Disjoint (P i) C :=
  (subset_diff.1 <| P.subset).2

@[simp]
lemma disjoint_right_of_sep_contract {P : (M ／ C).E.Bipartition} : Disjoint C (P i) :=
  (subset_diff.1 <| P.subset).2.symm

@[simp]
lemma disjoint_left_of_sep_delete {P : (M ＼ D).E.Bipartition} : Disjoint (P i) D :=
  (subset_diff.1 <| P.subset).2

@[simp]
lemma disjoint_right_of_sep_delete {P : (M ＼ D).E.Bipartition} : Disjoint D (P i) :=
  (subset_diff.1 <| P.subset).2.symm

def ofContractSep (M : Matroid α) (P : (M ／ C).E.Bipartition) (i : Bool) : M.E.Bipartition :=
  P.expand diff_subset i

@[simp]
lemma ofContractSep_apply (M : Matroid α) (P : (M ／ C).E.Bipartition) (i : Bool)
    (hC : C ⊆ M.E := by aesop_mat) : M.ofContractSep P i i = P i ∪ C := by
  simp_rw [ofContractSep, Bipartition.expand_apply, contract_ground, diff_diff_cancel_left hC]

@[simp]
lemma ofContractSep_apply_not (M : Matroid α) (P : (M ／ C).E.Bipartition) (i : Bool) :
    M.ofContractSep P i (!i) = P (!i) := by
  simp [ofContractSep]

@[simp]
lemma ofContractSep_not_apply (M : Matroid α) (P : (M ／ C).E.Bipartition) (i : Bool) :
    M.ofContractSep P (!i) i = P i := by
  simp [ofContractSep]

@[simp]
lemma ofContractSep_false_true (M : Matroid α) (P : (M ／ C).E.Bipartition) :
    M.ofContractSep P false true = P true := by
  simp [ofContractSep]

@[simp]
lemma ofContractSep_true_false (M : Matroid α) (P : (M ／ C).E.Bipartition) :
    M.ofContractSep P true false = P false := by
  simp [ofContractSep]

@[simp]
lemma ofContractSep_symm (M : Matroid α) (P : (M ／ C).E.Bipartition) (i : Bool) :
    (M.ofContractSep P i).symm = M.ofContractSep P.symm !i :=
  Bipartition.ext_bool (i := i) <| by simp

@[simp]
lemma ofContractSep_copy {C' : Set α} (M : Matroid α) (hE : (M ／ C').E = (M ／ C).E)
    (P : (M ／ C').E.Bipartition) : (M.ofContractSep (P.copy hE) i) = M.ofContractSep P i := by
  simp [ofContractSep]

lemma ofContractSep_contractSep (M : Matroid α) (P : M.E.Bipartition) (hC : C ⊆ P i) :
    M.ofContractSep (M.contractSep P C) i = P :=
  Bipartition.ext_bool (i := i) <| by
    rw [ofContractSep_apply _, contractSep_apply, diff_union_of_subset hC]

lemma contractSep_ofContractSep (M : Matroid α) (P : (M ／ C).E.Bipartition) (i : Bool)
    (hC : C ⊆ M.E := by aesop_mat) : M.contractSep (M.ofContractSep P i) C = P := by
  refine Bipartition.ext_bool (i := i) ?_
  rw [contractSep_apply, M.ofContractSep_apply,
    union_diff_cancel_right disjoint_left_of_sep_contract.inter_eq.subset]

def ofDeleteSep (M : Matroid α) (P : (M ＼ D).E.Bipartition) (i : Bool) : M.E.Bipartition :=
  P.expand diff_subset i

@[simp]
lemma ofDeleteSep_apply (M : Matroid α) (P : (M ＼ D).E.Bipartition) (i : Bool)
    (hD : D ⊆ M.E := by aesop_mat) : M.ofDeleteSep P i i = P i ∪ D := by
  simp_rw [ofDeleteSep, Bipartition.expand_apply, delete_ground, diff_diff_cancel_left hD]

@[simp]
lemma ofDeleteSep_apply_not (M : Matroid α) (P : (M ＼ D).E.Bipartition) (i : Bool) :
    M.ofDeleteSep P i (!i) = P (!i) := by
  simp [ofDeleteSep]

@[simp]
lemma ofDeleteSep_not_apply (M : Matroid α) (P : (M ＼ D).E.Bipartition) (i : Bool) :
    M.ofDeleteSep P (!i) i = P i := by
  simp [ofDeleteSep]

@[simp]
lemma ofDeleteSep_false_true (M : Matroid α) (P : (M ＼ D).E.Bipartition) :
    M.ofDeleteSep P false true = P true := by
  simp [ofDeleteSep]

@[simp]
lemma ofDeleteSep_true_false (M : Matroid α) (P : (M ＼ D).E.Bipartition) :
    M.ofDeleteSep P true false = P false := by
  simp [ofDeleteSep]

@[simp]
lemma ofDeleteSep_symm (M : Matroid α) (P : (M ＼ D).E.Bipartition) (i : Bool) :
    (M.ofDeleteSep P i).symm = M.ofDeleteSep P.symm !i :=
  Bipartition.ext_bool (i := i) <| by simp

@[simp]
lemma ofDeleteSep_copy {D' : Set α} (M : Matroid α) (hE : (M ＼ D').E = (M ＼ D).E)
    (P : (M ＼ D').E.Bipartition) : (M.ofDeleteSep (P.copy hE) i) = M.ofDeleteSep P i := by
  simp [ofDeleteSep]

@[simp]
lemma ofDeleteSep_deleteSep (M : Matroid α) (P : M.E.Bipartition) (hD : D ⊆ P i) :
    M.ofDeleteSep (M.deleteSep P D) i = P :=
  ofContractSep_contractSep M P hD

@[simp]
lemma deleteSep_ofDeleteSep (M : Matroid α) (P : (M ＼ D).E.Bipartition) (i : Bool)
    (hD : D ⊆ M.E := by aesop_mat) : M.deleteSep (M.ofDeleteSep P i) D = P :=
  contractSep_ofContractSep M P i hD

-- @[simp]
-- lemma contract_dual (P : M.E.Bipartition) (C : Set α) :
--     Matroid.dualSep (M.contractSep P C) = (M✶.deleteSep P C).copy (by simp) :=
--   Bipartition.ext <| by
--     simp

--     simp only [dual_ground, contract_ground, delete_ground, Bipartition.copy_apply]
--     simp
--   -- rw [Matroid.dualSep_apply, contractSep_apply, Bipartition.copy_apply,
--   --   deleteSep_apply]

-- lemma dual_contract (P : M.E.Bipartition) (C : Set α) :
--     P.dual.contract C = (P.delete C).dual.copy (by simp) :=
--   Partition.ext rfl

-- @[simp]
-- lemma delete_dual (P : M.E.Bipartition) (D : Set α) :
--     (P.delete D).dual = (P.dual.contract D).copy (by simp) :=
--   Partition.ext rfl

-- lemma dual_delete (P : M.E.Bipartition) (D : Set α) :
--     (P.delete D).dual = (P.dual.contract D).copy (by simp) :=
--   Partition.ext rfl



-- @[simps!]
-- abbrev contractDual (P : (M ／ C).Partition) : (M✶ ＼ C).Partition := P.dual.copy (by simp)

-- @[simps!]
-- abbrev deleteDual (P : (M ＼ D).Partition) : (M✶ ／ D).Partition := P.dual.copy (by simp)

/- Extend a partition `P` of some matroid `N` to a matroid `M` with larger ground set by
adding the extra elements to side `b` of `P`. `-/
-- def ofSubset (P : N.Partition) (hNM : N.E ⊆ M.E) (i : Bool) : M.E.Bipartition where
--   toFun i := bif (i == b) then P i ∪ (M.E \ N.E) else P i
--   pairwise_disjoint' := by
--     suffices Disjoint (M.E \ N.E) (P !i) by simpa [pairwise_disjoint_on_bool' b]
--     exact disjoint_sdiff_left.mono_right <| P.subset_ground _
--   iUnion_eq' := by
--     cases i
--     · simpa [← union_assoc]
--     simpa [union_right_comm _ (M.E \ N.E)]

-- lemma ofSubset_apply (P : N.Partition) (hNM : N.E ⊆ M.E) (b i : Bool) :
--     P.ofSubset hNM b i = bif (i == b) then P i ∪ (M.E \ N.E) else P i := rfl

-- lemma ofSubset_symm (P : N.Partition) (hNM : N.E ⊆ M.E) (i : Bool) :
--     (P.ofSubset hNM b).symm = P.symm.ofSubset hNM (!i) :=
--   Partition.ext <| by simp [ofSubset_apply]

-- @[simp]
-- lemma ofSubset_apply_self (P : N.Partition) (hNM : N.E ⊆ M.E) (i : Bool) :
--     P.ofSubset hNM b b = P i ∪ (M.E \ N.E) := by
--   simp [ofSubset_apply]

-- @[simp]
-- lemma ofSubset_apply_not (P : N.Partition) (hNM : N.E ⊆ M.E) (i : Bool) :
--     P.ofSubset hNM b (!i) = P (!i) := by
--   simp [ofSubset_apply]

-- @[simp]
-- lemma ofSubset_not_apply (P : N.Partition) (hNM : N.E ⊆ M.E) (i : Bool) :
--     P.ofSubset hNM (!i) b = P i := by
--   simp [ofSubset_apply]

-- @[simp]
-- lemma ofSubset_copy {N' : Matroid α} (P : N.Partition) (hN' : N = N') (hN'M : N'.E ⊆ M.E)
--     (i : Bool) : (P.copy hN').ofSubset hN'M b = P.ofSubset (hN' ▸ hN'M) b :=
--   Partition.ext_bool (b := !i) <| by simp

-- /- Extend a partition of `M ／ C` to one of `M` by extending using side `i`. -/
-- def ofContract (P : (M ／ C).E.Bipartition) (i : Bool) : M.E.Bipartition := P.shift M.E i

-- lemma ofContract_apply (P : (M ／ C).Partition) (hC : C ⊆ M.E := by aesop_mat) (b i : Bool) :
--     P.ofContract b i = bif i == b then P i ∪ C else P i := by
--   simp [ofContract, ofSubset_apply, inter_eq_self_of_subset_right hC]

-- @[simp]
-- lemma ofContract_apply_self (P : (M ／ C).Partition) (hC : C ⊆ M.E := by aesop_mat) (i : Bool) :
--     P.ofContract b b = P i ∪ C := by
--   simp [P.ofContract_apply]

-- @[simp]
-- lemma ofContract_apply_not (P : (M ／ C).Partition) (i : Bool) : P.ofContract b (!i) = P !i := by
--   simp [ofContract, ofSubset_apply]

-- @[simp]
-- lemma ofContract_not_apply (P : (M ／ C).Partition) (i : Bool) : P.ofContract (!i) b = P i := by
--   simpa using P.ofContract_apply_not (!i)

-- @[simp]
-- lemma ofContract_true_false (P : (M ／ C).Partition) : P.ofContract true false = P false :=
--   P.ofContract_apply_not true

-- @[simp]
-- lemma ofContract_false_true (P : (M ／ C).Partition) : P.ofContract false true = P true :=
--   P.ofContract_apply_not false

-- @[simp]
-- lemma ofContract_symm (P : (M ／ C).Partition) (i : Bool) :
--     (P.ofContract b).symm = P.symm.ofContract (!i) :=
--   ofSubset_symm ..

-- @[simp]
-- lemma ofContract_copy {C' : Set α} (P : (M ／ C).Partition) (h_eq : M ／ C = M ／ C') (i : Bool) :
--     (P.copy h_eq).ofContract b = P.ofContract b :=
--   Partition.ext_bool (b := !i) <| by simp

-- /-- Extend a partition of `M ＼ D` to a partition of `M` by adding `D` to the left side. -/
-- def ofDelete (P : (M ＼ D).Partition) (i : Bool) : M.E.Bipartition := P.ofSubset diff_subset b

-- lemma ofDelete_apply (P : (M ＼ D).Partition) (hD : D ⊆ M.E := by aesop_mat) (b i : Bool) :
--     P.ofDelete b i = bif i == b then P i ∪ D else P i := by
--   simp [ofDelete, ofSubset_apply, inter_eq_self_of_subset_right hD]

-- @[simp]
-- lemma ofDelete_apply_self (P : (M ＼ D).Partition) (hD : D ⊆ M.E := by aesop_mat) (i : Bool) :
--     P.ofDelete b b = P i ∪ D := by
--   simp [P.ofDelete_apply]

-- @[simp]
-- lemma ofDelete_apply_not (P : (M ＼ D).Partition) (i : Bool) : P.ofDelete b (!i) = P !i := by
--   simp [ofDelete]

-- @[simp]
-- lemma ofDelete_not_apply (P : (M ＼ D).Partition) (i : Bool) : P.ofDelete (!i) b = P i := by
--   simp [ofDelete]

-- @[simp]
-- lemma ofDelete_copy {D' : Set α} (P : (M ＼ D).Partition) (h_eq : M ＼ D = M ＼ D') (i : Bool) :
--     (P.copy h_eq).ofDelete b = P.ofDelete b :=
--   Partition.ext_bool (b := !i) <| by simp

-- @[simp]
-- lemma ofDelete_symm (P : (M ＼ D).Partition) (i : Bool):
--     (P.ofDelete b).symm = P.symm.ofDelete !i :=
--   ofSubset_symm ..

-- @[simp]
-- lemma ofDelete_dual (P : (M ＼ D).Partition) (i : Bool) :
--     (P.ofDelete b).dual = P.deleteDual.ofContract b := rfl

-- @[simp]
-- lemma ofContract_dual (P : (M ／ C).Partition) (i : Bool) :
--     (P.ofContract b).dual = P.contractDual.ofDelete b := rfl

-- @[simp]
-- lemma ofContract_contract (P : (M ／ C).Partition) (hC : C ⊆ M.E := by aesop_mat) (i : Bool) :
--     (P.ofContract b).contract C = P := by
--   apply Partition.ext
--   obtain rfl | rfl := b.eq_or_eq_not true
--   · rw [contract_apply, ofContract_apply_self, union_diff_cancel_right]
--     exact (P.disjoint_contract true).inter_eq.subset
--   rw [contract_apply, Bool.not_true, ← Bool.not_false, ofContract_apply_not, sdiff_eq_left]
--   simp

-- lemma contract_ofContract (P : M.E.Bipartition) (hC : C ⊆ P i) : (P.contract C).ofContract b =
-- P :=
--   Partition.ext_bool (b := b) <| by
--     rw [ofContract_apply_self, contract_apply, diff_union_of_subset hC]

-- lemma delete_ofDelete (P : M.E.Bipartition) (hD : D ⊆ P i) :
--     (P.delete D).ofDelete b = P :=
--   Partition.ext_bool (b := b) <| by rw [ofDelete_apply_self, delete_apply,
-- diff_union_of_subset hD]

-- @[simp]
-- lemma ofDelete_delete (P : (M ＼ D).Partition) (hD : D ⊆ M.E := by aesop_mat) :
--     (P.ofDelete b).delete D = P :=
--   Partition.ext_bool (b := b) <| by simp [ofDelete_apply_self _ hD]

-- lemma compl_delete (P : (M ＼ D).Partition) (hD : D ⊆ M.E := by aesop_mat) (i : Bool) :
--     M.E \ P i = P (!i) ∪ D := by
--   grw [← P.compl_eq, delete_ground, diff_diff_comm, diff_union_self, eq_comm, union_eq_left,
--     subset_diff, and_iff_right hD, P.subset_ground]
--   exact disjoint_sdiff_right

-- lemma compl_contract (P : (M ／ C).Partition) (hC : C ⊆ M.E := by aesop_mat) (i : Bool) :
--     M.E \ (P i) = P (!i) ∪ C :=  by
--   simpa using (P.dual.copy (M.dual_contract C)).compl_delete hC b

-- @[simp]
-- lemma compl_union_contract (P : (M ／ C).Partition) (i : Bool) : M.E \ (P i ∪ C) = P !i := by
--   rw [← P.compl_eq, union_comm, contract_ground, diff_diff]

-- @[simp]
-- lemma compl_union_delete (P : (M ＼ D).Partition) (i : Bool) : M.E \ (P i ∪ D) = P !i := by
--   rw [← P.compl_eq, union_comm, delete_ground, diff_diff]

-- lemma compl_delete_singleton (P : (M ＼ {e}).Partition) (he : e ∈ M.E := by aesop_mat)
--(i : Bool) :
--     M.E \ (P i) = insert e (P (!i)) := by
--   rw [compl_delete, union_singleton]

-- lemma compl_contract_singleton (P : (M ／ {e}).Partition) (he : e ∈ M.E := by aesop_mat)
-- (i : Bool) :
--     M.E \ (P i) = insert e (P !i) := by
--   rw [compl_contract, union_singleton]

lemma biConn_ofContractSep (P : (M ／ C).E.Bipartition) (i : Bool) :
    M.biConn (M.ofContractSep P i) = (M ／ C).biConn P + M.eLocalConn (P !i) C := by
  wlog hCE : C ⊆ M.E generalizing C P with aux
  · simpa using aux (C := C ∩ M.E) (P.copy (by simp)) inter_subset_right
  rw [← eConn_eq_biConn _ i, M.ofContractSep_apply, eConn_union_eq_eConn_contract_add,
    ← M.ofContractSep_apply, Bipartition.compl_eq, ofContractSep_apply_not, eConn_eq_biConn]
  simp [-contract_ground]

lemma biConn_ofDeleteSep (P : (M ＼ D).E.Bipartition) (i : Bool) :
    M.biConn (M.ofDeleteSep P i) = (M ＼ D).biConn P + M✶.eLocalConn (P !i) D := by
  rw [← biConn_dual, ← (M ＼ D).biConn_dual, dual_delete]
  exact M✶.biConn_ofContractSep P i

lemma biConn_ofContractSep_singleton_le (M : Matroid α) (P : (M ／{e}).E.Bipartition) :
    M.biConn (M.ofContractSep P i) ≤ (M ／ {e}).biConn P + 1 := by
  grw [biConn_ofContractSep, eLocalConn_le_eRk_right, eRk_le_encard, encard_singleton]

lemma biConn_ofDeleteSep_singleton_le (M : Matroid α) (P : (M ＼ {e}).E.Bipartition) :
    M.biConn (M.ofDeleteSep P i) ≤ (M ＼ {e}).biConn P + 1 := by
  grw [biConn_ofDeleteSep, eLocalConn_le_eRk_right, eRk_le_encard, encard_singleton]

lemma IsMinor.biConn_induce_le (hNM : N ≤m M) (P : M.E.Bipartition) :
    N.biConn (P.induce hNM.subset) ≤ M.biConn P := by
  grw [← eConn_eq_biConn _ true, Bipartition.induce_apply, eConn_inter_ground,
    ← eConn_eq_biConn _ true, hNM.eConn_le]

lemma biConn_eq_biConn_contractSep_add (M : Matroid α) (P : M.E.Bipartition) (hC : C ⊆ P i) :
    M.biConn P = (M ／ C).biConn (M.contractSep P C) + M.eLocalConn (P !i) C := by
  rw [← ofContractSep_contractSep M P hC, biConn_ofContractSep, contractSep_apply,
    contractSep_ofContractSep _, ofContractSep_contractSep _ _ hC, Disjoint.sdiff_eq_left]
  grw [← P.compl_eq, hC]
  exact disjoint_sdiff_left

lemma biConn_le_biConn_contractSep_add_eRk (P : M.E.Bipartition) (C : Set α) :
    M.biConn P ≤ (M ／ C).biConn (M.contractSep P C) + M.eRk C := by
  have aux : (C ∩ P true) ∪ (C ∩ P false) = C ∩ M.E := by
    rw [← inter_union_distrib_left, P.union_eq]
  have aux' : ((C ∩ P true) ∪ (C ∩ P false)) ∩ M.E = C ∩ M.E := by simp [aux]
  grw [M.biConn_eq_biConn_contractSep_add P (C := C ∩ P true) inter_subset_right,
    biConn_eq_biConn_contractSep_add _ (C := C ∩ P false) (i := false), eLocalConn_le_eRk_right,
    eLocalConn_le_eRk_right, ← eRelRk_eq_eRk_contract, add_assoc, eRelRk_add_eRk_eq]
  · simp_rw [contract_contract, contractSep_contractSep, M.contractSep_congr _ aux']
    simp [union_comm (C ∩ P false), aux]
  rw [contractSep_apply, subset_diff, and_iff_right inter_subset_right, disjoint_comm]
  exact P.disjoint_inter_left

lemma biConn_le_biConn_delete_add_eRk_dual (P : M.E.Bipartition) (D : Set α) :
    M.biConn P ≤ (M ＼ D).biConn (M.deleteSep P D) + M✶.eRk D := by
  rw [← biConn_dual, ← (M ＼ D).biConn_dual, dual_delete]
  exact M✶.biConn_le_biConn_contractSep_add_eRk P D

lemma biConn_eq_of_subset_of_subset_closure {N : Matroid α} {Q : N.E.Bipartition}
    {P : M.E.Bipartition} (forall_subset : ∀ i, Q i ⊆ P i)
    (forall_subset_closure : ∀ i, P i ⊆ M.closure (Q i)) : M.biConn P = M.biConn Q := by
  rw [M.biConn_eq_eLocalConn, M.biConn_eq_eLocalConn]
  refine le_antisymm ?_ ?_
  · grw [← eLocalConn_closure_closure (X := Q true),
      ← M.eLocalConn_mono (forall_subset_closure true) (forall_subset_closure false)]
  grw [M.eLocalConn_mono (forall_subset _) (forall_subset _)]

lemma biConn_eq_zero_iff_skew {P : M.E.Bipartition} (i : Bool) :
    M.biConn P = 0 ↔ M.Skew (P i) (P !i) := by
  rw [M.biConn_eq_eLocalConn_bool P i, eLocalConn_eq_zero]

lemma biConn_eq_zero_iff_eq_disjointSum {P : M.E.Bipartition} (i : Bool) :
    M.biConn P = 0 ↔ M = (M ↾ (P i)).disjointSum (M ↾ (P !i)) (P.disjoint_bool i) := by
  rw [biConn_eq_zero_iff_skew i, skew_iff_restrict_union_eq P.subset P.subset (P.disjoint_bool i),
    P.union_bool_eq, restrict_ground_eq_self]

lemma exists_bipartition_of_not_connected [M.Nonempty] (h : ¬ M.Connected) :
    ∃ P : M.E.Bipartition, M.biConn P = 0 ∧ ¬ P.Trivial := by
  obtain ⟨M₁, M₂, hdj, hM₁, hM₂, hM⟩ := eq_disjointSum_of_not_connected h
  refine ⟨M.toBipartition M₁.E true (by simp [hM]), ?_⟩
  rw [← eConn_eq_biConn _ true]
  simp [Bipartition.not_trivial_iff, hM, hdj.sdiff_eq_right, hM₁.ground_nonempty,
    hM₂.ground_nonempty]

lemma Connected.trivial_of_biConn_eq_zero (h : M.Connected) (hP : M.biConn P = 0) : P.Trivial := by
  by_contra! hcon
  rw [Bipartition.not_trivial_iff] at hcon
  rw [biConn_eq_zero_iff_eq_disjointSum true] at hP
  refine disjointSum_not_connected ?_ ?_ _ (hP ▸ h)
  <;> simp [← ground_nonempty_iff, hcon]

lemma exists_bipartition_iff_not_connected [M.Nonempty] :
    ¬ M.Connected ↔ ∃ P : M.E.Bipartition, M.biConn P = 0 ∧ ¬ P.Trivial :=
  ⟨exists_bipartition_of_not_connected,
    fun ⟨_, hP0, hP⟩ hM ↦ hP <| hM.trivial_of_biConn_eq_zero hP0⟩

end Minor

end Matroid




-- section wlog


-- -- protected lemma wlog_symm' (motive : {N : Matroid α} → (P : N.Partition) → Prop)
-- --     (property : {N : Matroid α} → N.Partition → Prop)
-- --     (h_symm : ∀ P, property P ∨ property P.symm)
-- --     (h_wlog : ∀ P, property P → motive P) (P₀ : M.E.Bipartition) :

-- protected lemma wlog_symm (motive : {N : Matroid α} → (P : N.Partition) → Prop)
--     (property : Matroid α → Set α → Prop)
--     (h_symm : ∀ ⦃N⦄ ⦃P : Matroid.Partition N⦄, motive P.symm → motive P)
--     (h_some : ∀ ⦃N⦄ ⦃P : Matroid.Partition N⦄, property N P.left → motive P)
--     (h_not : ∀ ⦃N⦄ ⦃P : Matroid.Partition N⦄, ¬ property N P.left → ¬ property N P.right →
-- motive P)
--     (P₀ : M.E.Bipartition) : motive P₀ := by
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
--       ¬ property N✶ P.left → ¬ property N✶ P.right → motive P) (P₀ : M.E.Bipartition) :
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
