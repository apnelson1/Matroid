import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Pairwise
import Matroid.ForMathlib.Data.Set.Subsingleton
import Matroid.ForMathlib.Set
-- import Mathlib.Tactic.DepRewrite
import Mathlib.Tactic.NthRewrite

open Set Function

variable {α : Type*} {r s t : Set α}

namespace Set

protected structure IndexedPartition {α : Type*} (s : Set α) (ι : Type*) where
  toFun : ι → Set α
  pairwise_disjoint' : Pairwise (Disjoint on toFun)
  iUnion_eq' : ⋃ i, toFun i = s

namespace IndexedPartition

variable {ι : Type*} {i j : ι} {P : s.IndexedPartition ι}

instance : FunLike (s.IndexedPartition ι) ι (Set α) where
  coe := IndexedPartition.toFun
  coe_injective' := by rintro ⟨f,h⟩ ⟨f', h'⟩; simp

@[simp]
protected lemma toFun_eq_coe (P : s.IndexedPartition ι) : P.toFun = P := rfl

@[simp]
protected lemma mk_apply (f : ι → Set α) (dj) (hu : ⋃ i, f i = s) (i : ι) :
    IndexedPartition.mk f dj hu i = f i := rfl

protected lemma ext {P Q : s.IndexedPartition ι} (h : ∀ i, P i = Q i) : P = Q := by
  cases P
  cases Q
  simp only [mk.injEq, IndexedPartition.mk_apply] at ⊢ h
  exact funext h

protected lemma pairwise_disjoint (P : s.IndexedPartition ι) : Pairwise (Disjoint on P) :=
  P.pairwise_disjoint'

protected lemma iUnion_eq (P : s.IndexedPartition ι) : ⋃ i, P i = s :=
  P.iUnion_eq'

@[simp]
protected lemma subset (P : s.IndexedPartition ι) {i : ι} : P i ⊆ s := by
  simp_rw [← P.iUnion_eq]
  exact subset_iUnion ..

lemma single_eq_diff_iUnion (P : s.IndexedPartition ι) (i : ι) : P i = s \ (⋃ j ≠ i, P j) := by
  simp only [subset_antisymm_iff, subset_diff, P.subset, disjoint_iUnion_right, true_and,
    diff_subset_iff]
  refine ⟨fun j hj ↦ (P.pairwise_disjoint hj).symm, ?_⟩
  simp_rw [← P.iUnion_eq, iUnion_subset_iff]
  intro j
  obtain rfl | hne := eq_or_ne j i
  · simp
  exact (subset_biUnion_of_mem hne).trans subset_union_left

protected lemma ext' {P Q : s.IndexedPartition ι} {j : ι} (h : ∀ i ≠ j, P i = Q i) : P = Q := by
  refine P.ext fun i ↦ ?_
  obtain hne | rfl := ne_or_eq i j
  · exact h _ hne
  rwa [single_eq_diff_iUnion, single_eq_diff_iUnion, iUnion₂_congr]

/-- Transfer a partition across a se equality. -/
protected def copy (P : s.IndexedPartition ι) (h_eq : s = t) : t.IndexedPartition ι where
  toFun := P.toFun
  pairwise_disjoint' := P.pairwise_disjoint
  iUnion_eq' := h_eq ▸ P.iUnion_eq

@[simp]
lemma copy_apply (P : s.IndexedPartition ι) (h_eq : s = t) (i : ι) : P.copy h_eq i = P i := rfl

/-- Intersect a partition with a smaller set -/
def induce (P : s.IndexedPartition ι) (hts : t ⊆ s) : t.IndexedPartition ι where
  toFun i := P i ∩ t
  pairwise_disjoint' := P.pairwise_disjoint.mono <| by grind
  iUnion_eq' := by rw [← iUnion_inter, P.iUnion_eq, inter_eq_self_of_subset_right hts]

@[simp]
lemma induce_apply {P : s.IndexedPartition ι} {hts : t ⊆ s} {i : ι} :
  (P.induce hts) i = P i ∩ t := rfl

protected def union (P : s.IndexedPartition ι) (Q : t.IndexedPartition ι) (hdj : Disjoint s t) :
    (s ∪ t).IndexedPartition ι where
  toFun i := P i ∪ Q i
  pairwise_disjoint' := by
    refine fun i j hne ↦ ?_
    simp only [disjoint_union_right, disjoint_union_left]
    exact ⟨⟨P.pairwise_disjoint hne, hdj.symm.mono Q.subset P.subset⟩,
      hdj.mono P.subset Q.subset, Q.pairwise_disjoint hne⟩
  iUnion_eq' := by simp_rw [← P.iUnion_eq, ← Q.iUnion_eq, iUnion_union_distrib]

@[simp]
protected lemma union_apply (P : s.IndexedPartition ι) (Q : t.IndexedPartition ι) {hdj} :
    (P.union Q hdj) i = P i ∪ Q i := rfl

/-- The partition of `s` with part `i` equal to `s` and the other parts empty. -/
protected def single [DecidableEq ι] (s : Set α) (i : ι) : s.IndexedPartition ι where
  toFun j := if j = i then s else ∅
  pairwise_disjoint' := by simp only [Pairwise, Disjoint, bot_eq_empty]; grind
  iUnion_eq' := by ext; simp

@[simp]
protected lemma single_apply [DecidableEq ι] (s : Set α) (i : ι) :
    IndexedPartition.single s i i = s := by
  simp [IndexedPartition.single]

protected lemma single_apply_of_ne [DecidableEq ι] (s : Set α) (hne : j ≠ i) :
    IndexedPartition.single s i j = ∅ := by
  simp [IndexedPartition.single, hne]

protected def shift [DecidableEq ι] (P : s.IndexedPartition ι) (t : Set α) (i : ι) :
    t.IndexedPartition ι :=
  ((P.induce inter_subset_right).union (IndexedPartition.single (t \ s) i)
    disjoint_sdiff_inter.symm).copy (by simp)

protected lemma shift_apply [DecidableEq ι] (P : s.IndexedPartition ι) (t : Set α) (i : ι) :
    P.shift t i i = (P i ∩ t) ∪ (t \ s) := by
  simp only [IndexedPartition.shift, copy_apply, IndexedPartition.union_apply, induce_apply,
    IndexedPartition.single_apply]
  have := P.subset (i := i)
  grind

protected lemma shift_apply_of_ne [DecidableEq ι] (P : s.IndexedPartition ι) {t : Set α}
    (hne : i ≠ j) : P.shift t i j = P j ∩ t := by
  simp only [IndexedPartition.shift, copy_apply, IndexedPartition.union_apply, induce_apply,
    IndexedPartition.single_apply_of_ne _ hne.symm, union_empty]
  rw [← inter_assoc, inter_right_comm, inter_eq_self_of_subset_left P.subset]

protected def diff (P : s.IndexedPartition ι) (t : Set α) : (s \ t).IndexedPartition ι :=
  P.induce diff_subset

@[simp]
lemma diff_apply (P : s.IndexedPartition ι) (t : Set α) (i : ι) : (P.diff t) i = P i \ t := by
  rw [IndexedPartition.diff, induce_apply, ← inter_diff_assoc,
    inter_eq_self_of_subset_left P.subset]

@[simp]
lemma subset_of_diff (P : (s \ t).IndexedPartition ι) (i : ι) : P i ⊆ s :=
  P.subset.trans diff_subset

@[simp]
lemma disjoint_of_diff (P : (s \ t).IndexedPartition ι) (i : ι) : Disjoint (P i) t :=
  (subset_diff.1 P.subset).2

/-- A partition is `Trivial` if it has exactly one nonempty cell. -/
protected def Trivial (P : s.IndexedPartition ι) : Prop := ∃ i, P i = s

lemma Trivial.exists_eq_single [DecidableEq ι] (h : P.Trivial) :
    ∃ i, P = IndexedPartition.single s i := by
  obtain ⟨i, hi⟩ := h
  refine ⟨i, IndexedPartition.ext' (j := i) fun j hji ↦ ?_⟩
  rw [IndexedPartition.single_apply_of_ne _ hji, ← inter_eq_self_of_subset_left P.subset]
  simp_rw [← hi, (P.pairwise_disjoint hji).inter_eq]

lemma trivial_of_subsingleton [Nonempty ι] (P : s.IndexedPartition ι) (h : s.Subsingleton) :
    P.Trivial := by
  rw [IndexedPartition.Trivial]
  by_contra! hcon
  have hi' : ∀ i, P i = ∅ := fun i ↦ (h.eq_or_eq_of_subset P.subset).elim id fun h ↦ (hcon i h).elim
  have hs : s = ∅ := by simp [← P.iUnion_eq, hi']
  exact hcon (Classical.arbitrary ι) <| by simp [hs, hi']


end IndexedPartition

def Bipartition (s : Set α) := s.IndexedPartition Bool

namespace Bipartition

instance : FunLike s.Bipartition Bool (Set α) where
  coe := IndexedPartition.toFun
  coe_injective' := by rintro ⟨f,h⟩ ⟨f', h'⟩; simp [Bipartition]

variable {P : s.Bipartition} {i j : Bool}

@[simp]
protected lemma toFun_eq_coe (P : s.Bipartition) : P.toFun = P := rfl

@[simp]
protected lemma mk_apply (f : Bool → Set α) (dj) (hu : ⋃ i, f i = s) (i : Bool) :
    IndexedPartition.mk f dj hu i = f i := rfl

@[simp]
protected lemma union_eq' : P false ∪ P true = s := by
  simp [← P.iUnion_eq, union_comm]

@[simp]
protected lemma union_eq : P true ∪ P false = s := by
  simp [← P.iUnion_eq]

@[simp]
protected lemma union_bool_eq (b : Bool) : P b ∪ P (!b) = s := by
  cases b <;> simp

@[simp]
protected lemma union_bool_eq' (b : Bool) : P (!b) ∪ P b = s := by
  cases b <;> simp

@[simp]
protected lemma disjoint_true_false : Disjoint (P true) (P false) := by
  rw [← pairwise_disjoint_on_bool']
  apply P.pairwise_disjoint

@[simp]
protected lemma disjoint_false_true : Disjoint (P false) (P true) :=
  P.disjoint_true_false.symm

@[simp]
protected lemma disjoint_bool (b : Bool) : Disjoint (P b) (P (!b)) := by
  cases b <;> simp

@[simp]
protected lemma compl_eq (P : s.Bipartition) (b : Bool) : s \ (P b) = P (!b) := by
  simp_rw [← P.union_bool_eq b, union_diff_cancel_left (P.disjoint_bool b).inter_eq.subset]

protected lemma compl_not_eq (P : s.Bipartition) (b : Bool) : s \ (P (!b)) = P b := by
  rw [P.compl_eq, Bool.not_not]

protected def _root_.Set.Disjoint.toBipartition (disjoint : Disjoint r s) (union_eq : r ∪ s = t) :
    t.Bipartition where
  toFun b := bif b then r else s
  pairwise_disjoint' := by rwa [pairwise_disjoint_on_bool']
  iUnion_eq' := by simpa

@[simp]
protected lemma _root_.Set.Disjoint.toBipartition_true {disjoint : Disjoint r s}
    {union_eq : r ∪ s = t} : disjoint.toBipartition union_eq true = r := rfl

@[simp]
protected lemma _root_.Set.Disjoint.toBipartition_false {disjoint : Disjoint r s}
    {union_eq : r ∪ s = t} : disjoint.toBipartition union_eq false = s := rfl

protected lemma ext_bool {P P' : s.Bipartition} (h : P i = P' i) : P = P' :=
  IndexedPartition.ext' (j := !i) <| by simpa

protected lemma ext {P P' : s.Bipartition} (h_left : P true = P' true) : P = P' :=
  P.ext_bool h_left

protected lemma ext_iff {P P' : s.Bipartition} (b : Bool) : P = P' ↔ P b = P' b :=
  ⟨fun h ↦ by simp [h], fun h ↦ P.ext_bool h⟩

@[simps]
protected def symm (P : s.Bipartition) : s.Bipartition where
  toFun b := P.toFun !b
  pairwise_disjoint' := P.pairwise_disjoint.comp_of_injective fun _ _ ↦ by simp
  iUnion_eq' := by simp [← P.iUnion_eq, union_comm]

protected lemma symm_true (P : s.Bipartition) : P.symm true = P false := rfl

protected lemma symm_false (P : s.Bipartition) : P.symm false = P true := rfl

@[simp]
protected lemma symm_apply (P : s.Bipartition) (b : Bool) : P.symm b = P !b := rfl

@[simp]
protected lemma symm_symm (P : s.Bipartition) : P.symm.symm = P := Bipartition.ext rfl

protected lemma compl_true (P : s.Bipartition) : s \ (P true) = P false := by
  rw [← Bool.not_false, P.compl_not_eq]

@[simp]
protected lemma compl_false (P : s.Bipartition) : s \ (P false) = P true := by
  rw [← Bool.not_true, P.compl_not_eq]

/-- A version of `copy` where the ground sets are equal, but the matroids need not be.
`copy` is preferred where possible, so that lemmas depending on matroid structure
like `eConn_copy` can be `@[simp]`. -/
@[simps] protected def copy (P : s.Bipartition) (h_eq : s = t) : t.Bipartition where
  toFun := P.toFun
  pairwise_disjoint' := P.pairwise_disjoint
  iUnion_eq' := h_eq ▸ P.iUnion_eq

@[simp]
lemma copy'_apply (P : s.Bipartition) (h_eq : s = t) (b : Bool) : P.copy h_eq b = P b := rfl


/-- A partition is trivial if one side is empty. -/
protected def Trivial (P : s.Bipartition) : Prop := IndexedPartition.Trivial P

lemma trivial_of_eq (h : P i = s) : P.Trivial :=
  ⟨_, h⟩

lemma trivial_of_eq_empty (h : P i = ∅) : P.Trivial :=
  trivial_of_eq (i := !i) <| by rw [← P.compl_eq, h, diff_empty]

protected lemma trivial_def : P.Trivial ↔ P true = ∅ ∨ P false = ∅ := by
  refine ⟨fun h ↦ ?_, fun h ↦ Or.elim h trivial_of_eq_empty trivial_of_eq_empty⟩
  obtain ⟨rfl | rfl, rfl⟩ := h.exists_eq_single
  · exact .inl <| IndexedPartition.single_apply_of_ne _ <| by trivial
  exact .inr <| IndexedPartition.single_apply_of_ne _ <| by trivial

lemma not_trivial_iff : ¬ P.Trivial ↔ ∀ b, (P b).Nonempty := by
  simp [nonempty_iff_ne_empty, P.trivial_def, and_comm]

protected lemma trivial_def' : P.Trivial ↔ P true = s ∨ P false = s := by
  refine ⟨fun h ↦ ?_, fun h ↦ Or.elim h trivial_of_eq trivial_of_eq⟩
  obtain ⟨rfl | rfl, rfl⟩ := h.exists_eq_single
  · exact .inr <| IndexedPartition.single_apply (s := s) false
  exact .inl <| IndexedPartition.single_apply (s := s) true

lemma Trivial.exists_eq (h : P.Trivial) : ∃ b, P b = s := h

/-- Intersect a partition with a smaller set -/
def induce (P : s.Bipartition) (h : t ⊆ s) : t.Bipartition := IndexedPartition.induce P h

@[simp]
lemma induce_apply (P : s.Bipartition) (h : t ⊆ s) (b) : P.induce h b = (P b) ∩ t := rfl

@[simp]
lemma induce_symm (P : s.Bipartition) (hN : t ⊆ s) : (P.induce hN).symm = P.symm.induce hN :=
  Bipartition.ext rfl

protected def diff (P : s.Bipartition) (t : Set α) : (s \ t).Bipartition := P.induce diff_subset

@[simp]
lemma diff_apply (P : s.Bipartition) (t : Set α) (i : Bool) : (P.diff t) i = P i \ t := by
  rw [Bipartition.diff, induce_apply, ← inter_diff_assoc, inter_eq_self_of_subset_left P.subset]

section Cross

variable {Q : s.Bipartition}

/-- Cross two bipartitions by intersecting their `b`-sides and unioning their `!b`-sides-/
protected def cross (P Q : s.Bipartition) (b : Bool) : s.Bipartition where
  toFun i := bif (i == b) then P i ∩ Q i else P i ∪ Q i
  pairwise_disjoint' := by
    simp only [pairwise_on_bool' b, BEq.rfl, cond_true, Bool.not_beq_self, cond_false,
      disjoint_union_right, disjoint_union_left]
    refine ⟨⟨(P.disjoint_bool b).mono_left ?_, (Q.disjoint_bool b).mono_left ?_⟩,
      (P.disjoint_bool b).symm.mono_right ?_, (Q.disjoint_bool b).symm.mono_right ?_⟩ <;> simp
  iUnion_eq' := by
    simp only [iUnion_bool' _ b, BEq.rfl, cond_true, Bool.not_beq_self, cond_false]
    rw [← P.compl_eq, ← Q.compl_eq, ← inter_eq_self_of_subset_left P.subset,
      ← inter_eq_self_of_subset_left Q.subset]
    grind

@[simp]
protected lemma cross_apply (P Q : s.Bipartition) (b : Bool) : (P.cross Q b) b = P b ∩ Q b := by
  rw [Bipartition.cross, IndexedPartition.mk_apply]
  simp

@[simp]
protected lemma cross_apply_not (P Q : s.Bipartition) (b : Bool) :
    (P.cross Q b) (!b) = P (!b) ∪ Q !b := by
  rw [Bipartition.cross, IndexedPartition.mk_apply]
  simp

@[simp]
protected lemma cross_not_apply (P Q : s.Bipartition) (b : Bool) :
    (P.cross Q !b) b = P b ∪ Q b := by
  rw [Bipartition.cross, IndexedPartition.mk_apply]
  simp

@[simp]
protected lemma cross_true_false (P Q : s.Bipartition) :
    (P.cross Q true) false = P false ∪ Q false :=
  P.cross_apply_not Q true

@[simp]
protected lemma cross_false_true (P Q : s.Bipartition) : (P.cross Q false) true = P true ∪ Q true :=
  P.cross_apply_not Q false

@[simp]
protected lemma cross_symm (P Q : s.Bipartition) (b : Bool) :
    (P.cross Q b).symm = P.symm.cross Q.symm !b :=
  Bipartition.ext_bool (i := b) <| by simp


/-- Cross two partitions by intersecting the left sets. -/
def inter (P Q : s.Bipartition) : s.Bipartition := P.cross Q true

@[simp]
lemma inter_true (P Q : s.Bipartition) : (P.inter Q) true = P true ∩ Q true := rfl

@[simp]
lemma inter_false (P Q : s.Bipartition) : (P.inter Q) false = P false ∪ Q false := rfl

/-- Cross two partitions by intersecting the right sets. -/
def union (P Q : s.Bipartition) : s.Bipartition := (P.symm.inter Q.symm).symm

@[simp]
lemma union_true (P Q : s.Bipartition) : (P.union Q) true = P true ∪ Q true := rfl

@[simp]
lemma union_false (P Q : s.Bipartition) : (P.union Q) false = P false ∩ Q false := rfl

@[simp]
lemma inter_symm (P Q : s.Bipartition) : (P.inter Q).symm = P.symm.union Q.symm := by
  simp [inter, union]

@[simp]
lemma union_symm (P Q : s.Bipartition) : (P.union Q).symm = P.symm.inter Q.symm :=
  Bipartition.ext rfl

@[simp]
lemma disjoint_inter_right (P : s.Bipartition) : Disjoint (P true ∩ t) (P false ∩ r) :=
  P.disjoint_true_false.mono inter_subset_left inter_subset_left

@[simp]
lemma disjoint_inter_left (P : s.Bipartition) : Disjoint (t ∩ P true) (r ∩ P false) :=
  P.disjoint_true_false.mono inter_subset_right inter_subset_right

@[simp]
lemma inter_ground_eq (P : s.Bipartition) (b) : P b ∩ s = P b :=
  inter_eq_self_of_subset_left P.subset

lemma union_inter_right' (P : s.Bipartition) (X : Set α) (b : Bool) :
    (P b ∩ X) ∪ (P (!b) ∩ X) = X ∩ s := by
  rw [← union_inter_distrib_right, P.union_bool_eq, inter_comm]

lemma union_inter_left' (P : s.Bipartition) (X : Set α) (b : Bool) :
    (X ∩ (P b)) ∪ (X ∩ (P !b)) = X ∩ s := by
  rw [← inter_union_distrib_left, P.union_bool_eq, inter_comm]

@[simp]
lemma union_inter_right (P : s.Bipartition) (t : Set α) (h : t ⊆ s) (b : Bool) :
    (P b ∩ t) ∪ ((P !b) ∩ t) = t := by
  rw [union_inter_right', inter_eq_self_of_subset_left h]

@[simp]
lemma union_inter_left (P : s.Bipartition) (h : t ⊆ s) (b : Bool):
    (t ∩ (P b)) ∪ (t ∩ (P !b)) = t := by
  rw [union_inter_left', inter_eq_self_of_subset_left h]

end Cross

end Bipartition
