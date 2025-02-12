import Matroid.Connectivity.Basic
import Matroid.Connectivity.Local
import Matroid.ForMathlib.Finset

open Set

namespace Matroid

section separation

variable {α : Type*} {M : Matroid α} {j k : ℕ∞} {a b : α} {A : Set α}

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

@[simps] protected def symm (P : M.Partition) : M.Partition where
  left := P.2
  right := P.1
  disjoint := P.disjoint.symm
  union_eq := by rw [← P.union_eq, union_comm]

@[simps] protected def dual (P : M.Partition) : M✶.Partition where
  left := P.1
  right := P.2
  disjoint := P.disjoint
  union_eq := P.union_eq

@[simps] protected def ofDual (P : M✶.Partition) : M.Partition where
  left := P.1
  right := P.2
  disjoint := P.disjoint
  union_eq := P.union_eq

@[simp] lemma dual_ofDual (P : M.Partition) : P.dual.ofDual = P := rfl

@[simp] lemma ofDual_dual (P : M✶.Partition) : P.ofDual.dual = P := rfl

@[simp, aesop unsafe 10% (rule_sets := [Matroid])]
protected lemma left_subset_ground (P : M.Partition) : P.1 ⊆ M.E := by
  rw [← P.union_eq]; apply subset_union_left

@[simp, aesop unsafe 10% (rule_sets := [Matroid])]
protected lemma right_subset_ground (P : M.Partition) : P.2 ⊆ M.E := by
  rw [← P.union_eq]; apply subset_union_right

noncomputable abbrev eConn (P : M.Partition) : ℕ∞ := M.eLocalConn P.1 P.2

@[simp] lemma eConn_symm (P : M.Partition) : P.symm.eConn = P.eConn :=
  M.eLocalConn_comm _ _

lemma compl_left (P : M.Partition) : M.E \ P.1 = P.2 := by
  rw [← P.union_eq, union_diff_left, sdiff_eq_left]
  exact P.symm.disjoint

lemma compl_right (P : M.Partition) : M.E \ P.2 = P.1 := by
  rw [← symm_left, compl_left, symm_right]

lemma eConn_eq_left (P : M.Partition) : P.eConn = M.eConn P.1 := by
  rw [eConn, ← compl_left]

lemma eConn_eq_right (P : M.Partition) : P.eConn = M.eConn P.2 := by
  rw [← P.eConn_symm, P.symm.eConn_eq_left, symm_left]

@[simp] lemma eConn_dual (P : M.Partition) : P.dual.eConn = P.eConn := by
  rw [P.dual.eConn_eq_left, M.eConn_dual, P.dual_left, ← P.eConn_eq_left]

@[simp] lemma eConn_eq_zero_iff {P : M.Partition} : P.eConn = 0 ↔ M.Skew P.1 P.2 :=
  M.eLocalConn_eq_zero P.left_subset_ground P.right_subset_ground

@[mk_iff]
structure IsTutteSep (P : M.Partition) (k : ℕ∞) : Prop where
  conn_lt : P.eConn < k
  le_card_left : k ≤ P.1.encard
  le_card_right : k ≤ P.2.encard

lemma IsTutteSep.dual {k : ℕ∞} (h : P.IsTutteSep k) : P.dual.IsTutteSep k := by
  simpa [isTutteSep_iff] using h

@[simp] lemma isTutteSep_dual_iff {k : ℕ∞} : P.dual.IsTutteSep k ↔ P.IsTutteSep k := by
  simp only [isTutteSep_iff, eConn_dual, dual_left, dual_right]

@[simp] lemma isTutteSep_ofDual_iff {P : M✶.Partition} {k : ℕ∞} :
    P.ofDual.IsTutteSep k ↔ P.IsTutteSep k := by
  rw [← isTutteSep_dual_iff, ofDual_dual]

lemma IsTutteSep.zero_lt (h : P.IsTutteSep k) : 0 < k :=
  pos_iff_ne_zero.mpr <| by rintro rfl; simpa using h.conn_lt

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

end Partition

/-- The partition of `M` given by a subset of `M.E` and its complement.  -/
@[simps] protected def partition (M : Matroid α) (A : Set α) (hA : A ⊆ M.E := by aesop_mat) :
    M.Partition where
  left := A
  right := M.E \ A
  disjoint :=  disjoint_sdiff_right
  union_eq := by rwa [union_diff_cancel]

@[simp] lemma eConn_partition (hA : A ⊆ M.E) : (M.partition A).eConn = M.eConn A := by
  simp [eConn, Matroid.partition]

lemma partition_dual (hA : A ⊆ M.E) : M✶.partition A hA = (M.partition A).dual := rfl

lemma Circuit.isTutteSep {C : Set α} (hC : M.Circuit C) (hfin : C.Finite)
    (hcard : 2 * C.encard ≤ M.E.encard) : (M.partition C).IsTutteSep C.encard := by
  simp only [Partition.isTutteSep_iff, eConn_partition, partition_left,
    partition_right, inter_eq_self_of_subset_left hC.subset_ground, and_iff_right rfl.le]
  refine ⟨(M.eConn_le_eRk C).trans_lt ?_, ?_⟩
  · rw [← hC.eRk_add_one_eq, ENat.lt_add_one_iff]
    rw [eRk_ne_top_iff]
    exact finRk_of_finite M hfin
  rwa [← encard_diff_add_encard_of_subset hC.subset_ground, two_mul,
    WithTop.add_le_add_iff_right] at hcard
  rwa [encard_ne_top_iff]

lemma Circuit.isTutteSep_finset {C : Finset α} (hC : M.Circuit C)
    (hcard : 2 * C.card ≤ M.E.encard) : (M.partition C).IsTutteSep C.card := by
  convert hC.isTutteSep (by simp) ?_ <;>
  simp [hcard]

lemma Cocircuit.isTutteSep {C : Set α} (hC : M.Cocircuit C) (hfin : C.Finite)
    (hcard : 2 * C.encard ≤ M.E.encard) : (M.partition C).IsTutteSep C.encard := by
  simpa [partition_dual] using hC.circuit.isTutteSep hfin hcard

lemma Cocircuit.isTutteSep_finset {C : Finset α} (hC : M.Cocircuit C)
    (hcard : 2 * C.card ≤ M.E.encard) : (M.partition C).IsTutteSep C.card := by
  convert hC.isTutteSep (by simp) ?_ <;>
  simp [hcard]

def TutteConnected (M : Matroid α) (k : ℕ∞) := ∀ ⦃j⦄ ⦃P : M.Partition⦄, P.IsTutteSep j → k ≤ j

lemma TutteConnected.le (h : M.TutteConnected k) {P : M.Partition} (hP : P.IsTutteSep j) : k ≤ j :=
  h hP

lemma TutteConnected.mono {k : ℕ∞} (h : M.TutteConnected k) (hjk : j ≤ k) : M.TutteConnected j :=
  fun _ _ hi ↦ hjk.trans <| h.le hi

lemma TutteConnected.dual {k : ℕ∞} (h : M.TutteConnected k) : M✶.TutteConnected k :=
  fun j P hP ↦ by simpa [hP] using h (j := j) (P := P.ofDual)

@[simp] lemma tutteConnected_dual_iff {k : ℕ∞} : M✶.TutteConnected k ↔ M.TutteConnected k :=
  ⟨fun h ↦ by simpa using h.dual, TutteConnected.dual⟩

@[simp] lemma tutteConnected_one (M : Matroid α) : M.TutteConnected 1 :=
  fun _ _ h ↦ Order.one_le_iff_pos.2 h.zero_lt

@[simp] lemma tutteConnected_zero (M : Matroid α) : M.TutteConnected 0 :=
  M.tutteConnected_one.mono <| zero_le _

@[simp] lemma tutteConnected_two_iff [M.Nonempty] : M.TutteConnected 2 ↔ M.Connected := by
  simp only [TutteConnected, Partition.isTutteSep_iff, and_imp, connected_iff, ‹M.Nonempty›,
    true_and, show (2 : ℕ∞) = 1 + 1 by norm_num, ENat.add_one_le_iff (show 1 ≠ ⊤ by norm_num)]
  refine ⟨fun h e f he hf ↦ ?_, fun h k P hPk hkl hkr ↦ lt_of_not_le fun hle ↦ ?_⟩
  · contrapose! h
    use 1
    simp only [Nat.cast_one, ENat.lt_one_iff, Partition.eConn_eq_zero_iff,
      one_le_encard_iff_nonempty, le_refl, and_true]
    set P := M.partition {z | M.ConnectedTo e z} (fun _ ↦ ConnectedTo.mem_ground_right)
    refine ⟨P, ?_, ⟨e, by simpa [P]⟩, ⟨f, by simp [P, h, hf]⟩⟩
    simp_rw [skew_iff_forall_circuit P.disjoint P.left_subset_ground, or_iff_not_imp_right,
      not_subset, ← P.compl_left, mem_diff, union_diff_self, not_and, not_not, forall_exists_index,
      and_imp]
    exact fun C hC _ a haC h' b hbC ↦
      ConnectedTo.trans (h' (hC.subset_ground haC)) (hC.mem_connectedTo_mem haC hbC)
  rw [le_iff_eq_or_lt, ENat.lt_one_iff, or_comm] at hle
  obtain rfl | rfl := hle
  · simp at hPk

  simp only [Nat.cast_one, ENat.lt_one_iff, Partition.eConn_eq_zero_iff, Partition.union_eq] at hPk
  simp only [Nat.cast_one, one_le_encard_iff_nonempty] at hkr hkl
  obtain ⟨e, he⟩ := hkl
  obtain ⟨f, hf⟩ := hkr
  obtain ⟨rfl, -⟩ | ⟨C, hC, heC, hfC⟩ := h (P.left_subset_ground he) (P.right_subset_ground hf)
  · simp [← P.compl_left, he] at hf
  obtain hl | hr := hPk.subset_or_subset_of_circuit hC (by simpa using hC.subset_ground)
  · rw [← P.compl_left] at hf
    exact hf.2 (hl hfC)
  rw [← P.compl_right] at he
  exact he.2 (hr heC)

lemma Circuit.encard_ge_of_tutteConnected {C : Set α} (hC : M.Circuit C)
    (hM : 2*k ≤ M.E.encard + 2) (hconn : M.TutteConnected k) : k ≤ C.encard := by
  obtain hinf | hfin := C.finite_or_infinite.symm
  · simp [hinf.encard_eq]
  refine le_of_not_lt fun hlt ↦ ?_
  have hle : C.encard + 1 ≤ k := by rwa [ENat.add_one_le_iff (by rwa [encard_ne_top_iff])]
  have hle' := (mul_le_mul_left' hle 2).trans hM
  rw [mul_add, mul_one, WithTop.add_le_add_iff_right (by norm_num)] at hle'
  exact hlt.not_le <| hconn (hC.isTutteSep hfin hle')

lemma TutteConnected.le_girth (h : M.TutteConnected k) (hk : 2*k ≤ M.E.encard + 2) :
    k ≤ M.girth := by
  simp_rw [le_girth_iff]
  exact fun C hC ↦ hC.encard_ge_of_tutteConnected hk h

lemma TutteConnected.loopless (h : M.TutteConnected 2) (hM : M.E.Nontrivial) : M.Loopless := by
  have : M.Nonempty := ⟨hM.nonempty⟩
  exact Connected.loopless (tutteConnected_two_iff.1 h) hM

lemma TutteConnected.simple (h : M.TutteConnected 3) (hM : 4 ≤ M.E.encard) : M.Simple := by
  simpa [← three_le_girth_iff, (show (2 : ℕ∞) * 3 = 4 + 2 by norm_num),
    WithTop.add_le_add_iff_right (show (2 : ℕ∞) ≠ ⊤ by norm_num), imp_iff_right hM] using h.le_girth

section Global

variable {X X' Y Y' : Set α} {P : M.Partition} {e : α}

@[mk_iff]
structure Partition.SepOf (P : M.Partition) (X Y : Set α) : Prop where
  subset_left : X ⊆ P.left
  subset_right : Y ⊆ P.right

lemma Partition.sepOf_iff_left (P : M.Partition) (hY : Y ⊆ M.E) :
    P.SepOf X Y ↔ X ⊆ P.left ∧ Disjoint Y P.left := by
  rw [sepOf_iff, ← P.compl_left, subset_diff, and_iff_right hY]

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
  rw [Partition.sepOf_iff_left _ hYE, disjoint_comm, partition_left _ _ hXE, and_iff_left hXY]


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

lemma Partition.SepOf.eConnBetween_le_of_inter (hP : P.SepOf (M.core X) (M.core Y)) :
    M.eConnBetween X Y ≤ P.eConn :=
  iInf_le_of_le ⟨P, hP⟩ rfl.le

lemma Partition.SepOf.eConnBetween_le (hP : P.SepOf X Y) :
    M.eConnBetween X Y ≤ P.eConn :=
  (hP.mono (M.core_subset X) (M.core_subset Y)).eConnBetween_le_of_inter

lemma le_eConnBetween_iff_forall_sepOf_core {k : ℕ∞} : k ≤ M.eConnBetween X Y ↔
    ∀ (P : M.Partition), P.SepOf (M.core X) (M.core Y) → k ≤ P.eConn := by
  simp [eConnBetween, le_iInf_iff, Subtype.forall]

lemma eConnBetween_eq_iInf (hXY : Disjoint X Y) (hX : X ⊆ M.E) (hY : Y ⊆ M.E) :
    M.eConnBetween X Y = ⨅ P : {P : M.Partition // P.SepOf X Y}, P.1.eConn := by
  simp only [eConnBetween, le_antisymm_iff, le_iInf_iff, Subtype.forall]
  refine ⟨fun P hP ↦ ?_, fun P hP ↦ ?_⟩
  · exact iInf_le_of_le ⟨P, hP.mono (M.core_subset X) (M.core_subset Y)⟩ rfl.le
  refine iInf_le_of_le ⟨M.partition ((P.left ∪ X) \ Y), ?_⟩ ?_
  · simpa [Partition.sepOf_iff_left _ hY, disjoint_sdiff_right, subset_diff]
  rw [eConn_partition, ← eConn_core, core_diff, core_union, ← M.core_core X,
    union_eq_self_of_subset_right (M.core_subset_core hP.1), sdiff_eq_left.2, eConn_core,
    P.eConn_eq_left]
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

noncomputable def connBetween (M : Matroid α) (X Y : Set α) : ℕ :=
  (M.eConnBetween X Y).toNat

lemma eConnBetween_symm (M : Matroid α) : M.eConnBetween X Y = M.eConnBetween Y X := by
  apply le_antisymm <;>
  exact le_iInf fun ⟨P, hP⟩ ↦ iInf_le_of_le ⟨P.symm, by simpa⟩ (by simp)

lemma eConnBetween_mono_left (M : Matroid α) (hX : X' ⊆ X) (Y : Set α) :
    M.eConnBetween X' Y ≤ M.eConnBetween X Y :=
  le_iInf fun ⟨P, hP⟩ ↦ iInf_le_of_le ⟨P, hP.mono_left (M.core_subset_core hX)⟩ rfl.le

lemma eConnBetween_mono_right (M : Matroid α) (X : Set α) (hY : Y' ⊆ Y) :
    M.eConnBetween X Y' ≤ M.eConnBetween X Y :=
  le_iInf fun ⟨P, hP⟩ ↦ iInf_le_of_le ⟨P, hP.mono_right (M.core_subset_core hY)⟩ rfl.le

lemma eConnBetween_mono (M : Matroid α) (hX : X' ⊆ X) (hY : Y' ⊆ Y) :
    M.eConnBetween X' Y' ≤ M.eConnBetween X Y :=
  (M.eConnBetween_mono_left hX _).trans <| M.eConnBetween_mono_right _ hY

-- lemma eConnBetween_of_mono {N M : Matroid α} (h : ∀ A, N.eConn A ≤ M.eConn A)
--     (hcore : ∀ A, N.core A ⊆ M.core A) {X Y : Set α} :
--     N.eConnBetween X Y ≤ M.eConnBetween X Y := by
--   simp only [eConnBetween, le_iInf_iff, Subtype.forall]
--   intro P hP

--   refine iInf_le_of_le ⟨N.partition (P.left ∩ N.E) inter_subset_right, ?_⟩ ?_
--   · rw [Partition.sepOf_iff_left _ (by simp)]
--     sorry
--     -- simp
--     -- rw [Partition.sepOf_iff_left _ (by simp), partition_left ..,
--     --   and_iff_left <| hP.disjoint.symm.mono (hcore Y) (hcore X)]
--   simp only [eConn_partition, eConn_core]
--   rw [P.eConn_eq_left]


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
      exact P.disjoint.symm.mono hP.2 inter_subset_left
    simp only [eConn_partition, eLocalConn_inter_ground_left, diff_inter_self_eq_diff,
      removeLoops_eLocalConn]
    rw [← removeLoops_eLocalConn, ← eConn_eq_eLocalConn, removeLoops_eConn, ← hP_eq,
      P.eConn_eq_left]
  obtain ⟨P, hP, hP_eq⟩ := M.removeLoops.exists_partition_eConn_eq_eConnBetween_core (by simpa)
  refine iInf_le_of_le ⟨M.partition P.left ?_, ?_⟩ ?_
  · exact P.left_subset_ground.trans M.removeLoops_restriction.subset
  · rw [Partition.sepOf_iff_left _ (by simp)]
    simp only [partition_left]
    simp only [removeLoops_core] at hP
    exact ⟨hP.1, hP.disjoint_left.symm⟩
  simp [← hP_eq, P.eConn_eq_left]

lemma eConnBetween_restrict_le (M : Matroid α) (X Y R : Set α) :
    (M ↾ R).eConnBetween X Y ≤ M.eConnBetween X Y := by

  rw [le_eConnBetween_iff_forall_sepOf_inter]
  intro P hP
  rw [← eConnBetween_inter_ground_left, ← eConnBetween_inter_ground_right, restrict_ground_eq]
  set P' := (P.restrict R).restrict M.E
  -- have hP' : P.SepOf (X ∩ M.E)
  refine (Partition.SepOf.eConnBetween_le (P := (P.restrict R).restrict M.E) ?_).trans ?_
  ·
  --   (M ↾ univ).eConnBetween X Y = M.eConnBetween X Y := by
  -- simp [le_antisymm_iff, le_eConnBetween_iff_forall_sepOf_inter]

-- lemma eConnBetween_restrict_univ (M : Matroid α) (X Y : Set α) :
--     (M ↾ univ).eConnBetween X Y = M.eConnBetween X Y := by
--   simp [le_antisymm_iff, le_eConnBetween_iff_forall_sepOf_inter]
  -- simp only [le_antisymm_iff, le_eConnBetween_iff, eLocalConn_restrict_eq, inter_univ]
  -- refine ⟨fun P hP ↦ ?_, fun P hP ↦ ?_⟩
  -- · refine (Partition.SepOf.eConnBetween_le (P := P.restrict univ) ?_).trans ?_
  --   · simp [Partition.SepOf, hP.1, hP.2.trans subset_union_left]
  --   rw [Partition.eConn_restrict_eq, inter_univ, inter_univ]

  --   -- set Q := Partition.setCompl (M ↾ univ) P.left with hQ

  --   -- -- have : Q.SepOf X Y := by
  --   -- --   simp [Partition.SepOf, Q, hP.1, hP.2.trans (diff_subset_compl M.E P.right)]
  --   -- refine (Partition.SepOf.eConnBetween_le (P := Q) ?_).trans ?_
  --   -- · rw [Partition.SepOf, Partition.setCompl_left, and_iff_right hP.1, ← Q.compl_left,
  --   --     restrict_ground_eq]
  --   --   refine hP.2.trans ?_
  --   --   simp only [Partition.setCompl_left, Q, ← P.compl_left]
  --   --   exact diff_subset_diff_left <| subset_univ _
  --   -- rw [Partition.eConn, eLocalConn_restrict_univ_eq, Partition.eConn,
  --   --   ← eLocalConn_inter_ground_right]
  --   -- exact M.eLocalConn_mono rfl.le <| by
  --   --   rw [Partition.setCompl_right, ← diff_eq_compl_inter, P.compl_left]
  -- let P' := (P.restrict M.E).copy (show _ = M by simp)
  -- have hP' : P'.eConn = M.eLocalConn P.left P.right := by simp [P']
  -- have hP'sep :
  -- refine (Partition.SepOf.eConnBetween_le (P := P) ?_).trans ?_



-- lemma eConnBetween_delete_le (M : Matroid α) (X Y D : Set α) :
--     (M \)

lemma foo [M.RankFinite] (M : Matroid α) (X Y : Set α) (he : e ∈ M.E) (heX : e ∉ X) (heY : e ∉ Y) :
    (M ／ e).eConnBetween X Y = M.eConnBetween X Y ∨
    (M ＼ e).eConnBetween X Y = M.eConnBetween X Y := by
  _
