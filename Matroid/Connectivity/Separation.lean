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

noncomputable abbrev econn (P : M.Partition) : ℕ∞ := M.localEConn P.1 P.2

@[simp] lemma econn_symm (P : M.Partition) : P.symm.econn = P.econn :=
  M.localEConn_comm _ _

lemma compl_left (P : M.Partition) : M.E \ P.1 = P.2 := by
  rw [← P.union_eq, union_diff_left, sdiff_eq_left]
  exact P.symm.disjoint

lemma compl_right (P : M.Partition) : M.E \ P.2 = P.1 := by
  rw [← symm_left, compl_left, symm_right]

lemma econn_eq_left (P : M.Partition) : P.econn = M.econn P.1 := by
  rw [econn, ← compl_left]

lemma econn_eq_right (P : M.Partition) : P.econn = M.econn P.2 := by
  rw [← P.econn_symm, P.symm.econn_eq_left, symm_left]

@[simp] lemma econn_dual (P : M.Partition) : P.dual.econn = P.econn := by
  rw [P.dual.econn_eq_left, M.econn_dual, P.dual_left, ← P.econn_eq_left]

@[simp] lemma econn_eq_zero_iff {P : M.Partition} : P.econn = 0 ↔ M.Skew P.1 P.2 :=
  M.localEConn_eq_zero P.left_subset_ground P.right_subset_ground

@[mk_iff]
structure IsTutteSep (P : M.Partition) (k : ℕ∞) : Prop where
  conn_lt : P.econn < k
  le_card_left : k ≤ P.1.encard
  le_card_right : k ≤ P.2.encard

lemma IsTutteSep.dual {k : ℕ∞} (h : P.IsTutteSep k) : P.dual.IsTutteSep k := by
  simpa [isTutteSep_iff] using h

@[simp] lemma isTutteSep_dual_iff {k : ℕ∞} : P.dual.IsTutteSep k ↔ P.IsTutteSep k := by
  simp only [isTutteSep_iff, econn_dual, dual_left, dual_right]

@[simp] lemma isTutteSep_ofDual_iff {P : M✶.Partition} {k : ℕ∞} :
    P.ofDual.IsTutteSep k ↔ P.IsTutteSep k := by
  rw [← isTutteSep_dual_iff, ofDual_dual]

lemma IsTutteSep.zero_lt (h : P.IsTutteSep k) : 0 < k :=
  pos_iff_ne_zero.mpr <| by rintro rfl; simpa using h.conn_lt

end Partition


/-- The partition of `M` given by a subset of `M.E` and its complement.  -/
@[simps] protected def partition (M : Matroid α) (A : Set α) (hA : A ⊆ M.E := by aesop_mat) :
    M.Partition where
  left := A
  right := M.E \ A
  disjoint :=  disjoint_sdiff_right
  union_eq := by rwa [union_diff_cancel]

@[simp] lemma econn_partition (hA : A ⊆ M.E) : (M.partition A).econn = M.econn A := by
  simp [econn, Matroid.partition]

lemma partition_dual (hA : A ⊆ M.E) : M✶.partition A hA = (M.partition A).dual := rfl

lemma Circuit.isTutteSep {C : Set α} (hC : M.Circuit C) (hfin : C.Finite)
    (hcard : 2 * C.encard ≤ M.E.encard) : (M.partition C).IsTutteSep C.encard := by
  simp only [Partition.isTutteSep_iff, econn_partition, partition_left,
    partition_right, inter_eq_self_of_subset_left hC.subset_ground, and_iff_right rfl.le]
  refine ⟨(M.econn_le_eRk C).trans_lt ?_, ?_⟩
  · rw [← hC.eRk_add_one_eq, ENat.lt_add_one_iff]
    rw [eRk_ne_top_iff]
    exact FinRk.of_finite M hfin
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
  simp only [TutteConnected, Partition.isTutteSep_iff, and_imp, connected_iff, ‹M.Nonempty›, true_and,
    show (2 : ℕ∞) = 1 + 1 by norm_num, ENat.add_one_le_iff (show 1 ≠ ⊤ by norm_num)]
  refine ⟨fun h e f he hf ↦ ?_, fun h k P hPk hkl hkr ↦ lt_of_not_le fun hle ↦ ?_⟩
  · contrapose! h
    use 1
    simp only [Nat.cast_one, ENat.lt_one_iff, Partition.econn_eq_zero_iff,
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

  simp only [Nat.cast_one, ENat.lt_one_iff, Partition.econn_eq_zero_iff, Partition.union_eq] at hPk
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
