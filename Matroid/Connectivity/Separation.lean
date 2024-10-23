import Matroid.Connectivity.Basic
import Matroid.Connectivity.Local
import Matroid.ForMathlib.Finset

open Set

namespace Matroid

section separation

variable {α : Type*} {M : Matroid α} {j k : ℕ} {a b : α}

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

@[simps] protected def ofSet (M : Matroid α) (A : Set α) : M.Partition where
  left := A ∩ M.E
  right := M.E \ A
  disjoint :=  disjoint_sdiff_right.mono_left inter_subset_left
  union_eq := by rw [inter_comm, inter_union_diff]

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

@[simp] lemma econn_ofSet (M : Matroid α) (A : Set α) :
    (Partition.ofSet M A).econn = M.econn A := by
  simp [econn]

lemma ofSet_dual (M : Matroid α) (A : Set α) :
    (Partition.ofSet M✶ A) = (Partition.ofSet M A).dual := rfl

@[mk_iff]
structure IsTutteSep (P : M.Partition) (k : ℕ) : Prop where
  conn_lt : P.econn < k
  le_card_left : k ≤ P.1.encard
  le_card_right : k ≤ P.2.encard

lemma IsTutteSep.dual (h : P.IsTutteSep k) : P.dual.IsTutteSep k := by
  simpa [isTutteSep_iff] using h

@[simp] lemma isTutteSep_dual_iff : P.dual.IsTutteSep k ↔ P.IsTutteSep k := by
  simp only [isTutteSep_iff, econn_dual, dual_left, dual_right]

@[simp] lemma isTutteSep_ofDual_iff {P : M✶.Partition} :
    P.ofDual.IsTutteSep k ↔ P.IsTutteSep k := by
  rw [← isTutteSep_dual_iff, ofDual_dual]

lemma IsTutteSep.zero_lt (h : P.IsTutteSep k) : 0 < k := by
  rw [zero_lt_iff]
  rintro rfl
  simpa using h.conn_lt

end Partition

lemma Circuit.isTutteSep {C : Finset α} (hC : M.Circuit C) (hcard : 2 * C.card ≤ M.E.encard) :
    (Partition.ofSet M C).IsTutteSep C.card := by
  suffices M.econn ↑C < ↑C.card ∧ ↑C.card ≤ (M.E \ ↑C).encard by
    simpa [Partition.isTutteSep_iff, inter_eq_self_of_subset_left hC.subset_ground]
  refine ⟨(M.econn_le_er C).trans_lt ?_, ?_⟩
  · rw [← Finset.cast_r_eq, ← hC.r_add_one_eq, Nat.cast_lt]
    apply lt_add_one
  rwa [← encard_diff_add_encard_of_subset hC.subset_ground, two_mul,
    encard_coe_eq_coe_finsetCard, WithTop.add_le_add_iff_right] at hcard
  rw [← encard_coe_eq_coe_finsetCard, encard_ne_top_iff]
  exact C.finite_toSet

lemma Cocircuit.isTutteSep {C : Finset α} (hC : M.Cocircuit C) (hcard : 2 * C.card ≤ M.E.encard) :
    (Partition.ofSet M C).IsTutteSep C.card := by
  simpa [Partition.ofSet_dual] using hC.circuit.isTutteSep hcard

def TutteConnected (M : Matroid α) (k : ℕ) := ∀ ⦃j : ℕ⦄ ⦃P : M.Partition⦄, P.IsTutteSep j → k ≤ j

lemma TutteConnected.le (h : M.TutteConnected k) {P : M.Partition} (hP : P.IsTutteSep j) : k ≤ j :=
  h hP

lemma TutteConnected.mono (h : M.TutteConnected k) (hjk : j ≤ k) : M.TutteConnected j :=
  fun _ _ hi ↦ hjk.trans <| h.le hi

lemma TutteConnected.dual (h : M.TutteConnected k) : M✶.TutteConnected k :=
  fun j P hP ↦ by simpa [hP] using h (j := j) (P := P.ofDual)

lemma tutteConnected_dual_iff : M✶.TutteConnected k ↔ M.TutteConnected k :=
  ⟨fun h ↦ by simpa using h.dual, TutteConnected.dual⟩

@[simp] lemma tutteConnected_one (M : Matroid α) : M.TutteConnected 1 :=
  fun _ _ h ↦ h.zero_lt

@[simp] lemma tutteConnected_zero (M : Matroid α) : M.TutteConnected 0 :=
  M.tutteConnected_one.mono <| zero_le _

@[simp] lemma tutteConnected_two_iff [M.Nonempty] : M.TutteConnected 2 ↔ M.Connected := by
  simp only [TutteConnected, Partition.isTutteSep_iff, and_imp, Connected, ‹M.Nonempty›, true_and,
    show 2 = 1 + 1 by norm_num, Nat.add_one_le_iff]
  refine ⟨fun h e f he hf ↦ ?_, fun h k P hPk hkl hkr ↦ lt_of_not_le fun hle ↦ ?_⟩
  · contrapose! h
    use 1
    simp only [Nat.cast_one, ENat.lt_one_iff, Partition.econn_eq_zero_iff,
      one_le_encard_iff_nonempty, le_refl, and_true]
    set P := Partition.ofSet M {z | M.ConnectedTo e z}
    refine ⟨P, ?_, ⟨e, by simpa [P]⟩, ⟨f, by simp [P, h, hf]⟩⟩
    simp_rw [skew_iff_forall_circuit P.disjoint P.left_subset_ground, or_iff_not_imp_right,
      not_subset, ← P.compl_left, mem_diff, union_diff_self, not_and, not_not, forall_exists_index,
      and_imp]
    exact fun C hC _ a haC h' b hbC ↦
      ⟨ConnectedTo.trans (h' (hC.subset_ground haC)).1 <| .inr ⟨C, hC, haC, hbC⟩,
      (hC.subset_ground hbC)⟩

  obtain rfl | rfl := Nat.le_one_iff_eq_zero_or_eq_one.1 hle
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

lemma TutteConnected.le_girth (h : M.TutteConnected k) (hk : 2*k ≤ M.E.encard + 2) :
    k ≤ M.girth := by
  simp_rw [le_girth_iff, coe_le_encard_iff]
  refine fun C hC hfin ↦ le_of_not_lt fun hlt ↦ ?_
  rw [← hfin.coe_toFinset] at hC
  refine (h <| hC.isTutteSep ?_).not_lt <| by rwa [← ncard_eq_toFinset_card _ hfin]
  rw [Nat.lt_iff_add_one_le] at hlt
  rw [← ncard_eq_toFinset_card _ hfin]
  have e1 : (2 : ℕ∞) * (C.ncard + 1) ≤ 2 * ↑k :=
    mul_le_mul_left' (by rwa [← Nat.cast_one (R := ℕ∞), ← Nat.cast_add, Nat.cast_le]) _
  have := e1.trans hk
  rwa [mul_add, mul_one, WithTop.add_le_add_iff_right (by simp)] at this

lemma TutteConnected.loopless (h : M.TutteConnected k) (hk : 2 ≤ k) (hM : M.E.Nontrivial) :
    M.Loopless := by
  have : M.Nonempty := ⟨hM.nonempty⟩
  exact Connected.loopless (tutteConnected_two_iff.1 (h.mono hk)) hM

lemma TutteConnected.simple (h : M.TutteConnected 3) (hM : 4 ≤ M.E.encard) : M.Simple := by
  rw [← three_le_girth_iff]
  have h := h.le_girth
  rwa [(show (2 : ℕ∞) * (3 : ℕ) = 4 + 2 by norm_num), WithTop.add_le_add_iff_right (by simp),
    imp_iff_right hM, Nat.cast_ofNat] at h
