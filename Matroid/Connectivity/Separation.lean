import Matroid.Connectivity.Basic
import Matroid.Connectivity.Local

open Set

namespace Matroid

section separation

variable {α : Type*} {M : Matroid α} {k : ℕ} {P : Set α → Prop} {a b : α}

protected structure Partition (M : Matroid α) where
  left : Set α
  right : Set α
  disjoint : Disjoint left right
  union_eq : left ∪ right = M.E

@[simps] def Partition.symm (P : M.Partition) : M.Partition where
  left := P.2
  right := P.1
  disjoint := P.disjoint.symm
  union_eq := by rw [← P.union_eq, union_comm]

@[simps] def Partition.dual (P : M.Partition) : M✶.Partition where
  left := P.1
  right := P.2
  disjoint := P.disjoint
  union_eq := P.union_eq

@[simps] def Partition.of_subset (A : Set α) (hX : A ⊆ M.E := by aesop_mat) : M.Partition where
  left := A
  right := M.E \ A
  disjoint := disjoint_sdiff_right
  union_eq := by simp [hX]

@[simp, aesop unsafe 10% (rule_sets := [Matroid])]
lemma Partition.left_subset_ground (P : M.Partition) : P.1 ⊆ M.E := by
  rw [← P.union_eq]; apply subset_union_left

@[simp, aesop unsafe 10% (rule_sets := [Matroid])]
lemma Partition.right_subset_ground (P : M.Partition) : P.2 ⊆ M.E := by
  rw [← P.union_eq]; apply subset_union_right

noncomputable abbrev Partition.conn (P : M.Partition) : ℕ∞ := M.localConn P.1 P.2

lemma Partition.compl_left (P : M.Partition) : M.E \ P.1 = P.2 := by
  simp [← P.union_eq, P.disjoint.symm]

lemma Partition.compl_right (P : M.Partition) : M.E \ P.2 = P.1 := by
  simp [← P.union_eq, P.disjoint]

@[simp] lemma Partition.conn_symm (P : M.Partition) : P.symm.conn = P.conn :=
  M.localConn_comm _ _

@[simp] lemma Partition.conn_dual (P : M.Partition) : P.dual.conn = P.conn := by
  simp only [conn, dual, ← P.compl_left]
  exact Eq.symm <| M.conn_dual P.left

@[simp] lemma Partition.conn_eq_zero_iff {P : M.Partition} : P.conn = 0 ↔ M.Skew P.1 P.2 :=
  M.localConn_eq_zero P.left_subset_ground P.right_subset_ground

def Partition.IsTutteSep (P : M.Partition) (k : ℕ) :=
  P.conn < k ∧ k ≤ P.1.encard ∧ k ≤ P.2.encard

lemma connected_iff_not_exists_tutteSep [M.Nonempty] :
    M.Connected ↔ ¬ ∃ (P : M.Partition), P.IsTutteSep 1 := by
  rw [iff_not_comm]
  simp only [Connected, show M.Nonempty by assumption, true_and, not_forall, Classical.not_imp,
    exists_and_left, exists_prop, exists_and_left, Partition.IsTutteSep, Nat.cast_one,
    ENat.lt_one_iff, one_le_encard_iff_nonempty]
  simp only [Partition.conn_eq_zero_iff, and_self,
    skew_iff_forall_circuit (Partition.disjoint _) (Partition.left_subset_ground _)
      (Partition.right_subset_ground _)]

  refine ⟨fun ⟨P, ⟨hc, hA, hB⟩⟩ ↦ ?_, fun ⟨x, y, hy, hx, h⟩ ↦ ?_⟩
  · obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hB
    refine ⟨a, b, by simp [P.union_eq.symm, hb], by simp [P.union_eq.symm, ha], fun hconn ↦ ?_⟩
    obtain ⟨C, hC, haC, hbC⟩ := hconn.exists_circuit_of_ne (P.disjoint.ne_of_mem ha hb)
    obtain (hCA | hCB) := hc C hC (hC.subset_ground.trans_eq P.union_eq.symm)
    · exact P.disjoint.ne_of_mem (hCA hbC) hb rfl
    exact P.symm.disjoint.ne_of_mem (hCB haC) ha rfl
  refine ⟨Partition.of_subset {z | M.ConnectedTo x z} (fun z hz ↦ hz.mem_ground_right),
    ?_, ⟨x, by simpa⟩, ⟨y, by simp [hy, h]⟩⟩
  simp only [Partition.of_subset_left, Partition.of_subset_right, union_diff_self]
  rintro C hC -
  obtain ⟨e, he⟩ := hC.nonempty
  by_cases hex : M.ConnectedTo x e
  · refine .inl (fun y hy ↦ hex.trans <| hC.mem_connectedTo_mem he hy )
  refine .inr fun z hzC ↦ ⟨hC.subset_ground hzC, fun (hz : M.ConnectedTo x z) ↦ ?_⟩
  exact hex <| hz.trans <| hC.mem_connectedTo_mem hzC he




end separation
