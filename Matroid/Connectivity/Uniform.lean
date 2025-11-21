import Matroid.Connectivity.Higher
import Matroid.Paving

variable {α : Type*} {M : Matroid α} {X Y : Set α} {e f : α} {P : M.Partition} {k : ℕ∞}

open Set

namespace Matroid

lemma Paving.cyclicallyConnected (h : M.Paving) (hk : k < M.eRank) : M.CyclicallyConnected k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  refine cyclicallyConnected_iff_forall.2 fun P hPconn hP ↦ ?_
  rw [Partition.isCyclicSeparation_iff] at hP
  nth_grw 1 [h.eRank_le_eRk_add_one_of_dep hP.2, ← hPconn, ← h.eRelRk_ground_le_of_dep hP.1,
    ← P.compl_right, ← nullity_dual_eq _ _, ← P.eConn_right,
    M.eConn_add_nullity_dual_eq_eRk P.right] at hk
  exact hk.ne rfl

lemma Paving.cyclicallyConnected_of_verticallyConnected (h : M.Paving)
    (hconn : M.VerticallyConnected (k + 1)) (hk : k < M.eRank) : M.CyclicallyConnected (k + 1) := by
  refine cyclicallyConnected_iff_forall.2 fun P hPconn hP ↦ ?_
  rw [Partition.isCyclicSeparation_iff] at hP
  wlog hs : M.Spanning P.left generalizing P with aux
  · refine hconn.not_isVerticalSeparation (P := P) (by simpa) ?_
    rw [Partition.isVerticalSeparation_iff, ← not_spanning_iff, and_iff_right hs,
      ← not_spanning_iff]
    exact aux P.symm (by simpa) ⟨hP.2, hP.1⟩
  grw [← hPconn, ← P.eConn_left, hs.eConn_eq, P.compl_left,
    h.eRank_le_eRk_add_one_of_dep hP.2] at hk
  exact hk.ne rfl

lemma SparsePaving.tutteConnected_of_eRank_gt_eRank_dual_ge (h : M.SparsePaving)
    (h1 : k < M.eRank) (h2 : k ≤ M✶.eRank) : M.TutteConnected k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  rw [ENat.add_one_le_iff (by enat_to_nat)] at h2
  rw [tutteConnected_iff_verticallyConnected_cyclicallyConnected]
  · have h' := h.1.cyclicallyConnected h1
    have h'' := h.dual.1.cyclicallyConnected_of_verticallyConnected (by simpa) h2
    simp only [cyclicallyConnected_dual_iff] at h''
    exact ⟨h'', h'⟩
  rw [← eRank_add_eRank_dual]
  enat_to_nat!
  omega

lemma SparsePaving.tutteConnected_of_eRank_ge_eRank_dual_gt (h : M.SparsePaving)
    (h1 : k ≤ M.eRank) (h2 : k < M✶.eRank) : M.TutteConnected k :=
  by simpa using (h.dual.tutteConnected_of_eRank_gt_eRank_dual_ge h2 (by simpa)).dual
