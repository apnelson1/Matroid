import Matroid.Connectivity.Separation.Tutte

variable {α : Type*} {M : Matroid α} {j k : ℕ∞} {d k : ℕ∞} {A X Y : Set α} {P : M.Separation}
  {b : Bool} {f g : ℕ∞ → ℕ∞}

open Set Matroid Matroid.Separation Function

namespace Matroid

variable {i m n a b : ℕ∞}


/-- `M` is internally `k`-connected if it is `(0, 0, ..., 1, ⊤, ⊤, ⊤, ...)-offset-connected,
where the `1` occurs in position `k - 2`.
That is, every separation of order `k - 3` or less has one side with connectivity equal to
its cardinality, and each separation of order `k - 2` has a side with cardinality at most `k-1`. -/
def InternallyConnected (M : Matroid α) (k : ℕ∞) :=
  M.SeqConnected (fun M X ↦ M.nullity X + M✶.nullity X) (indicator
    {i | k < i + 1 + 1} ⊤ + indicator {i ≠ ⊤ | k = i + 1 + 1} 1)

@[simp]
lemma internallyConnected_zero (M : Matroid α) : M.InternallyConnected 0 := by
  simp [InternallyConnected, SeqConnected, PredConnected]

@[simp]
lemma internallyConnected_one (M : Matroid α) : M.InternallyConnected 1 := by
  simp [InternallyConnected, SeqConnected, PredConnected]

lemma internallyConnected_of_le_one (M : Matroid α) (hk : k ≤ 1) : M.InternallyConnected k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one
  · simp
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one
  · simp
  simp at hk

lemma InternallyConnected.tutteConnected (h : M.InternallyConnected (k + 1)) :
    M.TutteConnected k := by
  rw [tutteConnected_iff_seqConnected']
  refine SeqConnected.mono_right h fun n ↦ ?_
  obtain rfl | hne := eq_or_ne n ⊤
  · simp [indicator_apply]
  obtain rfl | hnk := eq_or_ne (n + 1) k
  · simp [hne, add_assoc]
  obtain hlt | hgt := lt_or_ge k (n + 1)
  · simp [indicator_apply, hlt, hlt.trans_le le_self_add]
  simp [indicator_apply, hgt.not_gt, hnk.symm]

@[simp]
lemma internallyConnected_dual_iff : M✶.InternallyConnected k ↔ M.InternallyConnected k :=
  seqConnected_dual_iff_of_forall (fun _ _ ↦ by simp [add_comm])

lemma TutteConnected.InternallyConnected (h : M.TutteConnected k) : M.InternallyConnected k :=
  (tutteConnected_iff_seqConnected'.1 h).mono_right fun n ↦ by simp

lemma InternallyConnected.exists_indep_coindep_of_eConn_lt (h : M.InternallyConnected (k + 1))
    (hP : P.eConn + 1 < k) : ∃ i, M.Indep (P i) ∧ M.Coindep (P i) := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp at hP
  exact h.tutteConnected.exists_indep_coindep (P := P) (Order.le_of_lt_add_one hP)

-- lemma InternallyConnected.foo (hk : k ≠ ⊤) : M.InternallyConnected (k + 1) ↔
--     M.TutteConnected k ∧ ∀ (P : M.Separation), P.eConn + 1 = k → P.IsTutteSeparation →
--     ∃ i, M.IsCircuit (P i) ∨ M.IsCocircuit (P i) := by
--   obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
--   have hktop : k ≠ ⊤ := by simpa using hk

--   refine ⟨fun h ↦ ⟨h.tutteConnected, fun P hPconn hP ↦ ?_⟩, fun h ↦ ?_⟩
--   · obtain rfl : P.eConn = k := by simpa using hPconn
--     obtain ⟨i, hi⟩ := BiConnected.exists_encard_le h P
--     have hle : (P i).encard ≤ P.eConn + 1 := by simpa [hktop] using hi
--     clear hi h hPconn hk

/-- If `P` is a separation of connectivity `k - 1` in an internally `(k + 1)`-connected matroid,
then one side of `P` is either an independent, coindependent `(k - 1)`-set,
or a `k`-set that is a circuit or cocircuit. -/
lemma InternallyConnected.exists_of_eConn_eq (hconn : M.InternallyConnected (k + 1))
    (hk : k ≠ ⊤) (hP : P.eConn + 1 = k) :
    ∃ i, ((P i).encard + 1 = k ∧ M.Indep (P i) ∧ M.Coindep (P i)) ∨
    ((P i).encard = k ∧ (M.IsCircuit (P i) ∨ M.IsCocircuit (P i))) := by
  obtain rfl := hP
  obtain ⟨i, hi⟩ := SeqConnected.exists_encard_le hconn P
  use i
  have htop : P.eConn ≠ ⊤ := by simpa using hk
  have hle : (P i).encard ≤ P.eConn + 1 := by simpa [htop] using hi
  rw [← M.eConn_add_nullity_add_nullity_dual (P i), add_assoc, P.eConn_eq,
    ENat.add_le_add_iff_left htop, ENat.le_one_iff_eq_zero_or_eq_one,
    add_eq_zero, nullity_eq_zero, nullity_eq_zero] at hle
  simp_rw [← M.eConn_add_nullity_add_nullity_dual (P i), P.eConn_eq, add_assoc,
    ENat.add_eq_add_left_iff, htop, or_false, ← add_assoc, ENat.add_eq_right_iff, add_eq_zero,
    nullity_eq_zero, ENat.one_ne_top, or_false, and_self]
  refine Or.imp id (fun h ↦ ⟨h, ?_⟩) hle
  clear hle hi hk
  wlog h0 : M✶.nullity (P i) = 0 generalizing M P with aux
  · have h0' : M.nullity (P i) = 0 := by enat_to_nat!; lia
    simpa [or_comm] using aux (P := P.dual) (by simpa) (by simpa) (by simpa [add_comm])
      (by simpa using h0')
  have hrw : (P i).encard = P.eConn + 1 := by
    rw [← M.eConn_add_nullity_add_nullity_dual (P i), add_assoc, h, P.eConn_eq]
  rw [h0, add_zero] at h
  have hdep : M.Dep (P i) := by simp [← not_indep_iff, ← nullity_eq_zero, h]
  have hg := hconn.tutteConnected.girth_ge_of_exists_eConn_ge ⟨P, rfl.le⟩
  obtain ⟨C, hCP, hC⟩ := hdep.exists_isCircuit_subset
  rw [← Finite.eq_of_subset_of_encard_le' ?_ hCP]
  · exact .inl hC
  · grw [hrw, ← hC.girth_le_card, hg]
  grw [← encard_lt_top_iff, hrw]
  simpa [lt_top_iff_ne_top]

lemma InternallyConnected.exists_encard_le_of_eConn_le (h : M.InternallyConnected (k + 1))
    (hP : P.eConn + 1 ≤ k) : ∃ i, (P i).encard ≤ k := by
  obtain ⟨i, hi⟩ := SeqConnected.exists_encard_le h P
  by_cases htop : P.eConn = ⊤
  · obtain rfl : k = ⊤ := by simpa [htop] using hP
    simp
  obtain rfl | hlt := hP.eq_or_lt
  · have h' : (P i).encard ≤ P.eConn + 1 := by simpa [indicator_apply, htop, hP.not_gt] using hi
    exact ⟨i, h'.trans (by simp)⟩
  have hle : (P i).encard ≤ P.eConn := by simpa [hP.not_gt, htop, hlt.ne.symm] using hi
  refine ⟨i, ?_⟩
  grw [hle, ← hP, ← le_self_add]

lemma InternallyConnected.exists_isParallel_or_isParallel_dual_of_eConn_eq_one
    (hM : M.InternallyConnected 3) (P : M.Separation) (hP : P.eConn = 1) : ∃ i,
    ((P i).Subsingleton) ∨ ∃ e f, e ≠ f ∧ P i = {e,f} ∧ (M.Parallel e f ∨ M✶.Parallel e f) := by
  rw [show (3 : ℕ∞) = 1 + 1 + 1 from rfl] at hM
  obtain ⟨i, h1 | h2⟩ := hM.exists_of_eConn_eq (by simp) (by simpa)
  · refine ⟨i, .inl ?_⟩
    rw [← encard_le_one_iff_subsingleton, ← ENat.add_le_add_iff_right (k := 1) (by simp), ← h1.1]
  rw [one_add_one_eq_two, encard_eq_two] at h2
  obtain ⟨⟨e, f, hef, h_eq⟩, hc⟩ := h2
  refine ⟨i, .inr ⟨e, f, hef, h_eq, Or.imp ?_ ?_ hc⟩⟩ <;>
  simp [h_eq, parallel_iff_isCircuit hef]


--   refine ⟨fun h ↦ ⟨h.tutteConnected, fun P hP ↦ ?_⟩, fun h ↦ ?_⟩
--   ·
