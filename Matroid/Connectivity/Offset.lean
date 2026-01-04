import Matroid.Connectivity.Vertical
import Mathlib.Algebra.Order.Group.Indicator

variable {α : Type*} {M : Matroid α} {j k : ℕ∞} {d k : ℕ∞} {A X Y : Set α} {P : M.Separation}
  {b : Bool} {f g : ℕ∞ → ℕ∞}

open Set Matroid Matroid.Separation Function

namespace Matroid.Separation

def IsOffsetSeparation (P : M.Separation) (f : ℕ∞ → ℕ∞) :=
  P.IsPredSeparation (fun _ M X ↦ M.nullity X + M✶.nullity X ≤ f (M.eConn X))

lemma IsOffsetSeparation_mono {f g : ℕ∞ → ℕ∞} (h : P.IsOffsetSeparation f) (hfg : ∀ n, g n ≤ f n) :
    P.IsOffsetSeparation g :=
  fun i h' ↦ h i (h'.trans (hfg _))

@[simp]
lemma isOffsetSeparation_zero : P.IsOffsetSeparation 0 ↔ P.IsTutteSeparation := by
  simp only [IsOffsetSeparation, Pi.zero_apply, nonpos_iff_eq_zero, add_eq_zero,
    nullity_eq_zero, isPredSeparation_iff, not_and, dual_ground,
    Separation.subset_ground, not_indep_iff, dep_dual_iff]

lemma IsOffsetSeparation.dual (h : P.IsOffsetSeparation f) : P.dual.IsOffsetSeparation f :=
  IsPredSeparation.dual (by simp [add_comm]) h

lemma IsOffsetSeparation.of_dual {P : M✶.Separation} (h : P.IsOffsetSeparation f) :
    P.ofDual.IsOffsetSeparation f :=
  IsPredSeparation.of_dual (by simp [add_comm]) h

lemma isOffsetSeparation_dual_iff : P.dual.IsOffsetSeparation f ↔ P.IsOffsetSeparation f :=
  isPredSeparation_dual_iff (by simp [add_comm])

end Separation

variable {i m n a b : ℕ∞}

/-- If `f` is a sequence of numbers, then `M` is `f`-offset-connected if each separation `P`
of order `k` has one side of cardinality at most `k + f k`.
This corresponds to Tutte connectivity when `f = (0, 0, ..., 0, ⊤, ⊤, ...)`,
and to internal connectivity when `f = (0, 0, ..., 0, 1, ⊤, ⊤, ...)`.
(For slightly nicer behaviour in the case where `k = ⊤`,
we phrase the definition in terms of nullity rather than cardinality. ) -/
def OffsetConnected (M : Matroid α) (f : ℕ∞ → ℕ∞) :=
    M.PredConnected (fun _ k M X ↦ M.nullity X + M✶.nullity X ≤ f k)

lemma OffsetConnected.exists (h : M.OffsetConnected f) (P : M.Separation) :
    ∃ i, M.nullity (P i) + M✶.nullity (P i) ≤ f P.eConn := by
  simpa using h P

lemma OffsetConnected.exists_encard_le (h : M.OffsetConnected f) (P : M.Separation) :
    ∃ i, (P i).encard ≤ P.eConn + f P.eConn := by
  obtain ⟨i, hi⟩ := h.exists P
  refine ⟨i, ?_⟩
  grw [← M.eConn_add_nullity_add_nullity_dual (P i), add_assoc, hi, P.eConn_eq]

lemma offsetConnected_iff_exists : M.OffsetConnected f ↔
    ∀ (P : M.Separation), ∃ i, M.nullity (P i) + M✶.nullity (P i) ≤ f P.eConn := Iff.rfl

lemma offsetConnected_iff_exists_encard_le (hf : f ⊤ = ⊤) : M.OffsetConnected f ↔
    ∀ (P : M.Separation), ∃ i, (P i).encard ≤ P.eConn + f P.eConn := by
  refine ⟨OffsetConnected.exists_encard_le, fun h P ↦ (?_ : ∃ i, _ ≤ _)⟩
  obtain ⟨i, hi⟩ := h P
  obtain htop | htop := eq_or_ne P.eConn ⊤
  · simp [htop, hf]
  exact ⟨i, by rwa [← ENat.add_le_add_iff_left htop, ← add_assoc, ← P.eConn_eq i,
    M.eConn_add_nullity_add_nullity_dual (P i), P.eConn_eq]⟩

lemma OffsetConnected.dual (h : M.OffsetConnected f) : M✶.OffsetConnected f := by
  rw [offsetConnected_iff_exists] at h ⊢
  intro P
  obtain ⟨i, hi⟩ := h P.ofDual
  exact ⟨i, by simpa [add_comm] using hi⟩

lemma OffsetConnected.of_dual (h : M✶.OffsetConnected f) : M.OffsetConnected f := by
  simpa using h.dual

@[simp]
lemma offsetConnected_dual_iff : M✶.OffsetConnected f ↔ M.OffsetConnected f :=
  ⟨OffsetConnected.of_dual, OffsetConnected.dual⟩

lemma OffsetConnected.mono (h : M.OffsetConnected f) (hfg : f ≤ g) : M.OffsetConnected g := by
  intro P
  obtain ⟨i, hP⟩ := h.exists P
  exact ⟨i, hP.trans <| hfg P.eConn⟩

@[simp]
lemma offsetConnected_top (M : Matroid α) : M.OffsetConnected ⊤ := by
  simp [OffsetConnected, PredConnected]

lemma tutteConnected_iff_offsetConnected :
    M.TutteConnected (k + 1) ↔ M.OffsetConnected (indicator {i | k < i + 1} ⊤) := by
  refine ⟨fun h P ↦ ?_, fun h P ↦ ?_⟩
  · obtain hlt | hle := lt_or_ge k (P.eConn + 1)
    · simp [hlt]
    simpa [-Bool.exists_bool, hle, ← not_isTutteSeparation_iff_exists] using
      h.not_isTutteSeparation hle
  obtain hlt | hle := lt_or_ge k (P.eConn + 1)
  · simp [hlt.not_ge]
  obtain ⟨i, hi⟩ := h.exists P
  exact ⟨i, by simpa [hle] using hi⟩

lemma tutteConnected_iff_offsetConnected' :
    M.TutteConnected k ↔ M.OffsetConnected (indicator {i | k < i + 1 + 1} ⊤) := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one <;>
  simp [tutteConnected_iff_offsetConnected]

/-- `M` is internally `k`-connected if it is `(0, 0, ..., 1, ⊤, ⊤, ⊤, ...)-offset-connected,
where the `1` occurs in position `k - 2`.
That is, every separation of order `k - 3` or less has one side with connectivity equal to
its cardinality, and every separation of order `k-2` has one side with cardinality at most `k-1`. -/
def InternallyConnected (M : Matroid α) (k : ℕ∞) :=
  M.OffsetConnected (indicator {i | k < i + 1 + 1} ⊤ + indicator {i ≠ ⊤ | k = i + 1 + 1} 1)

@[simp]
lemma internallyConnected_zero (M : Matroid α) : M.InternallyConnected 0 := by
  simp [InternallyConnected, OffsetConnected, PredConnected]

@[simp]
lemma internallyConnected_one (M : Matroid α) : M.InternallyConnected 1 := by
  simp [InternallyConnected, OffsetConnected, PredConnected]

lemma internallyConnected_of_le_one (M : Matroid α) (hk : k ≤ 1) : M.InternallyConnected k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one
  · simp
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one
  · simp
  simp at hk

lemma InternallyConnected.tutteConnected (h : M.InternallyConnected (k + 1)) :
    M.TutteConnected k := by
  rw [tutteConnected_iff_offsetConnected']
  refine OffsetConnected.mono h fun n ↦ ?_
  obtain rfl | hne := eq_or_ne n ⊤
  · simp [indicator_apply]
  obtain rfl | hnk := eq_or_ne (n + 1) k
  · simp [hne, add_assoc]
  obtain hlt | hgt := lt_or_ge k (n + 1)
  · simp [indicator_apply, hlt, hlt.trans_le le_self_add]
  simp [indicator_apply, hgt.not_gt, hnk.symm]

@[simp]
lemma internallyConnected_dual_iff : M✶.InternallyConnected k ↔ M.InternallyConnected k :=
  offsetConnected_dual_iff

lemma TutteConnected.InternallyConnected (h : M.TutteConnected k) : M.InternallyConnected k :=
  (tutteConnected_iff_offsetConnected'.1 h).mono fun n ↦ by simp

lemma InternallyConnected.exists_indep_coindep_of_eConn_lt (h : M.InternallyConnected (k + 1))
    (hP : P.eConn + 1 < k) : ∃ i, M.Indep (P i) ∧ M.Coindep (P i) := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp at hP
  exact h.tutteConnected.exists_indep_coindep (P := P) (Order.le_of_lt_add_one hP)

lemma InternallyConnected.foo (hk : k ≠ ⊤) : M.InternallyConnected (k + 1) ↔
    M.TutteConnected k ∧ ∀ (P : M.Separation), P.eConn + 1 = k → P.IsTutteSeparation →
    ∃ i, M.IsCircuit (P i) ∨ M.IsCocircuit (P i) := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  have hktop : k ≠ ⊤ := by simpa using hk

  refine ⟨fun h ↦ ⟨h.tutteConnected, fun P hPconn hP ↦ ?_⟩, fun h ↦ ?_⟩
  · obtain rfl : P.eConn = k := by simpa using hPconn
    obtain ⟨i, hi⟩ := OffsetConnected.exists_encard_le h P
    have hle : (P i).encard ≤ P.eConn + 1 := by simpa [hktop] using hi
    clear hi h hPconn hk




/-- If `P` is a separation of connectivity `k - 1` in an internally `(k + 1)`-connected matroid,
then one side of `P` is either an independent, coindependent `(k - 1)`-set,
or a `k`-set that is a circuit or cocircuit. -/
lemma InternallyConnected.exists_of_eConn_eq (hconn : M.InternallyConnected (k + 1))
    (hk : k ≠ ⊤) (hP : P.eConn + 1 = k) :
    ∃ i, ((P i).encard + 1 = k ∧ M.Indep (P i) ∧ M.Coindep (P i)) ∨
    ((P i).encard = k ∧ (M.IsCircuit (P i) ∨ M.IsCocircuit (P i))) := by
  obtain rfl := hP
  obtain ⟨i, hi⟩ := OffsetConnected.exists_encard_le hconn P
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
  obtain ⟨i, hi⟩ := OffsetConnected.exists_encard_le h P
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
