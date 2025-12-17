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

lemma TutteConnected.InternallyConnected (h : M.TutteConnected k) : M.InternallyConnected k :=
  (tutteConnected_iff_offsetConnected'.1 h).mono fun n ↦ by simp
