import Matroid.Connectivity.Separation

open Set

variable {α : Type*} {M : Matroid α} {j k : ℕ∞} {a b : α} {A : Set α} {P : M.Partition}

namespace Matroid.Partition

/-! ### Conditional Connectivity -/

/-- A Tutte separation is one where both sides exceed the connectivity in size -/
@[mk_iff]
structure IsTutteSeparation (P : M.Partition) : Prop where
  eConn_lt_left : P.eConn < P.left.encard
  eConn_lt_right : P.eConn < P.right.encard

lemma IsTutteSeparation.dual (hP : P.IsTutteSeparation) : P.dual.IsTutteSeparation :=
  ⟨by simpa using hP.eConn_lt_left, by simpa using hP.eConn_lt_right⟩

lemma IsTutteSeparation.of_dual {P : M✶.Partition} (hP : P.IsTutteSeparation) :
    P.ofDual.IsTutteSeparation :=
  ⟨by simpa using hP.eConn_lt_left, by simpa using hP.eConn_lt_right⟩

@[simp]
lemma IsTutteSeparation.dual_iff : P.dual.IsTutteSeparation ↔ P.IsTutteSeparation :=
  ⟨fun h ↦ ⟨by simpa using h.1, by simpa using h.2⟩, Partition.IsTutteSeparation.dual⟩

@[mk_iff]
structure IsVerticalSeparation (P : M.Partition) : Prop where
  eConn_lt_left : P.eConn < M.eRk P.left
  eConn_lt_right : P.eConn < M.eRk P.right

@[mk_iff]
structure IsInternalSeparation (P : M.Partition) : Prop where
  eConn_lt_left : P.eConn + 1 < P.left.encard
  eConn_lt_right : P.eConn + 1 < P.right.encard

lemma IsInternalSeparation.dual (hP : P.IsInternalSeparation) : P.dual.IsInternalSeparation :=
  ⟨by simpa using hP.eConn_lt_left, by simpa using hP.eConn_lt_right⟩

lemma IsInternalSeparation.of_dual {P : M✶.Partition} (hP : P.IsInternalSeparation) :
    P.ofDual.IsInternalSeparation :=
  ⟨by simpa using hP.eConn_lt_left, by simpa using hP.eConn_lt_right⟩

lemma IsInternalSeparation.IsTutteSeparation (hP : P.IsInternalSeparation) : P.IsTutteSeparation :=
  ⟨(le_self_add ..).trans_lt hP.1, (le_self_add ..).trans_lt hP.2⟩

lemma IsVerticalSeparation.IsTutteSeparation (hP : P.IsVerticalSeparation) : P.IsTutteSeparation :=
  ⟨hP.1.trans_le (M.eRk_le_encard ..), hP.2.trans_le (M.eRk_le_encard ..)⟩

@[simp]
lemma IsInternalSeparation.dual_iff : P.dual.IsInternalSeparation ↔ P.IsInternalSeparation :=
  ⟨fun h ↦ ⟨by simpa using h.1, by simpa using h.2⟩, Partition.IsInternalSeparation.dual⟩

lemma IsCircuit.isTutteSeparation {C : Set α} (hC : M.IsCircuit C) (hfin : C.Finite)
    (hcard : 2 * C.encard ≤ M.E.encard) : (M.partition C).IsTutteSeparation := by
  have hfinr : M.eRk C ≠ ⊤ := by simp [isRkFinite_of_finite _ hfin]
  simp only [Partition.isTutteSeparation_iff, eConn_partition, partition_left, partition_right]
  grw [eConn_le_eRk, ← ENat.add_one_le_iff hfinr, ← ENat.add_one_le_iff hfinr, hC.eRk_add_one_eq]
  grw [← encard_diff_add_encard_of_subset hC.subset_ground, two_mul,
    WithTop.add_le_add_iff_right (show C.encard ≠ ⊤ by simpa)] at hcard
  simp [hcard]

lemma IsCocircuit.isTutteSeparation {C : Set α} (hC : M.IsCocircuit C) (hfin : C.Finite)
    (hcard : 2 * C.encard ≤ M.E.encard) : (M.partition C).IsTutteSeparation := by
  simpa using (IsCircuit.isTutteSeparation hC hfin (by simpa)).of_dual

end Partition

/- ### Abstract Connectivity -/

/-- Every separation of `M` satisfying condition `cond` has connectivity at least `k-1`. -/
def IsPredConnected (cond : {M : Matroid α} → M.Partition → Prop) (M : Matroid α) (k : ℕ∞) : Prop :=
    ∀ ⦃P : M.Partition⦄, cond P → k ≤ P.eConn + 1

lemma IsPredConnected.mono {cond} {j k : ℕ∞} (h : IsPredConnected cond M k) (h_le : j ≤ k) :
    IsPredConnected cond M j :=
  fun _ hP ↦ h_le.trans <| h hP

lemma IsPredConnected.dual {cond} {k} (h : IsPredConnected cond M k)
    (h_cond : ∀ ⦃N : Matroid α⦄ ⦃P : N.Partition⦄, cond P → cond P.dual) :
    IsPredConnected cond M✶ k := by
  intro P hP
  rw [← P.ofDual_eConn]
  -- this is weird fighting with type theory; is there a better way to do this?
  have aux {M₀ M₁ : Matroid α} (h_eq : M₀ = M₁) {P : M₀.Partition} (hP : cond P) :
      cond (P.copy (show M₀.E = M₁.E by rw [h_eq])) := by
    subst h_eq
    convert hP
  exact h <| aux M.dual_dual <| h_cond hP

lemma IsPredConnected.ofDual {cond} {k} (h : IsPredConnected cond M✶ k)
    (h_cond : ∀ ⦃N : Matroid α⦄ ⦃P : N.Partition⦄, cond P → cond P.dual) :
    IsPredConnected cond M k := by
  simpa using h.dual h_cond

lemma IsPredConnected.mono_prop {cond cond' : {M : Matroid α} → M.Partition → Prop} {k}
    (h : IsPredConnected cond M k)
    (h_cond : ∀ ⦃M : Matroid α⦄ ⦃P : M.Partition⦄, cond' P → cond P) :
    IsPredConnected cond' M k :=
  fun _ hP ↦ h <| h_cond hP

lemma isPredConnected_two_iff (cond : {M : Matroid α} → M.Partition → Prop) :
    IsPredConnected cond M 2 ↔ ∀ (P : M.Partition), P.eConn = 0 → ¬ cond P := by
  refine ⟨fun h P hP hP' ↦ by simpa [hP] using h hP', fun h P hP ↦ ?_⟩
  have hle : 1 ≤ P.eConn := ENat.one_le_iff_ne_zero.2 <| mt (h P) (by simpa)
  rwa [← ENat.add_one_le_add_one_iff] at hle

lemma not_isPredConnected_iff (cond : {M : Matroid α} → M.Partition → Prop) :
    ¬ IsPredConnected cond M k ↔ ∃ (P : M.Partition), cond P ∧ P.eConn + 1 < k := by
  simp [IsPredConnected]

/- ### Tutte Connectivity -/

/-- Every Tutte separation has connectivity at least `k-1`. -/
def IsTutteConnected (M : Matroid α) (k : ℕ∞) : Prop :=
  IsPredConnected Partition.IsTutteSeparation M k

/-- Every vertical separation has connectivity at least `k-1`. -/
def IsVerticallyConnected (M : Matroid α) (k : ℕ∞) : Prop :=
  IsPredConnected Partition.IsVerticalSeparation M k

/-- Every internal separation, and every Tutte separation of order at most `k-2`,
 has connectivity at least `k-1` -/
def IsInternallyConnected (M : Matroid α) (k : ℕ∞) : Prop :=
    IsPredConnected (fun P ↦ P.IsInternalSeparation ∨ (P.IsTutteSeparation ∧ P.eConn + 2 ≤ k)) M k

lemma IsTutteConnected.dual (h : M.IsTutteConnected k) : M✶.IsTutteConnected k :=
  IsPredConnected.dual h fun _ _ ↦ Partition.IsTutteSeparation.dual

lemma IsTutteConnected.of_dual (h : M✶.IsTutteConnected k) : M.IsTutteConnected k := by
  simpa using h.dual

@[simp]
lemma isTutteConnected_dual_iff : M✶.IsTutteConnected k ↔ M.IsTutteConnected k :=
  ⟨IsTutteConnected.of_dual, IsTutteConnected.dual⟩

lemma isTutteConnectted_two_iff [M.Nonempty] : M.IsTutteConnected 2 ↔ M.Connected := by
  simp_rw [IsTutteConnected, isPredConnected_two_iff, Partition.eConn_eq_zero_iff_eq_disjointSum,
    Partition.isTutteSeparation_iff, not_and]
  refine ⟨fun h ↦ by_contra fun hconn ↦ ?_, fun h P hM hlt hlt' ↦ ?_⟩
  · obtain ⟨M₁, M₂, hdj, h₁, h₂, rfl⟩ := eq_disjointSum_of_not_connected hconn
    simpa [hdj.sdiff_eq_right, h₁.ground_nonempty, h₂.ground_nonempty] using
      h ((M₁.disjointSum M₂ hdj).partition M₁.E)
  rw [hM] at h
  grw [← zero_le P.eConn, encard_pos] at hlt hlt'
  refine disjointSum_not_connected ?_ ?_ _ h
  <;> simpa [← ground_nonempty_iff]

lemma not_isTutteConnected_iff : ¬ M.IsTutteConnected k ↔ ∃ (P : M.Partition) (j : ℕ),
    j + 2 ≤ k ∧ P.eConn = j ∧ j < P.left.encard ∧ j < P.right.encard := by
  simp only [IsTutteConnected, not_isPredConnected_iff, Partition.isTutteSeparation_iff,
    ← one_add_one_eq_two, ← add_assoc]
  constructor
  · rintro ⟨P, ⟨h1, h2⟩, hlt⟩
    refine ⟨P, P.eConn.toNat, ?_⟩
    rwa [ENat.coe_toNat (by intro h; simp [h] at hlt), and_iff_left h2, and_iff_left h1,
      and_iff_left rfl, ENat.add_one_le_iff (hlt.trans_le le_top).ne]
  rintro ⟨P, j, hlt, h0, h1, h2⟩
  rw [ENat.add_one_le_iff (by simp)] at hlt
  use P
  simp [h0, h1, h2, hlt]

lemma not_isTutteConnected_iff' {k : ℕ∞} : ¬ M.IsTutteConnected k ↔ ∃ (X : Set α) (j : ℕ),
    j + 2 ≤ k ∧ X ⊆ M.E ∧ M.eConn X = j ∧ j < X.encard ∧ j < (M.E \ X).encard := by
  rw [not_isTutteConnected_iff]
  constructor
  · rintro ⟨P, j, hlt, hconn, h1, h2⟩
    exact ⟨P.left, j, by norm_cast at hlt, P.left_subset_ground, by rwa [← P.eConn_eq_left], h1,
      by rwa [P.compl_left]⟩
  rintro ⟨X, j, hlt, hX, hconn, h1, h2⟩
  exact ⟨M.partition X, j, by norm_cast, by simpa, by simpa, by simpa⟩

/- ### Internal Connectivity -/

lemma IsInternallyConnected.dual (h : M.IsInternallyConnected k) : M✶.IsInternallyConnected k :=
  IsPredConnected.dual h fun N P hP ↦ by simpa

lemma IsInternallyConnected.of_dual (h : M✶.IsInternallyConnected k) :
    M.IsInternallyConnected k := by
  simpa using h.dual

lemma isInternallyConnected_dual_iff : M✶.IsInternallyConnected k ↔ M.IsInternallyConnected k :=
  ⟨IsInternallyConnected.of_dual, IsInternallyConnected.dual⟩

lemma IsTutteConnected.isInternallyConnected (hM : M.IsTutteConnected k) :
    M.IsInternallyConnected k :=
  IsPredConnected.mono_prop hM fun _ _ h ↦
    Or.elim h Partition.IsInternalSeparation.IsTutteSeparation And.left

lemma IsTutteConnected.isVerticallyConnected (hM : M.IsTutteConnected k) :
    M.IsVerticallyConnected k :=
  IsPredConnected.mono_prop hM <| fun _ _ ↦ Partition.IsVerticalSeparation.IsTutteSeparation

lemma IsInternallyConnected.IsTutteConnected (hM : M.IsInternallyConnected (k+1)) :
    M.IsTutteConnected k := by
  refine fun P hP ↦ ?_
  obtain h_le | h_lt := le_or_gt (P.eConn + 2) (k+1)
  · have h' : k ≤ P.eConn := by simpa [hP, h_le] using hM (P := P)
    exact h'.trans (by simp)
  rw [← ENat.add_one_le_add_one_iff, add_assoc, one_add_one_eq_two]
  exact h_lt.le

-- lemma isTutteConnected_deleteElem (h : M.IsTutteConnected (k + 1)) (e : α) :
--     (M ＼ {e}).IsTutteConnected k := by
--   contrapose! h
--   rw [not_isTutteConnected_iff'] at h ⊢
--   obtain ⟨X, j, hj, hXE, hX, hjX, hjX'⟩ := h



lemma isTutteConnected_delete {D : Set α} (hD : D.Finite)
    (h : M.IsTutteConnected (k + D.encard)) : (M ＼ D).IsTutteConnected k := by
  classical
  wlog hDE : D ⊆ M.E generalizing D with aux
  · rw [← delete_inter_ground_eq]
    refine aux (hD.inter_of_left M.E) (h.mono ?_) inter_subset_right
    grw [add_le_add_left]
    exact encard_le_encard inter_subset_left





  contrapose! h
  rw [not_isTutteConnected_iff'] at h ⊢
  obtain ⟨X, j, hj, hXE, hX, hjX, hjX'⟩ := h
  have hle : M.eConn (X ∪ D) ≤ ↑(j + hD.toFinset.card) := by
    have := eLocalConn_un
  refine ⟨X ∪ D, j + hD.toFinset.card, ?_, ?_, ?_, ?_⟩
  · grw [← hj, Nat.cast_add, hD.encard_eq_coe_toFinset_card, add_right_comm]
  · grw [hDE, hXE, delete_ground, union_eq_self_of_subset_left diff_subset]
  ·
  -- by_contra! hcon
  -- simp only [IsTutteConnected, exists_prop, IsPredConnected, not_forall, not_le] at hcon
  -- obtain ⟨P, hP, hPk⟩ := hcon
  -- have := h (M.partition (P.left ∪ D))
